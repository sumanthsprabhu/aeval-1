#ifndef AEVALSOLVER__HPP__
#define AEVALSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
using namespace expr::op::bind;
namespace ufo
{

  /** engine to solve validity of \forall-\exists formulas and synthesize Skolem relation */
  
  class AeValSolver {
  private:
    
    Expr s;
    Expr t;
    ExprSet v; // existentially quantified vars
    ExprSet sVars;
    ExprSet stVars;

    ExprMap modelInvalid;
    ExprMap separateSkols;

    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;
    
    unsigned partitioning_size;
    ExprVector projections;
    ExprVector instantiations;
    ExprVector interpolants;
    vector<ExprMap> skolMaps;
    vector<ExprMap> someEvals;
    Expr skolSkope;
    ExprSet sensitiveVars; // for compaction
    set<int> bestIndexes; // for compaction
    map<Expr, ExprVector> skolemConstraints;
    bool skol;
    bool debug;
    unsigned fresh_var_ind;
    
  public:

    AeValSolver (Expr _s, Expr _t, ExprSet &_v, bool _debug=false, bool _skol=true) :
      s(_s), t(_t), v(_v),
      efac(s->getFactory()),
      z3(efac),
      smt (z3),
      u(efac),
      fresh_var_ind(0),
      partitioning_size(0),
      skol(_skol),
      debug(_debug)
    {
      filter (boolop::land(s,t), bind::IsConst (), inserter (stVars, stVars.begin()));
      sVars = stVars;
      minusSets(stVars, v);
    }

    void splitDefs (ExprMap &m1, ExprMap &m2, int curCnt = 0)
    {
      ExprMap m3;
      ExprMap m4;
      for (auto & a : m1)
      {
        if (a.second == NULL) continue;
        if (emptyIntersect(a.second, v))
        {
          m3.insert(a);
        }
        else
        {
          m4.insert(a);
        }
      }
      if (m3.size() == curCnt)
      {
        m2 = m4;
        return;
      }
    }
    
    /**
     * Decide validity of \forall s => \exists v . t
     */
    boost::tribool solve ()
    {
      smt.reset();
      smt.assertExpr (s);
      if (!smt.solve ()) {
        if (debug) outs() << "\nE.v.: -; Iter.: 0; Result: valid\n\n";
        return false;
      }
      if (v.size () == 0)
      {
        smt.assertExpr (boolop::lneg (t));
        boost::tribool res = smt.solve ();
        if (debug) outs() << "\nE.v.: 0; Iter.: 0; Result: " << (res? "invalid" : "valid") << "\n\n";
        return res;
      }
      
      smt.push ();
      smt.assertExpr (t);
      
      boost::tribool res = true;
      
      while (smt.solve ())
      {
        if (debug) {
          outs() << ".";
          outs().flush ();
        }
        ZSolver<EZ3>::Model m = smt.getModel();

        if (debug)
        {
          outs() << "\nmodel " << partitioning_size << ":\n";
          for (auto &exp: stVars)
          {
            if (exp != m.eval(exp))
              outs() << "[" << *exp << "=" << *m.eval(exp) << "],";
          }
          outs() <<"\n";
        }

        getMBPandSkolem(m);

        smt.pop();
        smt.assertExpr(boolop::lneg(projections[partitioning_size++]));
        if (!smt.solve()) { res = false; break; }

        smt.push();
        smt.assertExpr (t);
      }
      
      if (debug) outs() << "\nE.v.: " << v.size() << "; Iter.: " << partitioning_size
             << "; Result: " << (res? "invalid" : "valid") << "\n\n";
      
      return res;
    }
    
    /**
     * Extract MBP and local Skolem
     */
    void getMBPandSkolem(ZSolver<EZ3>::Model &m)
    {
      Expr pr = t;
      ExprMap substsMap;
      ExprMap modelMap;
      for (auto &exp: v)
      {
        ExprMap map;
        ExprSet lits;
        u.getTrueLiterals(pr, m, lits, false);
        pr = z3_qe_model_project_skolem (z3, m, exp, conjoin(lits, efac), map);
        if (m.eval(exp) != exp) modelMap[exp] = mk<EQ>(exp, m.eval(exp));
        for (auto it = lits.begin(); it != lits.end(); ){
          if (contains(*it, exp)) ++it;
          else it = lits.erase(it);
        }
        substsMap[exp] = conjoin(lits, efac);
      }
      
      someEvals.push_back(modelMap);
      skolMaps.push_back(substsMap);
      projections.push_back(pr);
      partitioning_size++;
    }

    
    /**
     * Valid Subset of S (if overall AE-formula is invalid)
     */
    Expr getValidSubset(bool compact = true)
    {
      if (partitioning_size == 0){
        if (debug) outs() << "WARNING: Trivial valid subset (equal to False) due to 0 iterations\n";
        return mk<FALSE>(efac);
      }

      Expr prs;
      if (compact)
      {
        ExprSet all;
        vector<ExprSet> pprs;

        for (auto & a : projections)
        {
          ExprSet tmp;
          getConj(a, tmp);
          pprs.push_back(tmp);
          all.insert(tmp.begin(), tmp.end());
        }

        ExprSet common;

        for (auto & a : all)
        {
          bool everywhere = true;
          vector<ExprSet> pprsTmp = pprs;
          for (auto & p : pprsTmp)
          {
            bool found = false;
            for (auto it = p.begin(); it != p.end(); ++it)
            {
              if (*it == a) {
                found = true;
                p.erase(it);
                break;
              }
            }
            if (!found)
            {
              everywhere = false;
              break;
            }
          }
          if (everywhere)
          {
            pprs = pprsTmp;
            if (!isOpX<TRUE>(a)) common.insert(a);
          }
        }

        ExprSet cnjs;
        for (auto & p : pprs)
        {
          cnjs.insert(conjoin(p, efac));
        }

        if (!cnjs.empty())
        {
          Expr tmp = simplifyBool(disjoin(cnjs, efac));
          if (!isOpX<TRUE>(tmp)) common.insert(tmp);
        }
        prs = conjoin(common, efac);
      }
      else
      {
        prs = disjoin(projections, efac);
      }
      return simplifyBool(mk<AND>(s, prs));
    }
    
    /**
     * Self explanatory
     */
    void GetSymbolicMax(ExprVector vec, Expr& curMax)
    {
      curMax = vec[0];
      for (int i = 1; i < vec.size(); i++){
        if (u.isEquiv(mk<LT>(curMax, vec[i]), mk<TRUE>(efac))){
          curMax = vec[i];
        } else if (u.isEquiv(mk<LT>(curMax, vec[i]), mk<FALSE>(efac))){
          //  curMax is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);
          string varName = "_aeval_tmp_max_" + ind;
          Expr realVarName = mkTerm (varName, efac);
          Expr realVar = bind::realConst(realVarName);

          skolSkope = simplifiedAnd(skolSkope,
                          mk<EQ>(realVar, mk<ITE>(mk<LT>(curMax, vec[i]), vec[i], curMax)));
          curMax = realVar;
        }
      }
    }
    
    /**
     * Self explanatory
     */
    void GetSymbolicMin(ExprVector vec, Expr& curMin)
    {
      curMin = vec[0];
      for (int i = 1; i < vec.size(); i++){
        if (u.isEquiv(mk<GT>(curMin, vec[i]), mk<TRUE>(efac))){
          curMin = vec[i];
        } else if (u.isEquiv(mk<GT>(curMin, vec[i]), mk<FALSE>(efac))){
          //  curMin is OK
        } else {
          Expr eqRhs;
          string ind = lexical_cast<string> (fresh_var_ind++);
          string varName = "_aeval_tmp_min_" + ind;
          Expr realVarName = mkTerm (varName, efac);
          Expr realVar = bind::realConst(realVarName);
          eqRhs = mk<ITE>(mk<GT>(curMin, vec[i]), vec[i], curMin);
          skolSkope = simplifiedAnd(skolSkope, mk<EQ>(realVar, eqRhs));
          curMin = realVar;
        }
      }
    }
    
    /**
     * Weird thing, never happens in the experiments
     */
    void GetSymbolicNeg(ExprVector vec, Expr& lower, Expr& upper, Expr& candidate)
    {
      // TODO: maybe buggy in LIA, due to a naive shrinking of the segment;
      
      for (int i = 0; i < vec.size(); i++){

        ExprVector forLower;
        forLower.push_back(lower);
        forLower.push_back(vec[i]);
        Expr updLower;
        GetSymbolicMax(forLower, updLower);
      
        ExprVector forUpper;
        forUpper.push_back(upper);
        forUpper.push_back(vec[i]);
        Expr updUpper;
        GetSymbolicMin(forUpper, updUpper);

        // TODO: do optimizations

        // first, try to see if there are any concrete values for updLower and updUpper
        if (updLower == updUpper) {
          upper = updUpper;
        }
        else if (upper != updUpper) {
          // second, force the symbolic value for upper
          upper = mk<ITE> (mk<EQ>(updLower, updUpper), updUpper, upper);
        }

        candidate = mk<DIV>(mk<PLUS>(lower, upper), mkTerm (mpq_class (2), efac));
      }
    }
    
    /**
     * Aux
     */
    void pushVecRedund(ExprVector& vec, Expr a)
    {
      bool tmp = true;
      for (auto& b: vec){
        if (a == b) {
          tmp = false;
        } else if (lexical_cast<string>(a) == lexical_cast<string>(b)){
          tmp = false;
        }
      }
      if (tmp) vec.push_back(a);
    }
    
    /**
     * Based on type
     */
    Expr getDefaultAssignment(Expr var)
    {
      if (bind::isBoolConst(var)) return mk<TRUE>(efac);
      if (bind::isIntConst(var)) return mkMPZ(0, efac);
      else           // that is, isRealConst(var) == true
        return mkTerm (mpq_class (0), efac);
    }
    
    /**
     * Return "e + c"
     */
    Expr getPlusConst(Expr e, bool isInt, cpp_int c)
    {
      if (isOpX<MPZ>(e) && isInt)
        return mkMPZ(c + boost::lexical_cast<cpp_int> (e), efac);
      
      Expr ce = isInt ? mkMPZ(c, efac) :
                        mkTerm (mpq_class (lexical_cast<string>(c)), efac);
      return mk<PLUS>(e, ce);
    }
    
    /**
     * Extract function from relation
     */
    Expr getAssignmentForVar(Expr var, Expr exp)
    {
      if (debug)
      {
        outs () << "getAssignmentForVar " << *var << " in:\n";
        pprint(exp);
      }

      if (isOpX<TRUE>(exp))
      {
        return getDefaultAssignment(var);
      }
      if (!isNumeric(var))
      {
        ExprSet cnjs;
        getConj(exp, cnjs);
        for (auto & c : cnjs)
        {
          if (isOpX<EQ>(c))
          {
            if (var == c->left()) return c->right();
            if (var == c->right()) return c->left();
          }
          if (isBoolean(var))
          {
            if (c == var)
              return mk<TRUE>(efac);
            if (isOpX<NEG>(c) && c->left() == var)
              return mk<FALSE>(efac);
            if (isOpX<EQ>(c))
            {
              if (mk<NEG>(var) == c->left()) return mkNeg(c->right());
              if (mk<NEG>(var) == c->right()) return mkNeg(c->left());
            }
          }
        }
        assert(0);
      }

      bool isInt = bind::isIntConst(var);
      
      if (isOp<ComparissonOp>(exp))
      {
        // TODO: write a similar simplifier fo booleans
        if (!bind::isBoolConst(var) && var != exp->left())
          exp = ineqMover(exp, var);

        if (var != exp->left()) exp = ineqReverter(exp);

        assert (var == exp->left());

        if (isOpX<EQ>(exp) || isOpX<GEQ>(exp) || isOpX<LEQ>(exp)){
          if (exp->left() == exp->right()) return getDefaultAssignment(var);
          return exp->right();
        }
        else if (isOpX<LT>(exp)){
          return getPlusConst (exp->right(), isInt, -1);
        }
        else if (isOpX<GT>(exp)){
          return getPlusConst (exp->right(), isInt, 1);
        }
        else if (isOpX<NEQ>(exp)){
          return getPlusConst (exp->right(), isInt, 1);
        }
        else assert(0);
      }
      else if (isOpX<NEG>(exp)){
        if (isOpX<EQ>(exp->left())) {
          return getPlusConst (getAssignmentForVar(var, exp->left()), isInt, 1);
        }
      }
      else if (isOpX<AND>(exp)){

        exp = u.numericUnderapprox(exp); // try to see if there are only numerals

        if (isOpX<EQ>(exp)) return exp->right();

        bool incomplete = false;

        // split constraints

        ExprVector conjLT;
        ExprVector conjGT;
        ExprVector conjNEG;
        ExprVector conjEG;
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it){
          if (isOpX<EQ>(*it)){
            if (var == (*it)->left()) {
              pushVecRedund(conjEG, (*it)->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LT>(*it) || isOpX<LEQ>(*it)){
            if (var == (*it)->left()) {
              pushVecRedund(conjLT, (*it)->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GT>(*it) || isOpX<GEQ>(*it)){
            if (var == (*it)->left()) {
              pushVecRedund(conjGT, (*it)->right());
            } else {
              incomplete = true;
            }
          } else if (isOpX<NEG>(*it)){
            Expr negated = (*it)->left();
            
            if (isOpX<EQ>(negated)){
              
              if (var == negated->left()) {
                pushVecRedund(conjNEG, negated->right());
              } else {
                incomplete = true;
              }
            }
          }
        }

        // get the assignment (if exists)

        if (conjEG.size() > 0) return *(conjEG.begin()); // GF: maybe try to find the best of them

        if (incomplete) outs() << "WARNING: Some Skolem constraints unsupported\n";

        // get symbolic max and min

        Expr extraDefsMax = mk<TRUE>(efac);
        Expr curMax;
        if (conjGT.size() > 1){
          GetSymbolicMax(conjGT, curMax);
        } else if (conjGT.size() == 1){
          curMax = conjGT[0];
        }

        Expr extraDefsMin = mk<TRUE>(efac);
        Expr curMin;

        if (conjLT.size() > 1){
          GetSymbolicMin(conjLT, curMin);
        } else if (conjLT.size() == 1){
          curMin = conjLT[0];
        }

        // get value in the middle of max and min

        if (conjNEG.size() == 0){
          if (conjLT.size() > 0 && conjGT.size() > 0){
            return mk<DIV>(mk<PLUS>(curMin, curMax), mkTerm (mpq_class (2), efac));
          } else {
            if (conjLT.size() == 0){
              return getPlusConst (curMax, isInt, 1);
            } else {
              return getPlusConst (curMin, isInt, -1);
            }
          }
        }

        // here and later, we get conjNEG.size() > 0

        if (conjLT.size() > 0 && conjGT.size() == 0) {
          conjNEG.push_back(curMin);
          GetSymbolicMin(conjNEG, curMin);
          return getPlusConst (curMin, isInt, -1);
        }

        if (conjLT.size() == 0 && conjGT.size() > 0) {
          conjNEG.push_back(curMax);
          GetSymbolicMax(conjNEG, curMax);
          return getPlusConst (curMax, isInt, 1);
        }

        if (conjLT.size() == 0 && conjGT.size() == 0) {
          GetSymbolicMax(conjNEG, curMax);
          return getPlusConst (curMax, isInt, 1);
        }

        // now, both conjLT and conjGT are non-empty
        Expr curMid;
        GetSymbolicNeg(conjNEG, curMax, curMin, curMid);
        return curMid;
      }
      return exp;
    }
  
    /**
     * Check if there are bounded cycles (at most lvl steps) in the map
     */
    bool findCycles(ExprMap &m, Expr var, Expr var2, int lvl=3)
    {
      Expr entr = m[var];
      if (entr == NULL) return false;

      ExprSet all;
      filter (entr, bind::IsConst (), inserter (all, all.begin()));
      
      if (!emptyIntersect(var2, all)) return true;
      
      bool res = false;
      if (lvl > 0) for (auto& exp: all) res |= findCycles(m, exp, var2, lvl-1);
      
      return res;
    }
    
    /**
     * Actually, just print it to cmd in the smt-lib2 format
     */
    void serialize_formula(Expr form)
    {
      smt.reset();
      smt.assertExpr(form);
      
      string errorInfo;
      
      if (errorInfo.empty ()) {
        smt.toSmtLib (outs());
        outs().flush ();
      }
    }

    /**
     * Model of S /\ \neg T (if AE-formula is invalid)
     */
    void printModelNeg()
    {
      outs () << "(model\n";
      Expr witn = mk<IMPL>(s, t);
      for (auto &var : sVars){
        Expr assnmt = var == modelInvalid[var] ? getDefaultAssignment(var) : modelInvalid[var];
        if (debug)
          witn = replaceAll(witn, var, assnmt);

        outs () << "  (define-fun " << *var << " () " <<
          (bind::isBoolConst(var) ? "Bool" : (bind::isIntConst(var) ? "Int" : "Real"))
                << "\n    " << *assnmt << ")\n";
      }
      outs () << ")\n";

      if (debug){
        outs () << "Sanity check [model]: " << (bool)u.isFalse(witn) << "\n";
      }
    }

    Expr getSeparateSkol (Expr v) { return separateSkols [v]; }
    
    int getPartitioningSize() { return partitioning_size; }
    
    void searchDownwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchDownwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      if (indexes.empty()) return;

      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        return;
      }
      else
      {
        Expr subs = ae.getValidSubset(false);
        if (isOpX<FALSE>(subs))
        {
//          for (int j : indexes)
//          {
//            set<int> indexes2 = indexes;
//            indexes2.erase(j);
//            searchDownwards(indexes2, var, skol);
//          }
          return;
        }
        else
        {
          bool erased = false;

          for (auto i = indexes.begin(); i != indexes.end();)
          {
            if (!u.implies(subs, projections[*i]))
            {
              i = indexes.erase(i);
              erased = true;
            }
            else
            {
              ++i;
            }
          }
          if (erased)
          {
            searchDownwards(indexes, var, skol);
          }
          else
          {
            for (int j : indexes)
            {
              set<int> indexes2 = indexes;
              indexes2.erase(j);
              searchDownwards(indexes2, var, skol);
            }
          }
        }
      }
    }

    void searchUpwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchUpwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (find (indexes.begin(), indexes.end(), i) != indexes.end()) continue;
          set<int> indexes2 = indexes;
          indexes2.insert(i);
          searchUpwards(indexes2, var, skol);
        }
        return;
      }
    }
    
    void breakCyclicSubsts(ExprMap& cyclicSubsts, ExprMap& evals, ExprMap& substsMap)
    {
      if (cyclicSubsts.empty()) return;

      map<Expr, int> tmp;
      for (auto & a : cyclicSubsts)
      {
        ExprSet vars;
        filter (a.second, bind::IsConst (), inserter (vars, vars.begin()));
        for (auto & b : vars)
        {
          if (find(v.begin(), v.end(), b) != v.end())
            tmp[b]++;
        }
      }

      int min = 0;
      Expr a;
      for (auto & b : tmp)
      {
        if (b.second >= min)
        {
          min = b.second;
          a = b.first;
        }
      }

      for (auto b = cyclicSubsts.begin(); b != cyclicSubsts.end(); b++)
        if (b->first == a)
        {
          substsMap[a] = evals[a]->right();
          cyclicSubsts.erase(b); break;
        }

      substsMap.insert (cyclicSubsts.begin(), cyclicSubsts.end());
      splitDefs(substsMap, cyclicSubsts);
      breakCyclicSubsts(cyclicSubsts, evals, substsMap);
    }
    
    Expr combineAssignments(ExprMap& allAssms, ExprMap& evals)
    {
      ExprSet skolTmp;
      ExprMap cyclicSubsts;
      splitDefs(allAssms, cyclicSubsts);

      breakCyclicSubsts(cyclicSubsts, evals, allAssms);
      assert (cyclicSubsts.empty());
      for (auto & a : sensitiveVars)
      {
        assert (emptyIntersect(allAssms[a], v));
        skolTmp.insert(mk<EQ>(a, allAssms[a]));
      }
      return conjoin(skolTmp, efac);
    }

    Expr getSkolemFunction (bool compact = false)
    {
      if (partitioning_size == 0)
        return mk<TRUE>(efac);

      ExprSet skolUncond;
      ExprSet eligibleVars;
      skolemConstraints.clear(); // GF: just in case

      // GF: to clean further
      for (auto &var: v)
      {
        bool elig = compact;
        if (elig) eligibleVars.insert(var);
        else sensitiveVars.insert(var);
      }

      for (auto & a : v)
      {
        ExprVector t;
        for (int i = 0; i < partitioning_size; i++)
        {
          assert(skolMaps[i][a] != NULL);
          t.push_back(skolMaps[i][a]); // should be on i-th position
        }
        skolemConstraints[a] = t;
      }

      map<Expr, set<int>> inds;
      ExprMap sameAssms;
      for (auto & var : eligibleVars)
      {
        bool same = true;
        auto & a = skolemConstraints[var];
        for (int i = 1; i < partitioning_size; i++)
        {
          if (a[0] != a[i])
          {
            same = false;
            break;
          }
        }
        if (same)
        {
          sameAssms[var] = getAssignmentForVar(var, a[0]);
          Expr skol = mk<EQ>(var, sameAssms[var]);
          skolUncond.insert(skol);
          separateSkols [var] = sameAssms[var];
        }
        else
        {
          sensitiveVars.insert(var);
        }
      }

      for (auto & var : sensitiveVars)
      {
        bestIndexes.clear();
        if (find(eligibleVars.begin(), eligibleVars.end(), var) != eligibleVars.end()
            && compact)
        {
          set<int> indexes;
          for (int i = 0; i < partitioning_size; i++) indexes.insert(i);
          searchDownwards (indexes, var, skolemConstraints[var]);
          searchUpwards (bestIndexes, var, skolemConstraints[var]);
        }
        inds[var] = bestIndexes;
      }

      Expr skol;
      ExprSet skolTmp;
      if (sensitiveVars.size() > 0)
      {
        set<int> intersect;
        for (int i = 0; i < partitioning_size; i ++)
        {
          int found = true;
          for (auto & a : inds)
          {
            if (find (a.second.begin(), a.second.end(), i) == a.second.end())
            {
              found = false;
              break;
            }
          }
          if (found) intersect.insert(i);
        }

        if (intersect.size() <= 1)
        {
          int maxSz = 0;
          int largestPre = 0;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
            if (curSz > maxSz)
            {
              maxSz = curSz;
              largestPre = i;
            }
          }
          intersect.clear();
          intersect.insert(largestPre);
        }

        ExprMap allAssms = sameAssms;
        for (auto & a : sensitiveVars)
        {
          ExprSet cnjs;
          for (int b : intersect) getConj(skolemConstraints[a][b], cnjs);
          Expr def = getAssignmentForVar(a, conjoin(cnjs, efac));
          allAssms[a] = def;
        }
        Expr bigSkol = combineAssignments(allAssms, someEvals[*intersect.begin()]);

        for (auto & evar : v)
        {
          Expr newSkol;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
          }
        }

        for (int i = 0; i < partitioning_size; i++)
        {
          allAssms = sameAssms;
          if (find(intersect.begin(), intersect.end(), i) == intersect.end())
          {
            for (auto & a : sensitiveVars)
            {
              Expr def = getAssignmentForVar(a, skolemConstraints[a][i]);
              allAssms[a] = def;
            }
            bigSkol = mk<ITE>(projections[i], combineAssignments(allAssms, someEvals[i]), bigSkol);
            if (compact) bigSkol = u.simplifyITE(bigSkol);
          }
        }

        for (auto & a : sensitiveVars) separateSkols [a] = projectITE (bigSkol, a);

        skolUncond.insert(bigSkol);
      }
      return conjoin(skolUncond, efac);
    }


  };

  /**
   * Simple wrapper
   */
  template<typename Range> static Expr eliminateQuantifiers(Expr cond, Range& vars, bool strict = false)
  {
    ExprFactory &efac = cond->getFactory();
    SMTUtils u(efac);
    if (vars.size() == 0) return simplifyBool(cond);
    Expr newCond = simplifyArithm(simpleQE(cond, vars));

    if (!emptyIntersect(newCond, vars) &&
        !containsOp<FORALL>(cond) && !containsOp<EXISTS>(cond) && !isNonlinear(newCond))
    {
      ExprSet v;
      v.insert(vars.begin(), vars.end());
      AeValSolver ae(mk<TRUE>(efac), newCond, v); // exists quantified . formula
      if (ae.solve()) {
        newCond = ae.getValidSubset();
      } else {
        return mk<TRUE>(efac);
      }
    }
    
    ExprSet cnj;
    getConj(newCond, cnj);
    ineqMerger(cnj, true);

    if (strict) return (conjoin(cnj, efac));

    for (auto it = cnj.begin(); it != cnj.end(); )
    {
      ExprVector av;
      filter (*it, bind::IsConst (), inserter(av, av.begin()));
      map<Expr, ExprVector> qv;
      getQVars (*it, qv);
      for (auto & a : qv)
        for (auto & b : a.second)
          for (auto it1 = av.begin(); it1 != av.end(); )
            if (*it1 == b) { it1 = av.erase(it1); break; }
            else ++it1;

      if (emptyIntersect(av, vars)) ++it;
        else it = cnj.erase(it);
    }
    return (conjoin(cnj, efac));
  }

  inline void aeSolveAndSkolemize(Expr s, Expr t, bool skol, bool debug, bool opt, bool compact, bool split)
  {
    ExprSet fa_qvars, ex_qvars;
    ExprFactory& efac = s->getFactory();
    SMTUtils u(efac);
    if (t == NULL)
    {
      if (!(isOpX<FORALL>(s) && isOpX<EXISTS>(s->last()))) exit(0);
      s = regularizeQF(s);
      t = s->last()->last();
      for (int i = 0; i < s->last()->arity() - 1; i++)
        ex_qvars.insert(bind::fapp(s->last()->arg(i)));
      for (int i = 0; i < s->arity() - 1; i++)
        fa_qvars.insert(bind::fapp(s->arg(i)));

      s = mk<TRUE>(efac);
    }
    else
    {
      filter (s, bind::IsConst (), inserter (fa_qvars, fa_qvars.begin()));
      filter (t, bind::IsConst (), inserter (ex_qvars, ex_qvars.begin()));
      minusSets(ex_qvars, fa_qvars);
    }
        s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    Expr t_orig = t;
    if (opt)
    {
      ExprSet cnjs;
      getConj(t, cnjs);
      constantPropagation(fa_qvars, cnjs, true);
      // t = simpEquivClasses(fa_qvars, cnjs, efac);
      t = conjoin(cnjs, efac);
      t = simpleQE(t, ex_qvars);
      t = simplifyBool(t);
    }

    AeValSolver ae(s, t, ex_qvars, debug, skol);

    if (ae.solve()){
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
      ae.printModelNeg();
      outs() << "\nvalid subset:\n";
      u.serialize_formula(simplifyBool(simplifyArithm(ae.getValidSubset(compact))));
    } else {
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
      if (skol)
      {
        Expr skol = ae.getSkolemFunction(compact);
        if (split)
        {
          ExprVector sepSkols;
          for (auto & evar : ex_qvars) sepSkols.push_back(mk<EQ>(evar,
                           simplifyBool(simplifyArithm(ae.getSeparateSkol(evar)))));
          u.serialize_formula(sepSkols);
          if (debug) outs () << "Sanity check [split]: " <<
            (bool)(u.implies(mk<AND>(s, conjoin(sepSkols, s->getFactory())), t_orig)) << "\n";
        }
        else
        {
          outs() << "\nextracted skolem:\n";
          u.serialize_formula(simplifyBool(simplifyArithm(skol)));
          if (debug) outs () << "Sanity check: " << (bool)(u.implies(mk<AND>(s, skol), t_orig)) << "\n";
        }
      }
    }
  }

  static Expr eliminateQuantifiers(Expr cond, Expr var, bool strict = false)
  {
    ExprSet vars;
    vars.insert(var);
    return eliminateQuantifiers(cond, vars, strict);
  }

  template<typename Range> static Expr eliminateQuantifiersRepl(Expr cond, Range& vars, bool strict = false)
  {
    ExprFactory &efac = cond->getFactory();
    SMTUtils u(efac);
    ExprSet complex;
    findComplexNumerics(cond, complex);
    ExprMap repls;
    ExprMap replsRev;
    ExprSet varsCond; varsCond.insert(vars.begin(), vars.end());
    for (auto & a : complex)
    {
      Expr repl = bind::intConst(mkTerm<string>
            ("__repl_" + lexical_cast<string>(repls.size()), efac));
      repls[a] = repl;
      replsRev[repl] = a;
      if (!emptyIntersect(a, vars)) varsCond.insert(repl);
    }
    Expr condTmp = replaceAll(cond, repls);

    Expr tmp = eliminateQuantifiers(condTmp, varsCond, strict);
    tmp = replaceAll(tmp, replsRev);
    return tmp;
  }

  static Expr abduce (Expr goal, Expr assm)
  {
    ExprFactory &efac = goal->getFactory();
    SMTUtils u(efac);
    ExprSet complex;
    findComplexNumerics(assm, complex);
    findComplexNumerics(goal, complex);
    ExprMap repls;
    ExprMap replsRev;
    for (auto & a : complex)
    {
      Expr repl = bind::intConst(mkTerm<string>
            ("__repl_" + lexical_cast<string>(repls.size()), efac));
      repls[a] = repl;
      replsRev[repl] = a;
    }
    Expr goalTmp = replaceAll(goal, repls);
    Expr assmTmp = replaceAll(assm, repls);

    ExprSet varsGoal;
    filter (goalTmp, bind::IsConst (), inserter(varsGoal, varsGoal.begin()));

    Expr tmp = mkNeg(eliminateQuantifiers(mkNeg(mk<IMPL>(assmTmp, goalTmp)), varsGoal));
    tmp = replaceAll(tmp, replsRev);

    if (u.isFalse(mk<AND>(tmp, assm)))
    {
      outs () << "abduction unsuccessful\n";
      return NULL; // abduction unsuccessful
    }

    // sanity check:
    if (!u.implies(mk<AND>(tmp, assm), goal))
    {
      errs () << "WARNING: abduction fail: "<< * mk<AND>(tmp, assm) << "   does not imply " << *goal << "\n";
      return NULL;
    }
    return tmp;
  }
}

#endif
