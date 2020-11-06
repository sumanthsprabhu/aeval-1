#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"

#include <fstream>
#include <chrono>

using namespace std;
using namespace boost;

namespace ufo
{
  static void getCombinations(vector<vector<int>>& in, vector<vector<int>>& out, int pos = 0)
  {
    if (pos == 0) out.push_back(vector<int>());
    if (pos == in.size()) return;

    vector<vector<int>> out2;

    for (auto & a : in[pos])
    {
      for (auto & b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};
  
  class NonlinCHCsolver
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;
    bool hasArrays = false;
    ExprSet declsVisited;
    map<HornRuleExt*, vector<ExprVector>> abdHistory;
    int globalIter = 0;
    int strenBound;
    bool debug = false;
    map<Expr, Expr> extend;
    ExprVector fixedRels;

    public:

    NonlinCHCsolver (CHCs& r, int _b) : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b) {}

    bool checkAllOver (bool checkQuery = false)
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        if (!checkCHC(hr, candidates)) return false;
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        Expr rel = hr.srcRelations[i];
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        checkList.insert(disjoin(negged, m_efac));
      }
      return bool(!u.isSat(checkList));
    }

    void shrinkCnjs(ExprSet & cnjs)
    {
      ExprSet shrunk;
      ExprSet cnjsTmp = cnjs;
      for (auto c1 = cnjsTmp.begin(); c1 != cnjsTmp.end(); ++c1)
      {
        if (isOpX<OR>(*c1)) continue;
        for (auto c2 = cnjs.begin(); c2 != cnjs.end();)
        {
          if (!isOpX<OR>(*c2)) { ++c2; continue; };
          ExprSet dsjs;
          ExprSet newDsjs;
          getDisj(*c2, dsjs);
          for (auto & d : dsjs)
            if (u.isSat(*c1, d))
              newDsjs.insert(d);
          shrunk.insert(disjoin(newDsjs, m_efac));
          c2 = cnjs.erase(c2);
          cnjs.insert(disjoin(newDsjs, m_efac));
        }
        cnjs.insert(shrunk.begin(), shrunk.end());
        shrunk.clear();
      }
    }

    void preproGuessing(Expr e, ExprVector& ev1, ExprVector& ev2, ExprSet& guesses, bool backward = false, bool mutate = true)
    {
      if (!containsOp<FORALL>(e)) e = rewriteSelectStore(e);
      ExprSet complex;
      findComplexNumerics(e, complex);
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(ev1.begin(), ev1.end(), *it) != ev1.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, ev1);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = eliminateQuantifiers(eTmp, ev3);
      if (backward) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(simplifyArithm(eTmp, false, true));

      ExprSet tmp;

      if (mutate)
        mutateHeuristic(eTmp, tmp);
      else
        getConj(eTmp, tmp);

      for (auto g : tmp)
      {
        g = replaceAll (g, replsRev);
        if (!ev2.empty())
          g = replaceAll(g, ev1, ev2);
        guesses.insert(g);
      }
    }

    bool isFixedRel(const Expr & rel)
    {
      return find(fixedRels.begin(), fixedRels.end(), rel) != fixedRels.end(); 
    }

    void addFixedRel(Expr rel)
    {
      fixedRels.push_back(rel);
    }
    
    // search for a CHC having the form r1 /\ .. /\ rn => rel, where rel \not\in {r1, .., rn}
    bool hasNoDef(Expr rel)
    {
      for (auto & hr : ruleManager.chcs)
        if (hr.dstRelation == rel &&
          find (hr.srcRelations.begin(), hr.srcRelations.end(), rel) == hr.srcRelations.end())
            return false;
      return true;
    }

    // lightweight (non-inductive) candidate propagation both ways
    // subsumes bootstrapping (ssince facts and queries are considered)
    void propagate(bool fwd = true)
    {
      // outs() << "Entry\n";//DEBUG
      // printCands(false);//DEBUG
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
	// outs() << "hrd: " << *(hr.dstRelation) << "\n";//DEBUG
	
        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
	bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation) && extend.find(hr.dstRelation) == extend.end());
	bool dstFixed = isFixedRel(hr.dstRelation);
	
	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG
	
        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG
        if (fwd && srcVisited && !dstVisited && !dstFixed)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
	// printCands(false);//DEBUG

      }

      if (declsVisited.size() != szInit) propagate(fwd);
      // outs() << "Exit\n";//DEBUG
      // printCands(false);//DEBUG

    }

    void propagateCandidatesForward(HornRuleExt& hr)
    {
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery) return;

        Expr body = getQuantifiedCands(true, hr);

        ExprSet all;
        all.insert(body);
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          if (!hasArrays) // we need "clean" invariants in the case of arrays (to be used as ranges)
          {
            // currently, tries all candidates; but in principle, should try various subsets
            for (auto & c : candidates[rel])
              all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars[i]));
          }
        }

	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "before: " << *c << "\n";
	
        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);


        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "after: " << *c << "\n";

      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr, bool forceConv = false)
    {
      // outs() << "in backward\n";//DEBUG
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isFact) return;

        Expr dstRel = hr.dstRelation;
        ExprVector& rels = hr.srcRelations;

        ExprVector invVars;
        ExprVector srcVars;

        // identifying nonlinear cases (i.e., when size(occursNum[...]) > 1)
        map<Expr, set<int>> occursNum;
        for (int i = 0; i < rels.size(); i++)
        {
          occursNum[rels[i]].insert(i);
          for (int j = i+1; j < rels.size(); j++)
            if (rels[i] == rels[j])
              occursNum[rels[i]].insert(j);
        }

        for (int i = 0; i < hr.srcVars.size(); i++)
          srcVars.insert(srcVars.end(), hr.srcVars[i].begin(), hr.srcVars[i].end());

        if (hr.srcVars.size() == 1) invVars = ruleManager.invVars[rels[0]];

        ExprSet cands;
        if (hr.isQuery)
        {
          if (getQuantifiedCands(false, hr) == NULL) return;
          else cands.insert(mk<FALSE>(m_efac));
        }
        else cands.insert(simplifyBool(conjoin(candidates[dstRel], m_efac)));

        ExprSet mixedCands;
        ExprVector curCnd;

        for (int i = 0; i < rels.size(); i++)
        {
          ExprSet tmp;
          getConj(replaceAll(conjoin(candidates[rels[i]], m_efac),
                             ruleManager.invVars[rels[i]], hr.srcVars[i]), tmp);
          curCnd.push_back(conjoin(tmp, m_efac));
        }

        // actually, just a single candidate, in the most recent setting;
        // TODO: remove the loop (or find use of it)
        for (auto & c : cands)
        {
          ExprSet all, newCnd;
          all.insert(hr.body);
          all.insert(mkNeg(replaceAll(c, ruleManager.invVars[dstRel], hr.dstVars)));
          all.insert(curCnd.begin(), curCnd.end());

          // TODO: add more sophisticated blocking based on unseccussful tries from abdHistory

          preproGuessing(conjoin(all, m_efac), srcVars, invVars, newCnd, true, false);

          if (!(u.isSat(conjoin(curCnd, m_efac), conjoin(newCnd, m_efac))))
          {
            // simple heuristic: find if some current guess was already created by abduction
            // then, delete it and try again
            if (!hr.isInductive)
              for (auto & t : abdHistory[&hr])
                for (int j = 0; j < t.size(); j++)
                  if (u.implies(conjoin(candidates[rels[j]], m_efac), t[j]))
                    candidates[rels[j]].clear();
            continue;
          }

          // oftentimes, newCnd is a disjunction that can be simplified
          // by considering other candidates in curCnd
          ExprSet tmp, tmp2;
          for (auto c : newCnd) getConj(c, tmp);
          for (auto c : curCnd) getConj(c, tmp);
          shrinkCnjs(tmp);
          getConj(conjoin(tmp, m_efac), tmp2);
          ineqMerger(tmp2, true);
          simplifyPropagate(tmp2);
          Expr stren = simplifyArithm(conjoin(tmp2, m_efac));
          mixedCands.insert(stren);
        }

        if (hr.srcVars.size() == 1)
        {
	  if (!isFixedRel(rels[0])) {
	    if (forceConv) forceConvergence(candidates[rels[0]], mixedCands);
	    for (auto & m : mixedCands) getConj(m, candidates[rels[0]]);
	  }
        }
        else
        {
          // decomposition here
          // fairness heuristic: prioritize candidates for all relations, which are true
          // TODO: find a way to disable it if for some reason some invariant should only be true
          vector<bool> trueCands;
          ExprSet trueRels;
          int numTrueCands = 0;
          for (int i = 0; i < rels.size(); i++)
          {
            trueCands.push_back(u.isTrue(curCnd[i]));
            if (trueCands.back())
            {
              trueRels.insert(rels[i]);
              numTrueCands++;
            }
          }

          // numTrueCands = 0;       // GF: hack to disable fairness

          ExprSet allGuessesInit;
          if (numTrueCands > 0)      // at least one curCnd should be true
            for (int i = 0; i < rels.size(); i++)
              if (!trueCands[i])
                allGuessesInit.insert(curCnd[i]);

          // actually, just a single candidate, in the most recent setting;
          // TODO: remove the loop (or find use of it)
          for (auto it = mixedCands.begin(); it != mixedCands.end(); )
          {
            if (containsOp<ARRAY_TY>(*it)) { ++it; continue; }
            Expr a = *it;
            ExprSet processed;
            ExprSet allGuesses = allGuessesInit;
            ExprVector histRec;

            auto candidatesTmp = candidates;

            for (int i = 0; i < rels.size(); i++)
            {
              // skip the relation if it already has a candidate and there exists a relation with no candidate
              // (existing candidates are already in allGuesses)
              if (numTrueCands > 0 && !trueCands[i]) continue;

	      if (isFixedRel(rels[i])) continue;

              Expr r = rels[i];

	      
	      // Expr modelphi = conjoin(curCnd, m_efac);

	      // if (rels.size() == 1) {
	      // 	if (extend.find(r) != extend.end()) {
	      // 	  modelphi = mk<AND>(modelphi, replaceAll(extend[r], ruleManager.invVars[r], hr.srcVars[i]));
	      // 	}
	      // } else {
	      // 	for (int j = i+1; j < rels.size(); j++) {
	      // 	  if (extend.find(rels[j]) != extend.end()) {
	      // 	    modelphi = mk<AND>(modelphi, replaceAll(extend[rels[j]], ruleManager.invVars[rels[j]], hr.srcVars[j]));
	      // 	  }
	      // 	}
	      // }

	      if (!u.isSat(a, conjoin(curCnd, m_efac))) return; // need to recheck because the solver has been reset
		
              if (processed.find(r) != processed.end()) continue;

              invVars.clear();
              ExprSet backGuesses, allVarsExcept;
              ExprVector vars;
              for (int j = 0; j < rels.size(); j++)
              {
                Expr t = rels[j];
                if (processed.find(t) != processed.end()) continue;
                if (t == r)
                {
                  vars.insert(vars.begin(), hr.srcVars[j].begin(), hr.srcVars[j].end());
                  if (occursNum[r].size() == 1) invVars = ruleManager.invVars[rels[j]];
                }
                else
                  allVarsExcept.insert(hr.srcVars[j].begin(), hr.srcVars[j].end());
              }

              // model-based cartesian decomposition
              ExprSet all = allGuesses;
              all.insert(mkNeg(a));

              if (trueRels.size() != 1)                  // again, for fairness heuristic:
                all.insert(u.getModel(allVarsExcept));

	      // outs() << "truerels.size: " << trueRels.size() << "\n";//DEBUG
	      // outs() << "model: " << *(u.getModel(allVarsExcept)) << "\n";//DEBUG
	      //DEBUG
	      // for (auto v : allVarsExcept)
	      // 	outs() << "allvarsexcept: " << *v << "\n";
	      // for (auto a : all)
		// outs() << "all: " << *a << "\n";//DEBUG
	      
              // in the case of nonlin, invVars is empty, so no renaming happens:

              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                getConj(conjoin(backGuesses, m_efac), candidates[r]);
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
		//DEBUG
		// for (auto ag : allGuesses)
		//   outs() << "AG: " << *ag << "\n";
              }
              else
              {
                // nonlinear case; proceed to isomorphic decomposition for each candidate
                map<int, ExprVector> multiabdVars;

                for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                  for (auto & v : ruleManager.invVars[r])
                    multiabdVars[*it2].push_back(
                      cloneVar(v, mkTerm<string> (
                        "__multiabd_var" + lexical_cast<string>(*v) + "_" + to_string(*it2), m_efac)));

                Expr b = conjoin(backGuesses, m_efac);
                {
                  ExprSet sol;
                  int iter = 0;
                  while (++iter < 10 /*hardcode*/)
                  {
                    // preps for obtaining a new model

                    ExprSet cnj;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                    {
                      ExprSet dsj;
                      if (!sol.empty())
                        dsj.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      for (auto it3 = occursNum[r].begin(); it3 != occursNum[r].end(); ++it3)
                      {
                        ExprSet modelCnj;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          modelCnj.insert(mk<EQ>(hr.srcVars[*it2][i], multiabdVars[*it3][i]));
                        dsj.insert(conjoin(modelCnj, m_efac));
                      }
                      cnj.insert(disjoin(dsj, m_efac));
                    }

                    // obtaining a new model
                    ExprVector args;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      for (auto & v : hr.srcVars[*it2])
                        args.push_back(v->left());
                    args.push_back(mk<IMPL>(conjoin(cnj, m_efac), b));

                    ExprSet negModels;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      negModels.insert(mkNeg(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], multiabdVars[*it2])));

                    if (!u.isSat(extend.find(r) != extend.end() ? mk<AND>(extend[r], mknary<FORALL>(args)) : mknary<FORALL>(args),
				 sol.empty() ? mk<TRUE>(m_efac) : disjoin(negModels, m_efac)))
                    {
                      candidates[r].insert(sol.begin(), sol.end());
                      histRec.push_back(conjoin(sol, m_efac));
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                        allGuesses.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      break;
                    }
                    else
                    {
                      ExprSet models;
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      {
                        ExprSet elements;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          elements.insert(mk<EQ>(ruleManager.invVars[r][i], u.getModel(multiabdVars[*it2][i])));
                        models.insert(conjoin(elements, m_efac));
                      }
                      sol.insert (disjoin(models, m_efac)); // weakening sol by a new model
                    }

                    // heuristic to accelerate convergence
                    ExprVector chk;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      chk.push_back(replaceAll(disjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                    sol.clear();
                    for (auto it1 = occursNum[r].begin(); it1 != occursNum[r].end(); ++it1)
                    {
                      int cnt = 0;
                      for (auto it3 = occursNum[r].begin(); it3 != it1; ++it3, ++cnt)
                        chk[cnt] = replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it3]);
                      chk[cnt] = mk<TRUE>(m_efac);

                      ExprSet allNonlin;
                      allNonlin.insert(mkNeg(b));
                      allNonlin.insert(conjoin(chk, m_efac));
                      preproGuessing(conjoin(allNonlin, m_efac), hr.srcVars[*it1], ruleManager.invVars[r], sol, true, false);
                    }
                    u.removeRedundantConjuncts(sol);
                  }
                }
              }
              processed.insert(r);
            }

            // fairness heuristic (need to be tested properly):
            {
              bool tryAgain = false;
              if (!abdHistory[&hr].empty() && equivVecs(abdHistory[&hr].back(), histRec))
              {
                candidates = candidatesTmp;

                for (int i = 0; i < histRec.size(); i++)
                {
                  if (u.isEquiv(curCnd[i], histRec[i]))
                  {
                    numTrueCands++;
                    trueCands[i] = true;
                    trueRels.insert(rels[i]);
                  }
                  else
                  {
                    trueCands[i] = false;
                    allGuessesInit.insert(curCnd[i]);
                  }
                }
                tryAgain = true; // to keep
              }

              abdHistory[&hr].push_back(histRec);

              if (tryAgain)
              {
                if (abdHistory[&hr].size() > 5 /*hardcoded bound*/)
                {
                  tryAgain = false;
                  for (int i = 0; i < 5 /*hardcoded bound*/; i++)
                    if (abdHistory[&hr][abdHistory[&hr].size() - 1 - i] != histRec)
                    {
                      tryAgain = true;
                      break;
                    }
                }
              }

              if (!tryAgain) ++it;
            }
//            outs () << "sanity check: " << u.implies(conjoin(allGuesses, m_efac), a) << "\n";
          }
        }
      }
    }

    // inductive strengthening of candidates (by abduction)
    void strengthen(int deep = 0)
    {
      if (deep >= strenBound) return;

      // currently, relies on the order in CHC file; TBD: proper backwards traversing
      for (auto hr = ruleManager.chcs.rbegin(); hr != ruleManager.chcs.rend(); hr++)
      {
        if (!hr->isFact)
        {
          filterUnsat();
          if (!checkCHC(*hr, candidates))
          {
	    // outs() << "in strengthen before\n";//DEBUG
	     // printCands(false);//DEBUG
            propagateCandidatesBackward(*hr, deep == strenBound - 1);
	    // outs() << "in strengthen after\n";//DEBUG
	    // printCands(false);//DEBUG
            strengthen(deep+1);
          }
        }
      }
    }

    void forceConvergence (ExprSet& prev, ExprSet& next)
    {
      if (prev.size() < 1 || next.size() < 1) return;
      ExprFactory& efac = (*next.begin())->getFactory();

      ExprSet prevSplit, nextSplit, prevSplitDisj, nextSplitDisj, common;

      for (auto & a : prev) getConj (a, prevSplit);
      for (auto & a : next) getConj (a, nextSplit);

      mergeDiseqs(prevSplit);
      mergeDiseqs(nextSplit);

      if (prevSplit.size() != 1 || nextSplit.size() != 1)
        return; // GF: to extend

      getDisj(*prevSplit.begin(), prevSplitDisj);
      getDisj(*nextSplit.begin(), nextSplitDisj);

      for (auto & a : prevSplitDisj)
        for (auto & b : nextSplitDisj)
          if (a == b) common.insert(a);

      if (common.empty()) return;
      next.clear();
      next.insert(disjoin(common, efac));
    }

    bool equivVecs (ExprVector e1, ExprVector e2)
    {
      if (e1.size() != e2.size()) return false;
      for (int i = 0; i < e1.size(); i++)
      {
        if (!u.isEquiv(e1[i], e2[i])) return false;
      }
      return true;
    }

    void getImplicationGuesses(map<Expr, ExprSet>& postconds)
    {
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs)
      {
        if (r.isQuery) continue;

        int srcRelInd = -1;
        Expr rel = r.head->left();

	if (isFixedRel(rel)) continue;
	
        for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == rel) srcRelInd = i;
        if (srcRelInd >= 0)
          preproGuessing(r.body, r.srcVars[srcRelInd], ruleManager.invVars[rel], preconds[rel]);

        if (srcRelInd == -1) continue;
        int tot = 0;
        for (auto guess : postconds[rel])
        {
          if (tot > 5) break; // empirically chosen bound
          if (isOpX<IMPL>(guess) || isOpX<OR>(guess)) continue; // hack

          for (auto & pre : preconds[rel])
          {
            if (u.implies(pre, guess)) continue;
            tot++;
            Expr newGuess = mk<IMPL>(pre, guess);
            ExprVector tmp;
            tmp.push_back(replaceAll(newGuess, ruleManager.invVars[rel], r.srcVars[srcRelInd]));
            tmp.push_back(r.body);
            // simple invariant check (for speed, need to be enhanced)
            if (u.implies (conjoin(tmp, m_efac), replaceAll(newGuess, ruleManager.invVars[rel], r.dstVars)))
            {
              candidates[rel].insert(newGuess);
              ExprSet newPost;
              tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[rel], r.dstVars)));
              preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[rel], newPost);
              for (auto & a : newPost)
                candidates[rel].insert(mk<IMPL>(mk<NEG>(pre), a));
            }
          }
        }
      }
    }

    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false)
    {
      printCands(unsat, partialsolns, nonmaximal, simplify, outs());
    }

    template <typename OutputStream>
    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false, OutputStream & out = outs())
    {
      if (unsat)
      {
	out << "unsat";
	if (nonmaximal)
	  out << " (may not be maximal solution) \n";
	else
	  out << "\n";
      }

      for (auto & a : partialsolns.empty() ? candidates : partialsolns)
      {
        out << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          out << "(" << *b << " " << u.varType(b) << ")";
        }
        out << ") Bool\n  ";

        ExprSet lms = a.second;
        Expr sol = conjoin(lms, m_efac);

        // sanity checks:
        ExprSet allVars;
        filter (sol, bind::IsConst (), inserter (allVars, allVars.begin()));
        minusSets(allVars, ruleManager.invVars[a.first]);
        map<Expr, ExprVector> qv;
        getQVars (sol, qv);
        for (auto & q : qv) minusSets(allVars, q.second);
        assert (allVars.empty());
//        if (!u.isSat(sol)) assert(0);

        Expr res = simplifyBool(simplifyArithm(sol));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        u.print(res, out);
        out << ")\n";
      }
    }

    bool dropUnsat(map<Expr, ExprSet>& annotations, const ExprVector & unsatCore, const map<Expr, pair<Expr, Expr>> & flagToCand)
    {
      for (auto & c : unsatCore) {
	auto entry = flagToCand.find(c);
	if (entry == flagToCand.end()) continue;
	Expr rel = (entry->second).first;
	Expr cand = (entry->second).second;
	annotations[rel].erase(cand);
	return true;
      }

      return false;
    }
    
    /* vacuity check based on SAT check */
    void vacCheck(map<Expr, ExprSet>& annotations)
    {
      bool recurse = false;

      for (auto & hr : ruleManager.chcs) {

	if(hr.isFact) continue;
	
	ExprVector flags;
	ExprSet finalExpr;
	map<Expr, pair<Expr, Expr>> flagToCand;
	bool hasArray = false;

	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr rel = hr.srcRelations[i];
	  if (isFixedRel(rel)) {
	    for (auto cand : annotations[rel]) {
	      cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);
	      finalExpr.insert(cand);
	    }	    
	  } else {
	    for (auto cand : annotations[rel]) {
	      if (!hasArray && containsOp<FORALL>(cand))
		hasArray = true;	    
	      Expr flag = bind::boolConst(mkTerm<string>("__unsatcoreVar__" + to_string(flags.size()+1), m_efac));
	      flags.push_back(flag);
	      flagToCand[flag] = make_pair(rel, cand);
	      cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);	    
	      finalExpr.insert(mk<IMPL>(flag, cand));
	    }
	  }
	}

	if (!hr.isQuery && u.isSat(hr.body)) {
	  finalExpr.insert(hr.body);
	}

	// outs() << "BODY: " << *(hr.body) << "\n";
	// for (auto f : finalExpr)
	//   outs() << *f << "\n";

	if (!hasArray) {
	  ExprVector unsatCore;
	  if (!u.isSatAssuming(finalExpr, flags, std::back_inserter(unsatCore))) {
	    // outs() << "failed hr: " << *(hr.body) << "\n";
	    // outs() << "flags: " << flags.size() << "\n";
	    // outs() << "unsatcore: " << unsatCore.size() << "\n";
	    assert(dropUnsat(annotations, unsatCore, flagToCand));
	    recurse = true;
	  }
	} else {
	  if (!u.isSat(finalExpr)) {
	    ExprVector t1;
	    ExprVector t2;
	    u.splitUnsatSets(finalExpr, t1, t2);
	    for (int i = 0; i < hr.srcRelations.size(); i++) {
	      Expr rel = hr.srcRelations[i];
	      
	      for (auto itr =  annotations[rel].begin(); itr != annotations[rel].end();) {
		Expr c = replaceAll(*itr, hr.srcVars[i], ruleManager.invVars[rel]);
		if (find(t1.begin(), t1.end(), c) == t1.end()) {
		  itr = annotations[rel].erase(itr);
		} else {
		  ++itr;
		}
	      }
	      
	    }
	    recurse = true;
	  }
	}
	
	if (recurse)
	  return vacCheck(annotations);
      }	 	

    }


    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second)) {
	  assert(!isFixedRel(a.first));
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact) worklist.push_back(&hr);
	}

      multiHoudini(worklist, false);

      for (auto & a : candidates)
      {
        if (!u.isSat(a.second))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          u.splitUnsatSets(a.second, tmp, stub);
          a.second.clear();
          a.second.insert(tmp.begin(), tmp.end());
        }
      }

      vacCheck(candidates);
      
      return true;
    }

    
    Expr getQuantifiedCands(bool fwd, HornRuleExt& hr)
    {
      ExprSet qVars;
      Expr body = hr.body;
      if (fwd && hr.isFact)
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())  // immediately try proving properties if already quantified
        {
          // make sure that we can use it as a property (i.e., variables check)

          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          bool allGood = true;
          for (auto & v : allVars)
            if (find (hr.dstVars.begin(), hr.dstVars.end(), v) == hr.dstVars.end())
              { allGood = false; break; }
          if (allGood)
          {
            ExprSet tmpSet;
            getQuantifiedFormulas(hr.body, tmpSet);
            for (auto c : tmpSet)
            {
              // over-approximate the body such that it can pass through the seed mining etc..
              body = replaceAll(body, c, mk<TRUE>(m_efac));
              c = replaceAll(c, hr.dstVars, ruleManager.invVars[hr.dstRelation]);
              candidates[hr.dstRelation].insert(c);
            }
          }
        }
      }
      if (!fwd && hr.isQuery)  // similar for the query
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())
        {
          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            bool toCont = false;
            for (auto & v : allVars)
              if (find (hr.srcVars[i].begin(), hr.srcVars[i].end(), v) == hr.srcVars[i].end())
                { toCont = true; break; }
            if (toCont) continue;
            getQuantifiedFormulas(mkNeg(hr.body), candidates[hr.srcRelations[i]]);
          }
          return NULL; // just as an indicator that everything went well
        }
      }
      return body;
    }

    bool isSkippable(Expr model, ExprVector vars, map<Expr, ExprSet>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
        for (auto & b : a.second)
          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;

	
	if (isFixedRel(hr->dstRelation)) continue;
	
        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (isSkippable(model, hr->dstVars, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) { it = candidatesTmp[dstRel].erase(it); res2 = false; }
              else ++it;
            }
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist)
          if (find(hr->srcRelations.begin(), hr->srcRelations.end(), a.first) !=
              hr->srcRelations.end() || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    // only one level of propagation here; to be extended
    void arrayGuessing(Expr tgt)
    {
      bool arrFound = false;
      for (auto & var : ruleManager.invVars[tgt])
        if (bind::isConst<ARRAY_TY> (var)) {
          arrFound = true;
          break;
        }
      if (!arrFound) return;

      int ind;
      bool iterGrows;
      Expr iterator;
      Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
      Expr range;
      HornRuleExt *hr = 0;
      HornRuleExt *qr = 0;

      // preprocessing
      for (auto & a : ruleManager.chcs)
      {
        if (a.isQuery && a.srcRelations[0] == tgt /*hack for now*/ &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
          qr = &a;
        if (a.isInductive && a.dstRelation == tgt &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
        {
          ExprVector counters;
          hr = &a;

          getCounters(a.body, counters);
          for (Expr c : counters)
          {
            ind = getVarIndex(c, a.srcVars[0] /*hack for now*/);
            if (ind < 0) continue;

            if (u.implies(a.body, mk<GT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = false;
              break;
            }
            else if (u.implies(a.body, mk<LT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = true;
            }
          }
        }
      }

      if (iterator == NULL) return;

      // range computation
      for (auto & a : ruleManager.chcs)
      {
        if (!a.isInductive && a.dstRelation == tgt)
        {
          int max_sz = INT_MAX;
          for (Expr e : candidates[tgt])
          {
            if ((iterGrows &&
               ((isOpX<GEQ>(e) && iterator == e->left()) ||
                (isOpX<LEQ>(e) && iterator == e->right()))) ||
               (!iterGrows &&
                 ((isOpX<GEQ>(e) && iterator == e->right()) ||
                  (isOpX<LEQ>(e) && iterator == e->left()))))
            {
              Expr bound = (e->left() == iterator) ? e->right() : e->left();
              if (treeSize(bound) < max_sz)
              {
                range = iterGrows ? mk<AND>(mk<LEQ>(bound, qVar), mk<LT>(qVar, iterator)) :
                                    mk<AND>(mk<LT>(iterator, qVar), mk<LEQ>(qVar, bound));
                max_sz = treeSize(bound);
              }
            }
          }
        }
      }

      if (range == NULL) return;

      // cell property guessing
      Expr body = hr->body;
      body = unfoldITE(body);
      body = rewriteSelectStore(body);
      ExprSet tmp;
      ExprVector qVars1, qVars2;
      for (int i = 0; i < hr->dstVars.size(); i++)
      {
        if (ruleManager.invVars[hr->srcRelations[0]][i] == iterator)
        {
          qVars1.push_back(hr->dstVars[i]);
          qVars2.push_back(iterator);
        }
        else
        {
          qVars1.push_back(ruleManager.invVars[hr->srcRelations[0]][i]);
          qVars2.push_back(hr->dstVars[i]);
        }
      }
      body = simpleQE(body, qVars1);

      preproGuessing(body, qVars2, ruleManager.invVars[hr->srcRelations[0]], tmp);

      for (auto s : tmp)
      {
        if (!containsOp<SELECT>(s)) continue;
        s = replaceAll(s, iterator, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], hr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
        {
          candidates[tgt].insert(newGuess);
          // try to propagate (only one level now; TODO: extend)
          for (auto & hr2 : ruleManager.chcs)
          {
            if (hr2.isQuery) continue;
            if (find(hr2.srcRelations.begin(), hr2.srcRelations.end(), tgt) != hr2.srcRelations.end() &&
                hr2.dstRelation != tgt)
            {
              ExprSet cnjs;
              getConj(hr2.body, cnjs);
              Expr newRange;
              for (auto c : cnjs)
              {
                if (emptyIntersect(c, iterator)) continue;
                if (isOpX<NEG>(c)) c = mkNeg(c->left());
                c = ineqSimplifier(iterator, c);
                if (!isOp<ComparissonOp>(c)) continue;

                if (isOpX<EQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<PLUS>(c->right(), mkTerm (mpz_class (1), m_efac)));
                if (!iterGrows && isOpX<LEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (!iterGrows && isOpX<LT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<MINUS>(c->right(), mkTerm (mpz_class (1), m_efac)));

                if (newRange != NULL) break;
              }

              if (newRange == NULL) continue;

              ExprVector args;
              args.push_back(qVar->left());
              args.push_back(mk<IMPL>(newRange, s));
              Expr newCand = getForallCnj(
                    simpleQE(
                        mk<AND>(hr2.body,mknary<FORALL>(args)), hr2.srcVars[0]));

              newCand = replaceAll(newCand, hr2.dstVars, ruleManager.invVars[hr2.dstRelation]);
              // finally, try the propagated guess:
              candidates[hr2.dstRelation].insert(newCand);
            }
          }
        }
      }

      if (qr == 0) return;

      tmp.clear();
      getArrIneqs(mkNeg(qr->body), tmp);

      for (auto s : tmp)
      {
        ExprSet allv;
        filter (s, bind::IsConst (), inserter (allv, allv.begin()));
        for (auto & a : allv)
          if (bind::typeOf(a) == bind::typeOf(qVar) && find(hr->srcVars[0].begin(), hr->srcVars[0].end(), a) ==
              hr->srcVars[0].end()) s = replaceAll(s, a, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], qr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
          candidates[tgt].insert(newGuess);
      }
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    Result_t guessAndSolve()
    {
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }

      while (true)
      {
        auto candidatesTmp = candidates;
        for (bool fwd : { false, true })
        {
          if (debug)
          {
            outs () << "iter " << globalIter << "." << fwd << "\nCurrent candidates:\n";
            printCands(false);
          }
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
	  // outs() << "1st\n";//DEBUG
	  // printCands(false);//DEBUG
	  // outs() << "fwd: " << fwd << "\n";//DEBUG
	  propagate(fwd);
          filterUnsat();
	  // outs() << "2nd\n";//DEBUG
	  // printCands(false);//DEBUG
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
	  filterUnsat();
	  // outs() << "3rd\n";//DEBUG
	  // printCands(false);//DEBUG
          if (checkAllOver(true)) return Result_t::UNSAT;
        }
        if (equalCands(candidatesTmp)) break;
        if (hasArrays) break; // just one iteration is enough for arrays (for speed)
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      for (auto tgt : ruleManager.decls) arrayGuessing(tgt->left());
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    ExprVector getRels(const vector<string> & relsStr)
    {

      ExprVector rels;

      for (auto rs : relsStr) 
	for (auto d : ruleManager.decls) 
	  if (lexical_cast<string>(*bind::fname(d)) == rs)
	    rels.push_back(d->left());
	
      return rels;      
    }

    void sanitizeForDump(string & in)
    {
      in.erase(remove(in.begin(), in.end(), '_'), in.end());
      in.erase(remove(in.begin(), in.end(), '|'), in.end());

      map<char,char> substmap;
      // substmap['_'] = 'U';
      // substmap['|'] = 'B';
      substmap['\''] = 'P';
      substmap['$'] = 'D';
      substmap[':'] = 'C';
      substmap[';'] = 'c';
      
      for (size_t i = 0; i < in.size(); i++) {
	auto subst = substmap.find(in[i]);
	if (subst != substmap.end()) {
	  in[i] = subst->second;
	}
      }      
      // std::replace(in.begin(), in.end(), '\'', 'p');
      // std::replace(in.begin(), in.end(), '$', 'D');
      // std::replace(in.begin(), in.end(), ':', 'C');
    }

    void printAllVarsRels(const ExprSet & allVars, stringstream & decls)
    {
      for (auto v : allVars) {
	decls << "(declare-var " << *v << " " << u.varType(v) << ")\n";
      }

      for (auto d : ruleManager.decls) {
	if (d == ruleManager.failDecl) continue;
	decls << "(declare-rel " << *bind::fname(d) << " (";
        for (unsigned i = 0; i < bind::domainSz(d); i++)
        {
          Expr ty = bind::domainTy(d, i);
          if (isOpX<BOOL_TY>(ty)) decls << "Bool ";
          else if (isOpX<REAL_TY>(ty)) decls << "Real ";
          else if (isOpX<INT_TY>(ty)) decls << "Int ";
	  else decls << "UnSupportedSort";
	}
	decls << ")) \n";	
      }
    }


    string dumpToFile(stringstream & decls, stringstream & rules, string oldsmt = "", string postfix = "")
    {
      if (oldsmt.size() == 0) {
	oldsmt = ruleManager.infile;
      }
      
      string newsmt = oldsmt.substr(oldsmt.find_last_of("/"));
      newsmt = "/tmp/" + newsmt.substr(0, newsmt.find_last_of("."));
      newsmt += postfix + "_" + to_string(std::chrono::system_clock::now().time_since_epoch().count());
      newsmt += ".smt2";
      
      string ds = decls.str();
      string rs = rules.str();
      
      sanitizeForDump(ds);
      sanitizeForDump(rs);

      ofstream newsmtFile(newsmt);      
      newsmtFile << ds << "\n" << rs << "\n";
      newsmtFile.close();

      return newsmt;
    }

    // Adds two new rules in addition to the rules present in 'oldsmt': 
    // 1) candidate[rel](invVars[rel]) => rel(invVars[rel])
    // 2) ~candidate[rel](invVars[rel]) /\ tmprel(invVars[rel]) => rel(invVars[rel])
    // returns the name of the file where new rules are present 
    string constructMaximalRules(const Expr & rel, const string & oldsmt, const bool firstCall)
    {
      bool addWeakRules = !(firstCall && candidates[rel].size() == 0);
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = isOpX<FALSE>(ruleManager.failDecl) ? "fail" : lexical_cast<string>(ruleManager.failDecl);

      for (auto & hr : ruleManager.chcs)
      {
	for (int i = 0; i < hr.srcVars.size(); i++) {
	  allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
	}
	allVars.insert(hr.locVars.begin(), hr.locVars.end());
	allVars.insert(hr.dstVars.begin(), hr.dstVars.end());
	

	ExprSet antec;
	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr src = hr.srcRelations[i];
	  if (isFixedRel(src)){
	    Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
	    antec.insert(t);
	    
	  } else {
	    for (auto d : ruleManager.decls)
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
		Expr t = bind::fapp(d, hr.srcVars[i]);
		antec.insert(t);
		break;
	      }
	  }
	}

	antec.insert(hr.body);
	Expr conseq;
	bool addFail = false;
	
	if (isFixedRel(hr.dstRelation)) {
	  antec.insert(mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars)));
	  addFail = true;
	} else {
	  if (hr.isQuery) {
	    addFail = true;
	  } else {
	    for (auto d : ruleManager.decls)
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
		conseq = bind::fapp(d, hr.dstVars);
		break;
	      }	    
	  }
	}
	
	if (addFail) {
	  newRules << "(rule (=> ";
	  u.print(conjoin(antec, m_efac), newRules);
	  newRules << " " << queryRelStr << "))\n";
	} else {
	  newRules << "(rule ";
	  u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
	  newRules << ")\n";
	}
	//debug
	outs() << newRules.str();
      }

      printAllVarsRels(allVars, newDecls);
      
      newDecls << "(declare-rel " << queryRelStr << "())\n";

      if (addWeakRules) {
	const string tmpRelName = "tmprel";
      
	newDecls << "(declare-rel " << tmpRelName << " (";
	for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
	  newDecls << " " << u.varType(*itr);
	}
	newDecls << "))\n";	
      
	//candidate[rel] => rel
	newRules << "(rule (=> ";
	u.print(conjoin(candidates[rel], m_efac), newRules);
	newRules << "( " << *rel;
	for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
	  if (itr != ruleManager.invVars[rel].begin())
	    newRules << " ";
	  newRules << " " << *itr;
	}
	newRules << ")))\n";

	//~candidate[rel] /\ tmprel => rel
	newRules << "(rule (=> (and ";
	u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
	newRules << "( " << tmpRelName;
	for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
	  if (itr != ruleManager.invVars[rel].begin())
	    newRules << " ";
	  newRules << " " << *itr;
	}
	newRules << ")) ( " << *rel;
	for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
	  if (itr != ruleManager.invVars[rel].begin())
	    newRules << " ";
	  newRules << " " << *itr;
	}
	newRules << ")))\n";
      }
      
      newRules << "(query " << queryRelStr << ")\n";

      string newsmt = dumpToFile(newDecls, newRules, oldsmt);
      
      return newsmt;
    }


    void getOrCombinations(const vector<ExprVector> & clauses, int curRL, int curBT, ExprVector & curOutput, vector<ExprSet> & output)
    {
      if (curRL == clauses.size()) {
	output.push_back(ExprSet());
	ExprSet& cjs = output.back();
	for (auto co : curOutput) 
	  cjs.insert(co);
	curOutput.pop_back();
	return;
      }
      
      if (curBT == clauses[curRL].size()) {
	if (curOutput.size() > 0)
	  curOutput.pop_back();
	return;
      }
      
      curOutput.push_back(clauses[curRL][curBT]);
      
      getOrCombinations(clauses, curRL+1, 0, curOutput, output);
      getOrCombinations(clauses, curRL, curBT+1, curOutput, output);
    }
    
    string constructMaximalRulesV2(const Expr & rel, const string & oldsmt)
    {
      assert(candidates[rel].size() != 0);

      Expr curcand = conjoin(candidates[rel], m_efac);
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = isOpX<FALSE>(ruleManager.failDecl) ? "fail" : lexical_cast<string>(ruleManager.failDecl);

      Expr reld;
      
      for (auto d : ruleManager.decls) {
	if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*rel)) {
	  reld = d;
	  break;
	}
      }    

      
      for (auto & hr : ruleManager.chcs)
      {
	for (int i = 0; i < hr.srcVars.size(); i++) {
	  allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
	}
	allVars.insert(hr.locVars.begin(), hr.locVars.end());
	allVars.insert(hr.dstVars.begin(), hr.dstVars.end());
	

	vector<ExprVector> clauses;	
	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr src = hr.srcRelations[i];
	  ExprVector clause;
	  if (rel == src) {
	    clause.push_back(replaceAll(curcand, ruleManager.invVars[src], hr.srcVars[i]));
	    clause.push_back(bind::fapp(reld, hr.srcVars[i]));
	    
	  } else if (isFixedRel(src)){
	    Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
	    clause.push_back(t);
	    
	  } else {
	    for (auto d : ruleManager.decls) {
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
		Expr t = bind::fapp(d, hr.srcVars[i]);
		clause.push_back(t);
		break;
	      }
	    }
	  }
	  clauses.push_back(clause);
	}
	clauses.push_back(ExprVector{hr.body});

	if (hr.dstRelation == rel) {
	  clauses.push_back(ExprVector{mk<NEG>(replaceAll(curcand, ruleManager.invVars[rel], hr.dstVars))});
	}
	
	vector<ExprSet> antecs;
	ExprVector tmpOutput;
	getOrCombinations(clauses, 0, 0, tmpOutput, antecs);

	for (auto antecItr = antecs.begin(); antecItr != antecs.end();)
	{
	  if (!u.isSat(*antecItr)) {
	    antecItr = antecs.erase(antecItr);
	  } else {
	    antecItr++;
	  }
	}
	  
	Expr conseq;
	bool addFail = false;


	if (isFixedRel(hr.dstRelation)) {
	  conseq = mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars));
	  addFail = true;
	} else {	  
	  if (hr.isQuery) {
	    addFail = true;
	    conseq = mk<TRUE>(m_efac);
	  } else {
	    for (auto d : ruleManager.decls) {
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
		conseq = bind::fapp(d, hr.dstVars);
		break;
	      }
	    }
	  }
	}

	for (auto antec : antecs) {
	  if (addFail) {
	    newRules << "(rule (=> ";
	    u.print(mk<AND>(conjoin(antec, m_efac), conseq), newRules);
	    newRules << " " << queryRelStr << "))\n";	    
	  } else {
	    newRules << "(rule ";
	    u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
	    newRules << ")\n";	    
	  }
	}

	//debug
	outs() << newRules.str();
      }

      printAllVarsRels(allVars, newDecls);
      
      newDecls << "(declare-rel " << queryRelStr << "())\n";

      Expr relApp = bind::fapp(reld, ruleManager.invVars[rel]);
      
      newRules << "(rule (=> ";
      u.print(mk<AND>(relApp, curcand), newRules);
      newRules << " " << queryRelStr << "))\n";	    
            
      newRules << "(query " << queryRelStr << ")\n";

      string newchc = dumpToFile(newDecls, newRules, oldsmt);
      
      return newchc;
    }

    
    //runs solveIncrementally on the file with a new object and returns the result of it
    Result_t checkCex(const Expr & rel, const string & newsmt)
    {
      // string newSmt = constructMaximalRules(rel, smt);
      
      ExprFactory nm_efac;
      EZ3 nz3(nm_efac);
      CHCs nrm(nm_efac, nz3);
      nrm.parse(newsmt);
      NonlinCHCsolver newNonlin(nrm, 1);
      ExprVector query;
      query.push_back(nrm.failDecl);
      vector<ExprVector> empt;

      return newNonlin.solveIncrementally(14, 0, query, empt);
    }

    Result_t checkZ3()
    {
      ExprVector ucRels = ruleManager.getUnderConsRels();
      ExprVector asserts;
      
      for (auto hr : ruleManager.chcs) {
	ExprVector existsArgs;
	bool vacChkAdd = true;
	
	for (auto ucr : ucRels) {

	  if (vacChkAdd && find(hr.srcRelations.begin(), hr.srcRelations.end(), ucr) != hr.srcRelations.end()) {

	    vacChkAdd = false;
	    
	    for (int i = 0; i < hr.srcVars.size(); i++) {
	      for (auto v : hr.srcVars[i])
		existsArgs.push_back(v->left());
	    }
	    
	    ExprVector matrix;
	    for (int i = 0; i < hr.srcRelations.size(); i++) {
	      Expr src = hr.srcRelations[i];
	      for (auto d : ruleManager.decls)
		if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src))
		  matrix.push_back(bind::fapp(d, hr.srcVars[i]));
	    }
	    
	    if (!hr.isQuery) {
	      matrix.push_back(hr.body);
	    }

	    existsArgs.push_back(conjoin(matrix, m_efac));
	  }
	}
  
	
	if (existsArgs.size() > 0) {
	  asserts.push_back(mknary<EXISTS>(existsArgs));
	}

	ExprVector forallArgs;
	
	for (int i = 0; i < hr.srcVars.size(); i++) {
	  for (auto v : hr.srcVars[i])
	    forallArgs.push_back(v->left());
	}
	
	for (auto v : hr.dstVars)
	  forallArgs.push_back(v->left());
	

	ExprVector antec;	

	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr src = hr.srcRelations[i];
	  for (auto d : ruleManager.decls)
	    if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src))
	      antec.push_back(bind::fapp(d, hr.srcVars[i]));
	}

	if (hr.isQuery) {
	  forallArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), mk<NEG>(hr.body)));
	  
	} else {
	  antec.push_back(hr.body);
	  
	  for (auto d : ruleManager.decls)
	    if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation)))
	      forallArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), bind::fapp(d, hr.dstVars)));
	}

	asserts.push_back(mknary<FORALL>(forallArgs));		
      }

      //DEBUG
      for (auto a : asserts) {
      	u.print(a);
      	outs() << "\n";
      }
      
      boost::tribool res = u.isSat(asserts);

      if (boost::logic::indeterminate(res)) {
	return Result_t::UNKNOWN;
	
      } else if (!res) {
	return Result_t::SAT;
	
      } else {
	u.printModel();
	return Result_t::UNSAT;
      }
      
    }


    void getCurSoln(map<Expr, ExprSet> & soln, const ExprVector & rels, map<Expr, ExprVector> & invVars)
    {
      for (auto r : rels) {
	soln[r].clear();
	for (auto e : candidates) {
	  if (lexical_cast<string>(*r) == lexical_cast<string>(*(e.first))) {
	    for (auto c : e.second) {
	      soln[r].insert(replaceAll(c, ruleManager.invVars[e.first], invVars[r]));
	    }
	  }
	}
      }
    }

    Result_t getWeakerSoln(const Expr & rel, const ExprVector & rels, const string & newsmt, map<Expr, ExprSet> & soln)
    {
            
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newsmt);
      NonlinCHCsolver newNonlin(nrm, 1);
      ExprVector query;

      Result_t res = newNonlin.guessAndSolve();

      assert(res != Result_t::SAT);


      if (res == Result_t::UNSAT) {
	newNonlin.getCurSoln(soln, rels, ruleManager.invVars);   
	return Result_t::SAT;	
      }
      
      return Result_t::UNKNOWN;      
    }


    
    // chc solver based weaker solution synthesis
    Result_t checkMaximalCHC(const Expr & rel, Expr & betterSoln, bool firstCall, bool newenc = false, bool update=true)
    {
      if (!firstCall && u.isTrue(conjoin(candidates[rel], m_efac))) {
	return Result_t::UNSAT;
      }

      
      string newsmt;
      
      if (firstCall || !newenc) {
      	newsmt = constructMaximalRules(rel, ruleManager.infile, firstCall);
      } else {
      	newsmt = constructMaximalRulesV2(rel, ruleManager.infile);
      }


      //solveIncrementally() isn't working :(
      // Result_t cexRes = checkCex(rel, newsmt);

      // if (cexRes == Result_t::SAT) {
      // 	outs() << "CHC proved us\n";
      // 	return Result_t::UNSAT;
      // }
           
      map<Expr, ExprSet> soln;
      ExprVector rels;

      for (auto d : ruleManager.decls) {
	if (!isFixedRel(d->left())) {
	  rels.push_back(d->left());
	}
      }
      
      Result_t res = getWeakerSoln(rel, rels, newsmt, soln);

      if (res == Result_t::SAT) {
	outs() << "CHC proved s\n";
	betterSoln = conjoin(soln[rel], m_efac);
	if (update) {
	  for (auto e : soln) {
	    if (e.first == rel && !firstCall && newenc) {
	      Expr cur = conjoin(candidates[e.first], m_efac);
	      Expr nu = conjoin(e.second, m_efac);
	      candidates[e.first].clear();
	      candidates[e.first].insert(mk<OR>(cur, nu));
	    } else {
	      candidates[e.first].clear();
	      candidates[e.first].insert(e.second.begin(), e.second.end());
	    }
	  }
	}	
      }
      return res;
    }


    void dumpSMT(const ExprVector & constraints, const ExprSet & allVars, const bool newenc = false)
    {
      stringstream asserts;
      stringstream decls;

      printAllVarsRels(allVars, decls);

      for (auto c : constraints) {
	asserts << "(assert ";
	u.print(c, asserts);
	asserts << ")\n";
      }

      asserts << "(check-sat)\n(get-model)\n";

      dumpToFile(decls, asserts, ruleManager.infile, newenc ? "_smt_V2_" : "_smt_");
      
    }

    Result_t checkMaximalSMTV2(const Expr & rel, bool update = true)
    {
      Expr reld;
      for (auto d : ruleManager.decls) {
	if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*rel)) {
	  reld = d;
	  break;
	}
      }    
      Expr curcand = conjoin(candidates[rel], m_efac);
      ExprVector constraints;

      //new constraints
      {
	ExprVector args;
	for (auto v : ruleManager.invVars[rel])
	  args.push_back(v->left());
	args.push_back(mk<IMPL>(mk<AND>(bind::fapp(reld, ruleManager.invVars[rel]), curcand), mk<FALSE>(m_efac)));
	constraints.push_back(mknary<FORALL>(args));
	args.pop_back();
	
	args.push_back(bind::fapp(reld, ruleManager.invVars[rel]));
	constraints.push_back(mknary<EXISTS>(args));
      }

      ExprSet allVars;
      map<Expr, ExprVector> funcs;

      for (auto & hr : ruleManager.chcs)
      {
	ExprVector args;
	
	for (int i = 0; i < hr.srcRelations.size(); i++)
	  for (auto v : hr.srcVars[i]) {
	    args.push_back(v->left());
	    allVars.insert(v);
	  }

	for (auto v : hr.dstVars) {
	  args.push_back(v->left());
	  allVars.insert(v);
	}
	
	for (auto l : hr.locVars) {
	  args.push_back(l->left());
	  allVars.insert(l);
	}

	vector<ExprVector> clauses;	
	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr src = hr.srcRelations[i];
	  ExprVector clause;
	  if (rel == src) {
	    clause.push_back(replaceAll(curcand, ruleManager.invVars[src], hr.srcVars[i]));
	    Expr f = bind::fapp(reld, hr.srcVars[i]);
	    funcs.insert({f, hr.srcVars[i]});
	    clause.push_back(f);	    
	  } else if (isFixedRel(src)){
	    Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
	    clause.push_back(t);
	    
	  } else {
	    for (auto d : ruleManager.decls) {
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
		Expr f = bind::fapp(d, hr.srcVars[i]);
		funcs.insert({f, hr.srcVars[i]});
		clause.push_back(f);
		break;
	      }
	    }
	  }
	  clauses.push_back(clause);
	}
	
	if (!hr.isQuery)
	  clauses.push_back(ExprVector{hr.body});

	if (hr.dstRelation == rel) 
	  clauses.push_back(ExprVector{mk<NEG>(replaceAll(curcand, ruleManager.invVars[rel], hr.dstVars))});
	
	
	vector<ExprSet> antecs;
	ExprVector tmpOutput;
	getOrCombinations(clauses, 0, 0, tmpOutput, antecs);

	for (auto antecItr = antecs.begin(); antecItr != antecs.end();)
	{
	  if (!u.isSat(*antecItr)) {
	    antecItr = antecs.erase(antecItr);
	  } else {
	    antecItr++;
	  }
	}
	  
	Expr conseq;
	bool addFail = false;

	if (isFixedRel(hr.dstRelation)) {
	  addFail = true;
	  conseq = mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars));
	} else {	  
	  if (hr.isQuery) {
	    addFail = true;
	    conseq = hr.body;
	  } else {
	    for (auto d : ruleManager.decls) {
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
		conseq = bind::fapp(d, hr.dstVars);
		break;
	      }
	    }
	  }
	}

	for (auto antec : antecs) {
	  //vacuity
	  if (hr.srcRelations.size() > 0) {
	    args.push_back(conjoin(antec, m_efac));
	    constraints.push_back(mknary<EXISTS>(args));
	    args.pop_back();
	  }

	  //CHC
	  if (addFail) {
	    args.push_back(mk<IMPL>(mk<AND>(conjoin(antec, m_efac), conseq), mk<FALSE>(m_efac)));
	  } else {
	    args.push_back(mk<IMPL>(conjoin(antec, m_efac), conseq));
	  }
	  constraints.push_back(mknary<FORALL>(args));
	  args.pop_back();
	  
	}
      }
      
      dumpSMT(constraints, allVars, 2);
      
      boost::tribool res = u.isSat(constraints);

      if (boost::logic::indeterminate(res)) {
	//	outs() << "result is indeterminate \n";//DEBUG
	return Result_t::UNKNOWN;
	
      } else if (!res) {
	//	outs() << "result is us!\n";//DEBUG
	return Result_t::UNSAT;
      }

      u.printModel();//debug
      if (!update) {
	return Result_t::SAT;
      }

      for (auto func : funcs) {
	Expr fm = u.getModel(func.first);
	outs() << *(func.first) << " -> " << *fm << "\n";
      }

      for (auto d : ruleManager.decls) {
	//NOTE: assumption here is that funcs will have only nonfixed rels
	for (auto func : funcs) {
	  if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*((func.first)->left()->left()))) {
	    if (d->left() == rel) {
	      Expr cur = conjoin(candidates[d->left()], m_efac);
	      Expr nu = replaceAll(u.getModel(func.first), func.second, ruleManager.invVars[d->left()]);
	      candidates[d->left()].clear();
	      candidates[d->left()].insert(mk<OR>(cur, nu));		
	    } else {
	      candidates[d->left()].clear();
	      candidates[d->left()].insert(replaceAll(u.getModel(func.first), func.second, ruleManager.invVars[d->left()]));
	    }
	    break;
	  }
	}
      }
      return Result_t::SAT;
    }
    
    // smt solver based weaker solution synthesis
    Result_t checkMaximalSMT(const Expr & rel, Expr & betterSoln, bool firstTime, bool update=true)
    {
      
      if (!firstTime && isOpX<TRUE>(conjoin(candidates[rel], m_efac)))
	return Result_t::UNSAT;

      //debug
      // if (!firstTime) {
      // 	outs() << "\n\nV2 result: ";
      // 	switch(checkMaximalSMTV2(rel, false)) {
      // 	case Result_t::SAT : outs() << "SAT\n"; break;
      // 	case Result_t::UNSAT : outs() << "UNSAT\n"; break;
      // 	case Result_t::UNKNOWN : outs() << "UNKNOWN\n"; break;
      // 	}
      // }
      
      ExprVector newVars;
      Expr curCand;
      Expr newCand;
      
      if (!firstTime) {
	newVars.reserve(ruleManager.invVars[rel].size());
	
	ExprVector eqVars;
	for (int i = 0; i < ruleManager.invVars[rel].size(); i++) {
	  Expr newVar = bind::intConst(mkTerm<string>("_MAX_" + to_string(i), m_efac));
	  newVars.push_back(newVar);
	  eqVars.push_back(mk<EQ>(ruleManager.invVars[rel][i], newVar));
	}

	curCand = conjoin(candidates[rel], m_efac);
	newCand = mk<OR>(curCand, conjoin(eqVars, m_efac));
      }
      
      ExprVector constraints;

      if (!firstTime) {
	//weaker solution constraints
	//forall vars. cursoln -> newsoln
	//exists vars. newsoln /\ ~cursoln 
	ExprVector args;
	for (auto v : ruleManager.invVars[rel])
	  args.push_back(v->left());      
	args.push_back(mk<IMPL>(curCand, newCand));

	constraints.push_back(mknary<FORALL>(args));

	args.pop_back();
	args.push_back(mk<AND>(mk<NEG>(curCand), newCand));

	constraints.push_back(mknary<EXISTS>(args));	
      } 

      map<Expr, ExprVector> funcs;
      ExprSet allVars(newVars.begin(), newVars.end());

      //add original CHCs as constraints (substitute current relation and fixed relations by their interpretations)
      //also add vacuity check (i.e. exists srcvars. antecedent(chc))
      for (auto & hr : ruleManager.chcs)
      {
	ExprVector vacuityArgs;	
	ExprVector rargs;

	for (int i = 0; i < hr.srcRelations.size(); i++)
	  for (auto v : hr.srcVars[i]) {
	    rargs.push_back(v->left());
	    vacuityArgs.push_back(v->left());
	    allVars.insert(v);
	  }

	for (auto v : hr.dstVars) {
	  rargs.push_back(v->left());
	  vacuityArgs.push_back(v->left());
	  allVars.insert(v);
	}

	allVars.insert(hr.locVars.begin(), hr.locVars.end());
	

	ExprSet cnjs;
	for (int i = 0; i < hr.srcRelations.size(); i++) {
	  Expr src = hr.srcRelations[i];
	  if (!firstTime && src == rel) {
	    Expr t = replaceAll(newCand, ruleManager.invVars[rel], hr.srcVars[i]);
	    cnjs.insert(t);
	    
	  } else if (isFixedRel(src)){
	    Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
	    cnjs.insert(t);
	    
	  } else {
	    for (auto d : ruleManager.decls)
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
		Expr t = bind::fapp(d, hr.srcVars[i]);
		funcs.insert({t, hr.srcVars[i]});
		cnjs.insert(t);
		break;
	      }
	  }
	}

	Expr antec = conjoin(cnjs, m_efac);
	Expr conseq;
	
	if (!hr.isQuery) {
	  antec = mk<AND>(antec, hr.body);
	  
	  if (!firstTime && hr.dstRelation == rel) {
	    conseq = replaceAll(newCand, ruleManager.invVars[rel], hr.dstVars);
	    
	  } else if (isFixedRel(hr.dstRelation)) {
	    conseq = replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars);
	    
	  } else {
	    for (auto d : ruleManager.decls) {
	      if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
		Expr t = bind::fapp(d, hr.dstVars);
		conseq = t;
		// funcs.push_back(t);
		break;
	      }
	    }
	  }
	  
	} else {
	  conseq = mkNeg(hr.body);
	}

	//Replace dstvars in terms of srcvars; an optimisation which makes z3 solve faster sometime
	// ExprSet dummyVars;
	// AeValSolver ae(mk<TRUE>(m_efac), mk<TRUE>(m_efac), dummyVars); 
	// for(auto dv : hr.dstVars) {
	//   outs() << "hr.body: " << *(hr.body) << "\n";
	//   outs() << "dv: " << *(dv) << "\n";

	//   Expr e = ineqSimplifier(dv, hr.body, true);

	//   outs() << "e: " << *e << "\n";
	  
	//   Expr repExpr = ae.getAssignmentForVar(dv, e);

	//   if (isOpX<TRUE>(repExpr)) continue;
	  
	//   conseq = replaceAll(conseq, dv, repExpr);
	// }

	rargs.push_back(mk<IMPL>(antec, conseq));

	constraints.push_back(mknary<FORALL>(rargs));

	if (hr.srcRelations.size() > 0) {
	  vacuityArgs.push_back(antec);
	  constraints.push_back(mknary<EXISTS>(vacuityArgs));
	}

      }

      //DEBUG
      dumpSMT(constraints, allVars);
      
      boost::tribool res = u.isSat(constraints);


      if (boost::logic::indeterminate(res)) {
	//	outs() << "result is indeterminate \n";//DEBUG
	return Result_t::UNKNOWN;
	
      } else if (!res) {
	//	outs() << "result is us!\n";//DEBUG
	return Result_t::UNSAT;
      } 

      //debug
      u.printModel();
      for (auto func : funcs) {
	Expr fm = u.getModel(func.first);
	outs() << *(func.first) << " -> " << *fm << "\n";
      }

      if (!firstTime) {
	Expr model = u.getModel(newVars);

	outs() << "model: " << *model << "\n";//DEBUG
	outs() << "curCand: " << *curCand << "\n";//DEBUG
	betterSoln = mk<OR>(curCand, replaceAll(model, newVars, ruleManager.invVars[rel]));
	outs() << "bettersoln: " << *betterSoln << "\n";//DEBUG
      }
      
      if (update) {

	if (!firstTime) {
	  candidates[rel].clear();
	  candidates[rel].insert(betterSoln);
	}
	
	for (auto d : ruleManager.decls) {
	  //NOTE: assumption here is that funcs will have only nonfixed rels
	  for (auto func : funcs) {
	    if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*((func.first)->left()->left()))) {
	      candidates[d->left()].clear();
	      candidates[d->left()].insert(replaceAll(u.getModel(func.first), func.second, ruleManager.invVars[d->left()]));
	      break;
	    }
	  }
	}

	if (firstTime) {
	  betterSoln = conjoin(candidates[rel], m_efac);
	}
      }
      
      return Result_t::SAT;
      
    }
      

    //finds weakest interpretation for relations as per the order in relsOrderStr
    void maximalSolve (const vector<string> & relsOrderStr, const string & smt, bool useGAS = true, bool newenc = false)
    {
      	ExprVector relsOrder = getRels(relsOrderStr);
	if (relsOrder.size() == 0)
	  relsOrder = ruleManager.getUnderConsRels();

      int curRel = 0;
      bool firstCall = true;
      
      if (useGAS) {
	Result_t res = guessAndSolve();

	if (hasArrays) {
	  switch (res) {
	  case Result_t::UNSAT: printCands(); break;
	  case Result_t::UNKNOWN: outs() << "unknown\n"; break;
	  case Result_t::SAT: outs() << "sat\n"; break;	  
	  }
	  return;
	}

	switch(res) {
	case Result_t::UNSAT:
	  if (relsOrder.size() == 0) {
	    printCands();
	    return;
	  }
	  firstCall = false;
	  break;
	case Result_t::SAT:
	  outs() << "sat\n";
	  return;
	case Result_t::UNKNOWN:
	  candidates.clear();
	  firstCall = true;
	}
		  			
      }       
      
      outs() << "currel: " << *relsOrder[curRel] << "\n"; //DEBUG
      outs() << "curcand size: " << candidates[relsOrder[curRel]].size() << "\n";
      outs() << "curcand: " << *conjoin(candidates[relsOrder[curRel]], m_efac) << "\n";//DEBUG
	
      Expr betterSoln;

      while (true) {

	if (useGAS) {
	  Result_t maxResCHC = checkMaximalCHC(relsOrder[curRel], betterSoln, firstCall, newenc);
	  
	  if (maxResCHC == Result_t::SAT) {
	    firstCall = false;
	    continue;
	    
	  } else if(maxResCHC == Result_t::UNSAT) {
	    if (firstCall && candidates[relsOrder[curRel]].size() == 0) {
	      outs() << "sat!\n";
	      return;
	    }
	    firstCall = false;
	    if (curRel == relsOrder.size() - 1) {
	      printCands(true, candidates);
	      return;
	      
	    } else {
	      addFixedRel(relsOrder[curRel]);
	      curRel++;
	    }
	    continue;
	  }
	}

	Result_t maxRes;
	
	if (firstCall || !newenc) {
	  maxRes = checkMaximalSMT(relsOrder[curRel], betterSoln, firstCall);
	} else {
	  maxRes = checkMaximalSMTV2(relsOrder[curRel]);
	}
	  
	if (maxRes == Result_t::UNSAT) {
	  if (firstCall && candidates[relsOrder[curRel]].size() == 0) {
	      outs() << "sat!\n";
	      return;
	    }
	  if (curRel == relsOrder.size() - 1) {
	    printCands(true, candidates);
	    return;
	      
	  } else {
	    addFixedRel(relsOrder[curRel]);
	    curRel++;
	  }
	    
	} else if(maxRes == Result_t::UNKNOWN) {
	  if (candidates[relsOrder[curRel]].empty()) {
	    outs() << "unknown\n";
	  } else {
	    printCands(true, candidates, true);
	  }
	  return;
	}       
	firstCall = false;	 
      }
    }
    
    // naive solving, without invariant generation
    Result_t solveIncrementally(int bound, int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > bound)       // maximum bound reached
      {
        return Result_t::UNKNOWN;
      }
      else if (rels.empty()) // base case == init is reachable
      {
        return Result_t::SAT;
      }

      Result_t res = Result_t::UNSAT;

      // reserve copy;
      auto ssaStepsTmp = ssaSteps;
      int varCntTmp = varCnt;

      vector<vector<int>> applicableRules;
      for (int i = 0; i < rels.size(); i++)
      {
        vector<int> applicable;
        for (auto & r : ruleManager.incms[rels[i]])
        {
          Expr body = ruleManager.chcs[r].body; //ruleManager.getPostcondition(r);
          if (args.size() != 0)
            body = replaceAll(body, ruleManager.chcs[r].dstVars, args[i]);
          // identifying applicable rules
          if (u.isSat(body, conjoin(ssaSteps, m_efac)))
          {
            applicable.push_back(r);
          }
        }
        if (applicable.empty())
        {
          return Result_t::UNSAT;         // nothing is reachable; thus it is safe here
        }
        applicableRules.push_back(applicable);
      }

      vector<vector<int>> ruleCombinations;
      getCombinations(applicableRules, ruleCombinations);

      for (auto & c : ruleCombinations)
      {
        ssaSteps = ssaStepsTmp;
        varCnt = varCntTmp;
        ExprVector rels2;
        vector<ExprVector> args2;

        for (int i = 0; i < c.size(); i++)
        {
          // clone all srcVars and rename in the body
          auto &hr = ruleManager.chcs[c[i]];
          Expr body = hr.body;
          if (!hr.dstVars.empty()) body = replaceAll(body, hr.dstVars, args[i]);
          vector<ExprVector> tmp;
          for (int j = 0; j < hr.srcRelations.size(); j++)
          {
            rels2.push_back(hr.srcRelations[j]);
            ExprVector tmp1;
            for(auto &a: hr.srcVars[j])
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              tmp1.push_back(cloneVar(a, new_name));
            }
            args2.push_back(tmp1);
            body = replaceAll(body, hr.srcVars[j], tmp1);
            for (auto & a : hr.locVars)
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              body = replaceAll(body, a, cloneVar(a, new_name));
            }
          }

          ssaSteps.push_back(body);
        }

        if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
        {
          Result_t res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
          if (res_tmp == Result_t::SAT) return Result_t::SAT;           // bug is found for some combination
          else if (res_tmp == Result_t::UNKNOWN) res = Result_t::UNKNOWN;
        }
      }
      return res;
    }

    // naive solving, without invariant generation
    void solveIncrementally(int bound)
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      switch (solveIncrementally (bound, 0, query, empt))
      {
      case Result_t::SAT: outs () << "sat\n"; break;
      case Result_t::UNSAT: outs () << "unsat\n"; break;
      case Result_t::UNKNOWN: outs () << "unknown\n"; break;
      }
    }
  };

  inline void solveNonlin(string smt, int inv, int stren, bool maximal, const vector<string> & relsOrder, bool z3check, bool useGAS, bool newenc)
  {
    
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver nonlin(ruleManager, stren);
    
    if (z3check) {
      switch(nonlin.checkZ3()) {
      case Result_t::UNSAT: outs() << "unsat\n"; break;
      case Result_t::SAT: outs() << "sat!\n"; break;
      case Result_t::UNKNOWN: outs() << "unknown\n"; break;
      }
      return;
    }

    if (inv == 0) {      
      if (maximal) {
	nonlin.maximalSolve(relsOrder, smt, useGAS, newenc);	
      } else {
	switch(nonlin.guessAndSolve()) {
	case Result_t::UNSAT: nonlin.printCands(); break;
	case Result_t::SAT: outs() << "sat!\n"; break;
	case Result_t::UNKNOWN: outs() << "unknown\n"; break;
	}
      }
	
    } else {
      nonlin.solveIncrementally(inv);
    }
  };
}

#endif
