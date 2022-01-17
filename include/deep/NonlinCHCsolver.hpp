#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"

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
    vector<int> propOrder;
    map<Expr, ExprVector> invItrs;
    map<Expr, ExprVector> invSizeVars;
    map<Expr, bool> invItrInc;

    public:

    NonlinCHCsolver (CHCs& r, int _b) : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b) {}

    bool checkAllOver (bool checkQuery = false)
    {
      outs () << " checkAllOver\n";
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        if (!checkCHC(hr, candidates)) return false;
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      outs () << " check chc: ";
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        Expr rel = hr.srcRelations[i];
        outs () << rel << " ";
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        outs () << " -> " << rel << "\n";
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        checkList.insert(disjoin(negged, m_efac));
      }
      else
      {
        outs () << " -> false\n";
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

    void preproGuessing(Expr e, ExprVector& varsToKeep, ExprVector& varsToRename,
                        ExprSet& guesses, bool backward = false, bool mutate = true)
    {
      if (!u.isSat(e)) return;
      if (!containsOp<FORALL>(e) && !containsOp<EXISTS>(e)) e = rewriteSelectStore(e);

      ExprSet qVars, varsToElim, complex;
      ExprMap repls, replsRev;
      map<Expr, ExprSet> replIngr;

      getQuantifiedVars(e, qVars);
      filter (e, bind::IsConst (), inserter (varsToElim, varsToElim.begin()));
      minusSets(varsToElim, varsToKeep);
      minusSets(varsToElim, qVars);
      findComplexNumerics(e, complex);

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
      // eTmp = replaceQVars(eTmp, repls);
      if (backward && (containsOp<FORALL>(e) || containsOp<EXISTS>(e)))
      {
        eTmp = replaceAll (eTmp, replsRev);
        eTmp = simplifyQuants(eTmp);
        // eTmp = simplifyExists(eTmp);
        eTmp = u.removeRedundantConjuncts(eTmp);
        eTmp = simplifyBool(eTmp);
        eTmp = u.extendQuantified(eTmp);
        // eTmp = moveInsideQuantifiers(eTmp);
        map<Expr, ExprVector> qv;
        getQVars (eTmp, qv);

        for (auto tq : qv)
        {
          Expr q = tq.first;
          Expr ep = q->last();
          ep = simpleQE(ep, varsToElim);
          ep = rewriteSelectStore(ep);
          ep = eliminateQuantifiersRepl(ep, varsToElim);
          ep = u.removeRedundantDisjuncts(ep);
          ep = simplifyBool(simplifyArithm(ep));
          if (isOpX<FALSE>(ep) || isOpX<TRUE>(ep))
          {
            eTmp = replaceAll(eTmp, q, ep);
            continue;
          }
          ExprSet epCnjs;
          getConj(ep, epCnjs);

          for (auto & v : varsToKeep)
          {
            ExprSet tmpm;
            for (auto & p : epCnjs)
              if (contains(p, v) && !containsOp<ARRAY_TY>(p))
                tmpm.insert(p);

            if (isNumeric(v))
            {
              ExprSet tmp = {v};
              epCnjs.insert(eliminateQuantifiers(conjoin(tmpm, m_efac), tmp));
            }
          }

          Expr toReplace = conjoin(epCnjs, m_efac);
          if (emptyIntersect(toReplace, tq.second))
            eTmp = replaceAll(eTmp, q, toReplace);
          else
            eTmp = replaceAll(eTmp, q->last(), toReplace);   // TODO: multiple things
        }
        // eTmp = moveInsideQuantifiers(eTmp);
      }
      else
      {
        varsToElim.clear();
        filter (eTmp, bind::IsConst (), inserter (varsToElim, varsToElim.begin())); // prepare vars
        for (auto it = varsToElim.begin(); it != varsToElim.end(); )
        {
          if (find(varsToKeep.begin(), varsToKeep.end(), *it) != varsToKeep.end() ||
              find(qVars.begin(), qVars.end(), *it) != qVars.end())
          it = varsToElim.erase(it);
          else
          {
            Expr tmp = replsRev[*it];
            if (tmp == NULL) ++it;
            else
            {
              ExprSet tmpSet = replIngr[*it];
              minusSets(tmpSet, varsToKeep);
              minusSets(tmpSet, qVars);
              if (tmpSet.empty()) it = varsToElim.erase(it);
              else ++it;
            }
          }
        }
      }

      outs() << "eTmp: ";
      pprint(eTmp);
      outs() << "\nto elim: ";
      pprint(varsToElim);
      outs () << "\n";
      
      eTmp = eliminateQuantifiers(eTmp, varsToElim);
      outs () << "  res = " << eTmp << "\n";
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
        // g = simplifyBool(simplifyExists(simplifyQuants(g)));
        if (!varsToRename.empty())
          g = replaceAll(g, varsToKeep, varsToRename);
        guesses.insert(g);
      }
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
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
        bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation));
        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

        if (fwd && srcVisited && !dstVisited)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
      }

      if (declsVisited.size() != szInit) propagate(fwd);
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

        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);

        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr, bool forceConv = false)
    {
        if (hr.isFact) return;

        Expr dstRel = hr.dstRelation;
        ExprVector& rels = hr.srcRelations;

        // identifying nonlinear cases (i.e., when size(occursNum[...]) > 1)
        map<Expr, set<int>> occursNum;
        for (int i = 0; i < rels.size(); i++)
        {
          occursNum[rels[i]].insert(i);
          for (int j = i+1; j < rels.size(); j++)
            if (rels[i] == rels[j])
              occursNum[rels[i]].insert(j);
        }

        ExprVector invVars, srcVars;
        for (int i = 0; i < hr.srcVars.size(); i++)
          srcVars.insert(srcVars.end(), hr.srcVars[i].begin(), hr.srcVars[i].end());

        if (hr.srcVars.size() == 1) invVars = ruleManager.invVars[rels[0]];

        propagateRangeBackward(hr, srcVars, invVars);

        ExprSet cands;
        if (hr.isQuery)
          cands.insert(mk<FALSE>(m_efac));
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

          // TODO: add more sophisticated blocking based on unsuccessful tries from abdHistory
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
          if (forceConv) forceConvergence(candidates[rels[0]], mixedCands);
          for (auto & m : mixedCands) getConj(m, candidates[rels[0]]);
        }
        else
        {
          decompose(hr, curCnd, occursNum, mixedCands);
        }
      }

    void decompose(HornRuleExt& hr, ExprVector& curCnd, map<Expr, set<int>>& occursNum, ExprSet& mixedCands)
    {
          Expr dstRel = hr.dstRelation;
          ExprVector& rels = hr.srcRelations;
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

              Expr r = rels[i];
              if (!u.isSat(a, conjoin(curCnd, m_efac))) return;  // need to recheck because the solver has been reset
              if (processed.find(r) != processed.end()) continue;

              ExprVector invVars;
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
                {
                  for (auto & v : hr.srcVars[j])
                  if ((containsOp<ARRAY_TY>(a) && containsOp<ARRAY_TY>(v)) ||
                      !containsOp<ARRAY_TY>(a))
                  allVarsExcept.insert(v);
                }
              }

              // model-based cartesian decomposition
              ExprSet all = allGuesses;
              all.insert(mkNeg(a));

              if (trueRels.size() != 1)                  // again, for fairness heuristic:
                all.insert(u.getModel(allVarsExcept));

              // in the case of nonlin, invVars is empty, so no renaming happens:

              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                getConj(conjoin(backGuesses, m_efac), candidates[r]);
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
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

                    if (!u.isSat(mknary<FORALL>(args), sol.empty() ? mk<TRUE>(m_efac) : disjoin(negModels, m_efac)))
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

    void propagateRangeBackward(HornRuleExt& hr, ExprVector& invVars, ExprVector& srcVars, int i = 0)
    {
      Expr& srcRel = hr.srcRelations[i];
      ExprSet allCands;
      for (auto & c : hr.srcRelations) allCands.insert(candidates[c].begin(), candidates[c].end());
      Expr e = conjoin(allCands, m_efac);
      if (containsOp<FORALL>(e))
      {
        e = u.removeRedundantConjuncts(mk<AND>(e, hr.body));
        if (!containsOp<FORALL>(e))
        {
          vector<HornRuleExt*> worklist;
          worklist.push_back(&hr);
          bool candInd = multiHoudini(worklist, false);  // hope to only call weakenForall
          if (candInd) return;
          else
          {
            if (!checkCHC(hr, candidates))
            {
              Expr model = u.getModel();
              if (isSkippable(model, hr.dstVars)) return;

              ExprSet newCands;
              for (auto it = candidates[srcRel].begin(); it != candidates[srcRel].end(); ++it)
              {
                Expr c = *it;
                if (isOpX<FORALL>(c))
                {
                  ExprSet qVars, range, cellFla, newRange, allSatFla, models, all, newCnd;
                  getQuantifiedVars(c, qVars);
                  getDisj(c->last(), range);
                  Expr repl = mkNeg(replaceAll(c, ruleManager.invVars[srcRel], hr.dstVars));
                  allSatFla.insert(model);
                  allSatFla.insert(repl->last());
                  ExprMap matchVars;
                  while (u.isSat(allSatFla))
                  {
                    Expr nextModel = u.getModel();
                    allSatFla.insert(mkNeg(nextModel));
                    models.insert(nextModel);
                    for (auto & q : qVars)
                      for (auto & s : srcVars)
                        if (u.getModel(q) == u.getModel(s))
                          matchVars[s] = q;
                  }

                  Expr allModels = disjoin(models, m_efac);
                  for (auto & r : range)
                  {
                    if (containsOp<SELECT>(r))
                    {
                      cellFla.insert(r);
                      continue;
                    }
                    if (u.isSat(r, allModels)) newRange.insert (mkNeg(r));
                    else newRange.insert(r);
                  }

                  all.insert(replaceAll(hr.body, matchVars));
                  all.insert(mkNeg(replaceAll(disjoin(cellFla, m_efac), ruleManager.invVars[srcRel], hr.dstVars)));
                  ExprVector srcVarsE = srcVars;
                  srcVarsE.insert(srcVarsE.end(), qVars.begin(), qVars.end());
                  ExprVector invVarsE = invVars;
                  invVarsE.insert(invVarsE.end(), qVars.begin(), qVars.end());
                  preproGuessing(conjoin(all, m_efac), srcVarsE, invVarsE, newCnd, true, false);
                  getDisj(conjoin(newCnd, m_efac), newRange);
                  Expr newCand = replaceAll(c, c->last(), disjoin(newRange, m_efac));
                  newCands.insert(newCand);
                }
              }
              candidates[srcRel].insert(newCands.begin(), newCands.end());
              multiHoudini(worklist, false);  // to double-check
            }
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
            propagateCandidatesBackward(*hr, deep == strenBound - 1);
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

      // mergeDiseqs(prevSplit);
      // mergeDiseqs(nextSplit);

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

    void printCands(bool unsat = true, bool simplify = false)
    {
      if (unsat) outs () << "unsat\n";

      for (auto & a : candidates)
      {
        outs () << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          outs () << "(" << *b << " " << u.varType(b) << ")";
        }
        outs () << ") Bool\n  ";

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

        Expr res = (simplifyArithm(sol));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        u.print(res);
        outs () << ")\n";
      }
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second))
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact) worklist.push_back(&hr);

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

    bool isSkippable(Expr model, ExprVector vars/*, map<Expr, ExprSet>& cands*/)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp)) return true;
      }

//      for (auto & a : cands)
//        for (auto & b : a.second)
//          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    // GF: currently works only for linear (inductive) CHCs, to extend
    Expr strengthenExists(Expr fla, Expr model)
    {
      ExprSet all;
      getDisj(fla, all);
      bool res = false;
      for (auto it = all.begin(); it != all.end(); )
      {
        if (u.isSat(model, *it))
        {
          res = true;
          it = all.erase(it);
        }
        else ++it;
      }
      if (res) return disjoin(all, fla->getFactory());
      return NULL;
    }

    Expr weakenForall(Expr fla, ExprVector& srcVars, ExprVector& dstVars, Expr model)
    {
      ExprSet qfree;
      getDisj(fla->last(), qfree);
      int erased = 0;
      Expr newCand = fla;

      ExprSet lits;
      getLiterals(fla->last(), lits);
      for (auto & l : lits)
      {
        if (!u.isSat(model, replaceAll(l, srcVars, dstVars)) && !containsOp<SELECT>(l)){
          erased++;
          newCand = replaceAll(newCand, l, mk<FALSE>(m_efac));
          // TODO: should be more careful replacement in the case of quantifier alternation
        }
      }
      if (!qfree.empty() && erased != 0) return newCand;
      return NULL;
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      outs () << "multihoudini, size " << worklist.size() << "\n";

      if (!anyProgress(worklist)) return false;
      auto candidatesTmp = candidates;
      bool res1 = true;
      bool res3 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;

        if (checkCHC(*hr, candidatesTmp))
        {
          outs () << "all good\n";
        }
        else
        {
          res3 = false;
          bool res2;
          Expr dstRel = hr->dstRelation;

          ExprVector srcVars;
          for (int i = 0; i < hr->srcVars.size(); i++)
            srcVars.insert(srcVars.end(), hr->srcVars[i].begin(), hr->srcVars[i].end());

          Expr model = u.getModel(hr->dstVars);
          Expr modelSrc = u.getModel(srcVars);
          outs() << "msrc: " << *modelSrc << "\n";
          outs() << "mdst: " << *model << "\n";
          
          if (isSkippable(model, hr->dstVars))//, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
           outs () << "weaken\n";
            Expr newCand = NULL;
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) {
                res2 = false;
                if (isOpX<FORALL>(repl))
                  newCand = weakenForall(*it, ruleManager.invVars[dstRel], hr->dstVars, model);
                else if (containsOp<EXISTS>(repl) && hr->isInductive)
                  newCand = strengthenExists(*it, modelSrc);
                it = candidatesTmp[dstRel].erase(it);
              }
              else ++it;
            }
            if (newCand != NULL)
              candidatesTmp[dstRel].insert(newCand);
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return res3;
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

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    enum AbdType : unsigned char
      {
       REAL = 0,
       MOCK
      };

    void initRangeAbduction()
    {
      for (auto & hr : ruleManager.chcs) {
        if (find(hr.srcRelations.begin(), hr.srcRelations.end(), hr.dstRelation) != hr.srcRelations.end()) {
          auto & itrs = invItrs[hr.dstRelation];
          auto & sizeVars = invSizeVars[hr.dstRelation];
          auto & inc  = invItrInc[hr.dstRelation];
          getIterators(hr, itrs, sizeVars, inc);
        }
      }
      return constructPropOrder();
    }


    //Construct the order in which range abduction has to be performed
    //BFS with fail decl as root; priority to chcs having the same relation in src and dst
    void constructPropOrder()
    {
      ExprVector visited;
      deque<int> q;
      for (auto chcNum : ruleManager.incms[ruleManager.failDecl]) {
        q.push_back(chcNum);
      }
      visited.push_back(ruleManager.failDecl);
      while (!q.empty()) {
        int cur = q.front();
        q.pop_front();
        propOrder.push_back(cur);
        for (auto sinv : ruleManager.chcs[cur].srcRelations) {
          if (find(visited.begin(), visited.end(), sinv) != visited.end()) continue;
          vector<int> incms = ruleManager.incms[sinv];
          for (auto incmsItr = incms.begin(); incmsItr != incms.end();) {
            int i = *incmsItr;
            if (find(ruleManager.chcs[i].srcRelations.begin(),
                     ruleManager.chcs[i].srcRelations.end(),
                     sinv) != ruleManager.chcs[i].srcRelations.end()) {
              q.push_back(i);
              incmsItr = incms.erase(incmsItr);
            } else {
              ++incmsItr;
            }
          }
          for (auto i : incms) {
            q.push_back(i);
          }
          visited.push_back(sinv);
        }
      }
    }

    //Simple initial candidate: formula present in the query
    void getQueryArrayCandidates()
    {
      for (auto & hr : ruleManager.chcs) {
        if (hr.isQuery) {
          assert(hr.srcRelations.size() == 1 &&
                 "Nonlinear CHCs are not supported");
          //hr.body can have fail; following check avoids adding fail
          ExprSet cand;
          ExprSet cnjs;
          getConj(hr.body, cnjs);
          ExprVector allVars = hr.locVars;
          for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
          for (auto & a : cnjs)
          {
            if (!emptyIntersect(a, allVars)) {
              cand.insert(mkNeg(a));
            }
          }
          Expr c = disjoin(cand, m_efac);
          c = replaceAll(c, hr.srcVars[0], ruleManager.invVars[hr.srcRelations[0]]);
          candidates[hr.srcRelations[0]].insert(c);
          return;
        }
      }
    }

    void getIterators(HornRuleExt& hr, ExprVector& itrs, ExprVector & sizeVars, bool & incr)
    {
      for (int i = 0; i < hr.srcVars[0].size(); i++) {
        Expr sv = hr.srcVars[0][i];
        Expr dv = hr.dstVars[i];
        if (containsOp<ARRAY_TY>(sv) || containsOp<ARRAY_TY>(dv)) continue;
        if (u.implies(hr.body, mk<GT>(sv,dv))) {
          incr = false;
          itrs.push_back(sv);
        } else if (u.implies(hr.body, mk<LT>(sv,dv))) {
          incr = true;
          itrs.push_back(sv);
        } else if (u.implies(hr.body, mk<EQ>(sv,dv))) {
          sizeVars.push_back(sv);
        }
      }
    }


    Expr getMockArrayAssign(HornRuleExt& hr, const ExprVector & qVars)
    {
      ExprSet dassign;
      for (int i = 0; i < hr.srcVars[0].size(); i++) {
        if (containsOp<ARRAY_TY>(hr.srcVars[0][i])) {
          for (auto qv : qVars) {
            dassign.insert(mk<EQ>(hr.dstVars[i],
                                  mk<STORE>(hr.srcVars[0][i],
                                            qv,
                                            mk<SELECT>(hr.srcVars[0][i], qv))));
          }
        } else if (!containsOp<ARRAY_TY>(hr.dstVars[i])) {
          dassign.insert(mk<EQ>(hr.dstVars[i], hr.srcVars[0][i]));
        }
      }
      outs () << "   mock:  ";
      pprint(dassign, 3);
      return conjoin(dassign, m_efac);
    }

    Expr getMockArrayAssignNew(Expr nbt, const ExprVector & qVars)
    {
      // GF: hack for now; to extend
      ExprSet returnCnj;
      if (isOpX<EQ>(nbt))
      {
        Expr srcVar = NULL, dstVar = NULL;
        if (isOpX<FAPP>(nbt->left()))
          srcVar = nbt->left();
        if (isOpX<FAPP>(nbt->right()))
          dstVar = nbt->right();
        if (isOpX<STORE>(nbt->left()) && isOpX<FAPP>(nbt->left()->left()))
          srcVar = nbt->left()->left();
        if (isOpX<STORE>(nbt->right()) && isOpX<FAPP>(nbt->right()->left()))
          dstVar = nbt->right()->left();
        // TODO: extend for the case of nested STORE-s
        if (srcVar != NULL && dstVar != NULL)
          for (auto & q : qVars)
            returnCnj.insert(mk<EQ>(mk<SELECT>(srcVar, q),
                                 mk<SELECT>(dstVar, q)));
        else assert(0 && "not implemented");
      }

      return conjoin(returnCnj, m_efac);
    }
    
    //perform range abduction
    Expr getArrayFormula(HornRuleExt& hr, Expr dc, AbdType abd, ExprVector qVars, ExprVector itrVars)
    {
      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      ExprVector srcVars(hr.srcVars[0].begin(), hr.srcVars[0].end());
      ExprVector dstVars(hr.dstVars.begin(), hr.dstVars.end());
      ExprVector srcInvVars(ruleManager.invVars[srcRel].begin(), ruleManager.invVars[srcRel].end());
      ExprVector dstInvVars(ruleManager.invVars[dstRel].begin(), ruleManager.invVars[dstRel].end());

      ExprVector all;
      ExprSet newCnd;
      
      if (isOpX<FORALL>(dc) || isOpX<EXISTS>(dc)) {     
        all.push_back(mkNeg(replaceAll(dc->last(), dstInvVars, dstVars)));
      } else {
        //TODO: handle unquantified
        return mk<TRUE>(m_efac);
      }

      ExprVector vars2keep, prjcts, res;
      u.flatten(hr.body, prjcts, false, vars2keep, [](Expr a, ExprVector& b){return a;});
      for (auto b : prjcts)
      {
        ExprSet nbody, nbodyTmp;
        getConj(b, nbodyTmp);
        for (auto nbt : nbodyTmp)
        {
          outs () << "    >>> nbt " << nbt << "\n";
          if (containsOp<ARRAY_TY>(nbt)) {
            if (abd == AbdType::REAL) {
              nbt = replaceAll(nbt, itrVars, qVars);
              nbt = rewriteSelectStore(nbt);
              all.push_back(nbt);
            }
            else if (isOpX<EQ>(nbt) && isOpX<ARRAY_TY>(typeOf(nbt->left())))
            {
              Expr srcVar = NULL, dstVar = NULL;
              if (isOpX<FAPP>(nbt->left()))
                srcVar = nbt->left();
              if (isOpX<FAPP>(nbt->right()))
                dstVar = nbt->right();
              if (isOpX<STORE>(nbt->left()) && isOpX<FAPP>(nbt->left()->left()))
                srcVar = nbt->left()->left();
              if (isOpX<STORE>(nbt->right()) && isOpX<FAPP>(nbt->right()->left()))
                dstVar = nbt->right()->left();
              if (isOpX<STORE>(nbt->left()) && isOpX<STORE>(nbt->left()->left()) && isOpX<FAPP>(nbt->left()->left()->left()))
                srcVar = nbt->left()->left()->left();
              if (isOpX<STORE>(nbt->right()) && isOpX<STORE>(nbt->right()->left()) && isOpX<FAPP>(nbt->right()->left()->left()))
                dstVar = nbt->right()->left()->left();
              // TODO: extend for the case of nested STORE-s
              if (srcVar != NULL && dstVar != NULL)
                for (auto & q : qVars)
                  all.push_back(mk<EQ>(mk<SELECT>(srcVar, q),
                                       mk<SELECT>(dstVar, q)));
              else assert(0 && "not implemented");
            }
          }
          else all.push_back(nbt);
          outs () << "      ----> " << all.back() << "\n";
        }
        ExprVector abdVars(qVars.begin(), qVars.end());
        for (auto sv : srcVars) {
          if (find(itrVars.begin(), itrVars.end(), sv) == itrVars.end()) {
            abdVars.push_back(sv);
          }
        }
        Expr newCnd = keepQuantifiersRepl(conjoin(all, m_efac), abdVars);
        res.push_back(mkNeg(newCnd));
      }
      
      //preproGuessing(conjoin(all, m_efac), abdVars, abdVars, newCnd, true, false);      
      return replaceAll(conjoin(res, m_efac), srcVars, srcInvVars);
    }

    void getRangeFormulas(const ExprVector & qVars, const ExprVector & itrVars, ExprVector & sizeVars, ExprVector & rangeFormulas, bool incr)
    {
      for (auto qv : qVars) {
        for (auto iv : itrVars) {
          if (incr) {
            rangeFormulas.push_back(mk<GEQ>(qv,iv));
          } else {
            rangeFormulas.push_back(mk<LEQ>(qv,iv));
          }
        }
        // for (auto sv : sizeVars) {
        //   if (incr) {
        //     rangeFormulas.push_back(mk<GEQ>(qv,sv));
        //   } else {
        //     rangeFormulas.push_back(mk<LEQ>(qv,sv));
        //   }
        // }
      }      
    }

    
    void abduce(HornRuleExt& hr)
    {
      if (hr.isFact) return;

      if (hr.isQuery) {
        getQueryArrayCandidates();
        return;
      }
        
      assert(hr.srcRelations.size() == 1 &&
             "Nonlinear CHCs are not supported");

      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      ExprSet dstCands;      
      for (auto c : candidates[dstRel]) {
        dstCands.insert(simplifyBool(simplifyArithm(c)));
      }
      
      for (auto dc : dstCands) {
        ExprSet dcDisjs;
        getDisj(dc, dcDisjs);
        
        for (auto dcd : dcDisjs) {
          boost::tribool forall(boost::indeterminate);
          if (isOpX<FORALL>(dcd)) {
            forall = true;
          } else if (isOpX<EXISTS>(dcd)) {
            forall = false;
          } else {
            //TODO: handle non quantified case
            continue;
          }
          
          outs () << ">>>>>>>>>>>>>> next cand: "<< dcd<<"\n";

          ExprSet qVarsTmp;
          getQuantifiedVars(dcd, qVarsTmp);
          ExprVector qVars(qVarsTmp.begin(), qVarsTmp.end());
          ExprVector & itrVars = invItrs[srcRel];
          ExprVector & sizeVars = invSizeVars[srcRel];
          bool itrUp = invItrInc[srcRel];

          ExprVector arrayFormulas;
          arrayFormulas.push_back(getArrayFormula(hr, dcd, AbdType::REAL, qVars, itrVars));
          arrayFormulas.push_back(getArrayFormula(hr, dcd, AbdType::MOCK, qVars, itrVars));

          
          for (auto af : arrayFormulas) {
            outs() << "af: " << *af << "\n";
          }
          
          for (auto qv : qVars) {
            for (auto iv : itrVars) {
              Expr rf;
              if (itrUp) {
                rf = mk<GEQ>(qv,iv);
              } else {
                rf = mk<LEQ>(qv,iv);
              }

              outs() << "RF: " << *rf << "\n";
              ExprVector args1 = {qv->left()};
              ExprVector args2 = args1;
              if (forall == true)
              {
                if (hr.isInductive)
                {
                  args1.push_back(mk<OR>(arrayFormulas[0], mk<NEG>(rf)));
                  args2.push_back(mk<OR>(arrayFormulas[1], rf));
                  if (containsOp<ARRAY_TY>(arrayFormulas[0]))
                    candidates[srcRel].insert(mknary<FORALL>(args1));
                  if (containsOp<ARRAY_TY>(arrayFormulas[1]))
                    candidates[srcRel].insert(mknary<FORALL>(args2));
                }
                else
                {
                  bool cp1 = containsOp<ARRAY_TY>(arrayFormulas[0]);
                  bool cp2 = containsOp<ARRAY_TY>(arrayFormulas[1]);
                  if (!cp1 && cp2)
                    args1.push_back(arrayFormulas[1]);
                  else if (!cp2 && cp1)
                    args1.push_back(arrayFormulas[0]);
                  else if (!cp1 && !cp2) continue;
                  else
                    assert(0 && "not implemented");
                  candidates[srcRel].insert(mknary<FORALL>(args1));
                }
              } else if (forall == false) {
                if (hr.isInductive)
                {
                  args1.push_back(mk<AND>(arrayFormulas[1], mk<NEG>(rf)));
                  args2.push_back(mk<AND>(arrayFormulas[0], rf));
                  Expr e1 = mknary<EXISTS>(args1);
                  Expr e2 = mknary<EXISTS>(args2);
                  candidates[srcRel].insert(mk<OR>(e1, e2));
                }
                else
                {
                  bool cp1 = containsOp<ARRAY_TY>(arrayFormulas[0]);
                  bool cp2 = containsOp<ARRAY_TY>(arrayFormulas[1]);
                  if (!cp1 && cp2)
                    args1.push_back(arrayFormulas[1]);
                  else if (!cp2 && cp1)
                    args1.push_back(arrayFormulas[0]);
                  else if (!cp1 && !cp2) continue;
                  else
                    assert(0 && "not implemented");
                  candidates[srcRel].insert(mknary<EXISTS>(args1));
                }                
              }
            }
          }
        }
      }
    }

    void newWeaken(HornRuleExt& hr)
    {
      if (hr.isFact) return;

      if (hr.isQuery) {
        getQueryArrayCandidates();
        return;
      }

      assert(hr.srcRelations.size() == 1 &&
             "Nonlinear CHCs are not supported");

      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      outs () << " - - newWeaken - - " <<  srcRel << " -> " << dstRel << "\n";
      ExprSet dstCands;
      for (auto c : candidates[dstRel]) {
        dstCands.insert(simplifyBool(simplifyArithm(c)));
      }

      for (auto dcd : dstCands) {
        boost::tribool forall(boost::indeterminate);
        if (isOpX<FORALL>(dcd)) {
          forall = true;
        } else if (isOpX<EXISTS>(dcd)) {
          forall = false;
        } else {
          //TODO: handle non quantified case
          continue;
        }

        outs () << ">>>>>>>>>>>>>> next cand: "<< dcd <<"\n";

        ExprSet qVarsTmp;
        getQuantifiedVars(dcd, qVarsTmp);

        for (auto qv : qVarsTmp) {

          for (auto iv : invItrs[srcRel]) {
            Expr rf;
            if (invItrInc[srcRel]) {
              rf = mk<GEQ>(qv,iv);
            } else {
              rf = mk<LEQ>(qv,iv);
            }

            outs() << "RF: " << *rf << "\n";

            auto candidatesTmp = candidates;
            if (forall == true)
            {
              dcd = replaceAll(dcd, dcd->last(), mk<OR>(rf, dcd->last()));
            } else if (forall == false) {
              dcd = replaceAll(dcd, dcd->last(), mk<AND>(rf, dcd->last()));
            }
            
            candidatesTmp[srcRel].insert(dcd);
            if (checkCHC(hr, candidatesTmp)) {
              candidates[srcRel].insert(dcd);
            }
          }
        }
      }
    }

    
    //Backward propagation from query
    void inferInv1()
    {
      for (int i = 0; i < propOrder.size(); i++) {
        auto & hr = ruleManager.chcs[propOrder[i]];
        outs () << "\n\n\n===============\ninferInv1 for chc:  " <<
          (hr.srcRelations.empty() ? "" : lexical_cast<string>(hr.srcRelations[0]))
                << " -> " << hr.dstRelation << "\n";

        auto candidatesTmp = candidates;
        if (!hr.srcRelations.empty())
        {
          outs () << "cands [src]:  \n";
          pprint(candidates[hr.srcRelations[0]], 2);
          if (hr.srcRelations[0] != hr.dstRelation)
          {
            outs () << "cands [dst]:  \n";
            pprint(candidates[hr.dstRelation], 2);
          }
        }

        bool res = checkCHC(hr, candidates);
        if (res) {
          outs () << "   failed\n";
          newWeaken(hr);
        } else {
          abduce(hr);
          printCands(false);
          // filterUnsat();          
          vector<HornRuleExt*> worklist;
          for (int j = 0; j <= i; j++) {
            auto &hr2 = ruleManager.chcs[propOrder[j]];
            worklist.push_back(&hr2);
          }
          multiHoudini(worklist);
          
          //no progress
          if (equalCands(candidatesTmp)) {
            break;
          }
        }
      }
      
      // double check
      filterUnsat();
      if (checkAllOver(true)) {
        return printCands();
      } else {
        outs () << "unknown\n";
      }
    }

    //backward and forward, single CHC propagation
    void inferInv2()
    {
      hasArrays = true;
      for (auto & hr : ruleManager.chcs) {
        auto candidatesTmp = candidates;
        for (bool fwd : {false, true}) {
          bool res = checkCHC(hr, candidates);
          if (!res) {
            if (fwd) {
              propagateCandidatesForward(hr);
              vector<HornRuleExt*> worklist;
              worklist.push_back(&hr);
              multiHoudini(worklist);
            } else {
              propagateCandidatesBackward(hr);
              filterUnsat();
              strengthen();
            }
            //no progress
            if (equalCands(candidatesTmp)) {
              break;
            }
            inferInv2();
          }
        }
      }
      // double check
      if (checkAllOver(true)) {
        return printCands();
      } else {
        outs () << "unknown\n";
      }
    }


    //backward, multiple CHC propagation
    void inferInv3()
    {
      for (auto & hr : ruleManager.chcs) {
        auto candidatesTmp = candidates;
        bool res = checkCHC(hr, candidates);
          if (!res) {
            declsVisited.clear();
            declsVisited.insert(ruleManager.failDecl);
            propagate(false);
            filterUnsat();
            strengthen();
            if (equalCands(candidatesTmp)) {
              break;
            }
            inferInv3(); //perhaps, this call is not required?
          }
      }
      //double check
      if (checkAllOver(true)) {
        return printCands();
      } else {
        outs () << "unknown\n";
      }
    }

    //Backward and forward, multiple CHC propagation
    void guessAndSolve()
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
            outs () << "\n\n\n  ####   ITER   ####   " << globalIter << "." << fwd << "   ####\nCurrent candidates:\n";
            printCands(false);
          }
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
          propagate(fwd);
          filterUnsat();
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
          if (checkAllOver(true)) return printCands();
        }
        if (equalCands(candidatesTmp)) break;
        globalIter++;
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return printCands();
      outs () << "unknown\n";
    }

    // naive solving, without invariant generation
    int solveIncrementally(int bound, int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > bound)       // maximum bound reached
      {
        return 2;
      }
      else if (rels.empty()) // base case == init is reachable
      {
        return 0;
      }

      int res = 1;

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
          return 1;         // nothing is reachable; thus it is safe here
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
          int res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
          if (res_tmp == 0) return 0;           // bug is found for some combination
          else if (res_tmp == 2) res = 2;
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
        case 0: outs () << "sat\n"; break;
        case 1: outs () << "unsat\n"; break;
        case 2: outs () << "unknown\n"; break;
      }
    }
  };

  inline void solveNonlin(string smt, int inv, int stren)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver nonlin(ruleManager, stren);
    if (inv == 0) {
      nonlin.initRangeAbduction();
      nonlin.inferInv1();
    } else
      nonlin.solveIncrementally(inv);
  };
}

#endif
