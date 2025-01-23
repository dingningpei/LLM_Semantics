#include <cstdio>
#include <algorithm>
#include <cassert>
#include "core/options.h"
#include "core/engine.h"
#include "core/sat.h"
#include "core/sat-types.h"
#include "core/propagator.h"
#include "parallel/parallel.h"
#include "ldsb/ldsb.h"
#define PRINT_ANALYSIS 0

#include <iostream>

//---------
// inline methods

inline void SAT::learntLenBumpActivity(int l) {
	if (l >= MAX_SHARE_LEN) return;
	if (engine.conflicts % 16 == 0) {
		double new_ll_time = wallClockTime();
		double factor = exp((new_ll_time-ll_time)/learnt_len_el);
		if ((ll_inc *= factor) > 1e100) {
			for (int i = 0; i < MAX_SHARE_LEN; i++) learnt_len_occ[i] *= 1e-100;
			ll_inc *= 1e-100;
		}
		ll_time = new_ll_time;
		confl_rate /= factor;
	}
	learnt_len_occ[l] += ll_inc;
	confl_rate += 1 / learnt_len_el;
}

inline void SAT::varDecayActivity() {
	if ((var_inc *= 1.05) > 1e100) {
		for (int i = 0; i < nVars(); i++) activity[i] *= 1e-100;
		for (int i = 0; i < engine.vars.size(); i++) engine.vars[i]->activity *= 1e-100;
		var_inc *= 1e-100;
	}
}

inline void SAT::varBumpActivity(Lit p) {
	int v = var(p);
        activity[v] += var_inc;
	if (so.vsids) {
		if (order_heap.inHeap(v)) order_heap.decrease(v);
		if (so.sat_polarity == 1) polarity[v] = sign(p)^1;
		if (so.sat_polarity == 2) polarity[v] = sign(p);
	}
	if (c_info[v].cons_type == 1) {
		int var_id = c_info[v].cons_id;
		if (!ivseen[var_id]) {
			engine.vars[var_id]->activity += var_inc;
			ivseen[var_id] = true;
			ivseen_toclear.push(var_id);
		}
	}
}

inline void SAT::claDecayActivity() {
	if ((cla_inc *= 1.001) > 1e20) {
		for (int i = 0; i < learnts.size(); i++) learnts[i]->activity() *= 1e-20;
		cla_inc *= 1e-20;
	}
}

//---------
// main methods

Clause* SAT::_getExpl(Lit p) {
//	fprintf(stderr, "L%d - %d\n", decisionLevel(), trailpos[var(p)]);
	Reason& r = reason[var(p)];
	return engine.propagators[r.d.d2]->explain(p, r.d.d1);
}

Clause* SAT::getConfl(Reason& r, Lit p) {
	switch(r.d.type) {
		case 0:
			return r.pt;
		case 1:
			return engine.propagators[r.d.d2]->explain(p, r.d.d1);
		default:
			Clause& c = *short_expl;
			c.sz = r.d.type; c[1] = toLit(r.d.d1); c[2] = toLit(r.d.d2);
			return short_expl;
	}
}

void SAT::analyze() {
    //printf("Begin\n");
 Analyze:
    engine.clearPropState();
    //printf("Label\n");
    bool added_pending = false;
    
    Clause* confl_tmp = confl;
	avg_depth += 0.01*(decisionLevel()-avg_depth);

	checkConflict();
	varDecayActivity();
	claDecayActivity();
	getLearntClause();
	explainUnlearnable();
	clearSeen();

        vec<int> btlevels;
        int maxbtlevel = -1;
        for (int i = 0; i < out_learnts.size(); i++) {
            int btlevel = findBackTrackLevel(out_learnts[i]);
            btlevels.push(btlevel);
            if (btlevel > maxbtlevel)
                maxbtlevel = btlevel;
        }


	back_jumps += decisionLevel()-1-maxbtlevel;
//	fprintf(stderr, "btlevel = %d\n", btlevel);
        //fprintf(stdout,"Backjump to level: %d trail.size()==%d\n",btlevel,trail.size());
        //printf("Decision level before %d\n",decisionLevel());
        if (so.backtrack) {
            btToLevel(decisionLevel()-1);
        } else {
            btToLevel(maxbtlevel);
        }

	confl = NULL;

        int last_learnt_size = -1;
        int xuips = 0;
        for (int learnt = 0; learnt < out_learnts.size(); learnt++) {
            //out_learnt = out_learnts[learnt];
            if (last_learnt_size == out_learnts[learnt].size())
                continue;

            last_learnt_size = out_learnts[learnt].size();
            if (so.sort_learnt_level && out_learnts[learnt].size() >= 4) {
		std::sort((Lit*) out_learnts[learnt] + 2, (Lit*) out_learnts[learnt] + out_learnts[learnt].size(), lit_sort);
            }


            Clause *c = Clause_new(out_learnts[learnt], true);
            c->activity() = cla_inc;

            learntLenBumpActivity(c->size());

            //Clause::gen_to_learnt[confl_tmp] = c;

            if (so.parallel && so.learn && c->size()-(rand()/RAND_MAX) <= so.share_param) {
		slave.shareClause(*c);
            }

            //if (learnt == 0) {
            //sat.printClause(*c);
                if (so.learn && c->size() >= 2) addClause(*c, so.one_watch);
                //}

            if (so.backtrack) {
                if (!so.learn || c->size() <= 2) rtrail[btlevels[learnt]].push(c);
            } else {
                if (!so.learn || c->size() <= 2) rtrail.last().push(c);
            }               
            

            //printf(" %d clauses:\n",out_learnts.size());
            //printClause(*c);printf("\n");

            if (so.xuip == 1 || learnt == 0) {
                assert(btlevels[learnt] == findBackTrackLevel(out_learnts[learnt]));
                assert(btlevels[learnt] <= decisionLevel());
                enqueue(out_learnts[learnt][0], c->size() == 2 ? Reason(out_learnts[learnt][1]) : c);
            } else {
                if (value(out_learnts[learnt][0]) == l_Undef) {
                    assert(btlevels[learnt] == findBackTrackLevel(out_learnts[learnt]));
                    assert(btlevels[learnt] <= decisionLevel());                    
                    enqueue(out_learnts[learnt][0], c->size() == 2 ? Reason(out_learnts[learnt][1]) : c);
                    added_pending = false;
                } else if (value(out_learnts[learnt][0]) == l_False) {
                    assert(btlevels[learnt] <= decisionLevel());
                    confl = c;
                    //printf("This happened\n");
                    goto Analyze;
                }
            }
            xuips++;

            if (so.backtrack) {

                engine.forceBetterSolution();
                //if(learnt == 0) {
                    static int id_gen = 0;
                    struct BackJumpInfo current_bji;
                    current_bji.uniqueID = ++id_gen;
                    current_bji.level = btlevels[learnt];
                    current_bji.last_level = decisionLevel();
                    current_bji.c = c;
                    pending.push(current_bji);
                    //}
                if (!added_pending && learnt == 0) {
                    for (int i = pending.size() - 1; i >= 0; i--) { 
                        struct BackJumpInfo bji = pending[i];
                        if (bji.level <= decisionLevel() && value(*(bji.c)[0]) == l_Undef)  {
                            enqueue(*(bji.c)[0], bji.c->size() == 2 ? Reason(*(bji.c)[1]) : bji.c);
                            bji.last_level = decisionLevel();
                        } else if (bji.level <= decisionLevel() && value(*(bji.c)[0]) == l_False){
                            confl = bji.c;
                            //printf("This other thing happened\n");
                            goto Analyze;
                        } 
                    }
                    added_pending = false;
                }

                sat.cleanPendingClausesBelow(decisionLevel());

            }

        
            if (PRINT_ANALYSIS) printClause(*c);

            if (so.ldsbad) {
		assert(!so.parallel);
		vec<Lit> out_learnt2;
		out_learnt2.push(out_learnt[0]);
		for (int i = 0; i < decisionLevel(); i++) out_learnt2.push(~decLit(decisionLevel()-i));
		c = Clause_new(out_learnt2, true);
		rtrail.last().push(c);
            }

            if (so.ldsb && !ldsb.processImpl(c)) engine.async_fail = true;

            if (learnts.size() >= so.nof_learnts ||
		learnts_literals >= so.learnts_mlimit/4) reduceDB();
        }

        analysis_counter++;
        xuip_per_analyze += xuips;
}


void SAT::getLearntClause() {
	Lit p = lit_Undef;
	int pathC = 0;
	int clevel = findConflictLevel();
        // printf("clevel = %d\n",clevel);
        // printf("trail.size() == %d \n",trail.size());
        // printf("trail[clevel].size() == %d \n",trail[clevel].size());
        // printf("dec_info.last() == %d\n",(((IntVar*)engine.dec_info.last().var)->var_id));
	vec<Lit>& ctrail = trail[clevel];
	Clause* expl = confl;
        assert(expl != NULL);
	Reason last_reason = NULL;

	index = ctrail.size();

	out_learnts.clear();
        int current_learnt = 0;
        out_learnts.push();
	out_learnts[current_learnt].push();      // (leave room for the asserting literal)

        int old_size = 0;
        vec<int> seen_idxs;
        vec<Lit> seen_lits;
	while (true) {
StartNewUIP:
		assert(expl != NULL);          // (otherwise should be UIP)
		Clause& c = *expl;


                /*                
                if (Clause::clause2prop.find(expl) != Clause::clause2prop.end()) {
                    if (Clause::prop2contrib.find(Clause::clause2prop[expl]) == Clause::prop2contrib.end()) {
                        Clause::prop2contrib[Clause::clause2prop[expl]] = 0;
                    }
                    Clause::prop2contrib[Clause::clause2prop[expl]]++;
                }
                //*/

		if (PRINT_ANALYSIS) {
                    if (p != lit_Undef) c[0] = ~p;
			printClause(c);
		}

		if (c.learnt) c.activity() += cla_inc;
                int prev_dec_level_counter = 0;

		for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
                    
			Lit q = c[j];
			int x = var(q);

                        assert(p == lit_Undef || trailpos[x] <= trailpos[var(p)]);
			if (!seen[x] && !flags[x].opt_var_lit) {
				varBumpActivity(q);
                                seen_idxs.push(x);
                                seen_lits.push(q);
                                seen[x] = 1;
                                //engine.vars[c_info[x].cons_id]->expl_appear++;
                                if (isCurLevel(x)) {
                                    pathC++;
                                } else {
                                    out_learnts[current_learnt].push(q);
                                    prev_dec_level_counter++;
                                }
			} else if (!isCurLevel(x)) {
                            prev_dec_level_counter++;
                        }
		}

FindNextExpl:

                if (so.xuip != -1) {
                    if (pathC == 0) {
                        if(current_learnt > 0 && //For the first one, at lest one thing has to be at the current 
                           prev_dec_level_counter == c.size() - 1) { //All on the rhs of c is at prev dec level
                            out_learnts[current_learnt].resize(1);
                            assert(out_learnts[current_learnt].size() == 1);
                            for (int i = 0; i < seen_idxs.size(); i++) {
                                seen[seen_idxs[i]] = 0;
                            }
                            for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
                                Lit q = c[j];
                                int x = var(q);
                                if (!flags[x].opt_var_lit) {
                                    if (isCurLevel(x)) {
                                        NEVER;
                                    } else if(!seen[x]) {
                                        out_learnts[current_learnt].push(q);
                                        seen[x] = 1;
                                    }
                                }
                            }
                            assert(p != lit_Undef);
                            out_learnts[current_learnt][0] = ~p;  
                            assert(out_learnts.size() > 1);
                            clearSeen();
                            //out_learnts.pop();
                            break;
                        } else {
                            NEVER;
                        }
                    }
                }


		assert(pathC > 0);
		// Select next clause to look at:

		while (!seen[var(ctrail[--index])]){
                    assert(index >= 0);
                }
		p = ctrail[index];

                assert(seen[var(p)]);

		seen[var(p)] = 0;

                if(!flags[var(p)].opt_var_lit) {
                    pathC--;
                }

		if (pathC == 0 && flags[var(p)].uipable) {
                    if (so.xuip == out_learnts.size() || index == 0) {
                        out_learnts[current_learnt][0] = ~p;
                        clearSeen();
                        break;
                    } else {
                        //One more uip
                        out_learnts[current_learnt][0] = ~p;
                        clearSeen();
                        out_learnts.push();
                        current_learnt++;
                        out_learnts[current_learnt].push();      // (leave room for the asserting literal)
                        for (int i = 1; i < out_learnts[current_learnt-1].size(); i++) {
                            out_learnts[current_learnt].push(out_learnts[current_learnt -1][i]); 
                        }
                        last_reason = reason[var(p)];
                        expl = getExpl(p);
                        pathC = 0;
                        goto StartNewUIP;
                    }
                }


                if (flags[var(p)].opt_var_lit){
                    NEVER; //It is marked as not seen
                }


		if (last_reason == reason[var(p)]) {
                    goto FindNextExpl;
                }

		last_reason = reason[var(p)];
		expl = getExpl(p);
	}
}

int SAT::findConflictLevel() {
	int tp = -1;
        if(PRINT_ANALYSIS) printClause(*confl);
	for (int i = 0; i < confl->size(); i++) {
		int l = trailpos[var((*confl)[i])];
		if (l > tp) tp = l;
	}
	int clevel = engine.tpToLevel(tp);

	if (so.sym_static && clevel == 0) {
		btToLevel(0);
		engine.async_fail = true;
		NOT_SUPPORTED;
		// need to abort analyze as well
		return 0;
	}
	assert(clevel > 0);

	// duplicate conflict clause in case it gets freed
	if (clevel < decisionLevel() && confl->temp_expl) {
		confl = Clause_new(*confl);
		confl->temp_expl = 1;
		rtrail[clevel].push(confl);
	}
	btToLevel(clevel);

//	fprintf(stderr, "clevel = %d\n", clevel);

	if (PRINT_ANALYSIS) printf("Conflict: level = %d\n", clevel);

	return clevel;
}

void SAT::explainUnlearnable() {
	pushback_time -= wallClockTime();

	vec<Lit> removed;
        for (int j = 0; j < out_learnts.size(); j++) {
            for (int i = 1; i < out_learnts[j].size(); i++) {
		Lit p = out_learnts[j][i];
		if (flags[var(p)].learnable) continue;
		assert(!reason[var(p)].isLazy());
		Clause& c = *getExpl(~p);
		removed.push(p);
		out_learnts[j][i] = out_learnts[j].last(); out_learnts[j].pop(); i--;
		for (int j = 1; j < c.size(); j++) {
			Lit q = c[j];
			if (!seen[var(q)]) {
				seen[var(q)] = 1;
				out_learnts[j].push(q);
			}
		}
            }
        }

	for (int i = 0; i < removed.size(); i++) seen[var(removed[i])] = 0;

	pushback_time += wallClockTime();
}

void SAT::clearSeen() {
	for (int i = 0; i < ivseen_toclear.size(); i++) ivseen[ivseen_toclear[i]] = false;
	ivseen_toclear.clear();

        for (int j = 0; j < out_learnts.size(); j++) {
            for (int i = 0; i < out_learnts[j].size(); i++) 
                seen[var(out_learnts[j][i])] = 0;    // ('seen[]' is now cleared)

        }
}

int SAT::findBackTrackLevel(vec<Lit>& lits) {
	if (lits.size() < 2) {
		nrestarts++;
		return 0;
	}

	int max_i = 1;
	for (int i = 2; i < lits.size(); i++) {
		if (trailpos[var(lits[i])] > trailpos[var(lits[max_i])]) max_i = i;
	}
	Lit p = lits[max_i];
	lits[max_i] = lits[1];
	lits[1] = p;

	return engine.tpToLevel(trailpos[var(p)]);
}


//---------
// debug

// Lit:meaning:value:level

void SAT::printLit(Lit p) {
    ChannelInfo& ci = c_info[var(p)];
    if (isRootLevel(var(p))) {printf("RL%d:(int?%d):%d:%d, ", toInt(p), ci.cons_type == 1,var(p),assigns[var(p)]); return;}
    printf("%d:", toInt(p));
    if (ci.cons_type == 1) {
        engine.vars[ci.cons_id]->printLit(ci.val, ci.val_type * 3 ^ sign(p));
    } else if (ci.cons_type == 2) {
        engine.propagators[ci.cons_id]->printLit(ci.val, sign(p));
    } else {
        printf(":%d:%d:%d,%d, ", sign(p), trailpos[var(p)],var(p),assigns[var(p)]);
    }
}

template <class T>
void SAT::printClause(T& c) {
	printf("Size:%d - ", c.size());
	printLit(c[0]);
	printf(" <- ");
	for (int i = 1; i < c.size(); i++) printLit(~c[i]);
	printf("\n");
}

void SAT::checkConflict() {
	assert(confl != NULL);
	for (int i = 0; i < confl->size(); i++) {
		if (value((*confl)[i]) != l_False) printf("Analyze: %dth lit is not false\n", i);
		assert(value((*confl)[i]) == l_False);
	}

/*
	printf("Clause %d\n", learnts.size());
	printf("Conflict clause: ");
	printClause(*confl);
*/

}

void SAT::checkExplanation(Clause& c, int clevel, int index) {
	NOT_SUPPORTED;
	for (int i = 1; i < c.size(); i++) {
		assert(value(c[i]) == l_False);
		assert(trailpos[var(c[i])] < engine.trail_lim[clevel]);
		vec<Lit>& ctrail = trail[trailpos[var(c[i])]];
		int pos = -1;
		for (int j = 0; j < ctrail.size(); j++) {
			if (var(ctrail[j]) == var(c[i])) {
				pos = j;
				if (trailpos[var(c[i])] == clevel) assert(j <= index);
				break;
			}
		}
		assert(pos != -1);
	}

}

