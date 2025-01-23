#include <cstdio>
#include <iostream>
#include <cassert>
#include "core/options.h"
#include "core/engine.h"
#include "core/sat.h"
#include "core/propagator.h"
#include "branching/branching.h"
#include "mip/mip.h"
#include "parallel/parallel.h"
#include "ldsb/ldsb.h"
#include "mdd/opts.h"
#include "globals/mddglobals.h"
#include <stack>

Engine engine;

uint64_t bit[65];
uint32_t bit32[33];

int hash_counter = 0;
vec<int> core_key;
vec<int> dom_key;

int mdd_hash_hits = 0;

Tint trail_inc;

Engine::Engine() :
		finished_init(false)
	, problem(NULL)
	, opt_var(NULL)
	, best_sol(-1)
	, last_prop(NULL)

	, start_time(wallClockTime())
	, opt_time(0)
        , first_time(0)
	, conflicts(0)
	, nodes(1)
	, propagations(0)
	, solutions(0)
	, next_simp_db(0)
        , static_key(NULL)
        , hash_hits(0)
        , collisions(0)
{
	p_queue.growTo(num_queues);
	for (int i = 0; i < 64; i++) bit[i] = ((long long) 1 << i);
	branching = new BranchGroup();
        //if (so.mip)
        mip = new MIP();

        hsh = new Entry*[TABLESIZE];        
	rassert(hsh);
	memset(hsh, 0, TABLESIZE * sizeof(Entry*));
        hsh_count = 0;
	for (int i = 0; i < 32; i++) bit32[i] = (1 << i);

}

void Engine::newDecisionLevel() {
    //printf("New dec\n");
	trail_inc++;
	trail_lim.push(trail.size());
	sat.newDecisionLevel();
	if (so.mip) mip->newDecisionLevel();
	assert(dec_info.size() == decisionLevel());
}

void Engine::doFixPointStuff() {
	// ask other objects to do fix point things

	for (int i = 0; i < pseudo_props.size(); i++) {
		pseudo_props[i]->doFixPointStuff();
	}
}

void Engine::makeDecision(DecInfo& di, int alt) {
    ++nodes;
    //fprintf(stdout,"DECISION******************************************* %d %d\n", decisionLevel(),di.val);
    for (int i = 0; i < propagators.size(); i++)
        propagators[i]->notifyNewDecLevel();

    if (!so.nonbinary) {
        /* TODO: Change this to make it always work? Chuffed doesnt support bools in the search strategy?
           if (di.var && ((Var*)di.var)->getType() == BOOL_VAR) 
           ((BoolView*) di.var)->setVal(di.val); 
           else //*/
        if (di.var) {
            //printf("Decision: %p [=?%d] %d\n",di.var,di.type ^ alt, di.val);
            ((IntVar*) di.var)->set(di.val, di.type ^ alt);
        } else {
            sat.enqueue(toLit(di.val ^ alt));
        }

        //fprintf(stdout,"DECISION*******************************************\n");
        //	if (opt_var && di.var == opt_var && ((IntVar*) di.var)->isFixed()) printf("objective = %d\n", ((IntVar*) di.var)->getVal());

    } else {
        if (so.use_hash) {
            assert(entries.size() == trail_lim.size());
            assert(branchingDescs.size() == entries.size());
	}

	BranchingDesc& b = branchingDescs.last();
	DecInfo& di = b.choices[b.alt++];


        //printf("Decision: %p [=?%d] %d\n",di.var,di.type, di.val);
	if (di.var) ((IntVar*) di.var)->set(di.val, di.type);
	else sat.enqueue(toLit(di.val));
    }

    if (so.ldsb && di.var && di.type == 1) 
        ldsb.processDec(sat.trail.last()[0]);
}

void optimize(IntVar* v, int t) {
	engine.opt_var = v;
	engine.opt_type = t;
	engine.branching->add(v);
	v->setPreferredVal(t == OPT_MIN ? PV_MIN : PV_MAX);

}

inline bool Engine::constrain() {
	best_sol = opt_var->getVal();
	opt_time = wallClockTime() - start_time - init_time;

        entries.clear();
        branchingDescs.clear();

        if (so.backtrack) {
            if (!opt_type) {
                while (best_sol <= opt_var->getMin() && decisionLevel() > 0) {
                    //printf("Backtracking to level %d, ",decisionLevel()-1);
                    //printf("opt_var = [%d,%d]\n",engine.opt_var->getMin(), engine.opt_var->getMax());
                    sat.btToLevel(decisionLevel()-1);
                }
            } else {
                while (best_sol >= opt_var->getMin() && decisionLevel() > 0) {
                    sat.btToLevel(decisionLevel()-1);
                }
            }
        } else {
            sat.btToLevel(0);
        }

	if (so.parallel) {
		Lit p = opt_type ? opt_var->getLit(best_sol+1, 2) : opt_var->getLit(best_sol-1, 3);
		vec<Lit> ps;
		ps.push(p);
		Clause *c = Clause_new(ps, true);
		slave.shareClause(*c);
		free(c);
	}

//	printf("opt_var = %d, opt_type = %d, best_sol = %d\n", opt_var->var_id, opt_type, best_sol);
//	printf("opt_var min = %d, opt_var max = %d\n", opt_var->min, opt_var->max);

	if (so.mip) mip->setObjective(best_sol);
        
        if (so.lazy && so.backtrack) {
            if(!forceBetterSolution()) {
                //You can't find a better solution! You got to decisionLevel == 0 and 
                //the bound wont let you find anything better.
                return false;
            }
            sat.cleanPendingClausesBelow(decisionLevel());
            return true;
        } else {
            return (opt_type ? opt_var->setMin(best_sol+1) : opt_var->setMax(best_sol-1));
        }
            
}

bool Engine::propagate() {
	if (async_fail) {
		async_fail = false;
		assert(!so.lazy || sat.confl);
		return false;
	}

	last_prop = NULL;

	WakeUp:
        bool satc = sat.consistent();
        bool satp = sat.propagate();
	if (!satc && !satp) 
            return false;
	for (int i = 0; i < v_queue.size(); i++) {
		v_queue[i]->wakePropagators();
	}
	v_queue.clear();

	if (sat.confl) 
            return false;

	last_prop = NULL;

	for (int i = 0; i < num_queues; i++) {
		if (p_queue[i].size()) {
			Propagator *p = p_queue[i].last(); p_queue[i].pop();
			propagations++;
			bool ok = p->propagate();
			p->clearPropState();
			if (!ok)  {
                            //printf("Propagator %d cuased failure\n",p->prop_id);
                            return false;
                        }
			goto WakeUp;
		}
	}

	return true;
}

// Clear all uncleared intermediate propagation states
void Engine::clearPropState() {
	for (int i = 0; i < v_queue.size(); i++) v_queue[i]->clearPropState();
	v_queue.clear();

	for (int i = 0; i < num_queues; i++) {
		for (int j = 0; j < p_queue[i].size(); j++) p_queue[i][j]->clearPropState();
		p_queue[i].clear();
	}

        sat.new_sat.clear();
}

void Engine::btToPos(int pos) {
	for (int i = trail.size(); i-- > pos; ) {
		trail[i].undo();
	}
  trail.resize(pos);
}

void Engine::btToLevel(int level) {
	if (decisionLevel() == 0 && level == 0) return;
	assert(decisionLevel() > level);

	btToPos(trail_lim[level]);
  trail_lim.resize(level);
	dec_info.resize(level);
}



void Engine::topLevelCleanUp() {
	trail.clear();

	if (so.fd_simplify && propagations >= next_simp_db) simplifyDB();

	sat.topLevelCleanUp();
}

void Engine::simplifyDB() {
	int cost = 0;
	for (int i = 0; i < propagators.size(); i++) {
		cost += propagators[i]->checkSatisfied();
	}
	cost += propagators.size();
	for (int i = 0; i < vars.size(); i++) {
		cost += vars[i]->simplifyWatches();
	}
	cost += vars.size();
	cost *= 10;
//	printf("simp db cost: %d\n", cost);
	next_simp_db = propagations + cost;
}

void Engine::blockCurrentSol() {
	if (outputs.size() == 0) NOT_SUPPORTED;
	Clause& c = *Reason_new(outputs.size());
	bool root_failure = true;
	for (int i = 0; i < outputs.size(); i++) {
		Var *v = (Var*) outputs[i];
		if (v->getType() == BOOL_VAR) {
			c[i] = ((BoolView*) outputs[i])->getValLit();
		} else {
			c[i] = ((IntVar*) outputs[i])->getValLit();
		}
		if (!sat.isRootLevel(var(c[i]))) root_failure = false;
		assert(sat.value(c[i]) == l_False);
	}
	if (root_failure) sat.btToLevel(0);
	sat.confl = &c;
}


int Engine::getRestartLimit(int starts) {
//	return so.restart_base * ((int) pow(1.5, starts));
//	return so.restart_base;
	return (((starts-1) & ~starts) + 1) * so.restart_base;
}

void Engine::toggleVSIDS() {
	if (!so.vsids) {
		vec<Branching*> old_x;
		branching->x.moveTo(old_x);
		branching->add(&sat);
		for (int i = 0; i < old_x.size(); i++) branching->add(old_x[i]);
		branching->fin = 0;
		branching->cur = -1;
		so.vsids = true;
	} else {
		vec<Branching*> old_x;
		branching->x.moveTo(old_x);
		for (int i = 1; i < old_x.size(); i++) branching->add(old_x[i]);
		branching->fin = 0;
		branching->cur = -1;
		so.vsids = false;
	}
}

Entry::Entry() {
	id = hash_counter++;
	ck = new int[core_key.size()];
	dk = new int[dom_key.size()];
	ck[0] = core_key.size();
	edk = dk + dom_key.size();
	for (int i = 1; i < core_key.size(); i++) ck[i] = core_key[i];
	for (int i = 0; i < dom_key.size(); i++) dk[i] = dom_key[i];
	h = murmurHash2(ck, core_key.size()) & (TABLESIZE-1);
        use_count = 0;
}

bool Entry::equiv(Entry *n) {
	if (n->h != h) return false;
        //printf("test1\n");
	if (n->ck[0] != ck[0]) return false;
        //printf("test2\n");
	if (n->dk[0] != dk[0]) return false;
        //printf("test3\n");
	for (int i = 1; i < ck[0]; i++) {
		if (n->ck[i] != ck[i]) return false;
	}
        return true;
}

bool Entry::dominate(Entry *n) {
	if (n->h != h) return false;
        //printf("test1\n");
	if (n->ck[0] != ck[0]) return false;
        //printf("test2\n");
	if (n->dk[0] != dk[0]) return false;
        //printf("test3\n");
	for (int i = 1; i < ck[0]; i++) {
		if (n->ck[i] != ck[i]) return false;
	}
        //printf("test4 ,   %d\n",dk[0]);
	int *a = n->dk+1;
	int *b = dk+1;
	for (int i = 0; i < dk[0]; i++) {
		if (*a != *b) return false;
		switch ((((unsigned int) *a) >> 30)) {
			case 0:
				// integer dom
				if (a[1] > b[1]) return false;
				a += 2;
				b += 2;
				break;
			case 1:
				// SET dom
				if (a[1] & ~b[1]) return false;
				if (a[2] & ~b[2]) return false;
				a += 3;
				b += 3;
				break;
			case 2:
				// Range set dom
                                if (a[1] < b[1] || a[2] > b[2]) return false;
                                a += 3;
                                b += 3;
				//assert(false);
				break;
			case 3:
				// Variable length SET dom
				if (a[1] != b[1]) return false;
				for (int i = 2; i <= a[1]; i++) {
					// a is not subset of b, then false
					if (a[i] & ~b[i]) return false;
				}
				a += a[1]+2;
				b += b[1]+2;
				break;
			default:
				assert(false);
				break;
		}
	}
	assert(a == n->edk);
	assert(b == edk);

	return true;
}

void Engine::shrinkhash(std::unordered_map<Entry*,_MDD>& pb2nd, int min) {

    //if (hsh_count %100000 == 0) printf("%d\n",hsh_count);
    int new_min = min+1;
    if (hsh_count >= MAX_HASH_SIZE) {
        printf("Clearing hash [%d hits]...\n",mdd_hash_hits);
        for (int i = 0; i < TABLESIZE; i++) {
            Entry* r = hsh[i];
            Entry* p = NULL;
            while (r) {
                if (r->use_count <= min) {
                    if (p == NULL) {
                        hsh[i] = r->next;
                    } else {
                        p->next = r->next;
                    }
                    delete r;
                    pb2nd.erase(r);
                    hsh_count--;
                } else {
                    p = r;
                    new_min = new_min < r->use_count ? new_min : r->use_count;
                }
                r = r->next;
            }
        }
        shrinkhash(pb2nd,new_min); //Very ugly.. will find a better way
        printf("Done [size now is %d]\n",hsh_count);
    }
}

Entry* Engine::checkhash() {
    bool log = false;
    core_key.clear(); core_key.push(0);
    dom_key.clear(); dom_key.push(0);

    if (so.use_static) {
        //		static_key->getKey();
    } else {
        if (log) printf("entries.size() = %d  | decisionlevel = %d\n", entries.size(), decisionLevel());
        for (int i = 0; i < keyables.size(); i++) {
            keyables[i]->getKey();
        }
        if (log) printf("keyables = %d, var_keys = %d\n", keyables.size(), var_keys.size());
        for (int i = 0; i < var_keys.size(); i++) {
            var_keys[i]->getKey();
        }
        var_keys.clear();
        sat.getKey();
        core_key.push(-99999);
        for (int i = 0; i < bvars.size(); i++) {
            if (sat.assigns[bvars[i]]) //Bool fixed
                core_key.push(i);
        }
    }

    if (log) {
        printf("Core keys[%d]: ",core_key.size());
        for (int i = 0; i < core_key.size(); i++) printf("%d ",core_key[i]);
        printf("\nDoms keys[%d]: ",dom_key.size());
        for (int i = 0; i < dom_key.size(); i++) printf("%d ",dom_key[i]);
        printf("\n");
    }
    //problem->print();



    Entry *n = new Entry();
    if(log) printf("Create hash %d [key=%d, address = %p]\n", n->id,n->h,n);

    
    /*if (n->id == 1135 || n->id == 1403) {
        for (int i = 1; i < keyables.size(); i++) {
            IntVar* v = (IntVar*)keyables[i];
            printf("%d [",i);
            for (int j = v->getMin(); j <= v->getMax(); j++) 
                if (v->indomain(j))
                    printf("%d,",j);
            printf("]\n");
        }
        printf("Core keys[%d]: ",core_key.size());
        for (int i = 0; i < core_key.size(); i++) printf("%d ",core_key[i]);
        printf("\nDoms keys[%d]: ",dom_key.size());
        for (int i = 0; i < dom_key.size(); i++) printf("%d ",dom_key[i]);
        printf("\n");
        printf("\n\n");
        }*/
    

    Entry *r = hsh[n->h];
    if (log) printf("Match found %p\n",r);
    int cols = 0;
    while (r && !r->equiv(n)) { //(!r->dominate(n) || !n->dominate(r))) {
        cols++;
        r = r->next;
    }
    if(log) {
        printf("cols %d, r = %p\n ", cols,r);
        //problem->print();
    }

    if (r) {
        assert(r != n);
        //assert(r->dominate(n));
        //assert(n->dominate(r));
        hash_hits++;
        if (log) {
          printf("hit: %d/%d ", r->id, n->id);
          for (int i = 0; i < core_key.size(); i++) printf("%x ", core_key[i]);
           		for (int i = 0; i < 3; i++) printf("%x ", dom_key[i]);
          printf("\n");
        }
        delete n;
        r->use_count++;
        return r;
    }

    entries.push(n);

    return NULL;
}

void Engine::sethash() {
    if (entries.size() == 0) return; //Nothing to do! Root level I guess?
    assert(entries.size() > 0);
    Entry *e = entries.last(); entries.pop();
    if (hsh[e->h]) collisions++;
    e->next = hsh[e->h];
    hsh[e->h] = e;
    hsh_count++;
    //printf("Setting hash [entry=%p]\n",e);
}

RESULT Engine::search() {
        starts = 0;
	int nof_conflicts = so.restart_base;
	int conflictC = 0;
    bool cached_conflict = false;
    bool relaxed_assumptions = false;
    double last_interval = wallClockTime(); //Last interval for so.relax_after
RecoverSearch:

	while (true) {
		if (so.parallel && slave.checkMessages()) return RES_UNK;
                //printf("Decision elvel %d %d\n",decisionLevel(),sat.confl == NULL);

		if (!propagate()) {
			clearPropState();

			Conflict:
                        //printf("CONFLICT!!\n");
			conflicts++; conflictC++;


                        if (time(NULL) > so.time_out) {
                            if (!solutions && so.allow_overtime) {
                                //no-op
                            } else {
                                printf("\%\%Time limit exceeded!\n");
                                if (!solutions && so.show_partial_solution) {
                                    printf("\%\%Showing partial solution\n");
                                    problem->print();
                                    printf("\%\%The above is a partial solution\n");
                                }
                                return RES_UNK;
                            }
                        }
			if (decisionLevel() == 0) { return RES_GUN; }

			// Derive learnt clause and perform backjump
			if (so.lazy && !cached_conflict) {
                            if (sat.getConflictLevel() <= 0) {
                                printf("\%\%Some conflict happened at level 0, thus UNSAT\n");
                                return RES_GUN;
                            }
                            sat.analyze();
                        } else {
                            if (!so.nonbinary) {
                                sat.confl = NULL;
                                DecInfo& di = dec_info.last();
                                sat.btToLevel(decisionLevel()-1);
                                makeDecision(di, 1);
                                forceBetterSolution();
                                cached_conflict = false;  
                            } else {
                                sat.confl = NULL;
                                //printf("From decision level %d....\n",decisionLevel());
                                sat.btToLevel(decisionLevel()-1);
                                while (branchingDescs.last().finished()) {
                                    branchingDescs.last().choices.clear(true);
                                    branchingDescs.pop();
                                    if (!branchingDescs.size()) {
					return RES_GUN;
                                    }
                                    if (so.use_hash) sethash();
                                    //exit(1);
                                    sat.btToLevel(decisionLevel()-1);
                                }
                                //printf("....back to decision level %d\n",decisionLevel());
                                DecInfo dummy(NULL,-1); 
                                dec_info.push(dummy); 
                                newDecisionLevel();
                                makeDecision(dummy,-1);
                            }                          
			}
                        if (!so.vsids && !so.toggle_vsids &&  conflictC >= so.switch_to_vsids_after) {
                            printf("\%\%Switched to VSIDS\n");
                            if (so.restart_base >= 1000000000) so.restart_base = 100;
                            sat.btToLevel(0);
                            toggleVSIDS();
                        }

		} else {

                    //fprintf(stderr, "hash test %d\n",so.use_hash);
                    if (so.use_hash && checkhash()) {
                        //fprintf(stderr, "hash hit at conflict %d\n", conflicts+1); 
                        cached_conflict = true;
                        goto Conflict;
                    }


			if (conflictC >= nof_conflicts) {
                            //fprintf(stderr,"Restart!\n");
				starts++;
				nof_conflicts += getRestartLimit((starts+1)/2);
				sat.btToLevel(0);
				sat.confl = NULL;
				if (so.lazy && so.toggle_vsids && (starts % 2 == 0)) toggleVSIDS();

                                //Simplify 
                                for (int i = 0; i < propagators.size(); i++) {
                                    propagators[i]->simplify();
                                }


				continue;
			}
			

            if (!solutions && so.soft_assumptions && so.relax_every != -1 && 
                wallClockTime() - last_interval > so.relax_every) {
                //Relaxing half of the assumptions:
                if (assumptions.size()) {
                    int len = assumptions.size();
                    fprintf(stderr, "Relaxing assumptions\n");
                    if (so.relax_every_mode == 0) {
                        while (assumptions.size() > len/2)
                            assumptions.pop();
                    } else {
                        while (assumptions.size() > len/2) {
                            int arg_max = 0;
                            double max = 0;
                            for (int i = 0; i < assumptions.size(); i++) {
                                if (max < sat.activity[var(toLit(assumptions[i]))]) {
                                    max = sat.activity[var(toLit(assumptions[i]))];
                                    arg_max = i;
                                }
                            }
                            assumptions[arg_max] = assumptions[assumptions.size() - 1];
                            assumptions.pop();
                        }
                    }
                    fprintf(stderr, "Assumptions left: %d.\n",assumptions.size());
                    sat.btToLevel(0);
                    sat.confl = NULL;
                    last_interval = wallClockTime();
                }
            }

			if (decisionLevel() == 0) topLevelCleanUp();

			DecInfo *di = NULL;
			//printf("Current Decision Leve: %d \n",decisionLevel());
			// Propagate assumptions
			while (decisionLevel() < assumptions.size()) {
				int p = assumptions[decisionLevel()];
                //cout<<"Assuming "<<p<<endl;
				if (sat.value(toLit(p)) == l_True) {
					// Dummy decision level:
					assert(sat.trail.last().size() == sat.qhead.last());
					engine.dec_info.push(DecInfo(NULL, p));
					newDecisionLevel();
				} else if (sat.value(toLit(p)) == l_False) {
                    if (solutions || !so.soft_assumptions) return RES_GUN;
                    fprintf(stderr, "Problem is unsatisfiable. Relaxing assumptions to recover (Lit: %d).\n",p);
                    relaxed_assumptions = true;
                    if (assumptions.size() == 1) {
                        assumptions.pop();  //Only one assumption and it fails: remove it
                    } else {
                        vec<char> my_seen; my_seen.growBy(sat.seen.size(),0);
                        Clause* tmp = sat.getExpl(toLit(p));
                        assert(tmp);
                        vec<Lit> assum;
                        for (int i = 1; i < tmp->size(); i++) {
                            assum.push((*tmp)[i]);
                            //cout<<toInt(assum.last())<<",";
                        }
                        //cout<<endl;

                        //cout<<"Expl has size "<<tmp->size()<<endl;
                        for (int i = 0; i < assum.size(); i++) {
                            if (assumptions.size() == 0)
                                break;
                            Lit p = assum[i];
                            //cout<<"  Looking at "<<toInt(~p)<<endl;
                            bool is_assum = false;
                            for (int j = 0; j < assumptions.size(); j++) {
                                if (toInt(~p) == assumptions[j] || toInt(p) == assumptions[j]) {
                                    is_assum = true;
                                    //cout<<"    Removed assumption "<<toInt(p)<<endl;
                                    assumptions[j] = assumptions.last(); assumptions.pop(); j--;
                                }
                            }
                            if (is_assum) {
                                //cout<<"     Is Assumption"<<endl;
                                continue;
                            }
                            Clause* tmp = sat.getExpl(~p);
                            if (!tmp) {
                                assert(sat.trailpos[var(p)] == -1); //Was decided at the root level.
                                continue;
                            } else if (sat.trailpos[var(p)] == -1) {
                                continue; //Was decided at the root level.
                            }
                            assert(tmp);
                            Clause& c = *tmp;
                            //cout<<"      Expl has size "<<c.size()<<endl;
                            for (int j = 1; j < c.size(); j++) {
                                Lit q = c[j];
                                if (!my_seen[var(q)]) {
                                    //cout<<"     Added "<<toInt(q)<<endl;
                                    my_seen[var(q)] = 1;
                                    assum.push(q);
                                }
                            }
                        }
                    }

                    fprintf(stderr, "Assumptions left: %d.\n",assumptions.size());
                    sat.btToLevel(0);
                    goto RecoverSearch;

					return RES_LUN;
				} else {
					di = new DecInfo(NULL, p);
					break;
				}
			}


			if (!di) di = branching->branch();
                        //printf("Branched\n");
			if (!di) {
                fflush(stderr);
                if (so.check_prop) {
                    for (int i = 0; i < propagators.size(); i++) {
                        if(!propagators[i]->checkFinalSatisfied())
                            printf("ERROR: Some propagator is not satified for the following solution\n");
                    }
                }
                solutions++;
                if (so.print_sol) {
                    problem->print();
                    //printStats();
                    printf("time = %.2f;\n",wallClockTime() - start_time - init_time);
                    printf("----------\n");
                    //printf("solution found : obj = %d\n",opt_var->getVal());
                    //printf("Solution at level %d\n",decisionLevel());
                    fflush(stdout);
                    //toggleVSIDS();
				}
                if (solutions == 1) 
                    first_time = wallClockTime() - start_time - init_time;
                if (relaxed_assumptions && solutions == 1)
                    return RES_GUN;
				if (!opt_var) {
                    if (solutions == so.nof_solutions) return RES_SAT;
					if (so.lazy) blockCurrentSol();
					goto Conflict;
				}
				if (!constrain()) {
					return RES_GUN;
				}
				continue;
			}


			engine.dec_info.push(*di);

                        newDecisionLevel();

			doFixPointStuff();
                        
			makeDecision(*di, 0);

                        if (!so.nonbinary)
                            delete di; //In non binary this is an actual DecInfo that is needed in branchingDescs

		}
	}
}

bool test_mdd(MDDTable* tab, _MDD n, vec<IntView<4> >& vars);
bool test_mdd(MDDTable* tab, _MDD n, vec<IntVar*>& v);
int  mdd2mzn(MDD mdd, vec<IntVar*>& v);
void Engine::solve(Problem *p) {
	problem = p;

	init();

        /* FOR DEBUGGING
        for (auto it = mddfied_variables.begin(); 
             it != mddfied_variables.end(); ++it) {

            MDD& mdd = engine.loaded_mdds[it->first];
            mdd.table->print_mdd(mdd.val);

            vec<IntVar*> v;
            for (auto jt = it->second.begin(); 
                 jt != it->second.end(); ++jt) {
                v.push(*jt);
            }

            //v[0]->setVal(3);
            //if (v[1]->getMin()<5) v[1]->setMin(5); if(v[1]->getMax()>14)v[1]->setMax(14);
            //if(v[2]->getMin()<0)  v[2]->setMin(0); if(v[2]->getMax()>1) v[2]->setMax(1);
            
            //printf("Prop? %d\n",engine.propagate());
            //exit(0);

            vec<IntView<4> > views;
            for (int i = 0; i < v.size(); i++) {
                views.push(IntView<4>(v[i],1,mdd.shifts[i]));
            }
            //mdd2mzn(mdd,v);
            //mdd.table->print_mdd(mdd.val);
            mdd.val = mdd.table->mdd_not(mdd.val);
            bool ok = test_mdd(mdd.table,mdd.val,views);
            fprintf(stderr,"OK ===== %d\n",ok);
            assert(ok);
            assert(decisionLevel() == 0);
        }
        exit(0);
        //*/

	so.time_out += time(NULL);

        if (so.mddfy && so.presolve) {

            if (mddfied_variables.size() != 1) {
                fprintf(stderr,"Presolve: Error, no variables marked to be MDDfied.\n");
            }            
            assert(mddfied_variables.size() == 1);
            vec<IntVar*> v;
            for (auto jt = mddfied_variables.begin()->second.begin(); 
                 jt != mddfied_variables.begin()->second.end(); ++jt) {
                v.push(*jt);
                //printf("Taking out variabe %p\n",*jt);
            }

            MDD mdd = build_mdd(v);
            double time_mdd = wallClockTime() - start_time;
            int nbnodes = -1;
            if (false) {
                for (int i = 0; i < mdd.shifts.size(); i++) {
                    printf("%d:%d ",i,mdd.shifts[i]);
                }
                printf("\n");
                mdd.table->print_mdd(mdd.val);
            } else {
                nbnodes = mdd2mzn(mdd, v);
            }
            fprintf(stderr,"\nTime to build MDD: %.2f seconds\n",time_mdd);
            fprintf(stderr,"Hash hits: %d\n",mdd_hash_hits);
            fprintf(stderr,"MDD nodes: %d\n",nbnodes);
            
            if (so.presolve_test) {
                //For testing:
                MDDOpts mopts;
                vec<IntView<4> > views;
                for (int i = 0; i < v.size(); i++) {
                    views.push(IntView<4>(v[i],1,mdd.shifts[i]));
                }
                fprintf(stderr,"Testing built MDD\n");
                mdd.val = mdd.table->mdd_not(mdd.val);
                bool ok = test_mdd(mdd.table,mdd.val,v);
                fprintf(stderr,"OK ===== %d\n",ok);
                assert(ok);
            }
            if (so.verbosity >= 1) printStats();
            return ;
        }

        if (so.mddfy) {
            bool lazy = so.lazy;
            std::vector<MDDProp<4>* > mddprops;
            so.lazy = false;
            for (auto it = mddfied_variables.begin(); 
                 it != mddfied_variables.end(); ++it) {
                vec<IntVar*> v;
                for (auto jt = it->second.begin(); 
                     jt != it->second.end(); ++jt) {
                    v.push(*jt);
                }
                //printf("MDDfying annotated variables %d (%d)\n",it->first);
                mddfy(v,false);
                mddfy(v,true);
                assert(decisionLevel() == 0);
            }
            //printf("Done Mddfy-ing [%d MDDs, %d hits]. Starting search.\n",mddfied_variables.size(),mdd_hash_hits);
            conflicts = 0;
            nodes = 0;
            propagations = 0;            
            so.lazy = lazy;
        }
        assert(decisionLevel() == 0);

	init_time = wallClockTime() - start_time;
	base_memory = memUsed();

        forceBetterSolution();


	if (!so.parallel) {
		// sequential
		status = search();
		if (status == RES_GUN) {
                    if (solutions > 0) {
                        if(opt_var)
                            printf("=== Best solution is %d ===\n",best_sol);
                        printf("==========\n");
                    } else {
				printf("=====UNSATISFIABLE=====\n");
                    }
		}
	} else {
		// parallel
		if (so.thread_no == -1) master.solve();
		else slave.solve();
		if (so.thread_no == -1 && master.status == RES_GUN) printf("==========\n");
	}

	if (so.verbosity >= 1) printStats();

  if (so.parallel) master.finalizeMPI();
}


bool Engine::forceBetterSolution() {
    if (!engine.opt_var) return true;
    int sol = best_sol;
    if (!so.backtrack) return true;
    bool maximize = engine.opt_type;

    if (solutions == 0) {
        if (maximize)
            sol = engine.opt_var->getMin()-1;
        else
            sol = engine.opt_var->getMax()+1;
    }


    if(so.lazy) {
        //Learning
        if(maximize) {
            Lit l = engine.opt_var->getLit(sol+1,2);
            sat.flags[var(l)].setOptVarLit();
            sat.best_sol_lit = l;                    
            if(sat.value(l) == l_Undef) {
                sat.enqueue(l); // GE
            } else if (sat.value(l) == l_False) {
                printf("opt_var = [%d,%d]\n",engine.opt_var->getMin(), engine.opt_var->getMax());
                //goto Analyze;
                //NEVER;
                return false;
            }
            sat.trailpos[var(l)] = -1;
        } else {
            Lit l = engine.opt_var->getLit(sol-1,3);
            sat.flags[var(l)].setOptVarLit();
            sat.best_sol_lit = l;
            if(sat.value(l) == l_Undef) {
                sat.enqueue(l); // LE
            } else if (sat.value(l) == l_False) {
                printf("opt_var = [%d,%d]\n",engine.opt_var->getMin(), engine.opt_var->getMax());
                //goto Analyze;
                //NEVER;
                return false;
            }
            sat.trailpos[var(l)] = -1;                
        }

    } else {
        //Not learning
        if(opt_type && opt_var->setMinNotR(sol+1)) 
            return opt_var->setMin(sol+1);
        else if (opt_var->setMaxNotR(sol-1))
            return opt_var->setMax(sol-1);
    }
    return true;

}

bool valid_asg(vec<IntView<4> >& v, int c, bool log) {
    if (c == v.size()) {        
        if(log) {
            fprintf(stderr,">>>>>>>>>>>>>ASG=[");
            for (int i = 0; i < v.size(); i++) {
                if (!v[i].isFixed()) fprintf(stderr,"<%d,%d>,",v[i].getMin(), v[i].getMax());
                else fprintf(stderr,"%d,",v[i].getVal());
            }
            fprintf(stderr,"]\n");
        }
        return true;
    }
    bool found = false;
    for (int d = v[c].getMin(); d <= v[c].getMax(); d++) {
        if (!v[c].indomain(d)) continue;
        if (v[c].isFixed()) return valid_asg(v,c+1,log);
        DecInfo* di = NULL;
        di = new DecInfo(v[c].var,d-v[c].b,1); // x == d
        engine.dec_info.push(*di);            
        engine.newDecisionLevel();            
        engine.doFixPointStuff();
        engine.makeDecision(*di, 0);
        delete di;
        bool ok = engine.propagate();
        engine.clearPropState();
        sat.confl = NULL;
        if (ok){            
            found |= valid_asg(v,c+1,log);
        } 
        sat.btToLevel(engine.decisionLevel() - 1);
    }

    return found;
}

bool _test_mdd(MDDTable* tab, _MDD n, vec<IntView<4> >& vars) {
    bool log = false;
    if(log)fprintf(stderr,"Testing MDD!!\n");
    
    if(log) {
        fprintf(stderr,">>>>>>>>>>>>>[");
        for (int i = 0; i < vars.size(); i++) {
            if (!vars[i].isFixed()) fprintf(stderr,"<%d,%d>,",vars[i].getMin(), vars[i].getMax());
            else fprintf(stderr,"%d,",vars[i].getVal());
        }
        fprintf(stderr,"]\n");
    }


    const std::vector<MDDNode>& nodes = tab->getNodes();
    if (n == 1) {
        bool v = !valid_asg(vars,0,log);
        if(log) fprintf(stderr,"At node 1, not valid_assign? v == %d(should be 1) \n",v);
        return v;
    }
    if (n == 0) {
        bool v = valid_asg(vars,0,log);
        if(log) fprintf(stderr,"At node 0, valid_assign? v == %d(should be 1) \n",v);     
        return true;//v;
    }
    if(log)fprintf(stderr,"Popped node %d [%d]\n",n,nodes[n]->sz);

    for(int d = vars[nodes[n]->var].getMin(); d <= vars[nodes[n]->var].getMax(); d++ )
    {
        if (!vars[nodes[n]->var].indomain(d)) continue;
        //int jj = get_edge(d,n,nodes);
        int jj = 0;
        while (jj < nodes[n]->sz && d > nodes[n]->edges[jj].val) {
            jj++;
        }
        if (nodes[n]->edges[jj].val == d) {
            //return start;
        } else if (jj > 0) {
            jj--;//return start-1;  //You are pointing one edge ahead
        }
        bool ok = true;
        bool made_dec = false;
        if (!vars[nodes[n]->var].isFixed()) {
            DecInfo* di = NULL;
            di = new DecInfo(vars[nodes[n]->var].var,d-vars[nodes[n]->var].b,1); // x == d
            engine.dec_info.push(*di);            
            engine.newDecisionLevel();            
            engine.doFixPointStuff();
            engine.makeDecision(*di, 0);
            delete di;
            if(log)fprintf(stderr,"Set variable %d(%p) to %d\n",nodes[n]->var,vars[nodes[n]->var].var,d-vars[nodes[n]->var].b);
            ok = engine.propagate();          
            if(log)fprintf(stderr,"Propagate %d\n",ok);
            engine.clearPropState();
            sat.confl = NULL;
            made_dec = true;
        }
        if(ok)
        {
            bool reachT = !_test_mdd(tab, nodes[n]->edges[jj].dest, vars);
            if (reachT) {
                return false;
            }
        }
        if (made_dec)
            sat.btToLevel(engine.decisionLevel() - 1);
    }

    return true;
}
bool test_mdd(MDDTable* tab, _MDD n, vec<IntView<4> >& vars) {
    return _test_mdd(tab, n, vars);
}
bool test_mdd(MDDTable* tab, _MDD n, vec<IntVar*>& v) {
    vec<IntView<4> > vv;
    for (int i = 0; i < v.size(); i++) 
        vv.push(IntView<4>(v[i],1,v[i]->getMin() <0 ? -v[i]->getMin() : 0));
    return _test_mdd(tab, n, vv);
}


MDD Engine::build_mdd(vec<IntVar*>& v) {
    std::unordered_map<Entry*,_MDD> pb2nd;
    std::vector<bool> fixed_var(v.size(),false);
    MDDTable* tab = new MDDTable(v.size());
    _MDD root = MDDTRUE;
    MDD mdd(tab,root);

    vec<IntView<4> > vv;
    for (int i = 0; i < v.size(); i++) {
        vv.push(IntView<4>(v[i],1,v[i]->getMin() <0 ? -v[i]->getMin() : 0));
        mdd.shifts[i] = v[i]->getMin() <0 ? -v[i]->getMin() : 0;
    }
    start_time = wallClockTime();            
    mdd.val = _mddfy(vv,mdd,pb2nd,0,fixed_var);

    delete[] hsh;
    hsh = new Entry*[TABLESIZE];
    memset(hsh,0,TABLESIZE*sizeof(Entry*));
    return mdd;
}

MDDProp<4>* Engine::mddfy(vec<IntVar*>& v, bool add) {
    printf("MDDfy %d variables\n",v.size());
    std::unordered_map<Entry*,_MDD> pb2nd;
    std::vector<bool> fixed_var(v.size(),false);
    MDDTable tab(v.size());
    _MDD root = MDDTRUE;
    MDD mdd(&tab,root);

    MDDProp<4>* p = NULL;

    vec<IntView<4> > vv;
    for (int i = 0; i < v.size(); i++) 
        vv.push(IntView<4>(v[i],1,v[i]->getMin() <0 ? -v[i]->getMin() : 0));
    
    mdd.val = _mddfy(vv,mdd,pb2nd,0,fixed_var);

    mdd.table->print_mdd(mdd.val);
    printf("Number of nodes: %d\n",mdd.table->getNodes().size());

    if(!add) {
        mdd.val = mdd.table->mdd_not(mdd.val);
        bool ok = test_mdd(mdd.table,mdd.val,vv);
        printf("OK ===== %d\n",ok);
        assert(ok);
        assert(decisionLevel() == 0);
    } else {
        MDDOpts mopts;
        printf("Creating propagator %d\n",propagators.size());
        p = addMDD(vv,mdd, mopts);
        //p->debugStateTikz(0);
        printf("Created propagator %d\n",propagators.size()-1);
    }

    delete[] hsh;
    hsh = new Entry*[TABLESIZE];
    memset(hsh,0,TABLESIZE*sizeof(Entry*));
    return p;
}

_MDD Engine::_mddfy(vec<IntView<4> >& v, MDD& mdd, 
                    std::unordered_map<Entry*,_MDD>& pb2nd, int processed,
                    std::vector<bool>& fixed_var) {   
    bool log = false;

    vec<std::pair<IntView<4>,int> > fix_by_prop;
    //Propagate the last decision:
    _MDD node;
    bool ok = engine.propagate();
    engine.clearPropState();
    sat.confl = NULL;
    Entry* pb = NULL;

    if (ok) {
        if (so.presolve == 2)
            pb = checkhash();  //Get problem 
        if (log) printf("MDDFY %p (%p)\n",pb,so.presolve==1 ? NULL: entries.last());
        if (pb) {  //Already seen this problem before, we know which node in the MDD it is        
            if (log) printf("  Already known problem %p\n",pb);
            assert(pb2nd.find(pb) != pb2nd.end());
            node = pb2nd[pb];
            if(node != MDDFALSE && node != MDDTRUE) mdd_hash_hits++;
            if(log)printf("    hashed to node %d\n",node);
            for (int i = processed; i < v.size(); i++) {
                if (v[i].isFixed() && !fixed_var[i]) {
                    if(log)printf("    --v[%d] fixed to %d\n",i,v[i].getVal());
                    _MDD eq = mdd.table->mdd_vareq(i,v[i].getVal());
                    node = mdd.table->mdd_and(node,eq);
                }
            }    
            if (log) printf("   Returning node %d\n",node);    
            return node; //Return the root of the MDD corresponding to this subproblem
        } 
        if (so.presolve == 2) {
            assert(pb == NULL);
            pb = entries.last(); //This problem
        }
        int new_proc = v.size(); 
        for (int i = processed; i < v.size(); i++) {
            if (v[i].isFixed() && !fixed_var[i]) {
                fixed_var[i] = true;
                fix_by_prop.push(std::make_pair(v[i],i));
            }
            if (!v[i].isFixed()) new_proc = new_proc < i ? new_proc : i;
        }        
        processed = new_proc;

    }

    if (!ok) {
        if(log) printf("  MDDFALSE\n");
        //No solution to this subproblem
        node = MDDFALSE;
    } else if (processed == v.size()) {
        //No more variables, and di not fail on the way down
        if (log) printf("  MDDTRUE\n");
        node = MDDTRUE;
    } else { //Didn't match

        std::vector<edgepair> edges;
        IntView<4> x = v[processed];
        int var_id = processed;//var of this IntVar in the MDD
        assert(!x.isFixed());
        if (log) printf("  Popping variable %d(%p) [%d,%d]\n",var_id,x.var,x.getMin(),x.getMax());
        for (int d = x.getMin(); d <= x.getMax(); d++) {
            if (!x.indomain(d)) continue;
            if(log) printf("  Var %d, Trying value %d (level = %d)\n",var_id, d,decisionLevel());   

            DecInfo* di = NULL;
            di = new DecInfo(x.var,d-x.b,1); // x == d
            engine.dec_info.push(*di);            
            engine.newDecisionLevel();            
            engine.doFixPointStuff();
            engine.makeDecision(*di, 0);
            delete di;
            //x.var->decided = 1; //Just to test the late injection, tested on 37_coloring.fzn

            _MDD child = _mddfy(v,mdd,pb2nd,processed+1,fixed_var);
            edges.push_back(std::make_pair(d,child));

            sat.btToLevel(decisionLevel() - 1);                  
            if (log) printf("  Done (level = %d)\n",decisionLevel()); 
        }
        node = mdd.table->mdd_case(var_id,edges);
    }

    if(ok) {

        if(so.presolve == 2) {
            assert(pb2nd.find(pb) == pb2nd.end());
            pb2nd[pb] = node;
            assert(entries.last() == pb); //Subproblems have popped out
            //You can now find this problem, as all subproblems have been processed
            //and there is a node associated to it.
            if (log) printf("  Store this problem %p to %d\n",pb,node);
            sethash();
            shrinkhash(pb2nd);
        }

        for (int i = 0; i < fix_by_prop.size(); i++) {
            IntView<4> view = fix_by_prop[i].first;
            assert(view.isFixed());
            int index = fix_by_prop[i].second;
            if (log) printf("    Fixed by prop: var %d to value %d\n",index,view.getVal());
            fixed_var[index] = false;
            _MDD eq = mdd.table->mdd_vareq(index,view.getVal());
            node = mdd.table->mdd_and(node,eq);
        }

    }

    if (log) printf("  Returning node %d\n",node);
    return node;
}

 
int mdd2mzn(MDD mdd, vec<IntVar*>& v) {
    //Prelabel nodes to a readable value:
    
    std::unordered_map<_MDD, int> nmap;
    std::vector<int> rnmap;
    std::vector<int> ecount;
    std::vector<int> layer_length(v.size(),0);
    int ncount = 2; //0 and 1 are FFF and TTT
    ecount.push_back(0);
    ecount.push_back(0);
    rnmap.push_back(0);
    rnmap.push_back(1);
    nmap[0] = 0;
    nmap[1] = 1;
    

    _MDD r = mdd.val;
    if(r == MDDFALSE) {
        ERROR("MDD is False!\n");
    }
        
    const std::vector<MDDNode>& nodes = mdd.table->getNodes();
    std::vector<_MDD> status(nodes.size());
    std::vector<_MDD> queued;
    queued.push_back(r);
    status[0] = 1;
    status[1] = 1;
    status[r] = 1;
    unsigned int head = 0;

    while( head < queued.size() )
    {
        _MDD n = queued[head];
        assert(nmap.find(n) == nmap.end());
        layer_length[nodes[n]->var]++;
        nmap[n] = ncount++;
        rnmap.push_back(n);
        ecount.push_back(nodes[n]->sz);
        for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ ) {
            if( status[nodes[n]->edges[jj].dest] == 0 ) {
                status[nodes[n]->edges[jj].dest] = 1;
                queued.push_back(nodes[n]->edges[jj].dest);
            }
        }
        head++;
    }

    if (false) {
    
        std::cout<<"mdd(";
    
        //Variables
        std::cout<<"[";
        for (int i = 0; i < v.size(); i++) {
            assert(engine.presolved_variables.find(v[i]) != engine.presolved_variables.end());
            std::cout<<engine.presolved_variables[v[i]];
            if (i < v.size()-1)std::cout<<",";
        }
        std::cout<<"],";

        //Shitfs
        std::cout<<"[";
        for (int i = 0; i < v.size(); i++) {
            std::cout<<mdd.shifts[i];
            if (i < v.size()-1)std::cout<<",";
        }
        std::cout<<"],";

        //Number of nodes
        std::cout<< ncount<<",";

        //Edge count
        std::cout<<"[";
        for (int i = 0; i < layer_length.size(); i++) {
            std::cout<<layer_length[i];
            if (i < layer_length.size()-1)std::cout<<",";
        }
        std::cout<<"],";

        //Edges
        std::cout<<"[|";
        for (int i = 2; i < rnmap.size(); i++) {
            int n = rnmap[i];
            //Anything below the next edge goes to ...
            std::cout<<"-1"<<","<<nodes[n]->low<<"|"; 
            for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ ) {
                std::cout<<nodes[n]->edges[jj].val<<","<<nmap[nodes[n]->edges[jj].dest]<<"|";
            }       
        }
        std::cout<<"]";
        std::cout<<");"<<std::endl;
    } else {
        /*
        std::cout<<"mdd(";
        std::cout<<"[";
        for (int i = 0; i < v.size(); i++) {
            assert(engine.presolved_variables.find(v[i]) != engine.presolved_variables.end());
            std::cout<<engine.presolved_variables[v[i]];
            if (i < v.size()-1)std::cout<<",";
        }
        std::cout<<"],mddshifts,mddnodes,mddlayers,mddedges);"<<std::endl;
        //*/
        //Shitfs
        std::cout<<"mddshifts"<<so.mdd_name<<" = [";
        for (int i = 0; i < v.size(); i++) {
            std::cout<<mdd.shifts[i];
            if (i < v.size()-1)std::cout<<",";
        }
        std::cout<<"];\n";

        //Number of nodes
        std::cout<< "mddnodes"<<so.mdd_name<<" = "<<ncount<<";\n";

        //Edge count
        std::cout<<"mddlayers"<<so.mdd_name<<" = [";
        for (int i = 0; i < layer_length.size(); i++) {
            std::cout<<layer_length[i];
            if (i < layer_length.size()-1)std::cout<<",";
        }
        std::cout<<"];\n";
        return ncount;
        //Edges
        std::cout<<"mddedges"<<so.mdd_name<<" = [|";
        for (int i = 2; i < rnmap.size(); i++) {
            int n = rnmap[i];
            //Anything below the next edge goes to ...
            std::cout<<"-1"<<","<<nodes[n]->low<<"|"; 
            for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ ) {
                std::cout<<nodes[n]->edges[jj].val<<","<<nmap[nodes[n]->edges[jj].dest]<<"|";
            }       
        }
        std::cout<<"];\n";

    }    

    return ncount;
}
