#include <cstdio>
#include <cassert>
#include "core/options.h"
#include "core/engine.h"
#include "core/sat.h"
#include "parallel/parallel.h"
#include "mip/mip.h"
#include "ldsb/ldsb.h"

#include "../globals/td_bounded_path.h"
#include "../globals/tsp_heldkarp_lagrangian.h"

extern int mdd_hash_hits;
extern int hash_counter;


void Engine::printStats() {
	if (so.thread_no != -1) return;

	search_time = wallClockTime() - start_time - init_time;

	if (so.verbosity >= 2) {
		int nl = 0, el = 0, ll = 0;
		for (int i = 0; i < vars.size(); i++) {
			switch (vars[i]->getType()) {
				case INT_VAR: nl++; break;
				case INT_VAR_EL: el++; break;
				case INT_VAR_LL: ll++; break;
				case INT_VAR_SL: el++; break;
				default: NEVER;
			}
		}

		fprintf(stderr, "%d vars (%d no lits, %d eager lits, %d lazy lits)\n", vars.size(), nl, el, ll);
		fprintf(stderr, "%d propagators\n", propagators.size());
		fprintf(stderr, "%lld conflicts\n", conflicts);
		fprintf(stderr, "%lld nodes\n", nodes);
		fprintf(stderr, "%lld propagations\n", propagations);
		fprintf(stderr, "%lld solutions\n", solutions);
                fprintf(stderr, "%lld restarts\n", starts);
		fprintf(stderr, "%.2f seconds init time\n", init_time);
		if (opt_var) fprintf(stderr, "%.2f seconds opt time\n", opt_time);
		fprintf(stderr, "%.2f seconds first solution time\n", first_time);
		fprintf(stderr, "%.2f seconds search time\n", search_time);
		fprintf(stderr, "%.2fMb base memory usage\n", base_memory);
		fprintf(stderr, "%.2fMb trail memory usage\n", trail.capacity() * sizeof(TrailElem) / 1048576.0);
		fprintf(stderr, "%.2fMb peak memory usage\n", memUsed());
                fprintf(stderr,"%lld hash hits\n", hash_hits);
                fprintf(stderr,"%lld collisions\n", collisions);
		if (so.ldsb) fprintf(stderr, "%.2f seconds ldsb time\n", ldsb.ldsb_time);
		if (so.parallel) master.printStats();
		fprintf(stderr, "\n");
		sat.printStats();
		if (so.mip) mip->printStats();
                if (so.xuip != 1) {
                    fprintf(stderr,"%.5f enqueued UIPs per analysis\n", 
                            (float)sat.xuip_per_analyze/(float)sat.analysis_counter);
                }
                fprintf(stderr, "\n");
                fprintf(stderr, "MDD hash hits: %d\n",mdd_hash_hits);
                fprintf(stderr, "MDD hash counter: %d\n",hash_counter);
                fprintf(stderr, "Propagator stats:\n");
                fprintf(stderr, "TDBoundedPath:\n");
                fprintf(stderr, "%d explanations of average length %.2f\n",
                        TDBoundedPath::expl_count, 
                        TDBoundedPath::expl_count == 0 ? 0.00 :
                        ((float)TDBoundedPath::expl_len / (float)TDBoundedPath::expl_count));
                fprintf(stderr, "%d propgations of TDBoundedPath or inheritent class\n", TDBoundedPath::props);
                fprintf(stderr, "TSPPropagator:\n");
                fprintf(stderr, "%d calls to kruskal_1tree, with total length of unfixed edges %d\n",
                        TSPPropagator::nb_calls_kkl1tree, 
                        TSPPropagator::len_unk_on_call);
                fprintf(stderr, "%d calls to lagrangian_rel\n",
                        TSPPropagator::nb_calls_lagrel);
                fprintf(stderr, "%d calls to propagate\n",
                        TSPPropagator::nb_calls_prop);
                fprintf(stderr,"Sorting calls\n");
                //for (unsigned int i = 0; i < TSPPropagator::sort_size_stat.size(); i++) {
                    //fprintf(stderr,"%d\n",TSPPropagator::sort_size_stat[i]);
                //}
                //fprintf(stderr,"Kruskal calls\n");
                //for (unsigned int i = 0; i < TSPPropagator::kruskal_size_stat.size(); i++) {
                    //fprintf(stderr,"%d\n",TSPPropagator::kruskal_size_stat[i]);
                //}
                /*
                int zeros = 0;
                int usage = 0;
                int non_zeros = 0;
                fprintf(stderr,"Learnt %d clauses\n",TSPPropagator::my_clauses.size());
                for (unsigned int i = 0; i < TSPPropagator::my_clauses.size(); i++) {
                    if (Clause::usage_count.find(TSPPropagator::my_clauses[i]) == Clause::usage_count.end()) {
                        fprintf(stderr,"Error with some clause! 1\n");
                        exit(1);
                    }else if (Clause::gen_to_learnt.find(TSPPropagator::my_clauses[i]) == Clause::gen_to_learnt.end()) {
                        fprintf(stderr,"Error with some clause! 2.  %d %d\n",i,TSPPropagator::my_clauses_origin[i]);
                        continue;
                    } else if (Clause::usage_count.find(Clause::gen_to_learnt[TSPPropagator::my_clauses[i]]) == Clause::usage_count.end()) {
                        fprintf(stderr,"Error with some clause! 3\n");
                        
                    } else {
                        if (Clause::usage_count[Clause::gen_to_learnt[TSPPropagator::my_clauses[i]]] != 0) {
                            //fprintf(stderr,"Clause %p was used %d times\n",
                            //        TSPPropagator::my_clauses[i],Clause::usage_count[TSPPropagator::my_clauses[i]]);
                            non_zeros++;
                            usage += Clause::usage_count[Clause::gen_to_learnt[TSPPropagator::my_clauses[i]]];
                        } else {
                            zeros++;
                        }
                    }
                }
                fprintf(stderr,"%d clauses used in average %f times\n",non_zeros, (float)usage/(float)non_zeros);
                fprintf(stderr,"%d clauses never used out of %d (so, %f\%)\n",zeros, TSPPropagator::my_clauses.size(),
                        (float)zeros/(float)TSPPropagator::my_clauses.size());
                //*/
	}
	else {
		if (engine.opt_var != NULL) fprintf(stderr, "%d,", best_sol);
		fprintf(stderr, "%d,%d,%d,%lld,%lld,%lld,%lld,%.2f,%.2f\n", vars.size(), sat.nVars(), propagators.size(), conflicts, sat.back_jumps, propagations, solutions, init_time, search_time);
	}
}

void Engine::checkMemoryUsage() {
	fprintf(stderr, "%d int vars, %d sat vars, %d propagators\n", vars.size(), sat.nVars(), propagators.size());
	fprintf(stderr, "%.2fMb memory usage\n", memUsed());

	fprintf(stderr, "Size of IntVars: %d %d %d\n", static_cast<int>(sizeof(IntVar)), static_cast<int>(sizeof(IntVarEL)), static_cast<int>(sizeof(IntVarLL)));
	fprintf(stderr, "Size of Propagator: %d\n", static_cast<int>(sizeof(Propagator)));

	long long var_mem = 0;
	for (int i = 0; i < vars.size(); i++) {
		var_mem += sizeof(IntVarLL);
/*
		var_mem += vars[i]->sz;
		if (vars[i]->getType() == INT_VAR_LL) {
			var_mem += 24 * ((IntVarLL*) vars[i])->ld.size();
		}
*/
	}
	fprintf(stderr, "%lld bytes used by vars\n", var_mem);

	long long prop_mem = 0;
	for (int i = 0; i < propagators.size(); i++) {
		prop_mem += sizeof(*propagators[i]);
	}
	fprintf(stderr, "%lld bytes used by propagators\n", prop_mem);
/*
	long long var_range_sum = 0;
	for (int i = 0; i < vars.size(); i++) {
		var_range_sum += vars[i]->max - vars[i]->min;
	}
	fprintf(stderr, "%lld range sum in vars\n", var_range_sum);
*/
	long long clause_mem = 0;
	for (int i = 0; i < sat.clauses.size(); i++) {
		clause_mem += sizeof(Lit) * sat.clauses[i]->size();
	}
	fprintf(stderr, "%lld bytes used by sat clauses\n", clause_mem);
/*
	int constants, hundred, thousand, large;
	constants = hundred = thousand = large = 0;
	for (int i = 0; i < vars.size(); i++) {
		int sz = vars[i]->max - vars[i]->min;
		if (sz == 0) constants++;
		else if (sz <= 100) hundred++;
		else if (sz <= 1000) thousand++;
		else large++;
	}
	fprintf(stderr, "Int sizes: %d %d %d %d\n", constants, hundred, thousand, large);
*/
}
