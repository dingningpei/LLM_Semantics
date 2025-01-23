
#include "core/options.h"
#include "core/engine.h"
#include "core/sat.h"


Options so;

Options::Options() :
		nof_solutions(1)
	, time_out(1800)
	, rnd_seed(0)
	, verbosity(0)
	, print_sol(true)
	, restart_base(1000000000)

	, toggle_vsids(false)
	, branch_random(false)
	, switch_to_vsids_after(1000000000)
	, sat_polarity(0)

        , backtrack(false)

	, prop_fifo(false)

	, disj_edge_find(true)
	, disj_set_bp(true)

	, cumu_global(true)

	, sat_simplify(true)
	, fd_simplify(true)

	, lazy(true)
	, finesse(true)
	, learn(true)
	, vsids(false)
        , xuip(1)
#if PHASE_SAVING
	, phase_saving(0)
#endif
	, sort_learnt_level(false)
	, one_watch(true)

	, eager_limit(1000)
	, sat_var_limit(2000000)
	, nof_learnts(100000)
	, learnts_mlimit(500000000)

	, lang_ext_linear(false)
    
	, mdd(false)
	, mip(false)
	, mip_branch(false)

	, sym_static(false)
	, ldsb(false)
	, ldsbta(false)
	, ldsbad(false)

	, parallel(false)
	, num_threads(-1)
	, thread_no(-1)
	, share_param(10)
	, bandwidth(3000000)
	, trial_size(50000)
	, share_act(0)
	, num_cores(1)

	, saved_clauses(0)
	, use_uiv(false)
	
	, circuitalg(3)
	, prevexpl(1)
	, checkexpl(2)
	, checkfailure(4)
	, checkevidence(4)
	, preventevidence(1)
	, sccevidence(1)
    , sccoptions(4)
    , rootSelection(1)

	, alldiff_cheat(true)
	, alldiff_stage(true)
                    , steinerlp(false)
        , check_prop(false)

                    ,give_naive_explanations_HK(false)
                    ,use_last_conflict_HK(false)
                    ,wakeup_threshold_HK(0)
                    ,use_circuit_kf_prop(false)

                    ,use_hash(false)
                    ,use_static(false)
                    , nonbinary(false)
                    , mddfy(false)
                    , presolve(0) //1 = no keys,, 2 with keys
                    , mddfolder("")
                    , mdd_prop_type(-1)
                    , presolve_test(true)
                    , mdd_name("")
                    , show_partial_solution(false)
                    , allow_overtime(false)
                    , soft_assumptions(false)
                    , relax_every(-1)
                    , relax_every_mode(0) //0 just half, 1 half with highest activity
{}

char* hasPrefix(char* str, const char* prefix) {
	int len = strlen(prefix);
	if (strncmp(str, prefix, len) == 0) return str + len;
	else return NULL;
}

void parseOptions(int& argc, char**& argv) {
	int i, j;
	const char* value;

	#define parseIntArg(name)                                 \
	if ((value = hasPrefix(argv[i], "-" #name "="))) {        \
		so.name = atoi(value);                                  \
	} else 

	#define parseBoolArg(name)                                \
	if ((value = hasPrefix(argv[i], "-" #name "="))) {        \
		so.name = (strcmp(value, "true") == 0);                 \
	} else 

	#define parseStringArg(name)                                \
	if ((value = hasPrefix(argv[i], "-" #name "="))) {        \
            so.name = std::string(value);                         \
	} else 

	for (i = j = 1; i < argc; i++) {

		// PLEASE KEEP THE HELP TEXT IN flatzinc/fzn_chuffed.c UPDATED
		parseIntArg(nof_solutions)
		parseIntArg(time_out)
		parseIntArg(rnd_seed)
		parseIntArg(verbosity)
		parseBoolArg(print_sol)
		parseIntArg(restart_base)

		parseBoolArg(toggle_vsids)
		parseBoolArg(branch_random)
		parseIntArg(switch_to_vsids_after)
		parseIntArg(sat_polarity)

		parseBoolArg(backtrack)

		parseBoolArg(prop_fifo)

		parseBoolArg(disj_edge_find)
		parseBoolArg(disj_set_bp)
		
		parseBoolArg(cumu_global)

		parseBoolArg(sat_simplify)
		parseBoolArg(fd_simplify)

		parseBoolArg(lazy)
		parseBoolArg(finesse)
		parseBoolArg(learn)
                parseIntArg(xuip)
		parseBoolArg(vsids)
		parseBoolArg(sort_learnt_level)
		parseBoolArg(one_watch)

		parseIntArg(eager_limit)
		parseIntArg(sat_var_limit)
		parseIntArg(nof_learnts)
		parseIntArg(learnts_mlimit)

		parseBoolArg(lang_ext_linear)

		parseBoolArg(mdd)
		parseBoolArg(mip)
		parseBoolArg(mip_branch)

		parseBoolArg(sym_static)
		parseBoolArg(ldsb)
		parseBoolArg(ldsbta)
		parseBoolArg(ldsbad)

		parseBoolArg(well_founded)

		parseBoolArg(parallel)
		parseIntArg(share_param)
		parseIntArg(bandwidth)
		parseIntArg(trial_size)
		parseIntArg(share_act)

		parseIntArg(saved_clauses)
		parseBoolArg(use_uiv)

        parseIntArg(circuitalg)
        parseIntArg(prevexpl)
        parseIntArg(checkexpl)
        parseIntArg(checkfailure)
        parseIntArg(checkevidence)
        parseIntArg(sccevidence)
        parseIntArg(preventevidence)
        parseIntArg(sccoptions)
        parseIntArg(rootSelection)
    
		parseBoolArg(alldiff_cheat)
		parseBoolArg(alldiff_stage)

		parseBoolArg(steinerlp)

		parseBoolArg(check_prop)

                parseBoolArg(give_naive_explanations_HK)
                parseBoolArg(use_last_conflict_HK)
                parseIntArg(wakeup_threshold_HK)
                parseBoolArg(use_circuit_kf_prop)

                parseBoolArg(use_hash)
                parseBoolArg(use_static)                    
                parseBoolArg(nonbinary)
                parseBoolArg(mddfy)
                parseIntArg(presolve)

                parseStringArg(mddfolder)
                
                parseIntArg(mdd_prop_type)

                    parseBoolArg(presolve_test)
                    parseStringArg(mdd_name)

                    parseBoolArg(show_partial_solution)
                    parseBoolArg(allow_overtime)
                    parseBoolArg(soft_assumptions)

                    parseIntArg(relax_every)
                    parseIntArg(relax_every_mode)

		if (strcmp(argv[i], "-a") == 0) {
			so.nof_solutions = 0;
		} else if (strcmp(argv[i], "-f") == 0) {
			so.toggle_vsids = true;
			so.restart_base = 100;
		} else if (strcmp(argv[i], "-p") == 0) {
//			so.parallel = true;
			so.num_cores = atoi(argv[++i]);
		} else 

		if ((value = hasPrefix(argv[i], "-S"))) {
			so.verbosity = 1;
		} else if (argv[i][0] == '-') {
			ERROR("Unknown flag %s\n", argv[i]);
		} else argv[j++] = argv[i];
	}
	argc = j;

	rassert(so.sym_static + so.ldsb + so.ldsbta + so.ldsbad <= 1);

	if (so.ldsbta || so.ldsbad) so.ldsb = true;
	if (so.ldsb) rassert(so.lazy);
	if (so.mip_branch) rassert(so.mip);
	if (so.vsids) engine.branching->add(&sat);

        if (so.use_hash && !so.nonbinary) {
          fprintf(stderr,"Warning: using non-binary search because hashing is turned on.\n");
          so.nonbinary = true;
        }
        if (so.use_hash && so.lazy) {
          fprintf(stderr,"Warning: Turning off lazy because hashing is turned on.\n");
          so.lazy = false;
        }
        if (so.presolve && so.lazy) {
          fprintf(stderr,"Warning: Turning off lazy because presolving is turned on.\n");
          so.lazy = false;
        }
if (so.presolve) so.mddfy = true;


#ifndef PARALLEL
	if (so.parallel) {
		fprintf(stderr, "Parallel solving not supported! Please recompile with PARALLEL=true.\n");
		rassert(false);
	}
#endif

}
