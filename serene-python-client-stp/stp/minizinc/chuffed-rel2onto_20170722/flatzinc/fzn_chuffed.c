#include <cstdio>
#include <cstring>
#include "core/options.h"
#include "core/engine.h"
#include "flatzinc/flatzinc.h"

int main(int argc, char** argv) {
	parseOptions(argc, argv);
/*
	if (argc < 2) {
		printf("usage: %s [options] infile.fzn\n"
"\n"
"options:\n"
"\t-nof_solutions=n\n"
"\t-time_out=n\n"
"\t-rnd_seed=n\n"
"\t-verbosity=n\n"
"\t-print_sol=true|false\n"
"\t-restart_base=n\n"
"\n"
"\t-toggle_vsids=true|false\n"
"\t-branch_random=true|false\n"
"\t-switch_to_vsids_after=n\n"
"\t-sat_polarity=n\n"
"\n"
"\t-prop_fifo=true|false\n"
"\n"
"\t-disj_edge_find=true|false\n"
"\t-disj_set_bp=true|false\n"
"\n"
"\t-cumu_global=true|false\n"
"\n"
"\t-sat_simplify=true|false\n"
"\t-fd_simplify=true|false\n"
"\n"
"\t-lazy=true|false\n"
"\t-finesse=true|false\n"
"\t-learn=true|false\n"
"\t-vsids=true|false\n"
"\t-phase_saving=0|1|2\n"
"\t-sort_learnt_level=true|false\n"
"\t-one_watch=true|false\n"
"\n"
"\t-eager_limit=n\n"
"\t-sat_var_limit=n\n"
"\t-nof_learnts=n\n"
"\t-learnts_mlimit=n\n"
"\n"
"\t-lang_ext_linear=true|false\n"
"\n"
"\t-mdd=true|false\n"
"\t-mip=true|false\n"
"\t-mip_branch=true|false\n"
"\n"
"\t-sym_static=true|false\n"
"\t-ldsb=true|false\n"
"\t-ldsbta=true|false\n"
"\t-ldsbad=true|false\n"
"\n"
"\t-parallel=true|false\n"
"\t-share_param=n\n"
"\t-bandwidth=n\n"
"\t-trial_size=n\n"
"\t-share_act=n\n"
"\n"
"\t-saved_clauses=n\n"
"\t-use_uiv=true|false\n"
"\n"
"\t-alldiff_cheat=true|false\n"
"\t-alldiff_stage=true|false\n"
"\n"
"\t-a|--all|--all-solutions\n"
"\t--free\n"
"\t--parallel\n"
"\t-S\n", argv[0]);
		exit(1);
	}
*/

	if (argc == 1) {
		FlatZinc::solve(std::cin, std::cerr);
	} else {
		FlatZinc::solve(std::string(argv[1]));
	}

	engine.solve(FlatZinc::s);

	return 0;
}
