#ifndef CHUFFED_MDDOPTS__H
#define CHUFFED_MDDOPTS__H
#include <string>

class MDDOpts {
public:
  enum ExplAlg { E_MINIMAL, E_GREEDY, E_NAIVE };
  enum ExplStrat { E_TEMP, E_KEEP };
  enum Decomp { D_PROP, D_MINIMAL, D_MINISAT, D_TSEITIN, D_BASIC, D_SDNNF , D_LEVEL, D_COMPLETE};

  MDDOpts(void)
    : expl_alg(E_GREEDY), expl_strat(E_KEEP), decomp(D_PROP)
  { }

  MDDOpts(const MDDOpts& o)
    : expl_alg(o.expl_alg), expl_strat(o.expl_strat), decomp(o.decomp)
  { }

  void parse_arg(const std::string& arg)
  {
    if(arg == "explain_minimal")
      expl_alg = E_MINIMAL;
    else if(arg == "explain_greedy")
      expl_alg = E_GREEDY;
    else if(arg == "discard_explanations")
      expl_strat = E_TEMP;
    else if(arg == "store_explanations")
      expl_strat = E_KEEP;
  }


char* hasPrefix(char* str, const char* prefix) {
  int len = strlen(prefix);
  if (strncmp(str, prefix, len) == 0) return str + len;
  else return NULL;
}

  void parseOptions(int& argc, char**& argv) {
	int i, j;
	const char* value;
    for (i = j = 0; i < argc; i++) {
       if (strcmp(argv[i], "-enc=prop") == 0) {
	      decomp = D_PROP;
       } else if (strcmp(argv[i], "-enc=minimal") == 0) {
	      decomp = D_MINIMAL;
       } else if (strcmp(argv[i], "-enc=minisat") == 0) {
	      decomp = D_MINISAT;
       } else if (strcmp(argv[i], "-enc=tseitin") == 0) {
	      decomp = D_TSEITIN;
       } else if (strcmp(argv[i], "-enc=basic") == 0) {
	      decomp = D_BASIC;
       } else if (strcmp(argv[i], "-enc=sdnnf") == 0) {
	      decomp = D_SDNNF;
       } else if (strcmp(argv[i], "-enc=level") == 0) {
	      decomp = D_LEVEL;
       } else if (strcmp(argv[i], "-enc=complete") == 0) {
	      decomp = D_COMPLETE;
       } else if ((value = hasPrefix(argv[i], "-enc="))) {
            //deprecated
	    	decomp = static_cast<Decomp>(atoi(value));
	   } else
              argv[j++] = argv[i];
    }
	argc = j;
  }

  ExplAlg expl_alg;
  ExplStrat expl_strat;
  Decomp decomp;
};


#endif
