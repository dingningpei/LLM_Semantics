#ifndef engine_h
#define engine_h

#include "support/misc.h"
#include <vector>
#include <set>
#include <unordered_map>
#include "mdd/MDD.h"


template<int type>
class IntView;

template<int type>
class MDDProp;

class Var;

#define DEBUG 0

#define TABLESIZE 16777216  // 2^24
#define MAX_HASH_SIZE 1000000

enum OPT_TYPE { OPT_MIN = 0, OPT_MAX = 1 };
enum RESULT { RES_SAT, RES_LUN, RES_GUN, RES_UNK, RES_SEA };

class BranchGroup;
class Branching;
class BranchingDesc;
class BTPos;
class Checker;
class DecInfo;
class IntVar;
class Problem;
class Propagator;
class PseudoProp;
class TrailElem;
class Entry;

//-----

class Engine {

public:
	static const int num_queues = 6;

	// Problem setup
	vec<IntVar*> vars;                         // List of int vars
        vec<int> bvars;                            // List of indexes of sat.assign corresponding to BoolViews 
	vec<Branching*> outputs;                   // List of output vars
	vec<Propagator*> propagators;              // List of propagators
	vec<PseudoProp*> pseudo_props;             // List of pseudo propagators
	vec<Checker*> checkers;                    // List of constraint checkers
	vec<int> assumptions;                      // List of assumption literals
	bool finished_init;

	Problem *problem;
	BranchGroup *branching;
	IntVar *opt_var;
	int opt_type; 
	int best_sol;
	RESULT status;

	// Intermediate propagation state
	vec<IntVar*> v_queue;                      // List of changed vars
	vec<vec<Propagator*> > p_queue;            // Queue of propagators to run
	Propagator *last_prop;                     // Last propagator run, set for idempotent propagators
	bool async_fail;                           // Asynchronous failure

	// Decision stack
	vec<DecInfo> dec_info;
        
	// Trails
	vec<TrailElem> trail;                      // Raw data changes
	vec<int> trail_lim;

	// Statistics
    double start_time, init_time, opt_time, search_time, first_time;
	double base_memory;
    long long int conflicts, nodes, propagations, solutions, next_simp_db, starts;


	// Caching
	Entry **hsh;
    int hsh_count;
	vec<Entry*> entries;
	Propagator *static_key;
	long long int hash_hits;
	long long int collisions;
	vec<Keyable*> keyables;                    // List of keyables
	vec<Keyable*> var_keys;
        // For NonBinary Branching
        vec<BranchingDesc> branchingDescs;
private:

	// Init
	void init();
	void initMPI();


	void topLevelCleanUp();
	void simplifyDB();
	void blockCurrentSol();
	int  getRestartLimit(int starts);
	void toggleVSIDS();
public:

	// Engine core
	void newDecisionLevel();
	void doFixPointStuff();
	void makeDecision(DecInfo& di, int alt);
	bool constrain();
	bool propagate();

        bool forceBetterSolution();
	void clearPropState();
	// Constructor
	Engine();

	// Trail methods
	void btToPos(int pos);
	void btToLevel(int level);

	// Interface methods
	RESULT search();
	void solve(Problem *p);

	// Stats
	void printStats();
	void checkMemoryUsage();

        // Caching
	Entry* checkhash();
	void sethash();
    void shrinkhash(std::unordered_map<Entry*,_MDD>& pb2nd, int min = 5);

        

        std::unordered_map<int, std::vector<IntVar*> > mddfied_variables;
    std::unordered_map<IntVar*, std::string > presolved_variables;
    std::unordered_map<int,MDD> loaded_mdds;
    MDD build_mdd(vec<IntVar*>& v);
    MDDProp<4>* mddfy(vec<IntVar*>& v, bool add);
    _MDD _mddfy(vec<IntView<4> >& v, MDD& mdd, std::unordered_map<Entry*,_MDD>& pb2nd, 
                int processed, std::vector<bool>& fixed_var);

	int decisionLevel() const { return trail_lim.size(); }
	int trailPos() const { return trail.size(); }
	int tpToLevel(int tp) const {
		for (int i = trail_lim.size(); i--; ) if (tp >= trail_lim[i]) return i+1;
		return 0;
	}

};

extern Engine engine;

void optimize(IntVar* v, int t);

//-----

class TrailElem {
public:
	int *pt; int x; int sz;
	TrailElem(int *_pt, int _sz) : pt(_pt), x(_sz == 1 ? *((char*) pt) : _sz == 2 ? *((short*) pt) : *pt), sz(_sz) {}
	void undo() {
		switch (sz) {
			case 1: *((char*)  pt) = x; break;
			case 2: *((short*) pt) = x; break;
			default: *pt = x; break;
		}
	}
};

template <class T, class U>
static inline void trailChange(T& v, const U u) {
	int *pt = (int*) &v;
	engine.trail.push(TrailElem(pt, sizeof(T)));
	if (sizeof(T) == 8) {
		engine.trail.push(TrailElem(pt+1, sizeof(T)));
	}
	v = u;
}



//------

// Auto-trailed int

#define AUTOTRAIL(t)                               \
class T##t {                                       \
public:                                            \
	t v;                                             \
	T##t() {}                                        \
	T##t(t _v) : v(_v) {}                            \
	operator t () const { return v; }                \
	t operator = (t o);                              \
	t operator = (T##t o) { return *this = o.v; }    \
	t operator += (t o) { return *this = v + o; }    \
	t operator -= (t o) { return *this = v - o; }    \
	t operator *= (t o) { return *this = v * o; }    \
	t operator /= (t o) { return *this = v / o; }    \
	t operator %= (t o) { return *this = v % o; }    \
	t operator ^= (t o) { return *this = v ^ o; }    \
	t operator &= (t o) { return *this = v & o; }    \
	t operator |= (t o) { return *this = v | o; }    \
	t operator <<= (t o) { return *this = v << o; }  \
	t operator >>= (t o) { return *this = v >> o; }  \
	t operator ++ () { return *this = v + 1; }       \
	t operator -- () { return *this = v - 1; }       \
	t operator ++ (int dummy) { int tmp = v; *this = v + 1; return tmp; } \
	t operator -- (int dummy) { int tmp = v; *this = v - 1; return tmp; } \
};

AUTOTRAIL(char)
AUTOTRAIL(int)
AUTOTRAIL(int64_t)

#define AUTOTRAILFLOAT(t)                               \
class T##t {                                       \
public:                                            \
	t v;                                             \
	T##t() {}                                        \
	T##t(t _v) : v(_v) {}                            \
	operator t () const { return v; }                \
	t operator = (t o);                              \
	t operator = (T##t o) { return *this = o.v; }    \
	t operator += (t o) { return *this = v + o; }    \
	t operator -= (t o) { return *this = v - o; }    \
	t operator *= (t o) { return *this = v * o; }    \
	t operator /= (t o) { return *this = v / o; }    \
	t operator ++ () { return *this = v + 1; }       \
	t operator -- () { return *this = v - 1; }       \
	t operator ++ (int dummy) { int tmp = v; *this = v + 1; return tmp; } \
	t operator -- (int dummy) { int tmp = v; *this = v - 1; return tmp; } \
};

AUTOTRAILFLOAT(double)

cassert(sizeof(Tchar) == 1);
cassert(sizeof(Tint) == 4);
cassert(sizeof(Tint64_t) == 8);
cassert(sizeof(Tdouble) == 8);

inline char Tchar::operator = (char o) {
	int *pt = (int*) this;
	engine.trail.push(TrailElem(pt, 1));
	return v = o;
}

inline int Tint::operator = (int o) {
	int *pt = (int*) this;
	engine.trail.push(TrailElem(pt, 4));
	return v = o;
}

inline int64_t Tint64_t::operator = (int64_t o) {
	int *pt = (int*) this;
	engine.trail.push(TrailElem(pt, 4));
	engine.trail.push(TrailElem(pt+1, 4));
	return v = o;
}

inline double Tdouble::operator = (double o) {
	int *pt = (int*) this;
	engine.trail.push(TrailElem(pt, 4));
	engine.trail.push(TrailElem(pt+1, 4));
	return v = o;
}

//-----

class Problem {
public: 
	virtual void print() = 0;
	virtual void restrict_learnable() {}
};


extern int hash_counter;
extern vec<int> core_key;
extern vec<int> dom_key;

//-----

class Entry {
public:
	int id;               // id
	int h;                // hash value
	int *ck;              // core key
	int *dk;              // dom key
	int *edk;             // end of dom key
  Entry *next;
    int use_count;
	static unsigned int murmurHash2(const void * key, int len) {
		const unsigned int m = 0x5bd1e995;
		const int r = 24;
		unsigned int h = 1774601265 ^ len;
		const unsigned int * data = (const unsigned int*) key;
		while (len--) {
			unsigned int k = *data++;
			k *= m; k ^= k >> r; k *= m; h *= m; h ^= k;
		}
		h ^= h >> 13;	h *= m;	h ^= h >> 15;
		return h;
	} 

	Entry();

	~Entry() {
		delete[] ck;
		delete[] dk;
	}

	bool dominate(Entry *n);
	bool equiv(Entry *n);

};

#endif
