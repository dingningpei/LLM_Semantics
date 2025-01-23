#ifndef globals_h
#define globals_h

#include "core/propagator.h"

//-----
// Directives

void output_var(Branching* v);
void output_vars(vec<Branching*>& v);
void output_vars(vec<IntVar*>& v);

// Well Foundedness Directives

void add_inductive_rule(BoolView hl, vec<BoolView>& posb, vec<BoolView>& negb, int wf_id);
void wf_init();

//-----
// Propagators

// alldiff.c

void all_different(vec<IntVar*>& x, ConLevel cl = CL_DEF);
void all_different_offset(vec<int>& a, vec<IntVar*>& x, ConLevel cl = CL_DEF);
void inverse(vec<IntVar*>& x, vec<IntVar*>& y, int o1 = 0, int o2 = 0, ConLevel cl = CL_DEF);

// circuit.c

void circuit(vec<IntVar*>& x);

//From Kathryn's Branch:
// circuit_kf.c
// subcircuit_kf.c
void subcircuit_kf(vec<IntVar*>& x);
void subpath_kf(vec<IntVar*>& _x);
void circuit_kf(vec<IntVar*>& _x);
void path_kf(vec<IntVar*>& _x);

// tree.c
void tree(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, vec< vec<int> >& _en);
void steinerTree(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, 
                 vec< vec<int> >& _en,IntVar* _w, vec<int> _ws);


//biconnected.h
class BiConnectedPropagator;
BiConnectedPropagator* biconnected(vec<BoolView>& _vs, vec<BoolView>& _es, 
                                   vec< vec<int> >& _en, vec< vec<int> >& _adj);
BiConnectedPropagator* wbiconnected(vec<BoolView>& _vs, vec<BoolView>& _es, 
                                    vec< vec<int> >& _en, vec< vec<int> >& _adj,
                                    vec<int>& ws, IntVar* w);

//vrptw.c
void vrptw(vec<BoolView>& before, vec<IntVar*>& beginWork,
           vec<int>& travel, vec<int>& starts, vec<int>& ends, vec<int>& dur);

//mst.c
void mst(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, 
         vec< vec<int> >& _en, IntVar* _w, vec<int>& _ws);
void cmst(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, 
          vec< vec<int> >& _en, IntVar* _w, vec<int>& _ws, int _r, int _c);

//tsp_heldkarp_lagrangian.c
void tsp(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, 
         vec< vec<int> >& _en, IntVar* _w, vec<int>& _ws);
//directed_reachability.h
class DReachabilityPropagator;
DReachabilityPropagator* dreachable(int r, vec<BoolView>& _vs, vec<BoolView>& _es, 
                vec< vec<int> >& _in, vec< vec<int> >& _out, 
                vec< vec<int> >& _en);
DReachabilityPropagator* dreachable(int r, vec<BoolView>& _vs, vec<BoolView>& _es, 
                vec< vec<int> >& _in, vec< vec<int> >& _out, 
                vec< vec<int> >& _en, BoolView b);

//dag.h
void dag(int r, vec<BoolView>& _vs, vec<BoolView>& _es, 
         vec< vec<int> >& _in, vec< vec<int> >& _out, 
         vec< vec<int> >& _en);

//dtree.h
class DTreePropagator;
DTreePropagator* dtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es, 
           vec< vec<int> >& _in, vec< vec<int> >& _out, 
           vec< vec<int> >& _en);
DTreePropagator* reversedtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<int> >& _in, vec< vec<int> >& _out, 
                  vec< vec<int> >& _en);
void dptree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
            vec<IntVar*> _par,
            vec< vec<int> >& _in, vec< vec<int> >& _out, 
            vec< vec<int> >& _en);
void reversedptree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
                   vec<IntVar*> _par,
                   vec< vec<int> >& _in, vec< vec<int> >& _out, 
                   vec< vec<int> >& _en);
void path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
          vec< vec<int> >& _in, vec< vec<int> >& _out, 
          vec< vec<int> >& _en);
void pathsucc(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
              vec<IntVar*> _par,
              vec< vec<int> >& _in, vec< vec<int> >& _out, 
              vec< vec<int> >& _en);

//bounded_path.c
void bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<int> >& _in, vec< vec<int> >& _out, 
                  vec< vec<int> >& _en, vec<int>& _ws, IntVar* w);
//td_bounded_path.c
void td_bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                     vec<BoolView>& _order, vec<BoolView>& _order_opt, vec<IntVar*> pos,
                     vec< vec<int> >& _in, vec< vec<int> >& _out, 
                     vec< vec<int> >& _en, vec<vec<int> >& _ws, vec<int> ds, 
                     IntVar* w);
void td_bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                     vec<BoolView>& _order, vec<BoolView>& _order_opt, vec<IntVar*> pos,
                     vec< vec<int> >& _in, vec< vec<int> >& _out, 
                     vec< vec<int> >& _en, vec<vec< int> >& _ws, vec<int> _ds, 
                     IntVar* w, vec<IntVar*> _lowers, vec<IntVar*> _uppers);
// diff_logic.c
class DiffLogic;
DiffLogic * diff_logic(int numItems);
//network_flow.c
//void network_flow(vec<int>& supply, vec<int>& head, vec<int>& tail, 
//                  vec<IntVar *>& int_var, vec<BoolView>& bool_var, int flags,
//                  vec<BoolView>& available_edges);

// linear-bool.c

void bool_linear(vec<BoolView>& x, IntRelType t, IntVar* y);

//linear-bool-decom.c (from GG branch)
void bool_linear_decomp(vec<BoolView>& x, IntRelType t, int k);
void bool_linear_decomp(vec<BoolView>& x, IntRelType t, IntVar* kv);

// minimum.c

void minimum(vec<IntVar*>& x, IntVar* y);
void maximum(vec<IntVar*>& x, IntVar* y);

// table.c

void table(vec<IntVar*>& x, vec<vec<int> >& t);

// regular.c

void regular(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, int q0, vec<int>& f);

// disjunctive.c

void disjunctive(vec<IntVar*>& s, vec<int>& d);

// cumulative.c

void cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int b);
void cumulative2(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* b);

// lex.c

void lex(vec<IntVar*>& x, vec<IntVar*>& y, bool strict);

// sym-break.c

void var_sym_break(vec<IntVar*>& x);
void val_sym_break(vec<IntVar*>& x, int l, int u);

#endif
