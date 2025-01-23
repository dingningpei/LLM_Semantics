#ifndef TSP_HELDKARP_LAGRANGIAN
#define TSP_HELDKARP_LAGRANGIAN

#include "core/propagator.h"
#include "support/union_find.h"
#include <iostream>
#include "tree.h"
#include <set> 
#include <vector> 
#include <algorithm>    // std::sort
#include <unordered_map>
#include "biconnected.h"
/**
 * TSP Lagrangian relaxation
 * Very inspired from the work of JG Fages et al. in Choco
 * who was inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 */


class TSPPropagator : public GraphPropagator {
    int old_conflicts;
    int old_dl;
    int last_decision_position;
    bool first_run;
    int nb_runs_level;
    int wakeup_counter;
    int old_wakeup_counter;
    bool wakeup_enabled;
    static TSPPropagator* propagator;

public:
    void enable() {wakeup_enabled = true;}
    void disable() {wakeup_enabled = false;}    
    static TSPPropagator* getInstance() {return propagator;}    
    BiConnectedPropagator* bccp;
    static int nb_calls_kkl1tree;
    static int len_unk_on_call;
    static int nb_calls_lagrel;
    static int nb_calls_prop;
    //static std::vector<int> sort_size_stat;
    //static std::vector<int> kruskal_size_stat;
    //This is for testing only! Never use outside of specific tests:
    static std::vector<Clause*> my_clauses;
    static std::vector<int> my_clauses_origin;
    
    std::unordered_map<int,int> var2BoolView;

    IntVar* obj;

    int iters;
    int sprints;
    Tint* mand1;
    Tint* mand2;
    bool update_mand_vectors(int e);

    Tint* neigh_sizes;
    std::vector< std::vector<edge_id> > adj_map;

    vec<IntVar*> successor; //Unecessary, just for debug.


    int* original_ws;
    double* heldkarp_ws;
    
    struct EdgeSort {
        TSPPropagator* tsp;
        EdgeSort(TSPPropagator* tsp): tsp(tsp) {}
        bool operator() (int i, int j) { 
            return (tsp->original_ws[i] < tsp->original_ws[j]); 
        }
    } edge_sorter;
    friend EdgeSort;
    //All edges sorted
    int* unfixed_edges;
    int* unfixed_edges_map;
    Tint unfixed_edges_tsize;
    int unfixed_edges_size;
    int* sorted_edges;
    std::vector<int> in_edges;
    Tint in_edges_tsize;
    int in_edges_size;
    std::vector<int> out_edges;
std::vector<bool> removed_root_level;
    Tint out_edges_tsize;
    int out_edges_size;

    double lagrangian_step;
    bool lagrangian_step_zero;
    double total_penalty;
    double* penalties;


    Tdouble m1t_cost;
    int* m1t_degrees;

    
    enum VType{IN, OUT, UNK};
    std::vector<Tint> last_state_e;

protected:
    inline bool touches(int edge, int node) {
        return getEndnode(edge,0) == node || getEndnode(edge,1) == node;
    }
    void repair_backtrack();
    bool add_inedge(int e);
    template<typename T>
    bool find_two_cheapest(int node, int& e1, int& e2, T* wf);
    template<typename T>
    bool find_two_cheapest(int node, int& e1, int& e2, T*, vec<Lit>& ps);
    template<typename T>
    bool find_two_expensive(int node, int& e1, int& e2, T* wf);
    template<typename T>
    bool find_two_expensive(int node, int& e1, int& e2, T* wf, vec<Lit>& ps);
    bool check_two_edges(int node, int e1, int e2);

    //Give the "one" node that closes the only cycle
    bool kruskal_1tree(int one, bool filter = false); //Filter: perform propagation?
    double fast_kruskal_1tree(int one); //Never propagate, just compute the cost of the tree
    void add1node(int node, double& cost);
    void add1node(int node, double& cost, int& e1, int& e2, vec<Lit>& ps);
    void kruskal_pre_add(int one, int& counter, double& cost, UF<int>& uf, RerootedUnionFind<int>* ruf=NULL);
    std::pair<std::vector<int>,std::vector<int> > explain(vec<Lit>& expl_fail, 
                                                          double c, 
                                                          std::vector<int>& substitute, 
                                                          int in_edge = -1, bool verbose = false);
    double verify_explanation(std::vector<int>& medges, std::vector<int>& fedges,
                                int bound, int edge = -1, bool use_it = false);
    bool too_heavy_mandatory(double w);
    bool lagrangian_rel();
    void update_step(double hkb, double alpha);
    void update_penalties();
    void update_weights();
    void on_edge_removal(int e);
    void sort_edges(int* array, int size) {
        //sort_size_stat[size]++;
        //if (size == 199) {
        //    std::cout<<"At level "<<engine.decisionLevel()<<" "<<sort_size_stat[size]<<" "<<old_wakeup_counter<<" "<< unfixed_edges_size<<std::endl;
        //}
        int* copy = new int[size];
        memcpy(copy, array, sizeof(int)*size); 
        sort_edges(array,copy, 0, size);
        memcpy(array, copy, sizeof(int)*size); 
        delete[] copy;
        for (int i = 0; i < size -1; i++)
            assert(heldkarp_ws[array[i]] <= heldkarp_ws[array[i+1]]);
    }
    void sort_edges(int* dest, int* src, int low, int high);
    bool propagate_upper_bound();
public:

    TSPPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
                  IntVar* _w, vec<int>& _ws);
    TSPPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
                  IntVar* _w, vec<int>& _ws, vec<IntVar*> succs)
        : TSPPropagator(_vs,_es,_adj,_en,_w,_ws) {
        succs.copyTo(successor);
    
        for(int i = 0; i < nbEdges(); i++) {
            sat.addClause(getEdgeVar(i).getLit(true), successor[getHead(i)]->getLit(getTail(i), 0));
            sat.addClause(getEdgeVar(i).getLit(true), successor[getTail(i)]->getLit(getHead(i), 0));
            vec<Lit> c;
            c.push(getEdgeVar(i).getLit(false));
            c.push(successor[getHead(i)]->getLit(getTail(i), 1));
            c.push(successor[getTail(i)]->getLit(getHead(i), 1));
            sat.addClause(c);
        }
    }

    
    void wakeup(int i, int c);
    bool propagate();
    void clearPropState();
    void notifyNewDecLevel();
    bool checkFinalSatisfied();


    struct MemoizedExlanationElements {
        MemoizedExlanationElements(): heldkarp(NULL), multipliers(NULL),
                                      sorted_edges(NULL),clause(NULL) {} 
        MemoizedExlanationElements(TSPPropagator* p, std::vector<int> substitute,
                                   double tc) 
            : heldkarp(new double[p->nbEdges()]), 
              multipliers(new double[p->nbNodes()]), 
              sorted_edges(new int[p->unfixed_edges_size+p->in_edges.size()]),
              mand1_one(p->mand1[0]),
              mand2_one(p->mand2[0]),
              mand_count(p->in_edges_tsize),
              forb_count(p->out_edges_tsize),
              unf_count(p->unfixed_edges_tsize),
              subs(substitute),
              tree_cost(tc), upper_bound(p->obj->getMax()),clause(NULL) {
            memcpy(heldkarp,p->heldkarp_ws,sizeof(double)*p->nbEdges());
            memcpy(multipliers,p->penalties,sizeof(double)*p->nbNodes());
            memcpy(sorted_edges,p->sorted_edges,sizeof(int)*(p->unfixed_edges_size+p->in_edges.size()));
        }
        ~MemoizedExlanationElements() {
            if (heldkarp != NULL) { delete[] heldkarp; heldkarp = NULL;}
            if (multipliers != NULL) { delete[] multipliers; multipliers = NULL;}
            if (sorted_edges != NULL) { delete[] sorted_edges; sorted_edges = NULL;}
            clause = NULL; //chuffed has a copy, let him delete it
        }
        double* heldkarp;
        double* multipliers;
        int* sorted_edges;
        int mand1_one;
        int mand2_one;
        int mand_count;
        int forb_count;
        int unf_count;
        std::vector<int> subs;
        double tree_cost;
        int upper_bound;
        Clause* clause;
    };
    friend MemoizedExlanationElements;
    std::vector<struct MemoizedExlanationElements*> expl_builder;
    Tint expl_builder_tsize;
    
    Clause* explain(Lit p, int inf_id);



    double var_inc;
    std::vector<double> lit_expl_activity;
    std::unordered_map<int,int> lit2int;
    void lit_decay_expl_activity() {
        if ((var_inc *= 1.05) > 1e100) {
            for (unsigned int i = 0; i < lit_expl_activity.size(); i++) 
                lit_expl_activity[i] *= 1e-100;
            var_inc *= 1e-100;
        }
    }

    inline void lit_bump_expl_activity(Lit p) {        
        lit_expl_activity[lit2int[toInt(p)]] += var_inc;
    }


};

template<typename T>
bool TSPPropagator::find_two_cheapest(int node, int& e1, int& e2, T* wf) {
    vec<Lit> ps;
    return find_two_cheapest(node, e1, e2, wf, ps);
}
template<typename T>
bool TSPPropagator::find_two_cheapest(int node, int& e1, int& e2, T* wf, vec<Lit>& ps){
    e1 = -1;
    e2 = -1;
    bool m1 = false;
    //First look for mandatories:
    // for (unsigned int i = 0; i < adj[node].size(); i++) {
    //     int e = adj[node][i];
    //     if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
    //         if (so.lazy) 
    //             ps.push(getEdgeVar(e).getValLit());
    //         if (e1 == -1) {
    //             e1 = e; m1 = true;
    //         } else 
    //             e2 = e;
    //     } 
    // }
    e1 = mand1[node] == -1 ? mand2[node] : mand1[node];
    e2 = e1 == -1 ? -1 : (int)(e1 == mand1[node] ? (int)mand2[node] : -1);
    m1 = (e1 != -1);
    if (e1 != -1) ps.push(getEdgeVar(e1).getValLit());
    if (e2 != -1) ps.push(getEdgeVar(e2).getValLit());

    assert(e1 != e2 || (e1 == -1 && e2==-1));
    assert(e2 == -1 || e1 != -1);
    if (e1 != -1 && e2 != -1)  {
        assert(e1 != e2);
        return true; //found 2 edges
    }
    std::vector<int> tmp;
    for (unsigned int i = 0; i < adj[node].size(); i++) {
        int e = adj[node][i];
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
            if (so.lazy) 
                tmp.push_back(e);
        } else {
            if (!m1 && (e1 == -1 || wf[e] < wf[e1])) {
                e2 = e1;
                e1 = e;
            } else if (e != e1 && (e2 == -1 || wf[e] < wf[e2])) {
                e2 = e;
            }
        }
    }
    
    if (e1 != -1 && e2 != -1) {
        assert(e1 != e2);
        if (so.lazy) {
            //Find forbidden edges cheaper than e1 and e2
            for (unsigned int i = 0; i < tmp.size(); i++) {
                if (wf[tmp[i]] < wf[e2])
                    ps.push(getEdgeVar(tmp[i]).getValLit());
            }
        }
        return true; //found 2 edges
    }
    return false;    
}


template<typename T>
bool TSPPropagator::find_two_expensive(int node, int& e1, int& e2, T* wf) {
    vec<Lit> ps;
    return find_two_expensive(node, e1, e2, wf, ps);
}
template<typename T>
bool TSPPropagator::find_two_expensive(int node, int& e1, int& e2, T* wf, vec<Lit>& ps){
    e1 = -1;
    e2 = -1;
    bool m1 = false;
    //First look for mandatories:
    // for (unsigned int i = 0; i < adj[node].size(); i++) {
    //     int e = adj[node][i];
    //     if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
    //         if (so.lazy) 
    //             ps.push(getEdgeVar(e).getValLit());
    //         if (e1 == -1) {
    //             e1 = e; m1 = true;
    //         } else 
    //             e2 = e;
    //     } 
    // }
    e1 = mand1[node] == -1 ? mand2[node] : mand1[node];
    e2 = e1 == -1 ? -1 : (int)(e1 == mand1[node] ? (int)mand2[node] : -1);
    m1 = (e1 != -1);
    if (e1 != -1) ps.push(getEdgeVar(e1).getValLit());
    if (e2 != -1) ps.push(getEdgeVar(e2).getValLit());

    assert(e1 != e2 || (e1 == -1 && e2==-1));
    assert(e2 == -1 || e1 != -1);
    if (e1 != -1 && e2 != -1)  {
        assert(e1 != e2);
        return true; //found 2 edges
    }
    std::vector<int> tmp;
    for (unsigned int i = 0; i < adj[node].size(); i++) {
        int e = adj[node][i];
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
            if (so.lazy) 
                tmp.push_back(e);
        } else {
            if (!m1 && (e1 == -1 || wf[e] > wf[e1])) {
                e2 = e1;
                e1 = e;
            } else if (e != e1 && (e2 == -1 || wf[e] > wf[e2])) {
                e2 = e;
            }
        }
    }
    
    if (e1 != -1 && e2 != -1) {
        assert(e1 != e2);
        if (so.lazy) {
            //Find forbidden edges cheaper than e1 and e2
            for (unsigned int i = 0; i < tmp.size(); i++) {
                if (wf[tmp[i]] > wf[e2])
                    ps.push(getEdgeVar(tmp[i]).getValLit());
            }
        }
        return true; //found 2 edges
    }
    return false;    
}

#endif
