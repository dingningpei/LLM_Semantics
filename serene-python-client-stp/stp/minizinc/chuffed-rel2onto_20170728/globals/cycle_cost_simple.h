#ifndef CYCLE_COST_SIMPLE
#define CYCLE_COST_SIMPLE

#include "core/propagator.h"
#include "support/union_find.h"
#include <iostream>
#include "tree.h"
#include <set> 
#include <vector> 
#include <algorithm>    // std::sort



class CycleCostSimple : public GraphPropagator {
    
public:
    IntVar* obj;

    Tint* mand1;
    Tint* mand2;
    bool update_mand_vectors(int e);

    Tint* neigh_sizes;
    std::vector< std::vector<edge_id> > adj_map;

    int* original_ws;


    std::vector<int> in_edges;
    Tint in_edges_tsize;
    int in_edges_size;

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
    bool filter_expensive_edges_simple();

    bool propagate_upper_bound();
    void on_edge_removal(int e);

public:

    CycleCostSimple(vec<BoolView>& _vs, vec<BoolView>& _es, 
                    vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
                    IntVar* _w, vec<int>& _ws);
    
    void wakeup(int i, int c);
    bool propagate();
    void clearPropState();
    
    bool checkFinalSatisfied();

};

template<typename T>
bool CycleCostSimple::find_two_cheapest(int node, int& e1, int& e2, T* wf) {
    vec<Lit> ps;
    return find_two_cheapest(node, e1, e2, wf, ps);
}
template<typename T>
bool CycleCostSimple::find_two_cheapest(int node, int& e1, int& e2, T* wf, vec<Lit>& ps){
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
bool CycleCostSimple::find_two_expensive(int node, int& e1, int& e2, T* wf) {
    vec<Lit> ps;
    return find_two_expensive(node, e1, e2, wf, ps);
}
template<typename T>
bool CycleCostSimple::find_two_expensive(int node, int& e1, int& e2, T* wf, vec<Lit>& ps){
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
