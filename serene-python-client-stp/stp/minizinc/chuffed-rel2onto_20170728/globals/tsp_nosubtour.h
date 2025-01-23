#ifndef TSP_NO_SUBTOUR
#define TSP_NO_SUBTOUR

#include "core/propagator.h"
#include "support/union_find.h"
#include <iostream>
#include "tree.h"
#include <set> 
#include <vector> 
#include <algorithm>    // std::sort


/**
 * TSP Subtour elimination with explanations
 *
 */


class NoSubtourPropagator : public GraphPropagator {


    std::vector<int> new_in_edges;
    std::vector<int> in_edges;
    Tint in_edges_tsize;
    int in_edges_size;
    enum VType{IN, OUT, UNK};
    std::vector<Tint> last_state_e;

    //Subtour elimination:
    std::vector<Tint> extremity1;
    std::vector<Tint> extremity2;
    std::vector<Tint> chainl;
    RerootedUnionFind<Tint> ruf;

protected:
    Tint& other_extremity(int node);
    void update_inedges();
    void add_inedge(int e);
public:

    NoSubtourPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                        vec< vec<edge_id> >& _adj, vec< vec<int> >& _en);
    
    void wakeup(int i, int c);
    bool propagate();
    void clearPropState();
    
};

#endif
