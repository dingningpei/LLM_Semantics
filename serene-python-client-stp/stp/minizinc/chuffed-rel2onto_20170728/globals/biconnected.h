#ifndef BICONNECTEDPROPAGATOR_H
#define BICONNECTEDPROPAGATOR_H
#include "graph_propagator.h"
#include "../support/FloydWarshall.h"
#include "../support/union_find.h"

class BiConnectedPropagator : public GraphPropagator {

protected:
    std::vector<int> fixed_nodes;
    std::vector<int> fixed_edges;
    std::vector<bool> is_fixed_node;
    std::vector<bool> is_fixed_edge;

    std::vector<Tint> degree;
    std::vector<int> low_degree;

    std::vector<int> in_nodes;
    Tint in_nodes_tsize;
    std::vector<Tint> state_node;
    void add_innode(int i);
    void update_innodes();

    std::vector<std::vector<int> > nodes2edge;

    bool _biconnected(int u, int& count, 
                      std::vector<bool>& visited,
                      std::vector<int>& depth,
                      std::vector<int>& low,
                      std::vector<int>& parent,
                      int& last_mand,
                      std::stack<std::pair<int, std::pair<int,int> > >& arts);
public:
    bool biconnected(int u, int& count, std::vector<bool>& visited);
    std::vector<int> explain_biconnected(int start, int end, int avoid, 
                                         vec<Lit>& lits);
    std::vector<int> explain_biconnected(int start, int end, int avoid, 
                                         vec<Lit>& lits, 
                                         std::vector<int>& identical_nodes);
    bool verify_biconnected_expl(int s, int d, std::vector<int>& expl);
    void _verify_biconnected_expl(int u, int& count, std::vector<bool>& available,
                                  std::vector<bool>& visited,
                                  std::vector<int>& depth,
                                  std::vector<int>& low,
                                  std::vector<int>& parent,
                                  std::vector<bool>& articulation);
    bool verify_minimal_biconnected_expl(int s, int d, std::vector<int>& expl);
    bool connected(int u, int count, std::vector<bool>& visited);
    void explain_connected(int disc, std::vector<bool>& visited, vec<Lit>& lits);
    bool verify_connected_expl(int s, int d, std::vector<int>& expl);
    bool verify_minimal_connected_expl(int s, int d, std::vector<int>& expl);
    
    void depth_first_search(int origin, int avoid, std::vector<int>& seen);

    BiConnectedPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                          vec< vec<int> >& _en, vec< vec<int> >& _adj);

    virtual ~BiConnectedPropagator();

    virtual void wakeup(int i, int c);
    virtual bool propagate();
    virtual void clearPropState();
    virtual bool checkFinalSatisfied();
};


class WeightedBiConnectedPropagator : public BiConnectedPropagator {

    std::vector<int> ws;
    IntVar* w;

    UFRootInfo<Tint> uf; //Trailed UnionFind
    Tint mandatory_weight;
    std::vector<Tint> added;

    std::vector<Tint> was_sp;


    int hamiltonian_bound();
    int bounding_two_for_each();
    int bounding_two_closest();
    int dist_two_closest(int u);
public:
    WeightedBiConnectedPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                                  vec< vec<int> >& _en, vec< vec<int> >& _adj,
                                  vec<int>& weights, IntVar* _w);
    
    void wakeup(int i, int c);
    bool propagate();
    virtual bool checkFinalSatisfied();
};

#endif
