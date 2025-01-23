#ifndef TDBOUNDEDPATH_H
#define TDBOUNDEDPATH_H

#include "graph_propagator.h"
#include "../support/Dijkstra.h"
#include "directed_reachability.h"
#include <vector>
#include <string> 
#include <unordered_set>
#include <functional>

namespace std {
    template <>
    struct hash<Lit> {
        size_t operator () (const Lit &l) const { return toInt(l); }
    };
    template <>
    struct hash<std::pair<int,int> > {
        size_t operator () (const std::pair<int,int> &p) const { 
            return std::hash<int>{}(p.first)*std::hash<int>{}(p.second);
        }
    };
};


int dicho_function(std::vector<std::vector<int> >& fun, int t);

class ClosestNextStrategy;

class TDBoundedPath : public GraphPropagator{
    
    friend ClosestNextStrategy;

protected:
    typedef std::vector<std::vector<int> > vvi_t;

    int source;
    int dest;

    vec<BoolView> before; //before[a][b] <=> a is before b
    //Usefull for inferences since, when some node is not mandatory we can't
    //use the before BollView to do inferneces about its position for the DP!
    vec<BoolView> local_before; //before[a][b] => local_before
    Tint* preds;
    bool makeUBeforeV(int u, int v, vec<Lit> expl = vec<Lit>()); //First cell always empty in explanations!!
    bool makeLocallyUBeforeV(int u, int v, vec<Lit> expl = vec<Lit>());

    Tint* fixed_outgoing;
    Tint* fixed_incident;

    IntVar* w;
    
    vvi_t incident;
    vvi_t outgoing;
    vvi_t nodes2edge;
    vvi_t time_weight;
    std::vector<bool> is_negative;
    std::vector<bool> is_constant;
    bool all_constant;
    std::vector<int> task_time;
    vvi_t latest_time;
    std::vector<std::vector<std::vector<int> > > abrv_time_weight;
    std::vector<std::vector<std::vector<int> > > abrv_latest_time;
    std::set<int> fixed_edges;
    std::vector<std::pair<int,int> > u_before_v;
    
    enum State {IN, OUT, UNK};
    Tint* last_state_e;
    Tint* last_state_n;
    Tint available_edges;

    DReachabilityPropagator* reachable;
    DReachabilityPropagator* reachable_inv;

    inline bool isNegativeE(int e) {
        return is_negative[e];
    }
    inline bool isMandatoryN(int n) {
        return getNodeVar(n).isFixed() && getNodeVar(n).isTrue();
    }
    inline bool isForbiddenN(int n) {
        return getNodeVar(n).isFixed() && getNodeVar(n).isFalse();
    }
    inline bool isFixedN(int n) {
        return getNodeVar(n).isFixed();
    }
    inline bool isMandatoryE(int e) {
        return getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue();
    }
    inline bool isForbiddenE(int e) {
        return getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse();
    }
    inline bool isFixedE(int e) {
        return getEdgeVar(e).isFixed();
    }
    inline std::string stateE(int e) { //For debug
        if (!isFixedE(e)) return "U";
        else if (isMandatoryE(e)) return "M";
        else return "F";
    }
    inline std::string stateN(int n) { //For debug
        if (!isFixedN(n)) return "U";
        else if (isMandatoryN(n)) return "M";
        else return "F";
    }
    inline int duration(int n) {
        return task_time[n];
    }
    inline int weight(int e, int t) {
        if (is_constant[e]) return time_weight[e][0];
        //assert(e < time_weight.size());
        //assert(t < time_weight[e].size());
        int ret = (t >= (int)time_weight[e].size()) ? time_weight[e][0] : time_weight[e][t];
        if(ret < 0) std::cout<<time_weight[e][1]<<std::endl;
        assert(ret >= 0);
        return ret;
        return dicho_function(abrv_time_weight[e], t);
    }

public:
    inline BoolView& getUBeforeV(int u, int v) {return before[u*nbNodes() + v];}
    inline BoolView& getUBeforeVPossible(int u, int v) {return local_before[u*nbNodes() + v];}
    void set_reachable(DReachabilityPropagator* forw, DReachabilityPropagator* back) {
        reachable = forw;
        reachable_inv = back;
    }

protected:
    inline int depart_to_arrive(int e, int t) {
        if (is_constant[e]) return t - weight(e,t);
        if (t >= (int)latest_time[e].size()) {
            int xe = latest_time[e].size();
            int ve = latest_time[e][latest_time[e].size()-1];
            int xc = t;
            int vc = ve + (xc - xe);   
            return vc;
        } else {
            return latest_time[e][t];
        }
        return dicho_function(abrv_latest_time[e], t);
    }
    inline Lit dummy_lit() {return getNodeVar(source).getValLit();}

    
    //Earliest times you can laave for each node
    //furthest: furthest  node that is still reachable in time
    void find_earliest_ready(std::vector<int>& too_late, int& furthest_node);
    std::vector<int> earliest_ready;
    Tint* was_in_earliest;
    //Latest time we need to arrive to a node
    //too_slow: edges, that if taken, require I leave before 0 to be at the 
    //head on time
    void find_latest_arrivals(std::vector<int>& too_slow);
    std::vector<int> latest_arrivals;


    //If n is given and is mandatory,  return an explanation for failure.
    //If n is given but not mandatory, return an explanation for propagation.
    //If n == -1,                      return explanation for lower bound.
    //Use full epxlanations.
    std::vector<Lit> explain_naive(bool fail);
    //Use basic explanations: was_in_earliest
    void explain_basic(int n, std::vector<Lit>& ps);
    std::vector<Lit> explain_basic(int n = -1);


    //These are the advanced explanation for the basic propagation (not DP).
    
    //You need to get to 'n' at limit (not counting the task time).
    //Which removed edges would have allowed be to get to 'n' before limit? 
    //(i.e. make earliest_ready[n] -d(n) go smaller
    int explain_n_too_far(int n, int limit, std::vector<Lit>& lits, int ignore = -1); //Backward
    //You only managed to get to 'n' at 'start' (not counting task time)
    //Which removed edges could make me get to 'dest' faster from 'n'.
    //(i.e. make the latest_arrivals[n] go bigger).
    int explain_n_too_early(int n, int start, std::vector<Lit>& lits, int ignore = -1); //Forwar
    


    //For the basic explanations:
    void update_explanation();
    Tint explanation_tsize;
    std::vector<Lit> fail_expl;
    std::vector<Lit> prop_expl;

    //For the DijkstraMandatory
    void update_innodes();
    Tint in_nodes_tsize;
    std::vector<int> in_nodes_list;


    class FilteredDijkstraMandatory : public DijkstraMandatory {
    protected:
        TDBoundedPath* p;
        std::vector<std::bitset<BITSET_SIZE> > preds;
    public:
        std::vector<bool> is_dom;
        std::unordered_set<Lit> avoided;
        std::unordered_set<std::pair<int,int> > avoided_r;
        std::vector<map_type> side_table;
        FilteredDijkstraMandatory(TDBoundedPath* _btp, int _s, int _d,
                                  std::vector< std::vector<int> > _en, 
                                  std::vector< std::vector<int> > _in, 
                                  std::vector< std::vector<int> > _ou,
                                  std::vector<std::vector<int> >& _ws,
                                  std::vector<int> _ds)
            : DijkstraMandatory(_s,_d,_en,_in,_ou,_ws,_ds), p(_btp) {}

        void set_doms(std::vector<bool> _is_dom) {
            //Know who is a dominator to use their side_tables
            is_dom = _is_dom;
        } 
        int run(bool* ok = NULL, bool use_set_target = false) {
            avoided_r.clear();
            avoided.clear();
            side_table = std::vector<map_type>(p->nbNodes());
            std::bitset<BITSET_SIZE> pathS; pathS[source] = 1;
            std::bitset<BITSET_SIZE> mandS; mandS[source] = 1;
            tuple initial(source,duration(source), pathS,mandS);
            side_table[source][hash_fn(mandS)] = initial;

            return DijkstraMandatory::run(ok,false);
        }

        virtual bool ignore_node(int n) {
            if (p->getNodeVar(n).isFixed() && p->getNodeVar(n).isFalse())
                return true;
            return false;
        }

        virtual bool ignore_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse())
                return true;

            int hd = p->getHead(e);
            int tl = p->getTail(e);

            assert(!(p->getUBeforeV(hd,tl).isFixed() && p->getUBeforeV(hd,tl).isTrue()) ||
                   (p->getUBeforeVPossible(hd,tl).isFixed() && p->getUBeforeVPossible(hd,tl).isTrue()));
            //if (p->getUBeforeV(hd,tl).isFixed() && p->getUBeforeV(hd,tl).isTrue()) {
            if (p->getUBeforeVPossible(hd,tl).isFixed() && p->getUBeforeVPossible(hd,tl).isTrue()) {
                //Unnecessary in the explanations, It would be more expensive anyway.
                //avoided.insert(p->getUBeforeV(hd,tl).getValLit());
                //avoided_r.insert(std::make_pair(hd,tl));            
                //return true;
            }

            if (is_dom.size() == 0 || is_dom[hd]) {
                //Do not cross an edge if you haven't seen all the predecesors 
                //of the head yet
                DijkstraMandatory::tuple curr = current_iteration();
                int mpreds = p->preds[hd];// & target.to_ulong();
                if ((int)(mpreds & curr.path.to_ulong()) == mpreds) {
                    //std::cout<<"Triggered"<<std::endl;
                    /*if (so.lazy) {
                        std::bitset<BITSET_SIZE> tmp(mpreds);
                        for (int i = 0; i < p->nbNodes(); i++) {
                            if (tmp[i] && !curr.path[i]) {
                                assert(p->isMandatoryN(i));
                                assert(p->isMandatoryN(hd));
                                avoided.insert(p->getUBeforeV(i,hd).getValLit());
                                avoided_r.insert(std::make_pair(i,hd));            
                                break;
                            }
                        }
                        }*/
                    //If I had crossed it, I would see this in the table:
                    {
                        DijkstraMandatory::tuple copy = curr;
                        if (target[hd]) { //Other is mandatory
                            copy.mand[hd] = 1;
                        }
                        copy.cost += weight(e,curr.cost) + duration(hd);
                        copy.path[hd] = 1;
                        copy.node = hd;
                        DijkstraMandatory::table_iterator it = side_table[hd].find(hash_fn(copy.mand));
                        if (it == side_table[hd].end() || (it->second).cost > copy.cost)
                            side_table[hd][DijkstraMandatory::hash_fn(copy.mand)] = copy;

                        assert(is_dom.size() == 0 || (is_dom[hd] &&side_table[hd].size() == 1));
                    }
                
                    //return true;
                }
            }


            return false;
        }

        virtual bool mandatory_node(int u) {
            if (p->getNodeVar(u).isFixed() && p->getNodeVar(u).isTrue())
                return true;
            return false;
        }
        virtual bool mandatory_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isTrue())
                return true;
            return false;
        }
        virtual std::vector<int>& mandatory_nodes() {
            return p->in_nodes_list;
        }
        virtual inline int weight(int e, int time = -1) {
            if (time == -1) {
                return 0; //Do not ignore!!                
            }
            return p->weight(e,time);
        }

    };
    FilteredDijkstraMandatory* earliest_ready_dp;
    void explain_dest_dp(std::vector<Lit>& lits); //Backward


    struct SortArrivals {
        TDBoundedPath* p;
        SortArrivals(TDBoundedPath* _p) :p(_p){}
        bool operator() (int i,int j) { 
            return p->earliest_ready[i] - p->duration(i) < p->earliest_ready[j] - p->duration(j);
        }
    } sort_arrivals;
    struct SortLatests {
        TDBoundedPath* p;
        SortLatests(TDBoundedPath* _p) :p(_p){}
        bool operator() (int i,int j) { 
            return p->latest_arrivals[i] > p->latest_arrivals[j];
        }
    } sort_latests;




public:
    static int expl_count;
    static int expl_len;
    static int props;

    TDBoundedPath(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                  vec<BoolView>& _order, vec<BoolView>& _order_opt,
                  vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                  vec< vec<int> >& _en, vec< vec<int> >& ws, vec<int> ds, IntVar* w);
    virtual ~TDBoundedPath();
    virtual void wakeup(int i, int c);
    virtual bool propagate();
    virtual void clearPropState();
    

};



class TDBoundedPathArrivals : public TDBoundedPath {
    vec<IntVar*> lowers;
    vec<IntVar*> uppers;
    
    bool remove_node(int n, Clause* r = NULL);
    void _explain_n_too_far(int n, int limit, std::vector<Lit>& lits,std::vector<bool>& v);
    void _explain_n_too_early(int n, int start, std::vector<Lit>& lits,std::vector<bool>& v);
public:

    TDBoundedPathArrivals(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                          vec<BoolView>& _order, vec<BoolView>& _order_opt,
                          vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                          vec< vec<int> >& _en, vec< vec<int> >& ws, vec<int> ds,
                          IntVar* w, vec<IntVar*> _lowers, vec<IntVar*> _uppers);
    virtual bool propagate();


    bool propagate_arrivals();

    void explain_n_too_far(int n, int limit, std::vector<Lit>& lits);
    void explain_n_too_early(int n, int start, std::vector<Lit>& lits);
    void explain_dp(int start, int time, int avoid, std::bitset<BITSET_SIZE> target, 
                    std::unordered_set<Lit>& lits);

    inline Lit varNEv(IntVar* var,int val) {
        if (val > var->getMax()) return var->getMaxLit();
        if (val < var->getMin()) return var->getMinLit();
        assert(false); //Never happens
        return Lit();
    }

    bool propagateBefore(std::stack<int> arts);
    bool propagateDP(std::stack<int> arts, std::vector<int> low);
    std::vector<bool> getBiCC(int i, std::vector<int>& depth, std::vector<int>& low,
                              std::vector<bool>& visited, std::vector<int>& parent,
                              std::stack<int>& articulations, int d = 0);

};

#endif
