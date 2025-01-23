#include "biconnected.h"
#include <string>
#include <iostream>
#include <unordered_map>

#include "../core/sat.h"
#include "../support/Dijkstra.h"

using namespace std;

#define MIN(a,b) ((a<b)? a : b)


// int find_clevel(Clause* r) {
//     int tp = -1;
//     for (int i = 0; i < r->size(); i++) {
//         int l = sat.trailpos[var((*r)[i])];
//         if (l > tp) tp = l;
//     }
//     return engine.tpToLevel(tp);
// }

BiConnectedPropagator::BiConnectedPropagator(vec<BoolView>& _vs, 
                                             vec<BoolView>& _es, 
                                             vec< vec<int> >& _en, 
                                             vec< vec<int> >& _adj) 
    : GraphPropagator(_vs,_es,_en) {
    priority = 2;
    adj = vector<vector<int> >(nbNodes(), vector<int>());

    for (int i = 0; i < _adj.size(); i++)
        for (int j = 0; j < _adj[i].size(); j++)
            adj[i].push_back(_adj[i][j]);


    for (int i = 0; i < nbNodes(); i++)
        getNodeVar(i).attach(this, i , EVENT_LU);
    for (int i = 0; i < nbEdges(); i++)
        getEdgeVar(i).attach(this, nbNodes()+i , EVENT_LU);

    degree = vector<Tint>(nbNodes(), 0);

    for (int i = 0; i < nbNodes(); i++) {
        degree[i] = adj[i].size();
    }

    in_nodes_tsize = 0;
    state_node = vector<Tint>(nbNodes(), 0);

    is_fixed_node = vector<bool>(nbNodes(),false);
    is_fixed_edge = vector<bool>(nbEdges(),false);


    nodes2edge = std::vector<std::vector<int> >(nbNodes());
    for (int i = 0; i < nbNodes(); i++) 
        nodes2edge[i] = std::vector<int>(nbNodes(), -1);    
    for (int e = 0; e < nbEdges(); e++) {
        nodes2edge[getEndnode(e,0)][getEndnode(e,1)] = e;
        nodes2edge[getEndnode(e,1)][getEndnode(e,0)] = e;
    }
}

BiConnectedPropagator::~BiConnectedPropagator() {

}

void BiConnectedPropagator::add_innode(int i) {
    assert(getNodeVar(i).isFixed());
    assert(getNodeVar(i).isTrue());
    if (state_node[i] == 1) //Already in
        return;
    in_nodes_tsize++;
    in_nodes.push_back(i);
    state_node[i] = 1;
}

void BiConnectedPropagator::update_innodes() {
    if (in_nodes_tsize < (int)in_nodes.size()) {
        in_nodes.resize(in_nodes_tsize);
    }
}

void BiConnectedPropagator::wakeup(int i, int c) {
    update_innodes();
    if (i >= 0 && i < nbNodes()){
        
        if (getNodeVar(i).isFalse() && !is_fixed_node[i]) {
            fixed_nodes.push_back(i);
            is_fixed_node[i] = true;
        } else if (getNodeVar(i).isTrue()) {
            add_innode(i);            
        }
        pushInQueue();

    } else if(i >= nbNodes() && i < nbNodes()+nbEdges()) { 

        int j = i - nbNodes();
        if (getEdgeVar(j).isTrue() && !is_fixed_edge[j]) {
            fixed_edges.push_back(j);
            is_fixed_edge[j] = true;
        } else if (getEdgeVar(j).isFalse() && !is_fixed_edge[j]) {
            int u = getEndnode(j,0);
            int v = getEndnode(j,1);
            degree[u]--;
            if (degree[u] <= 1)
                low_degree.push_back(u);
            degree[v]--;
            if (degree[v] <= 1)
                low_degree.push_back(v);
        }
        pushInQueue();

    }  

}

bool BiConnectedPropagator::propagate() {
    update_innodes();

    /*for (unsigned int i = 0; i < low_degree.size(); i++) {
        int u = low_degree[i];
        if (!getNodeVar(u).isFixed()) {
            Clause* r = NULL;
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                for (unsigned int j = 0; j < adj[u].size(); j++) {
                    int e = adj[u][j];
                    if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse())
                        ps.push(getEdgeVar(e).getValLit());
                }
                assert(ps.size() >= (int)adj[u].size() - 1);
                r = Reason_new(ps);
                //assert(find_clevel(r) > 0);
            }
            getNodeVar(u).setVal(false,r);
            if (!coherence_outedges(u))
                return false;
            is_fixed_node[u] = true;
        } else if (getNodeVar(u).isTrue()) {
            if (so.lazy) {
                vec<Lit> ps;
                for (unsigned int j = 0; j < adj[u].size(); j++) {
                    int e = adj[u][j];
                    if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse())
                        ps.push(getEdgeVar(e).getValLit());
                }
                assert(ps.size() >= (int)adj[u].size() - 1);
                ps.push(getNodeVar(u).getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
                //assert(find_clevel(expl) > 0);
            }
            return false;   
        }
    }*/

    /*for (unsigned int i = 0; i < fixed_nodes.size(); i++) {
        int n = fixed_nodes[i];
        if (!coherence_outedges(n))
            return false;        
    }

    for (unsigned int i = 0; i < fixed_edges.size(); i++) {
        int e = fixed_edges[i];
        if (!coherence_innodes(e))
            return false;     
        add_innode(getEndnode(e,0));
        add_innode(getEndnode(e,1));
    }*/
    
    
    int r = in_nodes[0];
    int count = 0;
    vector<bool> seen = vector<bool>(nbNodes(), false);
    if(!biconnected(r, count, seen)) {
        return false;
    }

    if (!connected(r,count,seen)) {
        return false;
    }

    return true;
}

bool BiConnectedPropagator::biconnected(int u, int& count, 
                                        std::vector<bool>& visited) {
    visited = std::vector<bool>(nbNodes(), false);
    std::vector<int> depth = std::vector<int>(nbNodes(), -1);
    std::vector<int> low = std::vector<int>(nbNodes(), -1);
    std::vector<int> parent = std::vector<int>(nbNodes(), -1);
    parent[u] = u;
    int l_m = u;
    //<articulation_between <mandatory, some_to_be_removed> >
    std::stack<std::pair<int, std::pair<int,int> > > arts;
    bool ok = _biconnected(u,count, visited, depth, low, parent, l_m, arts);
    if (!ok) {
        return false;
    }
    while(!arts.empty()) {        
        int a = arts.top().first;
        int m = arts.top().second.first;
        int s = arts.top().second.second;
        arts.pop();
        if (getNodeVar(a).isFixed() && getNodeVar(a).isFalse()) {
            continue; //You already removed previously in this loop
        }

        Clause* r = NULL;

        vector<int> others;
        vector<int> edges;
        if (so.lazy) {
            vec<Lit> ps; ps.push();
            edges = explain_biconnected(m,s,a,ps,others);
            ps.push(getNodeVar(m).getValLit());
            r= Reason_new(ps);
        } else {
            depth_first_search(s,a, others);
        }
        for (unsigned int i = 0; i < others.size(); i++) {
            assert(a != others[i]);
            getNodeVar(others[i]).setVal(false,r);
            //There is no reason for the explanation to be minimal for everyone
            //in others:
            //  \     E          "dotted" edge must be in the explanation why we
            //  .\.  / \         remove B, but not needed for B C or D.
            //    \ /   \        The explanation is still valid though, and 
            //     B     D       Computing it once is cheaper....
            //    / \   /
            //   /   \ /
            // ART    C
            //assert(verify_minimal_biconnected_expl(m,others[i],edges));
            if(so.lazy)
                assert(verify_biconnected_expl(m,others[i],edges));
            if(!coherence_outedges(others[i]))
                return false;
            is_fixed_node[others[i]] = 1;
        }
    }

    return true;
}

bool BiConnectedPropagator::_biconnected(int u, int& count, 
                                         std::vector<bool>& visited,
                                         std::vector<int>& depth,
                                         std::vector<int>& low,
                                         std::vector<int>& parent,
                                         int& last_mand,
                                         std::stack<std::pair<int, std::pair<int,int> > >& arts) {
        
    assert(!getNodeVar(u).isFixed() || getNodeVar(u).isTrue());
    visited[u] = true;
    count++;
    depth[u] = count;
    low[u] = depth[u];

    //This is in case u is mandatory and an articulation
    //If that happens, last_mand cannot be in the explanation,
    //because it would be wrong! from last_mand there are
    //two paths to the nodes below! Tehre arent from passed_last, though
    int passed_last = last_mand; 

    if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue())
        last_mand = u; //overwrite parameter


    //cout<<"last_mand = "<<last_mand<<" from "<<u<<" passedlast="<<passed_last<<endl;

    int saved_mand = last_mand;
    int mand_changed = -1;

    for (unsigned int i = 0; i < adj[u].size(); i++) {
        int e = adj[u][i];
        int v = getOtherEndnode(e,u);

        if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
            (getNodeVar(v).isFixed() && getNodeVar(v).isFalse()))
            continue;

        if (!visited[v]){
            parent[v] = u;

            if(!_biconnected(v,count,visited, depth, low, parent,last_mand,arts))
                return false;
            if (last_mand != saved_mand)
                mand_changed = last_mand;
            
            //cout<<"last_mand = "<<last_mand<<" after call "<<u<<endl;
            if (low[v] >= depth[u] && parent[u] != u) {  
                //u is articulation && is not the root
                //cout<<"v: "<<v<<" "<<low[v]<<" "<<u<<" "<<low[u]<<endl;
                //Two options:
                //1) either last_mand == saved_mand: 
                //   in that case I dit not see a mandatory while recursing
                //   but I still am an articulation, so anything with depth > 
                //   than me must be removed.
                //   Expl: I can't get from saved mand to anything with depth >
                //   than me if I can't use myself => not(saved_mand)
                //2) or last_mand != saved_mand:
                //   I saw some mandatory node below me, and I am an artiuclation,
                //   so there is no 2 ways of getting to last_mand. FAIL
                //   Expl: I can't get from saved mand to anything with depth >
                //   than me if I can't use myself /\ saved_mand => fail
                int expl_node = saved_mand;
                if (last_mand == saved_mand) {
                    if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) 
                        expl_node = passed_last; //cant use saved_mand
                    arts.push(make_pair(u,make_pair(expl_node,v)));
                } else {
                    if (so.lazy) {
                        if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) 
                            expl_node = passed_last; //cant use saved_mand
                        vec<Lit> ps;
                        vector<int> edges = 
                            explain_biconnected(expl_node,last_mand,u,ps);
                        ps.push(getNodeVar(expl_node).getValLit());
                        ps.push(getNodeVar(last_mand).getValLit());
                        assert(verify_minimal_biconnected_expl(expl_node,last_mand,edges));
                        Clause *expl = Clause_new(ps);
                        expl->temp_expl = 1;
                        sat.rtrail.last().push(expl);
                        sat.confl = expl;
                        //assert(find_clevel(expl) > 0);
                    } 
                    return false;
                }

            } 
            last_mand = saved_mand; //Restore previous local state       
            low[u] = MIN(low[u],low[v]);

        } else if(parent[u] != v && depth[v] < depth[u]) {

            low[u] = MIN(low[u],depth[v]);

        }

    }

    //Restore previous global state
    if (mand_changed != -1)
        last_mand = mand_changed;
    

    return true;
}

vector<int> BiConnectedPropagator::explain_biconnected(int start, int end, 
                                                       int avoid, 
                                                       vec<Lit>& lits) {
    vector<int> dummy;
    return explain_biconnected(start,end,avoid,lits,dummy);
}
vector<int> BiConnectedPropagator::explain_biconnected(int start, int end, 
                                                       int avoid, 
                                                       vec<Lit>& lits,
                                                       std::vector<int>& identical_nodes) {
    //fullExpl(lits);
    //return vector<int>();
    std::vector<bool> blue(nbNodes(),false);
    std::stack<int> s;
    s.push(end);
    while(!s.empty()) {
        int c = s.top(); s.pop();
        if (blue[c]) 
            continue;
        blue[c] = true;
        identical_nodes.push_back(c);
        for (unsigned int i = 0; i < adj[c].size(); i++) {
            int e = adj[c][i];
            int o = getOtherEndnode(e,c);
            if (o == avoid) 
                continue;
            if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                (getNodeVar(o).isFixed() && getNodeVar(o).isFalse()))
                continue;
            if (!blue[o]) 
                s.push(o);
        }
        
    }

    vector<int> edges;
    std::vector<bool> pink(nbNodes(),false);    
    s.push(start);
    while(!s.empty()) {
        int c = s.top(); s.pop();
        if (pink[c]) 
            continue;
        pink[c] = true;
        for (unsigned int i = 0; i < adj[c].size(); i++) {
            int e = adj[c][i];
            int o = getOtherEndnode(e,c);
            if (o == avoid) 
                continue;
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
                if (blue[o]) {
                    lits.push(getEdgeVar(e).getValLit());
                    edges.push_back(e);
                    continue;
                }
            }
            if (!pink[o])
                s.push(o);
        }
        
    }
    return edges;
}


bool BiConnectedPropagator::verify_minimal_biconnected_expl(int s, int d, vector<int>& expl) {

    assert(verify_biconnected_expl(s,d,expl));
    //cout<<"Explanation correct"<<endl;
    vector<int> tmp = expl;
    for (unsigned int i = 0; i < tmp.size(); i++) {
        int old = tmp[i];
        tmp[i] = -1;
        //cout<<"--------------------------" << expl.size()<<" "<<i<<endl;
        int ok = verify_biconnected_expl(s,d,tmp);
        if (ok) {
            cout<<"Not minimal "<< s<<" "<<d<<endl;
            for (unsigned int j = 0; j < expl.size(); j++) {
                cout<<expl[j]<<" ";
            }
            for (unsigned int j = 0; j < expl.size(); j++) {
                cout<<tmp[j]<<" ";
            }
            cout<<endl;
            cout<<all_to_dot()<<endl;
            exit(1);
        }
        assert(!ok);
        if (ok)
            return false;
        tmp[i] = old;
    }
    return true;
}

bool BiConnectedPropagator::verify_biconnected_expl(int s, int d, vector<int>& expl) {

    assert(s != d);
    vector<bool> available = vector<bool>(nbEdges(),true);
    for (unsigned int i = 0; i < expl.size(); i++) {
        int e = expl[i];
        if (e != -1) {
            available[e] = false;
        }
    }

    std::vector<int> depth = std::vector<int>(nbNodes(), -1);
    std::vector<int> low = std::vector<int>(nbNodes(), -1);
    std::vector<int> parent = std::vector<int>(nbNodes(), -1);
    std::vector<bool> visited(nbNodes(),false);
    std::vector<bool> arts(nbNodes(),false);
    int count = 0;
    _verify_biconnected_expl(s,count, available, visited, depth, low, parent,arts);

    arts[s] = false; //No false alarms
    int x = d;
    while (parent[x] != x) {
        if (arts[parent[x]] && low[x] >= depth[parent[x]])
            return true;
        x = parent[x];
        if (x == s)
            return false;
    }
    return false;
}

void BiConnectedPropagator::_verify_biconnected_expl(int u, int& count, 
                                                     std::vector<bool>& available,
                                                     std::vector<bool>& visited,
                                                     std::vector<int>& depth,
                                                     std::vector<int>& low,
                                                     std::vector<int>& parent,
                                                     std::vector<bool>& articulation) {
    visited[u] = true;
    count++;
    depth[u] = count;
    low[u] = depth[u];

    for (unsigned int i = 0; i < adj[u].size(); i++) {
        int e = adj[u][i];
        int v = getOtherEndnode(e,u);

        if (!available[e])
            continue;

        if (!visited[v]){
            parent[v] = u;

            _verify_biconnected_expl(v,count,available,visited, depth, low, parent,articulation);

            if (low[v] >= depth[u] && parent[u] != u) {  
                articulation[u] = true;
            } 
            low[u] = MIN(low[u],low[v]);
        } else if(parent[u] != v && depth[v] < depth[u]) {
            low[u] = MIN(low[u],depth[v]);
        }
    }
}

bool BiConnectedPropagator::connected(int u, int count, std::vector<bool>& visited) {
    
    for (unsigned int i = 0; i < in_nodes.size(); i++) {
        int n = in_nodes[i];
        if (!visited[n]) {
            if (so.lazy) {
                vec<Lit> ps;
                explain_connected(n, visited, ps);
                ps.push(getNodeVar(u).getValLit());
                ps.push(getNodeVar(n).getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
                //assert(find_clevel(expl) > 0);
            }
            return false;
        }
    }
    
    for (int i = 0; i < nbNodes(); i++) {
        if (!visited[i] && !getNodeVar(i).isFixed()) {
            Clause* r = NULL;
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                explain_connected(i, visited, ps);
                ps.push(getNodeVar(u).getValLit());
                r = Reason_new(ps);
                //assert(find_clevel(r) > 0);
            }
            getNodeVar(i).setVal(false,r);
            if (!coherence_outedges(i))
                return false;
            is_fixed_node[i] = true;
        }
    }

    return true;
}


void BiConnectedPropagator::explain_connected(int disc, vector<bool>& blue, 
                                              vec<Lit>& lits) {
    std::vector<bool> pink(nbNodes(),false);
    std::stack<int> s;
    s.push(disc);
    while(!s.empty()) {
        int c = s.top(); s.pop();
        if (pink[c]) 
            continue;
        pink[c] = true;

        for (unsigned int i = 0; i < adj[c].size(); i++) {
            int e = adj[c][i];
            int o = getOtherEndnode(e,c);
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
                if (blue[o]) {
                    lits.push(getEdgeVar(e).getValLit());
                    continue;
                }
            }
            if (!pink[o])
                s.push(o);
        }
    }    
}

bool BiConnectedPropagator::verify_minimal_connected_expl(int s, int d, vector<int>& expl) {

    vector<int> tmp = expl;
    for (unsigned int i = 0; i < tmp.size(); i++) {
        int old = tmp[i];
        tmp[i] = -1;
        int ok = verify_connected_expl(s,d,tmp);
        assert(!ok);
        if (ok)
            return false;
        tmp[i] = old;
    }
    return true;
}

bool BiConnectedPropagator::verify_connected_expl(int s, int d, vector<int>& expl) {

    vector<bool> available = vector<bool>(nbEdges(),true);
    for (unsigned int i = 0; i < expl.size(); i++) {
        int e = expl[i];
        if (e != -1) {
            available[e] = false;
        }
    }
    vector<bool> used(nbNodes(),false);
    vector<int> pred(nbNodes(),-1);
    std::vector<bool> visited(nbNodes(),false);
    std::stack<int> st;
    st.push(s);
    pred[s] = s;
    while(!st.empty()) {
        int c = st.top(); st.pop();
        if (c == d) return false;
        if (visited[c]) 
            continue;
        visited[c] = true;        
        for (unsigned int i = 0; i < adj[c].size(); i++) {
            int e = adj[c][i];
            int o = getOtherEndnode(e,c);
            if (!available[e]) {
                continue;
            }
            if (!visited[o]) {
                pred[o] = c;
                st.push(o);
            }
        }   
    }

    if (!visited[d])
        return true;
    return false;
}

void BiConnectedPropagator::depth_first_search(int origin, int avoid, 
                                               std::vector<int>& seen) {
    std::vector<bool> visited(nbNodes(),false);
    std::stack<int> s;
    s.push(origin);
    while(!s.empty()) {
        int c = s.top(); s.pop();
        if (visited[c]) 
            continue;
        visited[c] = true;
        seen.push_back(c);
        for (unsigned int i = 0; i < adj[c].size(); i++) {
            int e = adj[c][i];
            int o = getOtherEndnode(e,c);
            if (o == avoid) 
                continue;
            if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                (getNodeVar(o).isFixed() && getNodeVar(o).isFalse()))
                continue;
            if (!visited[o]) 
                s.push(o);
        }
        
    }    
}

void BiConnectedPropagator::clearPropState() {
    fixed_nodes.clear();
    fixed_edges.clear();
    low_degree.clear();
    is_fixed_node = vector<bool>(nbNodes(),false);
    is_fixed_edge = vector<bool>(nbEdges(),false);
    GraphPropagator::clearPropState();
}

bool BiConnectedPropagator::checkFinalSatisfied() {
    //cout<<all_to_dot()<<endl;
    return true;
}


WeightedBiConnectedPropagator::WeightedBiConnectedPropagator(vec<BoolView>& _vs,
                                                             vec<BoolView>& _es,
                                                             vec< vec<int> >& _en,
                                                             vec< vec<int> >& _adj,
                                                             vec<int>& weights, 
                                                             IntVar* _w)
    : BiConnectedPropagator(_vs,_es,_en,_adj), w(_w), uf(nbNodes()),
      mandatory_weight(0) {
    
    for (int i = 0; i < weights.size(); i++) {
        ws.push_back(weights[i]);
    }
    
    w->attach(this, -1, EVENT_LU);
    
    added = std::vector<Tint>(nbEdges(), 0);

    was_sp = vector<Tint>(nbEdges(), 0);

    int lb = 0;
    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
            uf.isRoot(i)) {
            lb += dist_two_closest(i) / 2;
        }
    }
    if (w->setMinNotR(lb))
        w->setMin(lb);

}


void WeightedBiConnectedPropagator::wakeup(int i, int c) {
    if (i == -1) {
        pushInQueue();
    } else {
        BiConnectedPropagator::wakeup(i,c);
    }
}

bool WeightedBiConnectedPropagator::propagate() {
    if (!BiConnectedPropagator::propagate())
        return false;

    for (unsigned int i = 0; i < fixed_edges.size(); i++) {
        int e = fixed_edges[i];
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue() && !added[e]) {
            mandatory_weight += ws[e];
            added[e] = 1;
            uf.unite(getEndnode(e,0), getEndnode(e,1));
        }
    }
    int lb = mandatory_weight;
    if (in_nodes_tsize <= 1)
        return true;

    //int b2c = bounding_two_closest();
    int ham = hamiltonian_bound();
    //cout<< b2c<<" "<<ham<<endl;
    //int b2fe = bounding_two_for_each();
    //cout<< b2c<<" "<<b2fe<<endl;
    //assert(b2c <= b2fe);
    //assert(b2fe <= 576);
    lb += ham;//b2c;//b2fe;
    
    if (lb > w->getMax()) {
        if (so.lazy) {
            vec<Lit> ps; 
            string str = "";
            for (int i = 0; i < nbEdges(); i++) {
                if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
                    ps.push(getEdgeVar(i).getValLit());
                    str += "e_"+to_string(i)+" /\\ ";
                } else if (getEdgeVar(i).isFixed() && getEdgeVar(i).isFalse() && was_sp[i]) {
                    ps.push(getEdgeVar(i).getValLit());
                    str += "-e_"+to_string(i)+" /\\ ";
                }
            }
            assert(ps.size() >= 1);
            ps.push(w->getMaxLit());
            fullExpl(ps);
            Clause *expl = Clause_new(ps);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;

            //if (find_clevel(expl) <= 0)
            //    cout<<str<<" /\\ [[ w < "<<to_string(w->getMax())<<"]] ==> fail"<<endl;
            //assert(find_clevel(expl) > 0);
        }
        return false;
    }

    if (w->setMinNotR(lb)) {
        Clause* r = NULL;
        if (so.lazy) {
            vec<Lit> ps; ps.push(); 
            for (int i = 0; i < nbEdges(); i++) {
                if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
                    ps.push(getEdgeVar(i).getValLit());
                } else if (getEdgeVar(i).isFixed() && getEdgeVar(i).isFalse() && was_sp[i]) {
                    ps.push(getEdgeVar(i).getValLit());
                }
            }
            assert(ps.size() > 1);
            fullExpl(ps);
            ps.push(w->getMaxLit());
            r = Reason_new(ps);
        }
        w->setMin(lb, r);
    }

    return true;
}


int WeightedBiConnectedPropagator::hamiltonian_bound() {

    int nb_nodes = 0;
    int nb_edges = 0;
    vector< vector<int> > matrix(nbNodes(),vector<int>(nbNodes(),-1));
    vector< vector<int> > endnodes;
    vector< vector<int> > incident;
    vector< vector<int> > outgoing;
    vector<int> weights;
    std::unordered_map<int,int> mapping;

    int first = -1;
    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
            uf.isRoot(i)) {            
            if (first == -1) first = i;
            mapping[i] = nb_nodes;
            nb_nodes++;
            incident.push_back(vector<int>());
            outgoing.push_back(vector<int>());
        }
    }
    if (nb_nodes <= 1) return 0;

    if (nb_nodes > 10) {
        cout<<"nb_nodes == "<<nb_nodes<<endl;
        return bounding_two_for_each();
    }

    int last = nb_nodes;
    incident.push_back(vector<int>());
    outgoing.push_back(vector<int>());
    nb_nodes++;
    assert(nb_nodes <= 10);


    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
            uf.isRoot(i)) {

            int source = i;
            std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                                Dijkstra::Priority> q;
            vector<bool> visited = vector<bool>(nbNodes(), false);
            int count = 0;
            vector<int> cost = vector<int>(nbNodes(), -1);    
            vector<int> pred = vector<int>(nbNodes(), -1);    
            cost[source] = 0;
            pred[source] = source;
            q.push(Dijkstra::tuple(source,cost[source]));

            while (!q.empty() && count < nbNodes()) {                
                Dijkstra::tuple top = q.top(); q.pop();
                int curr = top.node;
                if (visited[curr]) continue;
                visited[curr] = true;
                count++; 
                if (curr != source &&
                    getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() &&
                    uf.isRoot(curr) && matrix[source][curr] == -1) {
                    matrix[source][curr] = cost[curr];

                    if(so.lazy) {
                        int x = curr;
                        while (pred[x] != x) {
                            was_sp[nodes2edge[pred[x]][x]] = 1;
                            x = pred[x];
                        }
                    }

                    int u = mapping[source];
                    int v = curr == first ? last : mapping[curr]; 

                    outgoing[u].push_back(nb_edges);
                    incident[v].push_back(nb_edges);
                    //cout<<"Edge from "<<u<<" to "<<v<<endl;
                    endnodes.push_back(vector<int>());
                    endnodes[nb_edges].push_back(u);
                    endnodes[nb_edges].push_back(v);
                    weights.push_back(cost[curr]);
                    nb_edges++;
                }
                
                for (unsigned int i = 0 ; i < adj[curr].size(); i++) {
                    int e = adj[curr][i];
                    int v = getOtherEndnode(e,curr); 
                    if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                        (getNodeVar(v).isFixed() && getNodeVar(v).isFalse()) ||
                        visited[v])
                        continue;
                    int w_e = ws[e];
                    if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
                        w_e = 0;
                    if (cost[v] == -1 || cost[v] > cost[curr] + w_e) {
                        cost[v] = cost[curr] + w_e;
                        pred[v] = curr;
                        q.push(Dijkstra::tuple(v, cost[v]));
                    }
                }
            }
        }
    }


    class DM : public DijkstraMandatory {
        vector<int> all;
    public:
        DM(int _s, int _d, vvi_t _en, vvi_t _in, vvi_t _ou,
           std::vector<int> _ws): DijkstraMandatory(_s,_d,_en,_in,_ou,_ws){
            all = std::vector<int>(_in.size());
            std::iota(all.begin(), all.end(), 0);
        }
        bool mandatory_node(int n) {return true;}
        std::vector<int>& mandatory_nodes() {return all;}
    } dm(0,last,endnodes,incident,outgoing,weights);

    dm.init();
    assert(nb_nodes == (int)outgoing.size());
    assert(nb_nodes == (int)incident.size());
    assert(nb_edges == (int)endnodes.size());
    int lb = dm.run();
    /*if (lb == -1) {
        cout<<"Outgoing"<<endl;
        for (int i = 0; i < outgoing.size(); i++) {
            cout<< i <<": ";
            for (int j = 0; j < outgoing[i].size(); j++)
                cout<<outgoing[i][j]<<" ";
            cout<<endl;
        }
        cout<<"Incident"<<endl;
        for (int i = 0; i < incident.size(); i++) {
            cout<< i <<": ";
            for (int j = 0; j < incident[i].size(); j++)
                cout<<incident[i][j]<<" ";
            cout<<endl;
        }
        for (int i = 0; i <endnodes.size(); i++) {
            assert(2 == endnodes[i].size());
            cout<<i<<": ("<<endnodes[i][0]<<","<<endnodes[i][1]<<")"<<endl; 
        }        
        exit(1);
        }*/

    return lb;
}

int WeightedBiConnectedPropagator::bounding_two_for_each() {
    vector<vector<int> > table(nbEdges(),vector<int>(nbNodes(),-1));
    typedef struct path{
        int from;
        int to; 
        int cost;
    } path;
    class path_priority {
    public:
        bool operator() (const path& lhs, const path&rhs) const {
            return lhs.cost > rhs.cost;
        }
    };
    std::priority_queue<path, std::vector<path>, path_priority> heap;
    std::priority_queue<path, std::vector<path>, path_priority> heap_shortest;

    vector<vector<int> > preds(nbNodes(), vector<int>(nbNodes(),-1));
    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
            uf.isRoot(i)) {

            int source = i;
            bool added_first_path = false;
            std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                                Dijkstra::Priority> q;

            vector<bool> visited = vector<bool>(nbNodes(), false);
            int count = 0;
            vector<int> cost = vector<int>(nbNodes(), -1);    
            cost[source] = 0;
            preds[source][source] = source;
            q.push(Dijkstra::tuple(source,cost[source]));
            while (!q.empty() && count < nbNodes()) {
                
                Dijkstra::tuple top = q.top(); q.pop();
                int curr = top.node;
                if (visited[curr]) continue;
                visited[curr] = true;
                count++;
                if (curr != source &&
                    getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() &&
                    uf.isRoot(curr) && table[source][curr] == -1) {
                    table[source][curr] = cost[curr];
                    //table[curr][source] = cost[curr]; //Exactly one time each path
                    if (!added_first_path) {
                        heap_shortest.push({source,curr,cost[curr]});
                        added_first_path = true;
                    } 
                    heap.push({source,curr,cost[curr]});
                }
                
                for (unsigned int i = 0 ; i < adj[curr].size(); i++) {
                    int e = adj[curr][i];
                    int v = getOtherEndnode(e,curr); 
                    if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                        (getNodeVar(v).isFixed() && getNodeVar(v).isFalse()) ||
                        visited[v])
                        continue;
                    int w_e = ws[e];
                    if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
                        w_e = 0;
                    if (cost[v] == -1 || cost[v] > cost[curr] + w_e) {
                        cost[v] = cost[curr] + w_e;
                        preds[source][v] = curr;
                        q.push(Dijkstra::tuple(v, cost[v]));
                    }             
                }
            }
        }
    }


    std::priority_queue<path, std::vector<path>, path_priority> heap2;
    heap2 = heap;
    int lb = 0;
    vector<vector<bool> > direct_link(nbNodes(),vector<bool>(nbNodes(), false));
    vector<int> path_counter(nbNodes(),0);
    vector<bool> contributed_one(nbNodes(),false);
    int paths = 0;

    //Pre-add shortest path from every node to some other node,
    //avoiding adding twice the same apth a--b and b--a.
    UF<int> avoid_cycle(nbNodes()); //While preadding shortest paths, avoid making a
    //cycle, or you might leave some node alone. If the LB is indeed a circuit, 
    //the last edge will be added by heap.
    while (!heap2.empty()) {
        int from = heap2.top().from;
        int to = heap2.top().to;
        int cost = heap2.top().cost;
        heap2.pop();
        //cout<<"Consider from "<<from<<" to "<<to<<endl;
        if (contributed_one[from]) continue;
        if (path_counter[from] == 2 || path_counter[to] == 2 ||
            direct_link[from][to] || avoid_cycle.connected(from,to))
            continue;
        //cout<<"Added from "<<from<<" to "<<to<<endl;
        contributed_one[from] = true;
        direct_link[from][to] = true;
        direct_link[to][from] = true;
        path_counter[from]++;
        path_counter[to]++;
        avoid_cycle.unite(from,to);
        lb += cost;
        paths++;
        if(so.lazy) {
            int x = to;
            while (preds[from][x] != x) {
                was_sp[nodes2edge[x][preds[from][x]]] = 1;
                x = preds[from][x];
            }
        }
    }

    while (!heap.empty()) { //TODO: stop adding when biconnected
        int from = heap.top().from;
        int to = heap.top().to;
        int cost = heap.top().cost;
        heap.pop();
        if (path_counter[from] >= 2 || //path_counter[to] == 2 || 
            direct_link[from][to])
            continue;
        //cout<<"Added* from "<<from<<" to "<<to<<endl;
        direct_link[from][to] = true;
        direct_link[to][from] = true;
        path_counter[from]++;
        path_counter[to]++;
        lb += cost;
        paths++;
        if(so.lazy) {
            int x = to;
            while (preds[from][x] != x) {
                was_sp[nodes2edge[x][preds[from][x]]] = 1;
                x = preds[from][x];
            }
        }
    }

    if (paths == 0) { 
        //All connected
        return lb;
    }

    if (paths == 1) {
        //This can only happen if there are only two roots.
        //In that case there is only one path in the heap, from
        //one to the other, but its safe to add it twice, so we 
        //multiply by two:
        lb *= 2;
    } else {
        for (int i = 0; i < 0*nbNodes(); i++) {
            if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() && uf.isRoot(i)) {
                if (path_counter[i] != 2) {
                    cout<<i<<" only has "<<path_counter[i]<<endl;
                    for (int i = 0; i < nbNodes(); i++) {
                        if (path_counter[i] > 0)
                            cout<<i<<"("<<path_counter[i]<<") ";
                    }
                    cout<<endl;
                    cout<<all_to_dot()<<endl;
                }
                assert(path_counter[i] == 2);
            }
        }
    }
    return lb;
}

int WeightedBiConnectedPropagator::bounding_two_closest() {
    int lb = 0;
    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
            uf.isRoot(i)) {
            lb += dist_two_closest(i) / 2;
        }
    }
    return lb;
}

int WeightedBiConnectedPropagator::dist_two_closest(int u) {
    

    vector<bool> visited = vector<bool>(nbNodes(), false);
    vector<int> pred = vector<int>(nbNodes(), -1);
    vector<int> cost = vector<int>(nbNodes(), -1);
    typedef Dijkstra::tuple tuple;
    std::priority_queue<tuple, std::vector<tuple>, Dijkstra::Priority> q;
    std::priority_queue<tuple, std::vector<tuple>, Dijkstra::Priority> empty;

    q.push(tuple(u,0));
    cost[u] = 0;
    pred[u] = u;
    int count = 0;
    

    int found_1 = -1;
    int cost_1 = 0;
    int found_2 = -1;
    int cost_2 = 0;
    

    while(!q.empty() && count < nbNodes() && found_1 == -1) {
        tuple top = q.top(); q.pop();
        int curr = top.node;
        visited[curr] = true;
        count++;
        


        if (getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() &&
            cost[curr] > 0) {
            //curr is a mand node that is in a different CC than u
            found_1 = curr;
            cost_1 = cost[curr];
            break;
        }
            

        for (unsigned int i = 0; i < adj[curr].size(); i++) {
            int e = adj[curr][i];
            int o = getOtherEndnode(e,curr);
            if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                (getNodeVar(o).isFixed() && getNodeVar(o).isFalse()) ||
                visited[o]) {
                continue;
            }
            int w_e = 0;
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
                w_e = 0;
            } else {
                w_e = ws[e];
            }

            assert(w_e >= 0);

            int new_cost = cost[curr] + w_e;
            if (cost[o] == -1 || cost[o] > new_cost) {
                cost[o] = new_cost;
                pred[o] = curr;
                tuple new_node(o, cost[o]);
                q.push(new_node);
            }             
            
        }
    }
    if (found_1 == -1)
        return 0;
    
    int x = found_1;
    while (pred[x] != x) {
        was_sp[nodes2edge[x][pred[x]]] = 1;
        x = pred[x];
    }
    q.swap(empty);

    visited = vector<bool>(nbNodes(), false);
    pred = vector<int>(nbNodes(), -1);
    cost = vector<int>(nbNodes(), -1);
    q.push(tuple(u,0));
    cost[u] = 0;
    pred[u] = u;
    count = 0;

    while(!q.empty() && count < nbNodes() && found_2 == -1) {
        tuple top = q.top(); q.pop();
        int curr = top.node;
        visited[curr] = true;
        count++;
        

        if (getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() &&
            cost[curr] > 0 && curr != found_1) {
            //curr is a mand node that is in a different CC than u
            found_2 = curr;
            cost_2 = cost[curr];
            break;
        }
            

        for (unsigned int i = 0; i < adj[curr].size(); i++) {
            int e = adj[curr][i];
            int o = getOtherEndnode(e,curr);
            if ((getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) ||
                (getNodeVar(o).isFixed() && getNodeVar(o).isFalse()) ||
                visited[o]) {
                continue;
            }

            int w_e = 0;
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
                w_e = 0;
            } else {
                w_e = ws[e];
            }

            int new_cost = cost[curr] + w_e;
            if (cost[o] == -1 || cost[o] > new_cost) {
                cost[o] = new_cost;
                pred[o] = curr;
                tuple new_node(o, cost[o]);
                q.push(new_node);
            }             
            
        }
    }

    if (found_1 != found_2 && found_2 != -1) {
        int x = found_2;
        while (pred[x] != x) {
            assert(nodes2edge[x][pred[x]] != -1);
            was_sp[nodes2edge[x][pred[x]]] = 1;
            x = pred[x];
        }
    }

    if (cost_2 < cost_1)
        cost_2 = cost_1;
    return cost_1 + cost_2;

}

bool WeightedBiConnectedPropagator::checkFinalSatisfied() {
    string res = "graph {\n";
    for (int n = 0; n < nbNodes(); n++) {
        if (getNodeVar(n).isFixed() && getNodeVar(n).isTrue())
            res += " " + to_string(n) + " [color = red];\n";
        if (getNodeVar(n).isFixed() && getNodeVar(n).isFalse())
            res += " " + to_string(n) + " [color = yellow];\n";
    }
    for (int e = 0; e < nbEdges(); e++) {
        res += " " + to_string(getTail(e)) + " -- " + to_string(getHead(e));
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) 
            res += " [color = red] ";
        else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) 
            res += " [color = yellow] ";
        res += "[label = \""+to_string(ws[e])+"\"]";
        res += ";\n";
    }
    res +="}";
    
    cout<<res<<endl;
    return true;
}

BiConnectedPropagator* wbiconnected(vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<int> >& _en, vec< vec<int> >& _adj,
                  vec<int>& ws, IntVar* w) {
    BiConnectedPropagator* bi = new WeightedBiConnectedPropagator(_vs,_es,_en,_adj,ws,w);

    if (so.check_prop)
        engine.propagators.push(bi);
    return bi;
}

BiConnectedPropagator* biconnected(vec<BoolView>& _vs, vec<BoolView>& _es, 
                 vec< vec<int> >& _en, vec< vec<int> >& _adj) {
    BiConnectedPropagator* bi = new BiConnectedPropagator(_vs,_es,_en,_adj);

    if (so.check_prop)
        engine.propagators.push(bi);
    cout<<"Biconnected propagator has ID: "<< bi->prop_id<<endl;
    return bi;
}
