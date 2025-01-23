#include "tsp_heldkarp_lagrangian.h"
#include "tsp_nosubtour.h"
#include "cycle_cost_simple.h"
#include "../support/LCA.c"

#include <bitset>
#include <unordered_map>
#include <limits>
#include <cmath>
#include <iomanip>
#include <sstream>

using namespace std;

std::vector<Clause*> TSPPropagator::my_clauses;
std::vector<int> TSPPropagator::my_clauses_origin;
//std::vector<int> TSPPropagator::sort_size_stat = std::vector<int>(100000,0);
//std::vector<int> TSPPropagator::kruskal_size_stat = std::vector<int>(100000,0);
TSPPropagator* TSPPropagator::propagator = NULL;

int expl_generated = 0;
int expl_used = 0;
int expl_size = 0;
int prop_calls = 0;
vector<Clause*> explanations;
Clause* TSPPropagator::explain(Lit p, int inf_id) {
    assert(false);
    exit(1);
    expl_used++;
    //cout<< expl_used<< " "<<expl_generated<<endl; 

    int edge_to_explain = -1; //Case of explaining why I forced some edge in.

    //lit_decay_expl_activity();
    //if (expl_builder[inf_id]->clause != NULL)
    //    return expl_builder[inf_id]->clause;

    //repair_backtrack();
    int idx = inf_id;
    if(inf_id % 2 == 1) {
        idx = inf_id - 1;
        assert(var2BoolView.find(var(p)) != var2BoolView.end());
        edge_to_explain = var2BoolView[var(p)];
    }

    

    // cout<<"1.When QUERYING inference "<<inf_id
    //     <<"("<< idx <<") we have "<<in_edges_tsize
    //     <<" mandatory edges and "<<unfixed_edges_tsize<<" unfixed ones "
    //     <<expl_builder.size()<<" "<<expl_builder_tsize<<endl; 


    double* pointer_hk = heldkarp_ws;
    heldkarp_ws = expl_builder[idx]->heldkarp;
    double* pointer_pe = penalties;
    penalties = expl_builder[idx]->multipliers;
    int* pointer_se = sorted_edges;
    sorted_edges = expl_builder[idx]->sorted_edges;
    int old_m1_one = mand1[0];
    mand1[0] = expl_builder[idx]->mand1_one;
    int old_m2_one = mand2[0];
    mand2[0] = expl_builder[idx]->mand2_one;

    int old_m = in_edges_tsize;
    int old_f = out_edges_tsize;
    int old_u = unfixed_edges_tsize;

    in_edges_tsize = expl_builder[idx]->mand_count;
    out_edges_tsize = expl_builder[idx]->forb_count;
    unfixed_edges_tsize = expl_builder[idx]->unf_count;

    assert(expl_builder[idx]->heldkarp != NULL); //I'm in the right index?


    // cout<<"1.When QUERYING inference "<<inf_id
    //     <<"("<< idx <<") we have "<<in_edges_tsize
    //     <<" mandatory edges, " << out_edges_tsize<<" forbidden and "<<unfixed_edges_tsize<<" unfixed ones "
    //     <<" "<<expl_builder_tsize<<endl; 



    for (int i = 0; i < in_edges_tsize; i++) {
        assert(getEdgeVar(in_edges[i]).isFixed());
        assert(getEdgeVar(in_edges[i]).isTrue());
    }
    for (int i = 0; i < out_edges_tsize; i++) {
        assert(getEdgeVar(out_edges[i]).isFixed());
        assert(getEdgeVar(out_edges[i]).isFalse());
    }
    for (int i = 0; i < unfixed_edges_tsize; i++) {
        //assert(!getEdgeVar(unfixed_edges[i]).isFixed());  //NOT TRUE
    }

    vec<Lit> ps; ps.push(p);
    
    std::pair<vector<int>, vector<int> > pair =
    explain(ps,
            expl_builder[idx]->tree_cost,
            expl_builder[idx]->subs,
            edge_to_explain);

    ps.push(obj->getMaxLit());

    if (inf_id % 2 == 0) { //Edge removal
        pair.first.push_back(var2BoolView[var(p)]);
        //double verified = verify_explanation(pair.first,pair.second, obj->getMax());
        //cout<<std::fixed<<verified<<" "<<obj->getMax()<<endl;
        //assert(verified > obj->getMax());
    } else { //Edge addition
        pair.second.push_back(var2BoolView[var(p)]);
        //double verified = verify_explanation(pair.first,pair.second, obj->getMax());
        //cout<<std::fixed<<verified<<" "<<obj->getMax()<<endl;
        //assert(verified > obj->getMax());
    }


    heldkarp_ws = pointer_hk;
    penalties = pointer_pe;
    sorted_edges = pointer_se;
    mand1[0] = old_m1_one;
    mand2[0] = old_m2_one;
    in_edges_tsize = old_m;
    out_edges_tsize = old_f;
    unfixed_edges_tsize = old_u;
    
    
    Clause* r = NULL; 
    r = Clause_new(ps,true);

    assert(r != NULL);

    sat.addClause(*r);

    expl_builder[inf_id]->clause = r;

    expl_size += ps.size();
    //return explanations[inf_id];
    return r;
}

bool TSPPropagator::propagate_upper_bound() {
    int sum = 0;
    vec<Lit> ps; ps.push();
    Clause* r = NULL;
    for (int n = 0; n < nbNodes(); n++) {
        int e1, e2;
        find_two_expensive(n,e1,e2,original_ws,ps);
        if (!check_two_edges(n,e1,e2)) {
            return false;
        }
        assert(e1 != -1 && e2 != -1);
        sum += original_ws[e1] + original_ws[e2];
    }
    sum /= 2;

    if(!obj->getMin() > sum) {
        //This can actually happen if the graph yat this point does not
        //actually contain a cycle. It can be biconnected and yet not contain a
        //cycle:
        //      /-------\
        //     A----B----C
        //    ||   ||    ||
        //    ||   ||    ||
        //    ||   ||    ||
        //    ||   ||    F---\   
        //    ||   ||     \   \
        //    ||    E======H  |
        //    ||          /   /
        //     D=========G----/ 
        // Where double lines mean mandatory and simple optional.
        // See Revision 1035, test eil101 (lazy=false) after 
        // sol 720 for an example
        //Since this very very rarelly happens, its better to just 
        // use the bicconected proapgator and not the circuit which is
        // more expensive and fail here.
        //cout<<available_to_dot()<<endl;
        //cout<<obj->getMin()<<" "<<sum<<endl;
        if (so.lazy) {
            vec<Lit> ps; fullExpl(ps); 
            Clause *expl = Clause_new(ps);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;                                
        }        
        return false;
    }

    if (obj->getMax() > sum && sum >= obj->getMin()) {
        //fullExpl(ps);
        if (so.lazy)
            r = Reason_new(ps);
        obj->setMax(sum,r);
    }
    return true;
}

string print_double(double d, int i = 15) {
    std::stringstream strstr;
    strstr << std::fixed << std::setprecision( i ) << d;
    std::string str = strstr.str();
    return str;
}
string print_raw_double_binary(double d)
{
    unsigned long long *double_as_int = (unsigned long long *)&d;
    int i;
    string s = "";
    bool some_one = false;
    for (i=0; i<=63; i++)
    {
        if ((*double_as_int >> (63-i)) & 1){
            s+="1"; some_one = true;
        } else
            s+="0";
    }
    if (s[0] =='0') s.erase(0,1);
    if (!some_one) s = "0";
    return s;
}

TSPPropagator::TSPPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                             vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
                             IntVar* _w, vec<int>& _ws)
    : GraphPropagator(_vs,_es,_en), 
      old_conflicts(0), old_dl(-1), first_run(true), wakeup_counter(0),
      wakeup_enabled(true), obj(_w),
      iters(5), sprints(30), edge_sorter(this), expl_builder_tsize(0),
      var_inc(1), lit_expl_activity(nbEdges()*2,0){
    TSPPropagator::propagator = this;
    //TSPPropagator::sort_size_stat = vector<int>(nbEdges(),0);
    //TSPPropagator::kruskal_size_stat = vector<int>(nbEdges(),0);



    priority = 5;

    removed_root_level = vector<bool>(nbEdges(), false);

    if(so.lazy) {
        for (int e = 0; e < nbEdges(); e++) {
            lit2int[toInt(getEdgeVar(e).getLit(true))] = e;
            lit2int[toInt(getEdgeVar(e).getLit(false))] = e+nbEdges();
        }
    }

    original_ws = new int[nbEdges()];
    heldkarp_ws = new double[nbEdges()];
    for (int i = 0; i < nbEdges(); i++) {
        original_ws[i] = _ws[i];
        heldkarp_ws[i] = _ws[i];
        getEdgeVar(i).attach(this, i, EVENT_LU);
        var2BoolView[getEdgeVar(i).v] = i;
    }
    for (int i = 0; i < nbNodes(); i++) 
        if (getNodeVar(i).setValNotR(true))
            getNodeVar(i).setVal(true); //TSP, all necessary

    nodes2edge = std::vector<std::vector<int> >(nbNodes());
    for (int i = 0; i < nbNodes(); i++) 
        nodes2edge[i] = std::vector<int>(nbNodes(),-1);    
    for (int e = 0; e < nbEdges(); e++) {
        nodes2edge[getEndnode(e,0)][getEndnode(e,1)] = e;
        nodes2edge[getEndnode(e,1)][getEndnode(e,0)] = e;
    }



    neigh_sizes = new Tint[nbNodes()];
    adj = vector<vector<int> >(_adj.size(), vector<int>());    
    adj_map = vector<vector<int> >(_adj.size(), vector<int>());    
    for (int i = 0; i < nbNodes(); i++)  {
        adj[i] = vector<int>(_adj[i].size(), -1);
        adj_map[i] = vector<int>(nbEdges(), -1);
        for (int j = 0; j < _adj[i].size(); j++)  {
            adj[i][j] = _adj[i][j];
            adj_map[i][_adj[i][j]] = j;
        }        
        neigh_sizes[i] = adj[i].size();
    }

    lagrangian_step = 0.0;
    lagrangian_step_zero = true;
    total_penalty = 0.0;
    penalties = new double[nbNodes()];
    std::memset(penalties,0.0,sizeof(double)*nbNodes());
    
    m1t_cost = 0;
    m1t_degrees = new int[nbNodes()];
    std::memset(m1t_degrees,0,sizeof(int)*nbNodes());

    in_edges_tsize = 0;
    in_edges_size = 0;
    out_edges_tsize = 0;
    out_edges_size = 0;
    last_state_e = vector<Tint>(nbEdges(),UNK);

    obj->attach(this,-1,EVENT_LU);

    mand1 = new Tint[nbNodes()]; std::memset(mand1,-1,sizeof(Tint)*nbNodes());
    mand2 = new Tint[nbNodes()]; std::memset(mand2,-1,sizeof(Tint)*nbNodes());


    //Count how many unfixed there are
    vector<bool> already(nbEdges(),false);
    int c1 = 0;
    for (int n = 0; n < nbNodes(); n++) {
        for (unsigned int i = 0; i < adj[n].size(); i++) {
            int e = adj[n][i];
            if (!getEdgeVar(e).isFixed() && !already[e]) {
                c1++; already[e] = true;
            } else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue() && !already[e]) {
                c1++;/*add_inedge(e);*/ already[e] = true;
            } else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse() && !already[e]) {
                c1++;/*on_edge_removal(e);*/ already[e] = true;
            }
        }
    }
    //Build arrays anf fill them
    unfixed_edges_tsize = c1;
    unfixed_edges_size = c1;
    unfixed_edges_map = new int[nbEdges()];
    unfixed_edges = new int[c1];
    sorted_edges = new int[c1];
    already = vector<bool>(nbEdges(),false);
    c1 = 0;
    for (int n = 0; n < nbNodes(); n++) {
        for (unsigned int i = 0; i < adj[n].size(); i++) {
            int e = adj[n][i];
            if (!getEdgeVar(e).isFixed() && !already[e]) {
                unfixed_edges[c1] = e; 
                unfixed_edges_map[e] = c1; 
                c1++;                
                already[e] = true;
            } else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue() && !already[e]) {
                unfixed_edges[c1] = e; 
                unfixed_edges_map[e] = c1;
                c1++;
                already[e] = true;
            } else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse() && !already[e]) {
                unfixed_edges[c1] = e; 
                unfixed_edges_map[e] = c1;
                c1++;
                already[e] = true;
            } 
        }
    }


    for (int e = 0; e < nbEdges(); e++) {
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
            add_inedge(e);
            update_mand_vectors(e);
        } else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse() && !already[e]) {
            on_edge_removal(e);
        } 
    }





    bool val = so.lazy;
    so.lazy = false;
    propagate_upper_bound();
    int lb;
    do {
        lb = obj->getMin();
        lagrangian_rel();
    } while (lb < obj->getMin());
    m1t_cost = obj->getMin();
    cout<<"Root level: The objective at this stage is ["<<obj->getMin()<<","<<obj->getMax()<<"] "<<endl;
    so.lazy = val;
    iters = 5;
    sprints = 30;

    cout<<"Edges left: "<<unfixed_edges_tsize<<" of "<<nbEdges()<< " originaly"<<endl;


    for (int i = 0; i < out_edges_size; i++) {
        removed_root_level[out_edges[i]] = true;
    }

    out_edges.clear();
    out_edges_size = 0;
    out_edges_tsize = 0;

    if(so.give_naive_explanations_HK)
        cout<<"Running TSPPropagator with naive explanations"<<endl;

    //TSPPropagator::sort_size_stat = vector<int>(nbEdges(),0);
    //TSPPropagator::kruskal_size_stat = vector<int>(nbEdges(),0);

    /*for (int i = 0; i < TSPPropagator::sort_size_stat.size(); i++) {
        TSPPropagator::sort_size_stat[i] = 0;
        TSPPropagator::kruskal_size_stat[i] = 0;
        }*/
    nb_runs_level = 0;

}

bool TSPPropagator::update_mand_vectors(int edge) {
    int u =  getEndnode(edge,0);
    int v =  getEndnode(edge,1);

    if (mand1[u] == -1) {
        mand1[u] = edge;
    } else if(mand2[u] == -1 && mand1[u] != edge) {
        mand2[u] = edge;
    }

    if (!(mand1[u] == edge || mand2[u] == edge))
        return false;

    if (mand1[v] == -1) {
        mand1[v] = edge;
    } else if(mand2[v] == -1 && mand1[v] != edge) {
        mand2[v] = edge;
    }

    if (!(mand1[v] == edge || mand2[v] == edge))
        return false;

    return true;
}

void TSPPropagator::repair_backtrack() {
    if (in_edges_tsize < in_edges_size) {
        //cout<<"Backtracked"<<endl;
        in_edges.resize(in_edges_tsize);
        in_edges_size = in_edges_tsize;
    }
    if (out_edges_tsize < out_edges_size) {
        //cout<<"Backtracked"<<endl;
        out_edges.resize(out_edges_tsize);
        out_edges_size = out_edges_tsize;
    }
    if (unfixed_edges_tsize > unfixed_edges_size) {
        //Backtracked
        for (int i = unfixed_edges_size; i < unfixed_edges_tsize; i++) {
            int e = unfixed_edges[i];
            heldkarp_ws[e] = original_ws[e] 
                + penalties[getEndnode(e,0)] 
                + penalties[getEndnode(e,1)];
        }        
        unfixed_edges_size = unfixed_edges_tsize;
        assert(unfixed_edges_size >= 0);
        assert(unfixed_edges_tsize >= 0);
    }

    //Not true anymore if you clean teh vectors after the root level
    //assert(in_edges.size() + out_edges_size == (nbEdges() - unfixed_edges_size));
}

bool TSPPropagator::add_inedge(int i) {
    if(last_state_e[i] != IN) {
        assert(last_state_e[i] == UNK);
        last_state_e[i] = IN;
        in_edges.push_back(i);
        in_edges_tsize++;
        in_edges_size++;    
        bool ok = update_mand_vectors(i);
        if(!ok && false) { // Never do this! It interrupts the HK and worsens the LB
            if(so.lazy) {
                int u = getEndnode(i,0);
                int v = getEndnode(i,1);
                if(mand1[u] != -1 && mand2[u] != -1) { //u already has 2 edges
                    vec<Lit> psf; 
                    psf.push(getEdgeVar(mand1[u]).getValLit());
                    psf.push(getEdgeVar(mand2[u]).getValLit());
                    psf.push(getEdgeVar(i).getValLit());
                    Clause *expl = Clause_new(psf);
                    expl->temp_expl = 1;
                    sat.rtrail.last().push(expl);
                    sat.confl = expl;                                
                }
                if(mand1[v] != -1 && mand2[v] != -1) { //u already has 2 edges
                    vec<Lit> psf; 
                    psf.push(getEdgeVar(mand1[v]).getValLit());
                    psf.push(getEdgeVar(mand2[v]).getValLit());
                    psf.push(getEdgeVar(i).getValLit());
                    Clause *expl = Clause_new(psf);
                    expl->temp_expl = 1;
                    sat.rtrail.last().push(expl);
                    sat.confl = expl;                                
                }
            }
            return false;
        }

        for (int j = 0; j < 2; j++) {
            int u = getEndnode(i,j);
            int pos = adj_map[u][i];
            int last = adj[u][neigh_sizes[u] - 1];
            adj[u][pos] = last; //the last edge goes wherever 'i' was
            adj_map[u][last] = pos;
            adj[u][neigh_sizes[u] - 1] = i; //removed edge goes at the back
            adj_map[u][i] = neigh_sizes[u] - 1;
            neigh_sizes[u]--;
        }

        int pos = unfixed_edges_map[i];
        int last = unfixed_edges[unfixed_edges_tsize - 1];
        unfixed_edges[pos] = last; //the last edge goes wherever 'i' was
        unfixed_edges_map[last] = pos;
        unfixed_edges[unfixed_edges_tsize - 1] = i; //removed edge goes at the back
        unfixed_edges_map[i] = unfixed_edges_tsize -1;
        unfixed_edges_tsize--;
        unfixed_edges_size--;
        assert(unfixed_edges_size >= 0);
        assert(unfixed_edges_tsize >= 0);

    }
    return true;
}


bool TSPPropagator::check_two_edges(int n, int e1, int e2) {
    if(e1 == -1 || e2 == -1) {
        vec<Lit> psf;
        if (so.lazy) {
            for (unsigned int i = neigh_sizes[n]; i < adj[n].size(); i++) {
                int e = adj[n][i];
                if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
                    psf.push(getEdgeVar(e).getValLit());
                }
            }
            //fullExpl(psf);
            Clause *expl = Clause_new(psf);
            //my_clauses.push_back(expl);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;                                
        }
        return false;
    }
    return true;
}



double TSPPropagator::fast_kruskal_1tree(int one) {
    //kruskal_size_stat[unfixed_edges_tsize]++;
    UF<int> uf(nbNodes());

    memset(m1t_degrees,0,sizeof(int)*nbNodes());
    double cost = 0;
    double* ws = heldkarp_ws;
    int counter = 0;
    kruskal_pre_add(one, counter, cost, uf);

    if (counter == nbNodes() - 2 && counter < nbNodes() - 2) { 

        add1node(one,cost);
        if (cost - floor(cost) < 0.001) 
            cost = floor(cost); //It could just be a floating point error
        return cost;
    }


    memcpy(sorted_edges,unfixed_edges,sizeof(int)*unfixed_edges_tsize);
    /*int pos = 0;
    for (int i = 0; i < nbNodes(); i++) {
        for (int j = 0; j < nbNodes(); j++){
            if (i < j && (!getEdgeVar(nodes2edge[i][j]).isFixed())) {
                sorted_edges[pos] = nodes2edge[i][j];
                pos++;
            }
        }
        }*/
    sort_edges(sorted_edges,unfixed_edges_tsize);
    //string debug ="";
    //Build MST
    int iter = 0;
    while (iter < unfixed_edges_tsize && counter < nbNodes() -2) {
        int e = sorted_edges[iter];

        if (touches(e,one) || 
            (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) ||
            (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse())) {
            iter++;
            continue;
        }

        bool connected = false;
        double w = ws[e];
        int u = getEndnode(e,0), v = getEndnode(e,1);
        assert(u!=v);        
        connected = uf.connected(u,v);
              
        if (!connected) {
            bool ok = uf.unite(u,v);
            assert(ok);
            counter++;
            cost += w;
            m1t_degrees[getEndnode(e,0)]++;
            m1t_degrees[getEndnode(e,1)]++;
            // debug += "Added edge "+to_string(getEndnode(e,0))+" "
            //    +to_string(getEndnode(e,1))+" cost "+print_raw_double_binary(w)+" "
            //    +print_raw_double_binary(cost)+"\n";
        }
        iter++;
    }


    assert(counter == nbNodes() - 2);
    
    //cout<<debug;
    //Close the cycle:
    add1node(one,cost);

    return cost;
}


int TSPPropagator::nb_calls_kkl1tree = 0;
int TSPPropagator::len_unk_on_call = 0;
bool TSPPropagator::kruskal_1tree(int one, bool filter) {
    //Build a one tree by avoiding all the time the node "one"
    //then adding the two cheapest edges touching "one"
    //cout<<"START"<<endl;
    //kruskal_size_stat[unfixed_edges_tsize]++;
    len_unk_on_call += unfixed_edges_tsize;
    nb_calls_kkl1tree++;
#ifndef NDEBUG
    //string debug = "";
#endif
    vec<Lit> expl_fail;

    memset(m1t_degrees,0,sizeof(int)*nbNodes());
    double* ws = heldkarp_ws;
    RerootedUnionFind<int> ruf(nbNodes());
    UF<int> uf(nbNodes());

    double cost = 0;
    int counter = 0;
    //Pre-add in_edges:

    vector<int> tree_edges;
    bool in_tree[nbEdges()];
    memset(in_tree, false, sizeof(bool)*nbEdges());

    kruskal_pre_add(one, counter, cost, uf, &ruf);
    /*{
        int* arr = new int[in_edges_tsize];
        for (int i = 0; i < in_edges_tsize; i++)
            arr[i] = in_edges[i];
        sort_edges(arr,in_edges_tsize);
        for (unsigned int i = 0; i < in_edges_tsize; i++) {
            int e = arr[i];
            assert(getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue());
            if (touches(e,one))
                continue;
            debug +="Pre-add "+ to_string(getEndnode(e,0))+" "
                +to_string(getEndnode(e,1))+" "
                +print_double(heldkarp_ws[e])+"\n";
            bool ok = uf.unite(getEndnode(e,0), getEndnode(e,1));
            assert(ok);
            ruf.unite(getEndnode(e,0), getEndnode(e,1));
            counter++;
            cost += heldkarp_ws[e];
            m1t_degrees[getEndnode(e,0)]++;
            m1t_degrees[getEndnode(e,1)]++;
        }
        delete[] arr;
    }//*/

    if (!filter && counter == nbNodes() - 2) {
        add1node(one,cost);
        m1t_cost = cost;
        double hkb = m1t_cost;
        if (hkb - floor(hkb) < 0.001) {
            hkb = floor(hkb); //It could just be a floating point error, so get close to the floor
        }        
        return too_heavy_mandatory(hkb);
    }

    //Always sort, because you need to sort in_edges as well...
    memcpy(sorted_edges,unfixed_edges,sizeof(int)*unfixed_edges_tsize);
    /*int pos = 0;
      for (int i = 0; i < nbNodes(); i++) {
      for (int j = 0; j < nbNodes(); j++){
      if (i < j && (!getEdgeVar(nodes2edge[i][j]).isFixed())){
      sorted_edges[pos] = nodes2edge[i][j];
      pos++;
      }
      }
            }*/
    //UNCOMMENT!
    for (int i = 0; i < in_edges_size; i++) 
        sorted_edges[unfixed_edges_tsize + i] = in_edges[i];
    sort_edges(sorted_edges,unfixed_edges_tsize+in_edges_size); //if lazy: sort all


    std::vector<int> support = vector<int>(nbEdges(),-1);
    std::vector<int> subs = vector<int>(nbEdges(),-1);

    int heaviest_edge = -1;

    //Build MST
    int iter = 0;
    while (iter < unfixed_edges_tsize + in_edges_size/*&& cost < obj->getMax()*/) {
        int e = sorted_edges[iter];
        if (touches(e,one) || 
            (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())) {
            iter++;
            continue;
        }
        assert(!(getEdgeVar(e).isFixed()));
        bool connected = false;
        double w = ws[e];
        int u = getEndnode(e,0), v = getEndnode(e,1);
        assert(u!=v);

#ifndef NDEBUG
        //debug +="Look at "+ to_string(getEndnode(e,0))+" "
        //        +to_string(getEndnode(e,1))+" "
        //        +print_double(heldkarp_ws[e])+" "+print_double(cost)+"\n";
#endif
        
        connected = uf.connected(u,v);
        
        if (connected){
            //Trying to connect nodes, but they are already connected
            vector<int> path;
            path = ruf.connectionsFromTo(u,v);
            assert(path.size() >= 2);
            int heaviest = -1;//nodes2edge[path[0]][path[1]];
            int heavy_mandatory = nodes2edge[path[0]][path[1]];

            for (int k = 0; k < path.size() - 1; k++){
                int e_path = nodes2edge[path[k]][path[k+1]];
                //heaviest is the heavies edge in the path that we have added 
                //before but only looking at the optional ones, because 
                //we can't remove the mandatory ones anyway.
                if(!getEdgeVar(e_path).isFixed()) //Skip mandatories
                    heaviest = (heaviest == -1)? 
                       e_path : (ws[e_path] > ws[heaviest] ? e_path : heaviest);
                heavy_mandatory = (ws[e_path] > ws[heavy_mandatory] ? e_path : heavy_mandatory);
                assert(e_path != e);
                subs[e_path] = (subs[e_path] == -1)? e : 
                    ((ws[subs[e_path]] > ws[e])? e : subs[e_path]);
            }
            support[e] = heaviest;
            if(support[e] == -1)
                support[e] = heavy_mandatory;
            
        }            
        
        if (counter < nbNodes() - 2 && !getEdgeVar(e).isFixed() && !connected) {
            bool ok = ruf.unite(u,v);
            assert(ok);
            uf.unite(u,v);
            counter++;
            cost += w;
            m1t_degrees[getEndnode(e,0)]++;
            m1t_degrees[getEndnode(e,1)]++;
            tree_edges.push_back(e);
            in_tree[e] = true;
#ifndef NDEBUG
            // debug +="Added edge "+ to_string(getEndnode(e,0))+" "
            //     +to_string(getEndnode(e,1))+" "
            //     +print_double(heldkarp_ws[e])+" "+print_double(cost)+"\n";
#endif
            // debug += "Added edge "+to_string(getEndnode(e,0))+" "
            //     +to_string(getEndnode(e,1))+" cost "+print_raw_double_binary(w)+" "
            //     +print_raw_double_binary(cost)+"\n";
            if(heaviest_edge == -1 || w > ws[heaviest_edge])
                heaviest_edge = e;
        }

        iter++;
    }
    

    assert(counter == nbNodes() - 2);
    //Close the cycle:
    int e1, e2;
    vec<Lit> dummy;
    add1node(one,cost,e1,e2, dummy);    
    m1t_cost = cost;
    if(!getEdgeVar(e1).isFixed() && (heaviest_edge == -1 || ws[e1] > ws[heaviest_edge]))
        heaviest_edge = e1;
    if(!getEdgeVar(e2).isFixed() && (heaviest_edge == -1 || ws[e2] > ws[heaviest_edge]))
        heaviest_edge = e2;
    in_tree[e1] = true;
    in_tree[e2] = true;
#ifndef NDEBUG
    // debug +="Post-added edge "+to_string(e1)+" "+to_string(getEndnode(e1,0))+" "
    //     +to_string(getEndnode(e1,1))+" "
    //     +print_double(heldkarp_ws[e1])+" "+print_double(cost)+"\n";
    // debug +="Post-added edge "+to_string(e2)+" "+to_string(getEndnode(e2,0))+" "
    //     +to_string(getEndnode(e2,1))+" "
    //     +print_double(heldkarp_ws[e2])+" "+print_double(cost)+"\n";
#endif
    //if (engine.decisionLevel() == 1)
    //    cout<<debug;

    double hkb = m1t_cost;
    if (hkb - floor(hkb) < 0.001) {
        hkb = floor(hkb); //It could just be a floating point error
    }

    std::pair<vector<int>, vector<int> > x_check;

    if (hkb > obj->getMax()) {
        if (so.lazy) {
            //cout<<"Explaining failure "<< print_double(hkb)<<" "<<print_double(m1t_cost)<<" "<< obj->getMax()<<" "<<print_raw_double_binary(hkb)<<endl;
            x_check =  explain(expl_fail,hkb,subs, -1 , true);
            expl_fail.push(obj->getMaxLit());
            if(so.lazy) {
                assert(verify_explanation(x_check.first,x_check.second, obj->getMax()) > obj->getMax());
            }
            Clause *expl = Clause_new(expl_fail);
            my_clauses.push_back(expl);
            my_clauses_origin.push_back(__LINE__);
            assert(expl != NULL);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;
        }
        return false;
    } else {
        /*//Backward explanation
        Reason reason = Reason(prop_id,expl_builder_tsize);
        // cout<<"When making inference "<<expl_builder_tsize<<" we had "<<
        //     in_edges_tsize<<" mandatory, "<< out_edges_tsize<<" forbidden and "
        //     <<unfixed_edges_tsize<<" unfixed"<<endl;
        expl_builder.push_back(new MemoizedExlanationElements(this,subs,(m1t_cost - 0.001)));
        expl_builder_tsize++;
        Reason reason2 = Reason(prop_id,expl_builder_tsize);
        // cout<<"When making inference "<<expl_builder_tsize<<" we had "<<
        //     in_edges_tsize<<" mandatory, "<< out_edges_tsize<<" forbidden and "
        //     <<unfixed_edges_tsize<<" unfixed"<<endl;
        expl_builder.push_back(new MemoizedExlanationElements());
        expl_builder_tsize++;
        //*/

        //*  //Forward explanation
        Clause* r = NULL;
        vec<Lit> ps;
        if (so.lazy) {
            ps.push();
            x_check = 
            explain(ps,(m1t_cost - 0.001),subs);
            ps.push(obj->getMaxLit());
            r = Reason_new(ps);
            //my_clauses.push_back(r);
        }//*/


        if (obj->setMinNotR(ceil(m1t_cost - 0.001))) {
            obj->setMin(ceil(m1t_cost - 0.001),r);
            if (so.lazy) {
                assert(ceil(verify_explanation(x_check.first,x_check.second, obj->getMax())) >= obj->getMin());
            }
        }

        if(filter) {
            double delta = obj->getMax()  - (m1t_cost - 0.001); //same as choco.
            vector<int> to_remove;
            int e_one_heavy = ws[e1] > ws[e2] ? e1 : e2;
            for (unsigned int i = 0; i < neigh_sizes[one]; i++) {
                int e = adj[one][i];
                if(e == e1 || e == e2) continue;
                if (ws[e] - ws[e_one_heavy] > delta) {
                    if(so.lazy) {
#ifndef NDEBUG                       
                        x_check.first.push_back(e);
                        double verified = verify_explanation(x_check.first,x_check.second, obj->getMax());
                        x_check.first.pop_back();
                        assert(verified > obj->getMax());
#endif                        
                    }
                    // cout<<"PRUNNING1 R "<< getEndnode(e,0)<<" "<<getEndnode(e,1)
                    //     <<" "<<getEndnode(e_one_heavy,1)<<" "<<print_double(ws[e_one_heavy])<<" "
                    //     <<" "<<getEndnode(e,1)<<" "<<print_double(ws[e])<<" "
                    //     <<" "<<print_double(obj->getMax()-m1t_cost)<<endl;
                    getEdgeVar(e).setVal(false,r);
                    to_remove.push_back(e);
                }
            }

            for (int i = 0; i < unfixed_edges_tsize; i++) {
                int e = unfixed_edges[i];
                int u = getEndnode(e,0), v = getEndnode(e,1);

                if (getEdgeVar(e).isFixed() || in_tree[e])
                    continue;
                
                // if ((getEndnode(e,0) == 30 && getEndnode(e,1) ==64) && support[e]>=0)
                //     cout<<">>PRUNNING2 R "<< getEndnode(e,0)<<" "<<getEndnode(e,1)
                //           <<" "<< ws[e]<<" "<<getEndnode(support[e],0)<<" "<<getEndnode(support[e],1)
                //         <<" "<<ws[support[e]]<<" "<<delta<<"    "<<getEdgeVar(support[e]).isFixed()<<endl;

                if (support[e] >= 0 && ws[e] - ws[support[e]] > delta) {
                    // if (getEndnode(e,0) == 51 && getEndnode(e,1) == 71)
                    // cout<<"PRUNNING2 R "<< getEndnode(e,0)<<" "<<getEndnode(e,1)
                    //     <<" "<< print_double(ws[e])<<" "<<getEndnode(support[e],0)<<" "<<getEndnode(support[e],1)
                    //     <<" "<<print_double(ws[support[e]])<<" "<<print_double(m1t_cost)<<" "<<obj->getMax()<<endl;
                    if(so.lazy) {
#ifndef NDEBUG                       
                        x_check.first.push_back(e);
                        double verified = verify_explanation(x_check.first,x_check.second, obj->getMax());
                        x_check.first.pop_back();
                        assert(verified > obj->getMax());
#endif
                    }
                    getEdgeVar(e).setVal(false,r);
                    to_remove.push_back(e);
                } else if (heaviest_edge >= 0 && ws[e] - ws[heaviest_edge] > delta) {
                    // This case only differs from the one above if 
                    // heaviest_edge == e1 || heaviest_edge == e2
                    // And it does make a difference!
                    if(so.lazy) {
#ifndef NDEBUG                       
                        x_check.first.push_back(e);
                        double verified = verify_explanation(x_check.first,x_check.second, obj->getMax());
                        x_check.first.pop_back();
                        assert(verified > obj->getMax());
#endif
                    }
                    getEdgeVar(e).setVal(false,r);
                    to_remove.push_back(e);                             
                    //if (getEndnode(e,0) == 42 || getEndnode(e,1) ==42)
                    // if (getEndnode(e,0) == 51 && getEndnode(e,1) == 71)      
                    //     cout<<"PRUNNING2 3 "<< getEndnode(e,0)<<" "<<getEndnode(e,1)<<endl;
                } 
            }

                        /*//Forward explanations
            if (so.lazy) {
                for (int i = 0; i < out_edges_tsize; i++)  {
                   ps.push(getEdgeVar(out_edges[i]).getValLit());
                   x_check.second.push_back(out_edges[i]);
                }
                r = Reason_new(ps);
                //my_clauses.push_back(r);
            }//*/


            for (int i = 0; i < to_remove.size(); i++) {
                on_edge_removal(to_remove[i]);
            }


            for (unsigned int i = 0; i < tree_edges.size(); i++) {
                int e = tree_edges[i];
                int u = getEndnode(e,0), v = getEndnode(e,1);
                //If substituting e with it's cheapest substitute is too expensive,
                //then e must be in the solution!
                if(subs[e] == -1) {                    
                    //This is bridge in the MST, but not necesserally in the 
                    //1tree, so you don't fail, you just force it in.
                        vec<Lit> ps; ps.push(); //fullExpl(ps);
                    if (so.lazy) {
                        int s = -1;
                        int d = v;
                        int a = u;
                        { //Find someone connected to u that is not v in the tree
                            if (mand1[u] != v && mand1[u] != -1) s = getOtherEndnode(mand1[u],u);  
                            if (s == -1) {
                                if (mand2[u] != v && mand2[u] != -1) s = getOtherEndnode(mand2[u],u); 
                                if (s == -1) {
                                    for (int i = 0; i < neigh_sizes[u]; i++) {
                                        if(in_tree[adj[u][i]] && getOtherEndnode(adj[u][i],u) != v) {
                                            s = getOtherEndnode(adj[u][i],u);
                                            break;
                                        }
                                    }   
                                }
                            }
                            if (s == -1) {
                                d = u;
                                a = v;
                                if (mand1[v] != u && mand1[v] != -1) s = getOtherEndnode(mand1[v],v);  
                                if (s == -1) {
                                    if (mand2[v] != u && mand2[v] != -1) s = getOtherEndnode(mand2[v],v); 
                                    if (s == -1) {
                                        for (int i = 0; i < neigh_sizes[v]; i++) {
                                            if(in_tree[adj[v][i]] && getOtherEndnode(adj[v][i],v) != u) {
                                                s = getOtherEndnode(adj[v][i],v);
                                                break;
                                            }
                                        }   
                                    }
                                }
                            }
                        }
                        if (s == -1) {fprintf(stderr,"Error, %s:%d\n",__FILE__,__LINE__); exit(1);}
                        bccp->explain_biconnected(s,d,a,ps);
                        //for (int i = 0; i < out_edges.size(); i++) 
                        //    ps.push(getEdgeVar(out_edges[i]).getValLit());
                    }
                    Clause* rtmp = NULL;
                    if (so.lazy) rtmp = Reason_new(ps);
                    //my_clauses.push_back(rtmp);
                    getEdgeVar(e).setVal(true,rtmp);
                    if(!add_inedge(e)) {
                        return false;
                    }
                }
                if (subs[e] != -1 && //subs[e] == -1 ||
                    (ws[subs[e]] - ws[e] > delta)) {
                    if(getEdgeVar(e).setValNotR(true)) {
                        if(so.lazy) {
#ifndef NDEBUG                       
                            x_check.second.push_back(e);
                            double verified = verify_explanation(x_check.first,x_check.second, obj->getMax());
                            x_check.second.pop_back();
                            assert(verified > obj->getMax());
#endif
                        }
                        getEdgeVar(e).setVal(true,r);
                        if(!add_inedge(e)) {
                            return false;
                        }
                        //if (getEndnode(e,0) == 51 && getEndnode(e,1) == 71)
                        // cout<<"PRUNNING E "<< getEndnode(e,0)<<" "<<getEndnode(e,1)
                        //     <<" "<< ws[e]<<" "<<getEndnode(subs[e],0)<<" "<<getEndnode(subs[e],1)
                        //     <<" "<<ws[subs[e]]<<" "<<obj->getMax()-m1t_cost<<endl;
                    }
                }
            }

        }

    }
    
    return true;

}

std::pair<std::vector<int>,std::vector<int> > 
TSPPropagator::explain(vec<Lit>& expl_fail, double c, 
                       std::vector<int>& substitute, 
                       int in_edge, bool verbose) {
    if (so.give_naive_explanations_HK)
        fullExpl(expl_fail);
#ifndef NDEBUG                       
    //string debug = "";
#endif
    /*static int calls = 0;
    cout<<"CALL "<<calls<<endl;
    debug+= "Start explanation: \n";
    debug +="graph {\n";
    for (int e = 0; e < nbEdges(); e++) {
        if (removed_root_level[e]) continue;
        debug += "  "+to_string(getEndnode(e,0))+" -- "+ to_string(getEndnode(e,1))+" ";
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse())
            debug += "[style = dotted] ";
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
            debug += "[style = bold, color = red] ";
        double w = original_ws[e] 
            + penalties[getEndnode(e,0)] 
            + penalties[getEndnode(e,1)];
        debug += "[label = \"("+to_string(getEndnode(e,0))+","+to_string(getEndnode(e,1))+"):"
            +to_string(original_ws[e])/*+print_double(w,5)+"\"]";
        debug += "\n";
    }
    debug += "}\n";*/



    vector<int> mexpl; //for verifications.
    vector<int> fexpl; //for verifications.
    //fullExpl(expl_fail);
    //return expl;
    int ccTreeNodeOf_in_edge = -1;

#ifndef NDEBUG                       
    RerootedUnionFind<int> ruf(nbNodes());
#endif

    UF<int> uf(nbNodes());
    vector<vector<int> > ccTree(2*nbNodes()+1, vector<int>());
    int ccTreeRoot = nbNodes() - 1; //Last node is the root
    int ccTreeNode2Edge[2*nbNodes()+1];
    int ccTreeParent[nbNodes()];
    std::bitset<300> ccTreeBitsets[2*nbNodes()+1];
    for (int i = 0; i < 2*nbNodes() - 1; i++) {
        ccTreeBitsets[i] = 0;
    }
    std::memset(ccTreeNode2Edge,-1, (2*nbNodes()+1)*sizeof(int));
    for (int i = 0; i < nbNodes(); i++) {
        ccTreeParent[i] = i;
        ccTreeBitsets[i][i] = 1;
    }


    std::vector<int> in_edges_cpy = in_edges;

            
    vector<bool> in_expl(nbEdges(),false);
    double cost = c; 
    double relaxed_cost = 0;
    int counter = 0;
    int m1_one = -1;
    int m2_one = -1;
#ifndef NDEBUG                       
    //debug += "Original cost is "+print_double(cost)+"\n";
#endif
    int seen = 0;
    int i = last_decision_position;
    bool forw = true;
    //while (seen < in_edges_tsize) {
    for (i = in_edges_tsize -1; i >= 0; i--) {//seen < in_edges_tsize) {
        int e = in_edges_cpy[i];
        seen++;
        if(touches(e,0)) continue;
        if (substitute[e] == -1) {
#ifndef NDEBUG                       
            //debug += "Edge "+to_string(getEndnode(e,0))+","+to_string(getEndnode(e,1)) +" has no substitue \n";
#endif
            continue;
        }
        if (cost - heldkarp_ws[e] + heldkarp_ws[substitute[e]] > obj->getMax()) {
#ifndef NDEBUG                       
            // debug+="No need to force "+to_string(e)+" "+to_string(getEndnode(e,0))+","+to_string(getEndnode(e,1))
            //     +" "+print_double(cost)+" "+print_double(heldkarp_ws[e])+"  "
            //     +" "+to_string(getEndnode(substitute[e],0))+","+to_string(getEndnode(substitute[e],1))+" "
            //     +print_double(heldkarp_ws[substitute[e]])+"\n";
#endif
            if(heldkarp_ws[e] > heldkarp_ws[substitute[e]]) {
               cost = cost - heldkarp_ws[e] + heldkarp_ws[substitute[e]];
#ifndef NDEBUG                       
               //debug+="Relaxed cost to "+print_double(cost)+" "+to_string(substitute[e])+"\n";
#endif
            }
        } else {
            expl_fail.push(getEdgeVar(e).getValLit());
#ifndef NDEBUG                       
            mexpl.push_back(e);
#endif
            //lit_bump_expl_activity(getEdgeVar(e).getValLit());
            assert(!in_expl[e]);
            in_expl[e] = true;           
        }
        // if (forw)
        //     i++;
        // else
        //     i--;
        // if (i >= in_edges_tsize){
        //     i = last_decision_position -1;
        //     forw = false;
        // }
    }


    sort(in_edges_cpy.begin(), in_edges_cpy.begin()+in_edges_tsize, edge_sorter);

    for (unsigned int i = 0; i < in_edges_tsize; i++) {
        int e = in_edges_cpy[i];
        if(in_expl[e]) {  //Building new MST
                relaxed_cost += heldkarp_ws[e];
                counter++;
                int ru = uf.find(getEndnode(e,0)), rv = uf.find(getEndnode(e,1));
                bool ok = uf.unite(ru,rv); assert(ok);
#ifndef NDEBUG                       
                ruf.unite(getEndnode(e,0),getEndnode(e,1));
#endif
                ccTreeRoot++;
                ccTree[ccTreeRoot].push_back(ccTreeParent[ru]);
                ccTree[ccTreeRoot].push_back(ccTreeParent[rv]);
                ccTreeBitsets[ccTreeRoot] = ccTreeBitsets[ccTreeParent[ru]] | ccTreeBitsets[ccTreeParent[rv]];
                ccTreeParent[ru] = ccTreeRoot;
                ccTreeParent[rv] = ccTreeRoot;
                ccTreeNode2Edge[ccTreeRoot] = e;
                if(e == in_edge) ccTreeNodeOf_in_edge = ccTreeRoot;
#ifndef NDEBUG                       
                // debug +="EXPLAIN: Pre-added edge "+ to_string(getEndnode(e,0))+" "
                //     +to_string(getEndnode(e,1))+" "
                //     +print_double(heldkarp_ws[e])+" "+print_double(relaxed_cost)
                //     +" "+to_string(getEndnode(substitute[e],0))+","+to_string(getEndnode(substitute[e],1))+" "
                //     +print_double(heldkarp_ws[substitute[e]])+"\n";
#endif
            }
      }

    int iter = 0;
    while (iter < unfixed_edges_tsize + in_edges_tsize ) {
        int e = sorted_edges[iter];
        if (touches(e,0)) {
            iter++;
            continue;
        }
        int u = getEndnode(e,0), v = getEndnode(e,1);
        assert(u!=v);                      
        if (!uf.connected(u,v)) {
            counter++;
            relaxed_cost += heldkarp_ws[e];
#ifndef NDEBUG                       
            ruf.unite(getEndnode(e,0),getEndnode(e,1));
#endif
            int ru = uf.find(getEndnode(e,0)), rv = uf.find(getEndnode(e,1));
            bool ok = uf.unite(ru,rv); assert(ok);
            ccTreeRoot++;
            ccTree[ccTreeRoot].push_back(ccTreeParent[ru]);
            ccTree[ccTreeRoot].push_back(ccTreeParent[rv]);
            ccTreeBitsets[ccTreeRoot] = ccTreeBitsets[ccTreeParent[ru]] | ccTreeBitsets[ccTreeParent[rv]];
            ccTreeParent[ru] = ccTreeRoot;
            ccTreeParent[rv] = ccTreeRoot;
            ccTreeNode2Edge[ccTreeRoot] = e;
            if(e == in_edge) ccTreeNodeOf_in_edge = ccTreeRoot;
#ifndef NDEBUG                       
            // debug +="EXPLAIN: Added edge "+ to_string(getEndnode(e,0))+" "
            //     +to_string(getEndnode(e,1))+" "
            //     +print_double(heldkarp_ws[e])+" "+print_double(relaxed_cost)+"\n";
#endif
        }
        iter++;
    }


    assert(counter == nbNodes() - 2);    

#ifndef NDEBUG                       
    //debug += "EXPLAIN: Relaxed cost before 1tree "+print_double(relaxed_cost)+"\n";
#endif
    //Closing the cycle
    m1_one = mand1[0] == -1 ? mand2[0] : mand1[0];
    m2_one = m1_one == -1 ? -1 : (int)(m1_one == mand1[0] ? (int)mand2[0] : -1);
    bool m1 = (m1_one != -1);
    if (m1_one != -1) {
        expl_fail.push(getEdgeVar(m1_one).getValLit());
        //lit_bump_expl_activity(getEdgeVar(m1_one).getValLit());
#ifndef NDEBUG                       
        mexpl.push_back(m1_one);
#endif
    }
    if (m2_one != -1) {
        expl_fail.push(getEdgeVar(m2_one).getValLit());
        //lit_bump_expl_activity(getEdgeVar(m2_one).getValLit());
#ifndef NDEBUG                       
        mexpl.push_back(m2_one);
#endif
    }
    if (m1_one == -1 || m2_one == -1) {
        std::vector<int> tmp;
        for (unsigned int i = 0; i < adj[0].size(); i++) {
            int e = adj[0][i];
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
                if (so.lazy) 
                    tmp.push_back(e);
            } else {
                if (!m1 && (m1_one == -1 || heldkarp_ws[e] < heldkarp_ws[m1_one])) {
                    m2_one = m1_one;
                    m1_one = e;
                } else if (e != m1_one && (m2_one == -1 || heldkarp_ws[e] < heldkarp_ws[m2_one])) {
                    m2_one = e;
                }
            }
        }
        assert(m1_one != -1 && m2_one != -1 && m1_one != m2_one);
        for (unsigned int i = 0; i < tmp.size(); i++) {
            double w_i = original_ws[tmp[i]]  //May be forbidden, so recompute to make sure
                + penalties[getEndnode(tmp[i],0)] 
                + penalties[getEndnode(tmp[i],1)];
            if (w_i < heldkarp_ws[m2_one]) {
                expl_fail.push(getEdgeVar(tmp[i]).getValLit());
                //lit_bump_expl_activity(getEdgeVar(tmp[i]).getValLit());
#ifndef NDEBUG                       
                fexpl.push_back(tmp[i]);
#endif
            }
        }
    }
    assert(m1_one != -1 && m2_one != -1 && m1_one != m2_one);
#ifndef NDEBUG                       
    // debug += "Using "+ to_string(m1_one)+"  "+to_string(getEdgeVar(m1_one).isTrue())
    //     +to_string(getEdgeVar(m1_one).isFalse())+"\n";
    // debug += "Using "+to_string(m2_one)+"  "+to_string(getEdgeVar(m2_one).isTrue())
    //     +to_string(getEdgeVar(m2_one).isFalse())+"\n";
#endif
    relaxed_cost += heldkarp_ws[m1_one] + heldkarp_ws[m2_one]; 
    cost = relaxed_cost;
#ifndef NDEBUG                       
    //debug+= "EXPLAIN: Relaxed cost after 1tree "+print_double(relaxed_cost)+"\n";
#endif
    LCAGraphManager lca(2*nbNodes()+1);
    lca.preprocess(ccTreeRoot, ccTree, ccTreeRoot); 


    //std::vector<int> out_edges_cpy = out_edges;
    //sort(out_edges_cpy.begin(), out_edges_cpy.begin()+out_edges_tsize, edge_sorter);


    for (unsigned int i = 0; i < out_edges_tsize; i++) {
        int support_e = -1;
        int e = out_edges[i];
        //expl_fail.push(getEdgeVar(e).getValLit());
        //fexpl.push_back(e);


        if (touches(e,0)) continue;


        int u = getEndnode(e,0), v = getEndnode(e,1);
        support_e = ccTreeNode2Edge[lca.getLCA(u,v)];

        //Find the support of e:
#ifndef NDEBUG     

        vector<int> path;
        path = ruf.connectionsFromTo(u,v);
        assert(path.size() >= 2);
        int arg_max = -1;
        for (int k = 0; k < path.size() - 1; k++){
            int e_path = nodes2edge[path[k]][path[k+1]];
            if (!in_expl[e_path] && 
                (arg_max == -1 || heldkarp_ws[e_path] > heldkarp_ws[arg_max])) {
                arg_max = e_path;
            }
        }
        assert(arg_max == -1 || heldkarp_ws[arg_max] == heldkarp_ws[support_e]);
#endif


        assert(support_e >= 0);


	if(in_expl[support_e]) continue;



        double w = original_ws[e] 
            + penalties[getEndnode(e,0)] 
            + penalties[getEndnode(e,1)];

        if (cost + w - heldkarp_ws[support_e] > obj->getMax()) {
#ifndef NDEBUG                       
            // debug+=" I can allowF "+to_string(e)+" ("+to_string(getEndnode(e,0))+","
            //     +to_string(getEndnode(e,1))+") since "
            //     +print_double(cost) +"+"+ print_double(w) +"-"+ print_double(heldkarp_ws[support_e])
            //     +" = "+ print_double(cost + w - heldkarp_ws[support_e]) 
            //     +" > "+to_string(obj->getMax())+"\n";
#endif
            if (w < heldkarp_ws[support_e]) {
                cost = cost + w - heldkarp_ws[support_e];
#ifndef NDEBUG                       
                //debug += "The cost is now "+print_double(cost)+"\n";
#endif
            }
            if(in_edge >= 0) {
                assert(ccTreeNodeOf_in_edge >= 0);
                int x = ccTreeNodeOf_in_edge;
                if((ccTreeBitsets[x][u] ^ ccTreeBitsets[x][v]) &&
                   c + w - heldkarp_ws[in_edge] <=  obj->getMax()) { 
                    //We know in_edge had asubstite, that's how we propagated it
                    //and it turns out that e would have been a better substitute
                    expl_fail.push(getEdgeVar(e).getValLit());
                    //lit_bump_expl_activity(getEdgeVar(e).getValLit());
#ifndef NDEBUG                       
                    fexpl.push_back(e);
#endif
                }        
            }

        } else {
#ifndef NDEBUG                       
            // debug+=" I cannot allowF "+to_string(e)+" ("+to_string(getEndnode(e,0))+","
            //     +to_string(getEndnode(e,1))+") since "
            //     +print_double(cost) +"+"+ print_double(w) +"-"+ print_double(heldkarp_ws[support_e])
            //     +" = "+ print_double(cost + w - heldkarp_ws[support_e]) 
            //     +" <= "+to_string(obj->getMax())+"\n";
#endif
            expl_fail.push(getEdgeVar(e).getValLit());
            //lit_bump_expl_activity(getEdgeVar(e).getValLit());
#ifndef NDEBUG                       
            fexpl.push_back(e);
#endif
        }
    }
#ifndef NDEBUG                       
                    //debug+="EXPLAIN: Relaxed cost at the end "+print_double(cost)+"\n";
    if(verbose) {
        //cout<<debug;
    }
#endif

    return make_pair(mexpl,fexpl);
}


double TSPPropagator::verify_explanation(vector<int>& medges, vector<int>& fedges,
                                         int bound, int edge, bool use_it) {

    double cost = 0;
    int counter = 0;
    int iter = 0;
    UF<int> uf(nbNodes());
    
    //string debug = "";

    vector<bool> used(nbEdges(),false);
    vector<bool> is_m(nbEdges(),false);
    vector<bool> is_f(nbEdges(),false);

    double hk[nbEdges()];
    for (unsigned int i = 0; i < nbEdges(); i++) {
        hk[i] = original_ws[i] + penalties[getEndnode(i,0)] + penalties[getEndnode(i,1)];
    }
    double* old_hk = heldkarp_ws;
    heldkarp_ws = hk;

    for (int i = 0; i < medges.size(); i++) {
        int e = medges[i];
        is_m[e] = true;
        if( touches(e,0)) continue;
        if(!used[e]) {
            uf.unite(getEndnode(e,0), getEndnode(e,1));
            counter++;
            cost += heldkarp_ws[e];
            used[e] = true;
            // debug +="VERIFY: Pre-dded edge "+ to_string(getEndnode(e,0))+" "
            //     +to_string(getEndnode(e,1))+" "
            //     +print_double(heldkarp_ws[e])+"\n";
        }
    }

    if (edge >= 0) {
        if(use_it) {
            is_m[edge] = true;
            if(!used[edge] && !touches(edge,0)) {
                uf.unite(getEndnode(edge,0), getEndnode(edge,1));
                counter++;
                cost += heldkarp_ws[edge];
                used[edge] = true;
            }
        } else {
            is_f[edge] = true;
            used[edge] = true;
        }
    }

    for (int i = 0; i < fedges.size(); i++) {        
        int e = fedges[i];
        is_f[e] = true;
        used[e] = true; //Act as if!
    }

    int arr[nbEdges()];
    for (int i = 0; i < nbEdges(); i++)
        arr[i] = i;
    sort_edges(arr,nbEdges()); //Just all edges!
    for (int i = 0; i < nbEdges() -1; i++) {
        assert(heldkarp_ws[arr[i]] <= heldkarp_ws[arr[i+1]]);
    }

    iter = 0;
    while (counter < nbNodes() - 2 && iter < nbEdges()) {
        int e = arr[iter];       
        if(touches(e,0) || used[e] || is_f[e] || removed_root_level[e]) {
            iter++;
            continue;
        }
        int u = getEndnode(e,0), v = getEndnode(e,1);
        if(!uf.connected(u,v)) {
            uf.unite(u,v);
            counter++;
            cost += heldkarp_ws[e];
            // debug +="VERIFY: Added edge "+ to_string(getEndnode(e,0))+" "
            //     +to_string(getEndnode(e,1))+" "
            //     +print_double(heldkarp_ws[e])+" "+to_string(getEdgeVar(e).isFalse())+"\n";
        }
        iter++;
    }

    //debug+= "VERIFY: Before adding 1tree "+ print_double(cost)+"\n";

    if(iter == nbEdges() && counter < nbNodes() -2) {
        //debug += "/////\\\\\\ Could not finish building the tree \n";       
    }

    int added = 0;
    for (int i = 0; i < adj[0].size(); i++) {
        int e = adj[0][i];
        if (is_m[e]) {
            //debug += "1Using "+ to_string(e)+"  "+to_string(is_m[e])+to_string(is_f[e])+"\n";
            cost += heldkarp_ws[e];
            added += 1;
            used[e] = true;
        }
    }


    if (added < 2) {
        int argmin = -1;
        for (int i = 0; i < adj[0].size(); i++) {
            int e = adj[0][i];
            if (is_f[e] || used[e]) continue;
            if (argmin == -1 ) {
                argmin = e;
            } else {
                if (heldkarp_ws[e] < heldkarp_ws[argmin])
                    argmin = e;
            }
        }   
        //debug += "2Using "+ to_string(argmin)+"  "+to_string(is_m[argmin])+to_string(is_f[argmin])+"\n";
        cost += heldkarp_ws[argmin];
        added += 1;
        used[argmin] = true;
    }
    if (added < 2) {
        int argmin = -1;
        for (int i = 0; i < adj[0].size(); i++) {
            int e = adj[0][i];
            if (is_f[e] || used[e]) continue;
            if (argmin == -1 ) {
                argmin = e;
            } else {
                if (heldkarp_ws[e] < heldkarp_ws[argmin])
                    argmin = e;
            }
        }   
        //debug += "3Using "+ to_string(argmin)+"  "+to_string(is_m[argmin])+to_string(is_f[argmin])+"\n";
        cost += heldkarp_ws[argmin];
        added += 1;
        used[argmin] = true;
    }
    assert(added == 2);

    //debug+= "VERIFY: Final cost "+ print_double(cost)+"\n";

    //cout<<debug;

    heldkarp_ws = old_hk;

    return cost;// + obj->getMax()*(iter == nbEdges() && counter < nbNodes() -2);
}

int runs = 0;
int TSPPropagator::nb_calls_lagrel = 0;
bool TSPPropagator::lagrangian_rel() {
    nb_calls_lagrel++;
    double hkb;
    double alpha = 2;
    double beta = 0.5;

    double old_m1t_cost = m1t_cost;
    if(!kruskal_1tree(0,true)) {
        //cout<< "Failed"<<__LINE__<<endl;
        return false;
    }

    if (engine.conflicts == old_conflicts && 
        //engine.decisionLevel() == old_dl &&
        m1t_cost == old_m1t_cost)  { //same MST at the same level, won't prune anything
        return true;
    }
    old_conflicts = engine.conflicts;
    old_dl = engine.decisionLevel();
    

    //cout<<"m1t_cost 1: "<<print_raw_double_binary(m1t_cost)<<endl;
    
    // for (int i = 0; i < nbNodes(); i++)
    //     cout<<std::fixed<<penalties[i]<<"P ";
    // cout<<endl;
    // for (int i = 0; i < nbEdges(); i++)
    //     cout<<heldkarp_ws[i]<<"E ";
    // cout<<endl;

    hkb = m1t_cost - total_penalty;
  
    if (hkb - floor(hkb) < 0.001) {
        hkb = floor(hkb);
    }
    //obj.updateLowerBound((int) Math.ceil(hkb), this);
    //HKfilter.performPruning((double) (obj.getUB()) + totalPenalities + 0.001);
    //double before = wallClockTime();
    for (int iter = iters; iter > 0; iter--) {
        double avg = 0;
        for (int i = sprints; i > 0; i--) {
            double new_lb = fast_kruskal_1tree(0);
            //avg += (wallClockTime() -before);
            double hkb = new_lb;
            if (hkb - floor(hkb) < 0.001) {
                hkb = floor(hkb);
            }
            if (hkb > obj->getMax()) {
                //Need to fail.
                bool ok = kruskal_1tree(0,false);
                if(ok) {
                    cout<<new_lb <<" "<<m1t_cost<<" "<<obj->getMax()<<endl;
                }
                assert(!ok);
                //cout<< "Failed"<<__LINE__<<endl;
                return false;
            }
            //cout<<" m1t_cost 2: "<<print_raw_double_binary(new_lb)<<endl;
            //cout<<" m1t_cost 2: "<<std::fixed<<new_lb<<" "<<print_raw_double_binary(new_lb)<<endl;
            // for (int i = 0; i < nbNodes(); i++)
            //     cout<<penalties[i]<<"P ";
            // cout<<endl;
            
            // for (int i = 0; i < nbEdges(); i++)
            //     cout<<heldkarp_ws[i]<<"E ";
            // cout<<endl;
            hkb = new_lb - total_penalty;
            if (hkb - floor(hkb) < 0.001) {
                hkb = floor(hkb);
            }
            //obj.updateLowerBound((int) Math.ceil(hkb), this);
            // HK.performPruning((double) (obj.getUB()) + totalPenalities + 0.001);
            //	DO NOT FILTER HERE TO SPEED UP CONVERGENCE (not always true)
            update_step(hkb, alpha);
            update_penalties();
            update_weights();
        }
        //cout<<"     after"<<(avg)*1000<<endl;
        if(!kruskal_1tree(0,true)) {
            //cout<< "Failed"<<__LINE__<<endl;
            return false;
        }
        hkb = m1t_cost - total_penalty;
        if (hkb - floor(hkb) < 0.001) {
            hkb = floor(hkb);
        }
        update_step(hkb, alpha);
        update_penalties();
        update_weights();
        //cout<<"m1t_cost 3: "<<print_raw_double_binary(m1t_cost)<<endl;
        // for (int i = 0; i < nbNodes(); i++)
        //    cout<<penalties[i]<<std::fixed<<"P ";
        // cout<<endl;
        // for (int i = 0; i < nbEdges(); i++)
        //     cout<<heldkarp_ws[i]<<"E ";
        // cout<<endl;
        alpha *= beta;
        beta /= 2;
    }

    return true;
}

void TSPPropagator::update_step(double hkb, double alpha) {
    double nb2viol = 0;
    double target = obj->getMax();
    if (target - hkb < 0) {
        target = hkb + 0.1;
    }
    int deg;
    for (int i = 0; i < nbNodes(); i++) {
        deg = m1t_degrees[i];
        nb2viol += (2 - deg) * (2 - deg);
    }
    if (nb2viol == 0) {
        lagrangian_step = 0;
        lagrangian_step_zero = true;
    } else {
        //cout<<"T"<<print_raw_double_binary(target)<<endl;
        //cout<<"H"<<print_raw_double_binary(hkb)<<endl;
        //cout<<"A"<<print_raw_double_binary(alpha)<<endl;
        lagrangian_step = alpha * (target - hkb) / nb2viol;
        lagrangian_step_zero = false;
    }
    
}

void TSPPropagator::update_penalties() {
    if (lagrangian_step_zero) { 
        return;
    }
    double sum = 0.0;
    int deg;
    for (int i = 0; i < nbNodes(); i++) {
        deg = m1t_degrees[i];
        penalties[i] += (deg - 2) * lagrangian_step;
        assert(penalties[i] < std::numeric_limits<double>::max() / (nbNodes() - 1));
        assert(penalties[i] > -std::numeric_limits<double>::max() / (nbNodes() - 1));
        sum += penalties[i];
    }
    total_penalty = 2 * sum;
    assert(abs(total_penalty) < 0.000001); //Trying to figure out what total_penalty really is...
}

void TSPPropagator::update_weights() {
    //Normal case, update all the intereseting ones
    for (unsigned int i = 0; i < in_edges_tsize; i++) {
        int e = in_edges[i];
        heldkarp_ws[e] = original_ws[e] 
            + penalties[getEndnode(e,0)] 
            + penalties[getEndnode(e,1)];
    }
    for (int i = 0; i < unfixed_edges_tsize; i++) {
        int e = unfixed_edges[i];
        heldkarp_ws[e] = original_ws[e] 
            + penalties[getEndnode(e,0)] 
            + penalties[getEndnode(e,1)];
    }
}


void TSPPropagator::on_edge_removal(int i) {
    last_state_e[i] = OUT;
    for (int j = 0; j < 2; j++) {
        int u = getEndnode(i,j);
        int pos = adj_map[u][i];
        int last = adj[u][neigh_sizes[u] - 1];
        adj[u][pos] = last; //the last edge goes wherever 'i' was
        adj_map[u][last] = pos;
        adj[u][neigh_sizes[u] - 1] = i; //removed edge goes at the back
        adj_map[u][i] = neigh_sizes[u] - 1;
        neigh_sizes[u]--;
    }
    out_edges.push_back(i);
    out_edges_tsize++;
    out_edges_size++;    

    int pos = unfixed_edges_map[i];
    int last = unfixed_edges[unfixed_edges_tsize - 1];
    unfixed_edges[pos] = last; //the last edge goes wherever 'i' was
    unfixed_edges_map[last] = pos;
    unfixed_edges[unfixed_edges_tsize - 1] = i; //removed edge goes at the back
    unfixed_edges_map[i] = unfixed_edges_tsize -1;
    unfixed_edges_tsize--;
    unfixed_edges_size--;
    assert(unfixed_edges_size >= 0);
    assert(unfixed_edges_tsize >= 0);
}

void TSPPropagator::wakeup(int i, int c) {
    repair_backtrack();

    if (engine.conflicts != old_conflicts) {
        last_decision_position = in_edges_size;
    }

    double hkb = m1t_cost;
    if (hkb - floor(hkb) < 0.001) {
        hkb = floor(hkb); //It could just be a floating point error, so get close to the floor
    }

    bool push = false;
    
    if (i == -1 && (int)m1t_cost != obj->getMin()/*&& abs(ceil(hkb)-(double)obj->getMin()) > 0.000001*/) {
        //cout<<"woke me up because of the bound. I was at "<< m1t_cost<<" now the bound is "<<obj->getMin()<<endl;
        push = true;
    } else if (i >= 0 && i < nbEdges()){        
        if (getEdgeVar(i).isTrue() && last_state_e[i] != IN) {
            //cout<<" Added edge "<<i<<" "<<getEndnode(i,0)<<" "<<getEndnode(i,1)<<" "<<original_ws[i]<<endl;
            add_inedge(i);
            push = true;
        } else if (getEdgeVar(i).isFalse() && last_state_e[i] != OUT) {
            //cout<<" Removed edge "<<i<<" "<<getEndnode(i,0)<<" "<<getEndnode(i,1)<<endl;
            on_edge_removal(i);
            push = true;
        }
    }
    if (push) wakeup_counter++;
    if (push && (first_run || wakeup_counter >= so.wakeup_threshold_HK)) {
        //if (unfixed_edges_tsize < 200 || nb_runs_level < 10)
        if (wakeup_enabled)
            pushInQueue();
    }

}

void TSPPropagator::notifyNewDecLevel() { 
    first_run = true; 
    wakeup_counter = 0;
    nb_runs_level = 0;
}

int TSPPropagator::nb_calls_prop = 0;
bool TSPPropagator::propagate() {
    first_run = false;
    nb_runs_level++;
    old_wakeup_counter = wakeup_counter;
    wakeup_counter = 0;

    nb_calls_prop++;

    repair_backtrack();
    prop_calls++;
    while(expl_builder_tsize < expl_builder.size()) {
        delete expl_builder.back();
        expl_builder.pop_back();
    }

    //    if (unfixed_edges_tsize+in_edges_size == 199 || unfixed_edges_tsize == 199)
    //    cout<<"Start propagation "<<engine.decisionLevel()<<endl;
    //sort_size_stat[engine.decisionLevel()]++;


    string deb ="";
    //for (int i = 0; i < in_edges_tsize; i++)
    //    deb += "("+to_string(getEndnode(in_edges[i],0))+","+to_string(getEndnode(in_edges[i],1))+") ";
    //int a = (mand1[27] == -1)? -1: getOtherEndnode(mand1[27],27);
    //int b = (mand2[27] == -1)? -1: getOtherEndnode(mand2[27],27);
    // string deb ="";
    // for (int i = 0; i < adj[64].size(); i++)
    //     if (!getEdgeVar(adj[64][i]).isFixed() ||getEdgeVar(adj[64][i]).isTrue())
    //         deb += "("+to_string(getOtherEndnode(adj[64][i],64));
    //cout<<"================================================PROPAGATE "<<deb<<endl;
    //int rcu = 0, rcm = 0;
    //for (int i = 0; i < adj[64].size(); i++) {
    //    rcu += !getEdgeVar(adj[64][i]).isFixed();
    //    rcm += getEdgeVar(adj[64][i]).isFixed() && getEdgeVar(adj[64][i]).isTrue();
    //}
    // cout<<"================================================PROPAGATE "<<
    //     getEdgeVar(nodes2edge[64][96]).isFixed()
    //     <<getEdgeVar(nodes2edge[64][7]).isFixed()
    //     <<getEdgeVar(nodes2edge[64][30]).isFixed()
    //     <<"   "<<neigh_sizes[64]<<" real count: "<<rcu<<" "<<rcm<<endl;

    int lb;
    //double before = wallClockTime();
    do {
        lb = obj->getMin();
        if (!lagrangian_rel()) {            
            return false;
        }
        //cout<<"Lower bound is "<<obj->getMin()<<" and I am at "<<lb<<endl;
    } while (lb < obj->getMin());
    //cout<<"after "<< floor((wallClockTime()-before)*1000)<<endl;
    m1t_cost = obj->getMin();

    //deb ="";
    //for (int i = 0; i < nbEdges(); i++)
    //    if(getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())
    //        deb += "("+to_string(getEndnode(i,0))+","+to_string(getEndnode(i,1))+") ";
    //cout<<"The objective at this stage is ["<<obj->getMin()<<","<<obj->getMax()<<"] "
    //    <<getEdgeVar(nodes2edge[94][102]).isFixed()<<getEdgeVar(nodes2edge[94][102]).isTrue()<<endl;

    return true;
}

void TSPPropagator::clearPropState() {
    GraphPropagator::clearPropState();
}

bool TSPPropagator::checkFinalSatisfied() {
    cout<<std::fixed<<(float)expl_size/expl_used<<" "<<prop_calls<<endl;
    return true;
}

bool TSPPropagator::too_heavy_mandatory(double ww) {
    if (ceil(ww) > obj->getMax()) {
        if (so.lazy) {
            vec<Lit> expl_fail;
            for (unsigned int i = 0; i < in_edges_tsize; i++) 
                expl_fail.push(getEdgeVar(in_edges[i]).getValLit());
            expl_fail.push(obj->getMaxLit());
            Clause *expl = Clause_new(expl_fail);
            my_clauses.push_back(expl);
            my_clauses_origin.push_back(__LINE__);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;
        }
        return false;
    }
    return true;
}

void TSPPropagator::add1node(int node, double& cost) {
    string debug = "";
    int e1, e2;
    bool ok = find_two_cheapest(node, e1, e2,heldkarp_ws);
    assert(ok);
    cost += heldkarp_ws[e1] + heldkarp_ws[e2]; 
    // debug += "Added edge "+to_string(getEndnode(e1,1))+" "
    //     +to_string(getEndnode(e2,1))+" cost "
    //     +print_raw_double_binary(cost)+"\n";
    m1t_degrees[getEndnode(e1,0)]++;
    m1t_degrees[getEndnode(e1,1)]++;
    m1t_degrees[getEndnode(e2,0)]++;
    m1t_degrees[getEndnode(e2,1)]++;
    //cout<<debug;
}

void TSPPropagator::add1node(int node, double& cost, int& ea, int& eb, vec<Lit>& ps) {
    string debug = "";
    int e1, e2;
    bool ok = find_two_cheapest(node, e1, e2,heldkarp_ws, ps);
    assert(ok);
    cost += heldkarp_ws[e1] + heldkarp_ws[e2]; 
    // debug += "Added edge "+to_string(getEndnode(e1,1))+" "
    //     +to_string(getEndnode(e2,1))+" cost "
    //     +print_raw_double_binary(cost)+"\n";
    m1t_degrees[getEndnode(e1,0)]++;
    m1t_degrees[getEndnode(e1,1)]++;
    m1t_degrees[getEndnode(e2,0)]++;
    m1t_degrees[getEndnode(e2,1)]++;
    //cout<<debug;
    ea = e1;
    eb = e2;
    
}

void TSPPropagator::kruskal_pre_add(int one, int& counter, double& cost, 
                                    UF<int>& uf, RerootedUnionFind<int>* ruf) {
    //string deb ="";
    /*(for (unsigned int i = 0; i < in_edges_tsize; i++) {
        int e = in_edges[i];
        assert(getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue());
        if (touches(e,one))
            continue;
        //deb +="Pre-add "+ to_string(getEndnode(e,0))+" "+to_string(getEndnode(e,1))+"\n";
        bool ok = uf.unite(getEndnode(e,0), getEndnode(e,1));
        if(!ok) {
            //cout<<deb;
            cout<<available_to_dot()<<endl;
        }
        assert(ok);
        if(ruf != NULL)
            ruf->unite(getEndnode(e,0), getEndnode(e,1));
        counter++;
        cost += heldkarp_ws[e];
        m1t_degrees[getEndnode(e,0)]++;
        m1t_degrees[getEndnode(e,1)]++;
        // cout<< "Pre-added edge "+to_string(getEndnode(e,0))+" "
        //     +to_string(getEndnode(e,1))+" cost "+print_double(heldkarp_ws[e])+" "
        //     +print_double(cost)<<endl;
        // cout<< "Pre-added edge "+to_string(getEndnode(e,0))+" "
        //     +to_string(getEndnode(e,1))+" cost "+print_raw_double_binary(heldkarp_ws[e])+" "
        //     +print_raw_double_binary(cost)<<endl;
   }//*/
        //*
    int sum = 0;
    int* arr = new int[in_edges_tsize];
    for (int i = 0; i < in_edges_tsize; i++)
        arr[i] = in_edges[i];
    sort_edges(arr,in_edges_tsize);
    for (unsigned int i = 0; i < in_edges_tsize; i++) {
        int e = arr[i];
        assert(getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue());
        if (touches(e,one))
            continue;
        //deb +="Pre-add "+ to_string(getEndnode(e,0))+" "+to_string(getEndnode(e,1))+"\n";
        bool ok = uf.unite(getEndnode(e,0), getEndnode(e,1));
        if(!ok) {
            //cout<<deb;
            cout<<available_to_dot()<<endl;
        }
        assert(ok);
        if(ruf != NULL)
            ruf->unite(getEndnode(e,0), getEndnode(e,1));
        counter++;
        cost += heldkarp_ws[e];
        sum += original_ws[e];
        m1t_degrees[getEndnode(e,0)]++;
        m1t_degrees[getEndnode(e,1)]++;
        // cout<< "Pre-added edge "+to_string(getEndnode(e,0))+" "
        //     +to_string(getEndnode(e,1))+" cost "+print_double(heldkarp_ws[e])+" "
        //     +print_double(cost)<<endl;
        // cout<< "Pre-added edge "+to_string(getEndnode(e,0))+" "
        //     +to_string(getEndnode(e,1))+" cost "+print_raw_double_binary(heldkarp_ws[e])+" "
        //     +print_raw_double_binary(cost)<<endl;
    }
    //cout<<"sumsum "<<sum<<endl;
    delete[] arr;//*/
}

void TSPPropagator::sort_edges(int* src, int* dest, int low, int high) {
    //assert(low >= 0);
    //assert(high >= 0);
    //assert(low <= unfixed_edges_tsize);
    //assert(high <= unfixed_edges_tsize);
    int length = high - low;
    // Insertion sort on smallest arrays
    if (length < 7) {
        for (int i = low; i < high; i++) {
            for (int j = i; j > low && heldkarp_ws[dest[j-1]] > heldkarp_ws[dest[j]]; j--) {
                double tmp = dest[j];
                dest[j] = dest[j-1];
                dest[j-1] = tmp;
            }
        }
        return;
    }
    // Recursively sort halves of dest into src
    int mid = ((unsigned int)(low + high)) >>1;
    sort_edges(dest, src, low, mid);
    sort_edges(dest, src, mid, high);
    // If list is already sorted, just copy from src to dest.  This is an
    // optimization that results in faster sorts for nearly ordered lists.
    if (heldkarp_ws[src[mid-1]] <= heldkarp_ws[src[mid]]) {
        std::memcpy(dest+low,src+low,sizeof(int)*length);
        return;
    }
    // Merge sorted halves (now in src) into dest
    for (int i = low, p = low, q = mid; i < high; i++) {
        if (q >= high || (p < mid && heldkarp_ws[src[p]] <= heldkarp_ws[src[q]]))
            dest[i] = src[p++];
        else
            dest[i] = src[q++];
    }
}

TSPPropagator* tsp_propagator;
void tsp(vec<BoolView>& _vs, vec<BoolView>& _es, 
         vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
         IntVar* _w, vec<int>& _ws) {
    
    tsp_propagator = new TSPPropagator(_vs,_es,_adj,_en,_w,_ws);
    if (so.check_prop)
        engine.propagators.push(tsp_propagator);        
    vec<vec<int> > adjfiltered;
    for (unsigned int i = 0; i < tsp_propagator->adj.size(); i++) {
        adjfiltered.push(vec<int>());
        for (unsigned int j = 0; j < tsp_propagator->adj[i].size(); j++) {
            if (!tsp_propagator->getEdgeVar(tsp_propagator->adj[i][j]).isFixed() ||
                tsp_propagator->getEdgeVar(tsp_propagator->adj[i][j]).isTrue())
                adjfiltered[i].push(tsp_propagator->adj[i][j]);
        }
    }
    cout<<"TSPPropagator has ID: "<< tsp_propagator->prop_id<<endl;
    NoSubtourPropagator* ns = new NoSubtourPropagator(_vs,_es,_adj,_en);
    cout<<"NoSubtourPropagator has ID: "<< ns->prop_id<<endl;
    tsp_propagator->bccp = biconnected(_vs,_es,_en,adjfiltered);
    CycleCostSimple* ccs = new CycleCostSimple(_vs,_es,adjfiltered,_en,_w,_ws);
    cout<<"CycleCostSimple has ID: "<< ccs->prop_id<<endl;
}

void tsp(vec<BoolView>& _vs, vec<BoolView>& _es, 
         vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
         IntVar* _w, vec<int>& _ws, vec<IntVar*> s) {
    tsp_propagator = new TSPPropagator(_vs,_es,_adj,_en,_w,_ws,s);
    if (so.check_prop)
        engine.propagators.push(tsp_propagator);        
    vec<vec<int> > adjfiltered;
    for (unsigned int i = 0; i < tsp_propagator->adj.size(); i++) {
        adjfiltered.push(vec<int>());
        for (unsigned int j = 0; j < tsp_propagator->adj[i].size(); j++) {
            if (!tsp_propagator->getEdgeVar(tsp_propagator->adj[i][j]).isFixed() ||
                tsp_propagator->getEdgeVar(tsp_propagator->adj[i][j]).isTrue())
                adjfiltered[i].push(tsp_propagator->adj[i][j]);
        }
    }
    cout<<"TSPPropagator has ID: "<< tsp_propagator->prop_id<<endl;
    NoSubtourPropagator* ns = new NoSubtourPropagator(_vs,_es,_adj,_en);
    cout<<"NoSubtourPropagator has ID: "<< ns->prop_id<<endl;
    tsp_propagator->bccp = biconnected(_vs,_es,_en,adjfiltered);
    CycleCostSimple* ccs = new CycleCostSimple(_vs,_es,adjfiltered,_en,_w,_ws);
    cout<<"CycleCostSimple has ID: "<< ccs->prop_id<<endl;

    if (so.use_circuit_kf_prop) {
        circuit_kf(s);
    }
}



class TSPStrategies : public BranchGroup {
    
public:
    enum TSPStrategyType {MIN_COST, MAX_COST, 
                          MIN_DELTA_DEGREE, MAX_DELTA_DEGREE,
                          MAX_REMOVED,MIN_REMOVED,
                          CLOSEST};
    //All I need:
    int* weights;
    std::vector< std::vector<edge_id> > adj;
    int nb_nodes;
    
    TSPStrategyType type;

    int choice;
    int val;
    bool use_last_conflict;
    int last_conflict_node;



    std::unordered_map<int,int> map; //edges to vars

    TSPStrategies(vec<Branching*>& _x, VarBranch vb, bool t, TSPStrategyType _type)
        : BranchGroup(_x,vb,t) {
        type = _type;
        head = 0;
        
        weights = new int[tsp_propagator->nbEdges()];
        memcpy(weights,tsp_propagator->original_ws,sizeof(int)*tsp_propagator->nbEdges());
        adj = tsp_propagator->adj;
        nb_nodes = tsp_propagator->nbNodes();

        int c = 0;
        for (int i = 0; i < tsp_propagator->nbEdges(); i++) {
            if(!tsp_propagator->getEdgeVar(i).isFixed()) {
                map[i] = c;
                c++;
            }
        }

        last_conflict_node = -1;
        use_last_conflict = so.use_last_conflict_HK;
    }

    bool finished() {
	if (fin) return true;
	for (int i = 0; i < x.size(); i++) {
            if (!x[i]->finished()) {
                return false;
            }
	}
	fin = 1;
	return true;
    }

    void choose_edge_from(int n) {
        bool lc_best = false;
        for (int i = 0; i < tsp_propagator->neigh_sizes[n]; i++) {
            int e = tsp_propagator->adj[n][i];
            if(tsp_propagator->getEdgeVar(e).isFixed())
                continue;
            switch (type) {
            case MAX_COST:
                if (val == -1 || val < weights[e])  {
                    val = weights[e];
                    choice = e;
                    last_conflict_node = n;
                }
                break;
            case MIN_COST:
                if (val == -1 || val > weights[e])  {
                    val = weights[e];
                    choice = e;
                    last_conflict_node = n;
                }
                break;
            case MAX_DELTA_DEGREE:
                {
                    int u = tsp_propagator->getEndnode(e,0);
                    int v = tsp_propagator->getEndnode(e,1);
                    int score_u = tsp_propagator->neigh_sizes[u] - 
                        0*((tsp_propagator->mand1[u] != -1) + 
                         (tsp_propagator->mand2[u] != -1));
                    int score_v = tsp_propagator->neigh_sizes[v] - 
                        0*((tsp_propagator->mand1[v] != -1) + 
                         (tsp_propagator->mand2[v] != -1));
                    int score = score_u + score_v;
                    if (val == -1 || val < score)  {
                        val = score;
                        choice = e;
                        last_conflict_node = n;
                    }
                }
                break;
            case MIN_DELTA_DEGREE:
                {
                    int u = tsp_propagator->getEndnode(e,0);
                    int v = tsp_propagator->getEndnode(e,1);
                    int score_u = tsp_propagator->neigh_sizes[u] - 
                        0*((tsp_propagator->mand1[u] != -1) + 
                         (tsp_propagator->mand2[u] != -1));
                    int score_v = tsp_propagator->neigh_sizes[v] - 
                        0*((tsp_propagator->mand1[v] != -1) + 
                         (tsp_propagator->mand2[v] != -1));
                    int score = score_u + score_v;
                    if (val == -1 || val > score)  {
                        val = score;
                        choice = e;
                        last_conflict_node = n;
                    }
                }
                break;
            case MAX_REMOVED:
                {
                    int u = tsp_propagator->getEndnode(e,0);
                    int v = tsp_propagator->getEndnode(e,1);
                    int score_u = tsp_propagator->neigh_sizes[u];
                    int score_v = tsp_propagator->neigh_sizes[v];
                    if (tsp_propagator->mand1[u] == -1 && tsp_propagator->mand2[u] == -1) score_u = 0;
                    if (tsp_propagator->mand1[v] == -1 && tsp_propagator->mand2[v] == -1) score_v = 0;
                    int score = score_u + score_v;
                    if (val == -1 || val < score)  {
                        val = score;
                        choice = e;
                        last_conflict_node = n;
                        if(lc_best){
                            if (score_u > score_v)
                                last_conflict_node = u;
                            else
                                last_conflict_node = v;
                        }
                    } else if (val == score) {
                        if (weights[choice] > weights[e]) {
                            val = score;
                            choice = e;
                            last_conflict_node = n;
                            if(lc_best){
                                if (score_u > score_v)
                                    last_conflict_node = u;
                                else
                                    last_conflict_node = v;
                            }   
                        }
                    }
                }
                break;
            case MIN_REMOVED:
                break;
            default:
                break;
            }
                
        }
    }

 
    DecInfo* conflict_edge_expl() {
        if(sat.learnts.size() > 0) {
            Clause* clause = sat.learnts[sat.learnts.size()-1];
            if(clause != NULL) {
                Lit p = *clause[0];
                if (tsp_propagator->var2BoolView.find(var(p)) != tsp_propagator->var2BoolView.end())
                    cout<<"Found ";
                else
                    cout<<"Nope! ";
                p = *clause[1];
                if (tsp_propagator->var2BoolView.find(var(p)) != tsp_propagator->var2BoolView.end())
                    cout<<"Found ";
                else
                    cout<<"Nope! ";
                p = *clause[2];
                if (tsp_propagator->var2BoolView.find(var(p)) != tsp_propagator->var2BoolView.end())
                    cout<<"Found"<<endl;
                else
                    cout<<"Nope!"<<endl;
            }
        }
        return NULL;
    }
   
    DecInfo* expl_activity() {
        int arg_max = -1;
        bool val = false;
        double max = 0;
        for (int i = 0; i < tsp_propagator->nbEdges(); i++) {
            if (!tsp_propagator->getEdgeVar(i).isFixed()) {
                if (arg_max == -1 || 
                    tsp_propagator->lit_expl_activity[tsp_propagator->lit2int[toInt(tsp_propagator->getEdgeVar(i).getLit(true))]] > max) {
                    arg_max = i;
                    val = true;
                    max = tsp_propagator->lit_expl_activity[tsp_propagator->lit2int[toInt(tsp_propagator->getEdgeVar(i).getLit(true))]];
                }
                if (arg_max == -1 || 
                    tsp_propagator->lit_expl_activity[tsp_propagator->lit2int[toInt(tsp_propagator->getEdgeVar(i).getLit(false))]] > max) {
                    arg_max = i;
                    val = false;
                    max = tsp_propagator->lit_expl_activity[tsp_propagator->lit2int[toInt(tsp_propagator->getEdgeVar(i).getLit(false))]];
                }
            }
        }

        if(arg_max != -1) {
             // cout<<"Chose "<<"("<<tsp_propagator->getEndnode(choice,0)
             //     <<","<<tsp_propagator->getEndnode(choice,1)<<") of weight "
             //     <<weights[choice]<<" lc: "<<last_conflict_node<<endl;
             // cout<<"       "<<tsp_propagator->getEdgeVar(tsp_propagator->nodes2edge[0][1]).isFixed()<< "  "<<
             //     weights[tsp_propagator->nodes2edge[0][1]]<<endl;
            return new DecInfo(x[map[arg_max]],val,1);
        }
        return NULL;

            
    }


    DecInfo* activity_nodes() {
        vector<int> nodes;
        vector<double> activities;
        for (int n = 0; n < nb_nodes; n++) {
            nodes.push_back(n);
            activities.push_back(0.0);
            for (int i = 0; i < tsp_propagator->adj[n].size(); i++) {
                int e = tsp_propagator->adj[n][i];
                activities[n] += sat.activity[var(tsp_propagator->getEdgeVar(e).getLit(true))];
                //cout<<" "<<print_raw_double_binary(sat.activity[var(tsp_propagator->getEdgeVar(e).getLit(true))])
                //    <<" edge "<<e<<endl;
            }
            //cout<<print_raw_double_binary(activities[activities.size()-1])<<endl;

        }
        struct sorter {
            vector<double> acs;
            sorter(vector<double>& ac) : acs(ac) {}
            bool operator() (int i,int j) { return (acs[i] > acs[j]);}
        } sorter_object(activities);



        std::stable_sort(nodes.begin(), nodes.end(), sorter_object);

        val = -1; choice = -1;
        for (int i = 0; i < nb_nodes; i++) {
            int n = nodes[i];
            choose_edge_from(n);
            if (choice != -1 &&
                (i == nb_nodes-1 || abs(activities[nodes[i+1]] - activities[n]) > 0.00001 )) { //Heavier in ties
                break;
            }
        }
        if(choice != -1) {
             // cout<<"Chose "<<"("<<tsp_propagator->getEndnode(choice,0)
             //     <<","<<tsp_propagator->getEndnode(choice,1)<<") of weight "
             //     <<weights[choice]<<" lc: "<<last_conflict_node<<endl;
             // cout<<"       "<<tsp_propagator->getEdgeVar(tsp_propagator->nodes2edge[0][1]).isFixed()<< "  "<<
             //     weights[tsp_propagator->nodes2edge[0][1]]<<endl;
            return new DecInfo(x[map[choice]],false,1);
        }
        return NULL;
    }

    int head;
    vector<int> heads;
    DecInfo* closest() {
        if (heads.size() == 0) {
            head = 0;
            heads.push_back(head);
        } else {
            head = heads[engine.decisionLevel()];
        }
        //cout<<"Head is "<<head<<" "<<engine.decisionLevel()<<endl;
        int closest = -1;
        for (int i = 0; i < tsp_propagator->adj[head].size(); i++) {
            int e = tsp_propagator->adj[head][i];
            int w = tsp_propagator->original_ws[e];
            if (tsp_propagator->getEdgeVar(e).isFixed()) continue;
            if (closest == -1 || w < tsp_propagator->original_ws[closest]) {
                closest = e;
            }
        } 

        if (closest != -1) {
            head = tsp_propagator->getOtherEndnode(closest,head);
            heads.push_back(head);
             // cout<<"Chose1 "<<"("<<tsp_propagator->getEndnode(closest,0)
             //     <<","<<tsp_propagator->getEndnode(closest,1)<<") of weight "
             //     <<weights[closest]<<endl;
            return new DecInfo(x[map[closest]],true,1);
        } else if (!finished()) {
            int node = -1;
            for (int i = 0; i < tsp_propagator->nbNodes(); i++) {
                int deg = 0;
                int local_closest = -1;
                for (int j = 0; j < tsp_propagator->adj[i].size(); j++) {
                    int e = tsp_propagator->adj[i][j];
                    int w = tsp_propagator->original_ws[e];                    
                    if (tsp_propagator->getEdgeVar(e).isFixed()) {
                        deg++;
                        continue;
                    }
                    if (local_closest == -1 || w < tsp_propagator->original_ws[local_closest]) {
                        local_closest = e;
                    }
                }
                if (deg == 1) {
                    closest = local_closest;
                    node = tsp_propagator->getOtherEndnode(local_closest,i);
                }
            }

            if (closest != -1) {
                head = node;
                heads.push_back(head);
             // cout<<"Chose2 "<<"("<<tsp_propagator->getEndnode(closest,0)
             //     <<","<<tsp_propagator->getEndnode(closest,1)<<") of weight "
             //     <<weights[closest]<<endl;
                return new DecInfo(x[map[closest]],true,1);
            } else {
                for (int i = 0; i < tsp_propagator->nbNodes(); i++) {
                    for (int j = 0; j < tsp_propagator->adj[i].size(); j++) {
                        int e = tsp_propagator->adj[i][j];
                        int w = tsp_propagator->original_ws[e];                    
                        if (tsp_propagator->getEdgeVar(e).isFixed()) {
                            continue;
                        }
                        if (closest == -1 || w < tsp_propagator->original_ws[closest]) {
                            closest = e;
                            node = tsp_propagator->getOtherEndnode(closest,i);
                        }
                    }
                }
                head = node;          
                heads.push_back(head);      
             // cout<<"Chose3 "<<"("<<tsp_propagator->getEndnode(closest,0)
             //     <<","<<tsp_propagator->getEndnode(closest,1)<<") of weight "
             //     <<weights[closest]<<endl;
                return new DecInfo(x[map[closest]],true,1);
            }

        }
        
        return NULL;
    }

    DecInfo* branch() {
        if (type == CLOSEST) return closest();

        //conflict_edge_expl();
        //return expl_activity();
        //return activity_nodes();
        //DecInfo(VARIABLE, VALUE, {1: ==, 0: !=})
        choice = -1;
        val = -1;


        if (use_last_conflict && last_conflict_node != -1) {
            choose_edge_from(last_conflict_node);            
        }
        if (choice == -1) {

            for (int n = 0; n < nb_nodes; n++) {
                choose_edge_from(n);
            }
            
        }

        if(choice != -1) {

            /*cout<<"Chose "<<"("<<tsp_propagator->getEndnode(choice,0)
                 <<","<<tsp_propagator->getEndnode(choice,1)<<") of weight "
                 <<weights[choice]<<","
                 <<last_conflict_node<<","
                 << tsp_propagator->original_ws[choice]<<","
                 << tsp_propagator->heldkarp_ws[choice]<<","
                 << tsp_propagator->heldkarp_ws[choice] - tsp_propagator->original_ws[choice]<<","
                 << tsp_propagator->getEndnode(choice,0)<<","
                 << tsp_propagator->getEndnode(choice,1)<<","
                 << tsp_propagator->m1t_degrees[tsp_propagator->getEndnode(choice,0)]<<","
                 << tsp_propagator->m1t_degrees[tsp_propagator->getEndnode(choice,1)]<<","
                 << tsp_propagator->neigh_sizes[tsp_propagator->getEndnode(choice,0)]<<","
                 << tsp_propagator->neigh_sizes[tsp_propagator->getEndnode(choice,1)]<<","
                 << (tsp_propagator->mand1[tsp_propagator->getEndnode(choice,0)] != -1) + (tsp_propagator->mand2[tsp_propagator->getEndnode(choice,0)] != -1)<<","
                 << (tsp_propagator->mand1[tsp_propagator->getEndnode(choice,1)] != -1) + (tsp_propagator->mand2[tsp_propagator->getEndnode(choice,1)] != -1)<<","
                 << sat.activity[var(tsp_propagator->getEdgeVar(choice).getLit(true))]<<","
                 << sat.activity[var(tsp_propagator->getEdgeVar(choice).getLit(false))]<<""
                 <<endl;
            */
            // cout<<"Chose "<<"("<<tsp_propagator->getEndnode(choice,0)
            //     <<","<<tsp_propagator->getEndnode(choice,1)<<") of cost "
            //      <<weights[choice]
            //      <<" lc: "<<last_conflict_node<<"    "
            //      << engine.decisionLevel()<<"    obj=["<< tsp_propagator->obj->getMin()<<","
            //     << tsp_propagator->obj->getMax()<<"]"<<"   "<< tsp_propagator->getEdgeVar(841).isFixed()
            //      <<endl;
             // << (tsp_propagator->mand1[8] == -1 ? -1 : tsp_propagator->getOtherEndnode(tsp_propagator->mand1[8],8))
             //     <<" "
             // << (tsp_propagator->mand2[8] == -1 ? -1 : tsp_propagator->getOtherEndnode(tsp_propagator->mand2[8],8))
             //     <<" "<<tsp_propagator->getEdgeVar(tsp_propagator->nodes2edge[8][59]).isFixed()<<tsp_propagator->getEdgeVar(tsp_propagator->nodes2edge[8][86]).isFixed()<<endl;

             // cout<<"       "<<tsp_propagator->getEdgeVar(tsp_propagator->nodes2edge[0][1]).isFixed()<< "  "<<
             //     weights[tsp_propagator->nodes2edge[0][1]]<<endl;
            return new DecInfo(x[map[choice]],true,1);
        }
        
        return NULL;
    }

};

/*void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
    if (var_branch == TSP_STRATEGY) {
        engine.branching->add(new TSPStrategies(x, var_branch, true,TSPStrategies::MIN_DELTA_DEGREE));
        return;
    }

    engine.branching->add(new BranchGroup(x, var_branch, true));
    if (val_branch == VAL_DEFAULT) return;
    PreferredVal p;
    switch (val_branch) {
    case VAL_MIN: p = PV_MIN; break;
    case VAL_MAX: p = PV_MAX; break;
    case VAL_SPLIT_MIN: p = PV_SPLIT_MIN; break;
    case VAL_SPLIT_MAX: p = PV_SPLIT_MAX; break;
    default: NEVER;
    }
    for (int i = 0; i < x.size(); i++) ((Var*) x[i])->setPreferredVal(p);
}
//*/
