#include<iostream>
#include<algorithm>
#include<vector>
#include<set>
#include<climits>
#include<cassert>
#include "common.h"
#include "interval.h"

#include "../core/engine.h"
#include "../core/sat.h"
#include <unordered_map>
#include <queue>
#include <stack>


using namespace std;

#ifndef _MDD_
#define _MDD_

struct bds {
    bds(int _lo = 0, int _up = 0): lo(_lo),up(_up) {}
    int lo;
    int up;
};

struct EventTable {
    std::unordered_map<int,struct bds> changed; //Level or var to bounds
    std::unordered_map<int,Lit> bool_changes; //var to lit
    std::unordered_map<int,int> ccount; //var to changes count
    int updates;
    EventTable():updates(0){}
    void merge(struct EventTable& other) {
        for ( auto it = other.changed.begin(); it != other.changed.end(); ++it ) {
            add(it->first, it->second);
        }
    }
    void add(int level, struct bds nbd) {
        ccount[level]++;
        if (changed.find(level) == changed.end()) {
            changed[level] = nbd;
        } else {
            struct bds bd = changed[level];
            bd.lo = bd.lo < nbd.lo ? bd.lo : nbd.lo;
            bd.up = bd.up > nbd.up ? bd.up : nbd.up;
            changed[level] = bd;
        }
    }
    void add_bool(int var, Lit l) {
        assert(l != lit_Undef);
        ccount[var]++;
        if (bool_changes.find(var) == bool_changes.end()) {
            if (bool_changes[var] != lit_Undef) 
                bool_changes[var] = l;
        } else {
            if (bool_changes[var] != l) {
                bool_changes[var] = lit_Undef;
            }
        }
    }
};


class Node {
 public:
    typedef unsigned int uint;
    typedef uint Literal;
    typedef uint NodeID;
    typedef uint Var;
    typedef int SelVar;
    typedef int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.
    //typedef long long int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.

private:
  vector<NodeID> children;
  Interval interval;
  Var v;
  uint level;
public:
    IntVar* intvar;
    struct EventTable bounds;
    struct EventTable conseq;
  inline Node ( const vector<NodeID>& _children, Interval& _interval, uint _level);
  inline Node ( bool b, NodeID id );
  inline Interval getInterval() const;
  inline Var getVar() const;
  inline void setVar( Var _v);
  inline uint getLevel () const;
  inline void setLevel (uint _level);
  inline uint numChildren () const;
  inline NodeID getChild ( uint x ) const;
  inline void removeChild( NodeID x);
};

class LiMDD {
 public:
    typedef unsigned int uint;
    typedef uint Literal;
    typedef uint NodeID;
    typedef uint Var;
    typedef int SelVar;
    typedef int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.
    //typedef long long int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.
vector<bool> dead;
public:
  vector<set<Interval> > lib;
  vector<Node> nodes;
  vector<bool> pols;
  vector<li> coeffs;
  vector<IntVar*> domains;
  li K;
  NodeID root;
  NodeID findNode(li currentK, uint level);

  void printMDD(LiMDD::NodeID n, int l) const;
public:


  inline LiMDD(const vector<li>& _coeffs, const vector<IntVar*>& _domains, li _K );
  inline LiMDD();
  inline void defineConstraint(const vector<li>& _coeffs, const vector<IntVar*>& _domains);
  inline bool isEmpty() const;
  inline NodeID getLastNode() const;
  inline NodeID getFirstNode() const;
  inline bool isLast( NodeID n) const;
  inline NodeID nextNode ( NodeID n ) const;
  inline Var getVar ( NodeID n ) const;
  inline void setVar ( NodeID n, Var v );
  inline uint getLevel ( NodeID n ) const;
  inline bool isTerminal ( NodeID n ) const;
  inline void setTerminal ( NodeID n, bool b );
  inline bool isTrue ( NodeID n ) const;
  inline NodeID getSon ( NodeID n, int numSon ) const;
  inline uint getNumSons ( NodeID n ) const;
  inline uint getSize() const { return nodes.size(); }
  inline NodeID getRoot() const { return root; }
  inline NodeID newRoot(li _K);
    inline void removeSon(NodeID n, NodeID c) {nodes[n].removeChild(c);}
bool cleanMDD(NodeID n,std::vector<bool>& v);

  inline pair<set<Interval>::iterator,set<Interval>::iterator> getListOfNodes(uint lvl);

  void printMDD() const;
    inline void slimMDD(std::vector<std::vector<Lit> >& l);
    void computeSize(int& nodes, int& edges) const;
};

void LiMDD::computeSize(int& nc, int& ec) const {
    nc = 0; ec = 0;
    std::vector<bool> done(nodes.size(),false);
    std::vector<bool> pushed(nodes.size(),false);
    std::queue<NodeID> q;
    q.push(root);

    while(!q.empty()) {        
        NodeID node = q.front();
        q.pop();
        done[node] = true;
        nc++;
        if (isTerminal(node)) continue;
        uint nS = getNumSons(node);        
        for (uint i = 0; i < nS; i++) {
            ec++;
            NodeID s = getSon(node,i);
            assert(!done[s]);
            if (!pushed[s]) { 
                q.push(s);
                pushed[s] = true;
            }
        }
    }

}


inline void LiMDD::slimMDD(std::vector<std::vector<Lit> >& lits) {
    //printf("*********\n");

    std::vector<bool> done(nodes.size(),false);
    std::vector<bool> pushed(nodes.size(),false);
    std::queue<NodeID> q;
    q.push(root);

    while(!q.empty()) {
        
        NodeID node = q.front();
        q.pop();
        done[node] = true;
        //printf("At node %d %p\n",node,nodes[node].intvar);
        if (isTerminal(node)) continue;
        //printf("At node %d %p\n",node,nodes[node].intvar);
        //Read list of assumptions at this node
        //Add assumptions
        //Propagate
        //Should return true
        //
        engine.btToLevel(0);
        sat.btToLevel(0);
        vec<Lit> decisions;
        //printf("Table \n");
        for ( auto it = nodes[node].bounds.changed.begin(); 
              it != nodes[node].bounds.changed.end(); 
              ++it ) {
            struct bds bd = it->second;
            //printf(" bd: %d %d   %p\n",bd.lo,bd.up,domains[it->first]);
            Lit l = lit_True;
            Lit u = lit_True;
            if (bd.lo > 0) { 
                assert(bd.lo-1 < lits[it->first].size());
                l = ~lits[it->first][bd.lo-1];
            } // else is tautological
            if (bd.up < lits[it->first].size())
                u = lits[it->first][bd.up];
            //else it's tautological
            if (sat.value(l) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(l));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            }
            if (sat.value(u) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(u));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            }
            decisions.push(l);
            decisions.push(u);
        }        
        bool ok = engine.propagate();
        engine.clearPropState();
        assert(ok);

        //printf("Consequences: %d %d\n",nodes[node].conseq.changed.size(),nodes[node].conseq.bool_changes.size());
        for ( auto it = nodes[node].conseq.changed.begin(); 
              it != nodes[node].conseq.changed.end(); 
              ++it ) {
            if (it->first != nodes[node].conseq.updates) continue;            
            struct bds bd = it->second;
            //printf("%d in [%d,%d]\n",it->first,bd.lo,bd.up);
            //if(engine.vars[it->first]->getMin() < bd.lo)
            //    engine.vars[it->first]->setMin(bd.lo);
            //if(engine.vars[it->first]->getMax() > bd.up)
            //    engine.vars[it->first]->setMax(bd.up);
            Lit l = engine.vars[it->first]->getLit(bd.lo,2);
            Lit u = engine.vars[it->first]->getLit(bd.up,3);
            if (sat.value(l) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(l));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            }
            if (sat.value(u) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(u));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            }
            //decisions.push(l);
            //decisions.push(u);
        ok = engine.propagate();
        engine.clearPropState();
        assert(ok);
        }        


        for ( auto it = nodes[node].conseq.bool_changes.begin(); 
              it != nodes[node].conseq.bool_changes.end(); 
              ++it ) {
            if (it->first != nodes[node].conseq.updates) continue;
            Lit l = it->second;
            if (l == lit_Undef) continue;
            if (sat.value(l) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(l));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            } else {
                assert(sat.value(l) == l_True);
            }
        }        
        ok = engine.propagate();
        engine.clearPropState();
        assert(ok);

        
        int dlevel = engine.decisionLevel();
        //printf("dlevel %d (%d,%d)\n",dlevel,decisions.size(),nodes[node].bounds.changed.size());

        vector<Node::NodeID> to_remove;

        uint nS = getNumSons(node);
        int offset = 0;//nodes[node].intvar->getMin();

        
        int trails = sat.trail.size();
        
        for (uint i = 0; i < nS; i++) {
            //printf("Trying value %d   %d %d %d\n",offset+(int)i,nodes[node].intvar->getMin(),nodes[node].intvar->getMax(),nS);

            Lit l = lit_True;
            Lit u = lit_True;
            if (offset+i > 0) { 
                assert(offset+i-1 < lits[getLevel(node)].size());
                l = ~lits[getLevel(node)][offset+i-1];
            } // else is tautological
            if (offset+i < lits[getLevel(node)].size())
                u = lits[getLevel(node)][offset+i];
            //else it's tautological


            if (sat.value(l) == l_False || sat.value(u) == l_False) {
                to_remove.push_back(getSon(node,i));
                continue;
            } 

            if (sat.value(l) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(l));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            } else {
                //printf("Lit l is true? %d\n",sat.value(l)==l_True);
            }
            if (sat.value(u) == l_Undef) {
                DecInfo* di = new DecInfo(NULL, toInt(u));
                engine.dec_info.push(*di);            
                engine.newDecisionLevel();            
                engine.doFixPointStuff();
                engine.makeDecision(*di, 0);
                delete di;
            } else {
                //printf("Lit u is true? %d\n",sat.value(u)==l_True);
            }
            ok = engine.propagate();
            //printf("Assuming value %d(==%d) (%p) --> %d\n",offset+(int)i,nodes[node].intvar->getVal(),nodes[node].intvar,ok);
            engine.clearPropState();

            if (!ok) {
                decisions.push(l);
                decisions.push(u);
                //sat.addClause(decisions);
                decisions.shrink(2);
                sat.btToLevel(dlevel);
                sat.confl = NULL;
                to_remove.push_back(getSon(node,i));
                continue;
            }
            assert(ok);

            NodeID s = getSon(node,i);
            assert(!done[s]);
            if (!pushed[s]) { 
                q.push(s);
                pushed[s] = true;
                //printf("Pushing node %d\n",s);
            }
            //Unite event tables
            nodes[s].bounds.merge(nodes[node].bounds);
            struct bds fx(offset+(int)i,offset+(int)i);
            nodes[s].bounds.add(getLevel(node), fx);
            //printf("  Adding to node %d\n",s);
            nodes[s].conseq.updates++;
            //Look for things that may have changed:
            for (int t = trails; t < sat.trail.size(); t++) {
                for (int l = 0; l < sat.trail[t].size(); l++) {
                    Lit lit = sat.trail[t][l];
                    int v = sat.c_info[var(lit)].cons_id;
                    if (sat.c_info[var(lit)].cons_type == 1) {
                        IntVar* iv = engine.vars[v];                     
                        struct bds bd(iv->getMin(), iv->getMax());
                        nodes[s].conseq.add(v,bd);
                    } else if (sat.c_info[(var(lit))].cons_type == 0) {
                        //Bool
                        nodes[s].conseq.add_bool(v,lit);
                    }
                }
            }

            


            sat.btToLevel(dlevel);
            assert(sat.trail.size() == trails);
        }

        for (unsigned int k = 0; k < to_remove.size(); k++) {
            nodes[node].removeChild(to_remove[k]);
        }
        to_remove.clear();
        
        sat.btToLevel(0);
    }

    std::vector<bool> v(dead.size(),false);
    cleanMDD(getRoot(),v);

}

//Remove nodes that don't lead to terminals because those edges were removed
bool LiMDD::cleanMDD(NodeID n, std::vector<bool>& visited) {
    if (visited[n]) return getNumSons(n) == 0;
    visited[n] = true;    
    if (isTerminal(n)) 
        return false;
    uint nS = getNumSons(n);

    if (nS == 0)
        return true;
    std::vector<NodeID> to_remove;
    for (unsigned int i = 0; i < nS; i++) {
        if (visited[getSon(n,i)]) continue;
        if (cleanMDD(getSon(n,i), visited)) {
            to_remove.push_back(getSon(n,i));
        }
    }

    for (unsigned int i = 0; i < to_remove.size(); i++) {
        removeSon(n,to_remove[i]);
        dead[to_remove[i]] = true;
    }

    if (getNumSons(n) == 0)
        return true;

    return false;
}

void LiMDD::printMDD() const {
    printMDD(getRoot(),0);
}

void LiMDD::printMDD(LiMDD::NodeID n, int l) const {
  Node node = nodes[n];
  if(isTerminal(n)) {
      if (isTrue(n)) cout<<"["<<n<<"][T]"<<endl;
      else  cout<<"["<<n<<"][F]"<<endl;
    return;
  }
  //cout<< node.getLevel()<<endl;
  cout <<"["<<n<<"]"<<"< x" << node.getLevel() << " > ["<<node.getInterval().getA()<<"," <<node.getInterval().getB() <<"]"<<endl;

  for (uint i = 0; i < node.numChildren(); i++) {
     for (int j = 0; j < l+1; j++) cout<<" ";
     cout<<" ^--> v"<<node.getLevel()<<"="<<i<<" ";
     printMDD(getSon(n,i),l+1);
  }

}


////////////////////////////////////////////////////////////////////////
////////////////////// Node Class Implementation: //////////////////////
////////////////////////////////////////////////////////////////////////

inline Node::Node ( const vector<NodeID>& _children, Interval& _interval, uint _level):
    children(_children),interval(_interval),v(NO_VAR),level(_level),intvar(NULL) {
  dassert ( children.size()>0 && level != TRUE_LIT && level != FALSE_LIT );
}
inline Node::Node ( bool b, NodeID id ):children(0),interval(b,id), v(NO_VAR), level(b?TRUE_LIT:FALSE_LIT),intvar(NULL) {}
inline Interval Node::getInterval() const { return interval; }
inline Node::Var Node::getVar () const { return v; }
inline void Node::setVar(Var _v) { v=_v; }
inline uint Node::getLevel() const { return level; }
inline void Node::setLevel(uint _level) { level=_level; }
inline uint Node::numChildren () const { return children.size(); }
inline Node::NodeID Node::getChild ( uint x ) const { 
  dassert( x < numChildren() );
  return children[x];
}
inline void Node::removeChild( Node::NodeID nid ) {
    for(std::vector<Node::NodeID>::iterator it = children.begin(); 
        it != children.end(); ++it) {        
        if(*it == nid) {
            children.erase(it); 
            break;
        }
    }
}


///////////////////////////////////////////////////////////////////////
////////////////////// MDD Class Implementation: //////////////////////
///////////////////////////////////////////////////////////////////////

// inline MDD::MDD(const vector<li>& _coeffs, const vector<li>& _domains, li _K ):
//   lib(_coeffs.size()+1),coeffs(_coeffs),domains(_domains),K(_K) {
//   dassert( coeffs.size() == domains.size() );
//   root = findNode(K,0);
// }
inline LiMDD::LiMDD( ) { root = NO_NODE; }
inline void LiMDD::defineConstraint(const vector<li>& _coeffs, const vector<IntVar*>& _domains) {
  coeffs  = _coeffs;
  domains = _domains;
  lib.resize(coeffs.size()+1);
}
inline bool LiMDD::isEmpty() const { return root == NO_NODE; }
inline LiMDD::NodeID LiMDD::getLastNode() const {
  dassert(nodes.size()>0 && root != NO_NODE );
  return (NodeID)nodes.size()-1;
}
inline LiMDD::NodeID LiMDD::getFirstNode() const {
  dassert(nodes.size()>0 && root != NO_NODE );
  return (NodeID)0;
}
inline bool LiMDD::isLast ( LiMDD::NodeID n ) const {
  dassert((uint)n<nodes.size());
  return ((uint)n==nodes.size()-1);
}
inline LiMDD::NodeID LiMDD::nextNode ( LiMDD::NodeID n ) const {
  dassert(!isLast(n));
  while (dead[++n]);
  return n;
}
inline bool LiMDD::isTerminal ( LiMDD::NodeID n ) const {
  dassert((uint)n<nodes.size());
  uint lvl = nodes[n].getLevel();
  return ( lvl == TRUE_LIT ) || ( lvl == FALSE_LIT );
}
inline void LiMDD::setTerminal ( LiMDD::NodeID n, bool b ) {
  dassert((uint)n<nodes.size() && !isTerminal(n));
  nodes[n].setLevel(b?TRUE_LIT:FALSE_LIT);
}
inline bool LiMDD::isTrue ( LiMDD::NodeID n ) const {
  dassert(isTerminal(n));
  return nodes[n].getLevel() == TRUE_LIT;
}
inline LiMDD::NodeID LiMDD::getSon ( LiMDD::NodeID n, int numSon ) const {
  dassert(numSon < getNumSons(n));
  return nodes[n].getChild(numSon);
}
inline uint LiMDD::getNumSons ( LiMDD::NodeID n ) const {
  dassert(!isTerminal(n));
  return nodes[n].numChildren();
}
inline LiMDD::Var LiMDD::getVar ( LiMDD::NodeID n ) const {
  //dassert(!isTerminal(n));
  const Node* nn =&(nodes[n]);
  Var v = nn->getVar();
  dassert ( v != NO_VAR );
  return v;
}
inline void LiMDD::setVar( NodeID n, Var v ) {
  //dassert(!isTerminal(n));
  Node* nn =&(nodes[n]);
  dassert ( nn->getVar() == NO_VAR );
  nn->setVar(v);
}
inline uint LiMDD::getLevel ( NodeID n ) const {
  dassert(!isTerminal(n));
  return nodes[n].getLevel();
}
inline LiMDD::NodeID LiMDD::newRoot(li _K) {
  K = _K;
  root = findNode(K,0);
  return root;
}

LiMDD::NodeID LiMDD::findNode(LiMDD::li currentK, LiMDD::uint level) {

  Interval aux = Interval(currentK);
  //cout << "Finding node with K " << currentK << " at level " << level <<" interval=["<< aux.getA()<<","<<aux.getB()<<"]"<<endl;


  set<Interval>::iterator it = lib[level].find(aux);
  if ( it != lib[level].end() ) {
    dassert(it->getA() <= currentK && it->getB() >= currentK);

    //cout << " Found node " << it->getNodeID() << " with interval [" << it->getA() << ", " << it->getB() << "]" << endl;

    return it->getNodeID();
  }
  //The node does not exist: we have to create it.
  if ( currentK < 0) {
    LiMDD::NodeID nid = nodes.size();
    lib[level].insert(Interval(false,nid));
    nodes.push_back(Node(false,nid));
    dead.push_back(false);
    dassert(lib[level].find(aux) != lib[level].end() && lib[level].find(aux)->getNodeID() == nid);

    //cout << " False node created with id " << lib[level].find(aux)->getNodeID() << " and interval [" << lib[level].find(aux)->getA() << ", " << lib[level].find(aux)->getB() << "]" << endl;

    return nid;
  }
  if (level == coeffs.size()) {
    LiMDD::NodeID nid = nodes.size();
    lib[level].insert(Interval(true,nid));
    nodes.push_back(Node(true,nid));
    dead.push_back(false);
    dassert(lib[level].find(aux) != lib[level].end() && lib[level].find(aux)->getNodeID() == nid);

    //cout << " True node created with id " << lib[level].find(aux)->getNodeID() << " and interval [" << lib[level].find(aux)->getA() << ", " << lib[level].find(aux)->getB() << "]" << endl;

    return nid;
  }
  // General case:
  vector<NodeID> ch;
  vector<Interval> vi;
  li newK = currentK;
  for (li i = 0; i <= domains[level]->getMax(); i++) {
    LiMDD::NodeID n = findNode(newK, level+1);
    ch.push_back(n);
    vi.push_back(nodes[n].getInterval());
    newK-=coeffs[level];
  }
  LiMDD::NodeID nid = nodes.size();
  lib[level].insert(Interval(vi,coeffs[level], nid));
  Interval interval(vi,coeffs[level], nid);
  nodes.push_back(Node(ch,interval,level));
  dead.push_back(false);
  dassert(lib[level].find(aux) != lib[level].end() && lib[level].find(aux)->getNodeID() == nid);
  nodes[nid].intvar = domains[level];
  //cout << " Node created with id " << lib[level].find(aux)->getNodeID() << " and interval [" << lib[level].find(aux)->getA() << ", " << lib[level].find(aux)->getB() << "]. Remember: K = " << currentK << " and lvl = " << level << endl;

  return nid;
}

inline pair<set<Interval>::iterator,set<Interval>::iterator> LiMDD::getListOfNodes(uint lvl) {
  return make_pair(lib[lvl].begin(), lib[lvl].end());
}


#endif /* _MDD_ */
