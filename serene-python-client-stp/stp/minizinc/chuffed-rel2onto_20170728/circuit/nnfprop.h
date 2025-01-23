#ifndef __NNFPROP_H__
#define __NNFPROP_H__

#include <utility>

#include "core/propagator.h"
#include "vars/int-view.h"
#include "support/misc.h"
#include "support/sparse_set.h"
#include "support/BVec.h"
#include <climits>

#include "FDNNF.h"

enum NodeT { N_AND, N_OR, N_LEAF };

typedef struct {
  NodeT type;
  int in_watch;
  int out_watch;

  int in_end;
  int out_end;
  unsigned int edges[1];
} noderef;

enum KillDir { K_BELOW = 1, K_ABOVE = 2, K_DOM = 3 };
enum InfType { INF_LB = 0, INF_UB = 1 };

typedef struct {
  int start;
  int dom;
} valref;

class NNFProp : public Propagator {
#if 0
  // structure to store propagation info for lazy explanation
  struct Pinfo {
    BTPos btpos;                               // backtrack point
    int leaf;                         // which leaf node is eliminated
    Pinfo(BTPos p, int l) : btpos(p), leaf(l) {}
    };
  vec<Pinfo> p_info;
#endif
  bool trailed_pinfo_sz;
public:
  NNFProp(vec< IntView<> >& xs, vec<valref>& vdat, vec<noderef*>& _node_data);
    
  // Wake up only parts relevant to this event
  void wakeup(int i, int c) {
//    assert(c&EVENT_U);
    if(!dead_nodes.elem(i))
    {
      changes.push(i);

      pushInQueue();
    }
  }
  
  // Propagate woken up parts
  bool propagate();
  Clause* explain(Lit p, int inf);
  Clause* explainConflict();
  
  void compact(); // Should only be called at decision level 0.

  // Clear intermediate states
  void clearPropState() {
    changes.clear();
    in_queue = false;
  }
  
  void toTikz(void);
   
private:
  bool fullProp();
  char fullPropMark(unsigned int);
  void fullPropFix(unsigned int n);

  bool incProp();
  
//  inline void killNode(int node, KillDir dir);
  
  // Non-incremental explanation.
  void fullExplain(unsigned int leaf, vec<Lit>& expln);
  void initLock(void);
  void setLock(unsigned int n);
  void unFix(unsigned int n);

  // Incremental explanation
  void incExplain(unsigned int leaf, vec<Lit>& expln);

  void print();

  // Create a Reason for a lazily explained bounds change
#if 0
  Reason createReason(int leaf) {
    if (!trailed_pinfo_sz) {
      engine.trail.last().push(TrailElem(&p_info._size(), 4));
      trailed_pinfo_sz = true;
    }
    p_info.push(Pinfo(engine.getBTPos(), leaf));
    return Reason(prop_id, p_info.size()-1);
  }
  Reason createReason(BTPos pos, int leaf) {
    if (!trailed_pinfo_sz) {
      engine.trail.last().push(TrailElem(&p_info._size(), 4));
      trailed_pinfo_sz = true;
    }
    p_info.push(Pinfo(pos, leaf));
    return Reason(prop_id, p_info.size()-1);
  }
#endif
  // Data
  int nleaves;
  vec< IntView<> > intvars;
  vec<valref> var_data;

//  TBitVec dead_nodes;
  TrailedSet dead_nodes;
  
//  ValVec<unsigned int, 2> kill_dir;
  // Kill flags: {--------------|X}
  //                death time   ^above/below.
  vec<int> kill_flags;
  vec<int> status;
   
  vec< vec<int> > watches;

  double act_decay;
  double act_inc;
  vec<double> activity;
  void bumpActivity(int val) { activity[val] += act_inc; }
  void decayActivity(void) { act_inc *= act_decay; }

  // Intermediate state
  vec<int> changes;
   
  vec<int> kaQ; // Queues of nodes that need processing.
  vec<int> kbQ; 
    
  int root;
  int timestamp;
  
  int n_nodes; 
  vec<noderef*> nodes;
};

void NNFCompile(FDNNF root, vec< IntView<> > xs,
        vec<noderef*>& noderefs);
NNFProp* newNNF(FDNNF r, vec< IntView<> >& xs);
void addNNF(vec<IntVar*>& xs, FDNNF r);
#endif
