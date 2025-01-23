#include <algorithm>
#include "nnfprop.h"
#include "support/misc.h"
#include "support/heap.h"

#include "NNF.h"
#include "circuit/FDNNF.h"

#include "circuit/nnfopts.h"

#define WEAK_THRESHOLD 2

#define NODE_LOCK 1

#define EXP_ABLE 1
#define EXP_CACHED 4

#define VAL_LIVE 1
#define NEEDS_SUPP 2

#define KILLED_ABOVE 1

#define TS_MAX ((INT_MAX>>1)&(~3))

#define LEAF_VAR(x) (nodes[(x)]->out_watch>>16)
#define LEAF_VAL(x) (nodes[(x)]->out_watch&((1<<16)-1))

struct ValActGt {
  const vec<double>& activity;
  bool operator () (int x, int y) const { return activity[x] < activity[y]; }
//  bool operator () (int x, int y) const { return activity[x] > activity[y]; }
  ValActGt(const vec<double>& act) : activity(act) { }
}; 

#ifdef SORT_LITS
struct LitActGt {
//  bool operator() (Lit x, Lit y) const { return sat.activity[var(x)] < sat.activity[var(y)]; }
  bool operator() (Lit x, Lit y) const { return sat.activity[var(x)] > sat.activity[var(y)]; }
};

struct LitAgeLt {
  bool operator() (Lit x, Lit y) const { return sat.level[var(x)] < sat.level[var(y)]; }
//  bool operator() (Lit x, Lit y) const { return sat.level[var(x)] > sat.level[var(y)]; }
};
#endif

NNFProp::NNFProp(vec< IntView<> >& xs, vec<valref>& vdat, vec<noderef*>& _nodes)
    : nleaves(vdat.last().start+vdat.last().dom),
      intvars( xs ), var_data(vdat), dead_nodes( _nodes.size() ),
//      kill_dir( _nodes.size() ),
      kill_flags( _nodes.size() ),
      status( _nodes.size() ),
      watches(2*_nodes.size()),
      act_decay(1/0.95), act_inc(1), activity(nleaves),
      root(nleaves), timestamp( 0 ), n_nodes(_nodes.size()),
      nodes( _nodes )
{
#if 0
  for( int ii = 0; ii < intvars.size(); ii++ )
//    intvars[ii].attach(this, ii, EVENT_LU);
    intvars[ii].attach(this, ii, EVENT_C);
#else
  for(int ii = 0; ii < nleaves; ii++)
  {
    ((BoolView) (intvars[LEAF_VAR(ii)].getLit(LEAF_VAL(ii),1))).attach(this, ii, EVENT_U);
  }
#endif
  
  for(int ii = 0; ii < nleaves; ii++)
  {
    noderef* node(nodes[ii]);
    
    if(node->in_end == 0)
    {
      // No incoming edges.
      int var(LEAF_VAR(ii));
      int val(LEAF_VAL(ii));
      if (intvars[var].remValNotR(val))
        intvars[var].remVal(val);
    } else {
      watches[2*(node->edges[0])+1].push(ii);
    }
  }

  // Assumption for now. May change at a later date.
  for(int ii = nleaves; ii < nodes.size(); ii++)
  {
    // The root has no incoming supports.
    noderef* node(nodes[ii]);
    if(ii != root)
    {
      assert(node->in_end > 0);
      watches[2*(node->edges[0])+1].push(ii);
    }

    // This should exclude leaves.
    assert(node->out_end > node->in_end);

    watches[2*node->edges[node->in_end]].push(ii);
    if(node->type == N_AND)
    {
      for(int jj = node->in_end+1; jj < node->out_end; jj++)
      {
        watches[2*node->edges[jj]].push(ii);
      }
    }
  }
//  if( prop_id == 0 )
//    print();
  pushInQueue();

}

void NNFProp::compact(void)
{
  assert( sat.decisionLevel() == 0 );
     
  for( int nn = 0; nn < n_nodes; nn++ )
  {
    noderef* node = nodes[nn]; 
    
    int jj = 0;
    int ii = 0;
    for( ; ii < node->in_end; ii++ )
    {
      if( !dead_nodes[node->edges[ii]] )
      {
        node->edges[jj] = node->edges[ii];
        jj++;
      }
    }
    node->in_end = jj;
    
    for( ; ii < node->out_end; ii++ )
    {
      if( !dead_nodes[node->edges[ii]] )
      {
        node->edges[jj] = node->edges[ii];
        jj++;
      }
    }
    node->out_end = jj;
  }
}

bool NNFProp::propagate(void)
{
#ifdef FULL_PROP
  return fullProp();
#else
  return incProp();
#endif

//  if(sat.decisionLevel() == 0)
//    compact();

  changes.clear();
}

Clause* NNFProp::explain(Lit p, int inf)
{
#if 0
  // Backtrack to the correct time.
  Pinfo pi = p_info[inf];
  engine.btToPos(pi.btpos);
  
  vec<Lit> expln;

  // Determine which leaf we're explaining.
  unsigned int leaf = (unsigned int) pi.leaf;

#ifndef SIMPLE_REASON
#ifdef INC_REASON
  incExplain(leaf, expln);
#else  
  // Mark the nodes that must remain unreachable.
  fullExplain(leaf, expln);
#endif
#else
  // Naive explanation for debugging.
  for(unsigned int cv = 0; cv < nleaves; cv++)
  {
    if(cv != leaf)
    {
      if(!intvars[LEAF_VAR(cv)].indomain(LEAF_VAL(cv)))
      {
        bumpActivity(cv);
        expln.push(intvars[LEAF_VAR(cv)].getLit(LEAF_VAL(cv),1));
      }
    }
  }
#endif

#ifdef SORT_LITS
//  std::sort(((Lit*) expln)+1, ((Lit*) expln) + expln.size(), LitAgeLt());
  std::sort(((Lit*) expln)+1, ((Lit*) expln) + expln.size(), LitActGt());
#endif

  Clause* r = Reason_new(expln.size());
  for( int ii = 1; ii < expln.size(); ii++ )
    (*r)[ii] = expln[ii];
  (*r)[0] = p;

  return r;
#else
  return NULL;
#endif
}

Clause* NNFProp::explainConflict(void)
{
  decayActivity();

  vec<Lit> expln;
  // Mark the nodes that must remain unreachable.
  fullExplain(UINT_MAX, expln);
  
#ifdef SORT_LITS
  std::sort(((Lit*) expln)+1, ((Lit*) expln) + expln.size(), LitAgeLt());
//  std::sort(((Lit*) expln)+1, ((Lit*) expln) + expln.size(), LitActGt());
#endif

  Clause* r = Reason_new(expln.size());
  for(int ii = 0; ii < expln.size(); ii++)
    (*r)[ii] = expln[ii];

  return r;
}

//////////////////////////////
// Non-incremental propagation.
// Needs a second bottom-up pass (unlike MDDs), since for
// a node (x /\ y), we don't know if x is supported until
// we walk y.
//////////////////////////////
bool NNFProp::fullProp(void)
{
#if 0
  if( timestamp == TS_MAX )
  {
    for( int nn = 0; nn < n_nodes; nn++ )
    {
      status[nn] = 0;
    }
    timestamp = 0;
  }
  timestamp += 4;

  // Initialize bounds
  for( int ii = 0; ii < intvars.size(); ii++ )
  {
    int start = var_data[ii].start;
    for( int val = 0; val < var_data[ii].dom; val++ )
    {
      status[start+val] = timestamp;
      if( intvars[ii].indomain(val) )
        status[start+val] |= VAL_LIVE|NEEDS_SUPP;
    }
  }
  
  bool ret = fullPropMark(root)&1;
  if( !ret )
  {
    if( so.lazy )
    {
      sat.confl = explainConflict();
    }
    return false;
  }
  fullPropFix(root);
  
  BTPos pos = engine.getBTPos();
  // Collect bounds
  for( int ii = 0; ii < nleaves; ii++ )
  {
    if(status[ii]&NEEDS_SUPP)
    {
      int var(LEAF_VAR(ii));
      int val(LEAF_VAL(ii));
      if (intvars[var].remValNotR(val))
      {
          Reason r = createReason(ii);
          if(!intvars[var].remVal(val,r)) return false;
      }
    }
  }
#endif
  return true;
}

char NNFProp::fullPropMark(unsigned int n)
{
  if( status[n] >= timestamp )
    return (status[n]&1);
  
  noderef* node = nodes[n];
  
  // We assume status of root nodes has already
  // been initialized.
  assert( node->type != N_LEAF ); 
  
  char ret;
  if( node->type == N_OR )
  {
    ret = 0;
    for( int ii = node->in_end; ii < node->out_end; ii++ )
    {
      ret |= fullPropMark(node->edges[ii]);
    }
  } else {
    assert( node->type == N_AND );
    ret = 1;
    for( int ii = node->in_end; ii < node->out_end; ii++ )
    {
      if( !fullPropMark(node->edges[ii]) )
      {
        ret = 0;
        break;
       }
     }
  }
  
  status[n] = timestamp|ret;
  return ret;
}

void NNFProp::fullPropFix(unsigned int n)
{
  if(!(status[n]&1))
    return;
  
  noderef* node = nodes[n];

  if(node->type == N_LEAF)
  {
    status[n]&=(~NEEDS_SUPP); 
    return;
  }
  
  for(int ii = node->in_end; ii < node->out_end; ii++)
    fullPropFix(node->edges[ii]);

  status[n] = 0;
}

//////////////////////////////
// Incremental propagation.
// Very similar to the algorithm for MDDs, although
// death from below can still propagate downwards, and
// there's additional complexity in the watches.
//////////////////////////////
bool NNFProp::incProp(void)
{
  // kaQ/kbQ contain nodes that are *definitely* dead.
  kaQ.clear();
  kbQ.clear();

  int timestamp = dead_nodes.size()<<1;
  for(int ii = 0; ii < changes.size(); ii++)
  {
    kill_flags[changes[ii]] = timestamp;
    dead_nodes.insert(changes[ii]);
    kbQ.push(changes[ii]);
  }
  changes.clear();

  timestamp = dead_nodes.size()<<1;

  // Things killed from below may cause things to be killed from above;
  // however, things killed from above only propagate downwards.
  int ii = 0;
  while(ii < kbQ.size())
  {
    int nid(kbQ[ii]);
    int jj = 0;

    // Check all the nodes where this is a
    // necessary child.
    vec<int>& out_ws(watches[2*nid]);
    for(int ww = 0; ww < out_ws.size(); ww++)
    {
      // Node that we're testing.
      // Check if it has any alternative children.
      int cid(out_ws[ww]);
      if(dead_nodes.elem(cid))
      {
        out_ws[jj++] = cid;
        continue;
      }

      noderef* cnode(nodes[cid]);

      if(cnode->type == N_OR)
      {
        for(int ii = cnode->in_end; ii < cnode->out_end; ii++)
        {
          if(!dead_nodes.elem(cnode->edges[ii]))
          {
            // New watch found.
            watches[2*cnode->edges[ii]].push(cid);
            goto out_wfound;
          }
        }
      } else {
        // For an AND node, we record the killing node
        // in the out_watch slot.
        cnode->out_watch = nid;
      }
      dead_nodes.insert(cid);
      kill_flags[cid] = timestamp;
      kbQ.push(cid);
      out_ws[jj++] = cid;
out_wfound:
      continue;
    }
    out_ws.resize(jj);

    // If it's an AND node, we need to kill the living
    // children as well.
    if(nodes[nid]->type == N_AND)
      kaQ.push(nid);

    ii++;
  }

  if(dead_nodes.elem(root))
  {
    if(so.lazy)
    {
      sat.confl = explainConflict();
    }
    return false;
  }

  ii = 0;
  while(ii < kaQ.size())
  {
    int nid(kaQ[ii]);
//    assert(nid < nodes.size());

    if(nid < nleaves)
    {
      // Leaf node: propagate the relevant value.
      int var(LEAF_VAR(nid));
      int val(LEAF_VAL(nid));
      if (intvars[var].remValNotR(val))
      {
#if 0
          Reason r = createReason(nid);
          if(!intvars[var].remVal(val,r)) return false;
#endif
      }
    }

    int jj = 0;
    vec<int>& in_ws(watches[2*nid+1]);
    for(int ww = 0; ww < in_ws.size(); ww++)
    {
      // Node that we're testing.
      // Check if it has any alternative parents.
      int cid(in_ws[ww]);
      if(dead_nodes.elem(cid))
      {
        in_ws[jj++] = cid;
        continue;
      }

      noderef* cnode(nodes[cid]);
      for(int ii = 0; ii < cnode->in_end; ii++)
      {
        if(!dead_nodes.elem(cnode->edges[ii]))
        {
          // New watch found.
          watches[2*cnode->edges[ii]+1].push(cid);
          goto in_wfound;
        }
      }
      // Watch not found.
      dead_nodes.insert(cid);
      kaQ.push(cid);
      kill_flags[cid] = timestamp|KILLED_ABOVE;

      in_ws[jj++] = cid;
in_wfound:
      continue;
    }
    in_ws.resize(jj);

    ii++;
  }

  return true;
}

//////////////////////////////
// Non-incremental explanation
// Follows a similar structure to MDDs.
//////////////////////////////

// Status is [<---k--->|L], where k is the number
// of children keeping the node unsatisfiable.
// If the node is satisfiable under the current assignment,
// status == 1.
// L is true if the circuit rooted from n must remain unsatisfiable
// for the whole ciruit to remain so.

// Each time a child becomes satisfiable, 
void NNFProp::initLock(void)
{
  for(int ii = 0; ii < n_nodes; ii++)
  {
    switch(nodes[ii]->type)
    {
      case N_AND:
        status[ii] = 2*(nodes[ii]->out_end - nodes[ii]->in_end);
        break;

      case N_LEAF:
      case N_OR:
        status[ii] = 2;
        break;
    }
  }
}

void NNFProp::setLock(unsigned int node)
{
  if(status[node]&1)
    return;

  assert(status[node] > 0);
  
  status[node] |= 1;

  // Locks propagate purely upwards.
  switch(nodes[node]->type)
  {
    case N_LEAF:
      break;

    case N_AND:
      // Exactly one un-fixed.
      if(status[node] == 3)
      {
        for(int ii = nodes[node]->in_end; ii < nodes[node]->out_end; ii++)
        {
          if(status[nodes[node]->edges[ii]])
            setLock(nodes[node]->edges[ii]);
        }
      }
      break;

    case N_OR:
      for(int ii = nodes[node]->in_end; ii < nodes[node]->out_end; ii++)
      {
        setLock(nodes[node]->edges[ii]);
      }
      break;
  }
}

void NNFProp::unFix(unsigned int node)
{
  // Already unfixed.
  if(!status[node])
    return;
  
  // Determine whether we propagate upwards.
  status[node] -= 2; // Decrement supports.
  if(status[node] < 2) // None remaining?
  {
    assert(!(status[node]&1));
    for(int ii = 0; ii < nodes[node]->in_end; ii++)
    {
      unFix(nodes[node]->edges[ii]); 
    }
  } else if(status[node] == 3) {
    // Locked, with one path remaining false.
    assert(nodes[node]->type == N_AND);
    for(int ii = nodes[node]->in_end; ii < nodes[node]->out_end; ii++)
    {
      if(status[nodes[node]->edges[ii]])
      {
        setLock(nodes[node]->edges[ii]);
      }
    }
  }
}

void NNFProp::fullExplain(unsigned int leaf, vec<Lit>& expln)
{
  initLock();
  if(leaf < UINT_MAX)
  {
    unFix(leaf);
    bumpActivity(leaf);
    expln.push(intvars[LEAF_VAR(leaf)].getLit(LEAF_VAL(leaf),0));
  }
  
  setLock(root);

  int lvar = leaf < UINT_MAX ? LEAF_VAR(leaf) : INT_MAX;
#ifndef WEAKEN
  vec<unsigned int> valQ;
  for(int cv = 0; cv < nleaves; cv++)
  {
//    if(cv == leaf)
    if(LEAF_VAR(cv) == lvar)
      continue;
     
    if(intvars[LEAF_VAR(cv)].indomain(LEAF_VAL(cv)))
    {
      unFix(cv);
    } else {
      valQ.push(cv);
    }
  }

#ifdef USE_ACT
  ValActGt sorter(activity);
  std::sort((unsigned int*) valQ, (unsigned int*) valQ + valQ.size(), sorter);
#endif

  for(int li = 0; li < valQ.size(); li++)
  {
    unsigned int cv = valQ[li];

    if(status[cv]&NODE_LOCK)
    {
      bumpActivity(cv);
      expln.push(intvars[LEAF_VAR(cv)].getLit(LEAF_VAL(cv),1));
    } else {
      unFix(cv);
    }
  }
#else
  vec< vec<unsigned int> > valQ;

  // Alternative version -- variable-by-variable, using positive literals.
  for(int vv = 0; vv < var_data.size(); vv++)
  {
    valQ.push();

    if(vv == lvar)
    {
      continue;
    } else {
      unsigned int vleaf = var_data[vv].start;
      for(int vi = 0; vi < var_data[vv].dom; vi++, vleaf++)
      {
        assert(LEAF_VAR(vleaf) == vv);
        assert(LEAF_VAL(vleaf) == vi);
        if(intvars[vv].indomain(vi))
        {
          unFix(vleaf);
        } else {
          valQ[vv].push(vleaf); 
        }
      }
    }
  }

  assert(var_data.size() == valQ.size());
  for(int vv = 0; vv < var_data.size(); vv++)
  {
    if(vv == lvar)
      continue;

#if 1
    int count = 0;

    if(intvars[vv].isFixed())
    {
      for(int vi = 0; vi < valQ[vv].size(); vi++)
      {
        unsigned int vleaf(valQ[vv][vi]);
        if(status[vleaf]&NODE_LOCK)
        {
          count++;
          if(count >= WEAK_THRESHOLD)
            break;
        }
      }
    }

    if(count >= WEAK_THRESHOLD)
    {
      expln.push(intvars[vv].getValLit());
    } else {
      for(int vi = 0; vi < valQ[vv].size(); vi++)
      {
        unsigned int vleaf(valQ[vv][vi]);
        assert(LEAF_VAR(vleaf) == vv);

        if(status[vleaf]&NODE_LOCK)
        {
          bumpActivity(vleaf);
          expln.push(intvars[vv].getLit(LEAF_VAL(vleaf),1));
        } else {
          unFix(vleaf);
        }
      }
    }
#else
    int lb(intvars[vv].getMin());
    int ub(intvars[vv].getMax());

    vec<unsigned int> below;
    vec<unsigned int> below_ok;

    vec<unsigned int> between;
    
    vec<unsigned int> above;
    vec<unsigned int> above_ok;

    int vi = 0;
    for(; vi < valQ[vv].size() && LEAF_VAL(valQ[vv][vi]) < lb; vi++)
    {
      unsigned int vleaf(valQ[vv][vi]);
      if(status[vleaf]&NODE_LOCK)
      {
        below.push(vleaf);
      } else {
        below_ok.push(vleaf);
      }
    }
    if(below.size() > 2)
    {
      expln.push(intvars[vv].getMinLit());
    } else {
      for(int ii = 0; ii < below.size(); ii++)
      {
        bumpActivity(below[ii]);
        expln.push(intvars[vv].getLit(LEAF_VAL(below[ii]),1));
      }
      for(int ii = 0; ii < below_ok.size(); ii++)
        unFix(below_ok[ii]);
    }
    
    for(; vi < valQ[vv].size() && LEAF_VAL(valQ[vv][vi]) <= ub; vi++)
    {
      unsigned int vleaf(valQ[vv][vi]);
      if(status[vleaf]&NODE_LOCK)
      {
        bumpActivity(vleaf);
        expln.push(intvars[vv].getLit(LEAF_VAL(vleaf),1));
      } else {
        unFix(vleaf);
      }
    }

    for(; vi < valQ[vv].size(); vi++)
    {
      unsigned int vleaf(valQ[vv][vi]);
      if(status[vleaf]&NODE_LOCK)
      {
        above.push(vleaf);
      } else {
        above_ok.push(vleaf);
      }
    }
    if(above.size() > 2)
    {
      expln.push(intvars[vv].getMaxLit());
    } else {
      for(int ii = 0; ii < above.size(); ii++)
      {
        bumpActivity(above[ii]);
        expln.push(intvars[vv].getLit(LEAF_VAL(above[ii]),1));
      }
      for(int ii = 0; ii < above_ok.size(); ii++)
        unFix(above_ok[ii]);
    }
#endif
  }

#endif
//  printf("!%d\n",expln.size());
}

/////////////////////////////
// Incremental explanation.
/////////////////////////////
void NNFProp::incExplain(unsigned int leaf, vec<Lit>& expln)
{
  SparseSet<> explQ(nodes.size());

  bumpActivity(leaf);
  expln.push(intvars[LEAF_VAR(leaf)].getLit(LEAF_VAL(leaf),0));

  // Need to explain each of the incoming nodes.
  for(int ii = 0; ii < nodes[leaf]->in_end; ii++)
  {
    explQ.insert(nodes[leaf]->edges[ii]);
  }
  
#ifdef WEAKEN
  vec< vec<Lit> > explV(intvars.size());
#endif

  for(unsigned int el = 0; el < explQ.size(); el++)
  {
    int nID(explQ[el]);
    noderef* node(nodes[nID]);
    
    if(node->type == N_LEAF)
    {
      bumpActivity(nID);
#ifdef WEAKEN
      explV[LEAF_VAR(nID)].push(intvars[LEAF_VAR(nID)].getLit(LEAF_VAL(nID), 1));
#else
      expln.push(intvars[LEAF_VAR(nID)].getLit(LEAF_VAL(nID),1));
#endif
      continue;
    }

    if(kill_flags[nID]&KILLED_ABOVE)
    {
      for(int ii = 0; ii < node->in_end; ii++)
      {
        if(!explQ.elem(node->edges[ii]))
          explQ.insert(node->edges[ii]);
      }
    } else {
      if(node->type == N_AND)
      {
        if(!explQ.elem(node->out_watch))
          explQ.insert(node->out_watch);
      } else {
        assert(node->type == N_OR);
        for(int ii = node->in_end; ii < node->out_end; ii++)
        {
          if(!explQ.elem(node->edges[ii]))
            explQ.insert(node->edges[ii]);
        }
      }
    }
  }
#ifdef WEAKEN
  int lvar = LEAF_VAR(leaf);
  for(int vv = 0; vv < explV.size(); vv++)
  {
    if(vv == lvar)
      continue;

    if(intvars[vv].isFixed() && explV[vv].size() >= WEAK_THRESHOLD)
    {
      expln.push(intvars[vv].getValLit());
    } else {
      for(int vi = 0; vi < explV[vv].size(); vi++)
        expln.push(explV[vv][vi]);
    }
  }
#endif
}

void NNFProp::print(void)
{
  assert( 0 );
#if 0
  for( int ii = 0; ii < nodes.size(); ii++ )
  {
    printf("%d (%d) ", ii, status[ii]);
    for( int jj = nodes[ii]->in_end; jj < nodes[ii]->out_end; jj++ )
    {
      int eid = nodes[ii]->edges[jj].id;
      printf("| [%d,%d] -> %d ",edges[eid].lb, edges[eid].ub, edges[eid].end);
    }
    printf("\n");
  }
#endif
}

//==================================
// NNF datastructure initialization
//==================================
static noderef* mk_noderef(NodeT type, vec<unsigned int>& in, vec<unsigned int>& out)
{
  noderef* node = (noderef*) malloc(sizeof(noderef) + sizeof(unsigned int)*(in.size() + out.size() - 1));
  
  node->type = type; 

  int ii = 0; 
  node->in_watch = in.size() > 0 ? in[0] : -1;
  for( ; ii < in.size(); ii++ )
  {
    node->edges[ii] = in[ii];
  }
  node->in_end = ii;

  
  node->out_watch = out.size() > 0 ? out[0] : -1;
  for( int jj = 0; jj < out.size(); ii++, jj++ )
  {
    node->edges[ii] = out[jj];
  }
  node->out_end = ii;
  
  return node;
}

void NNFCompile(FDNNFTable& t, _FDNNF root, vec<int>& dom,
        vec<valref>& vdat, vec<noderef*>& noderefs)
{
  // Assume NNF is not a leaf node.
  assert( !(root&1) );

//  root = t.expand(0, root);
//  t.print_mdd(root);
  // Add code to ensure N = A \/ B => Vars(A) == Vars(B).
  // (Adding redundant x \/ ~x nodes, or additional T(x) terminals).

  const std::vector<FDNNFNode>& nodes(t.getNodes());
  std::vector<int>& status(t.getStatus());

  vec<NodeT> node_type;
  vec< vec<unsigned int> > node_parents;
  vec< vec<unsigned int> > node_children;
  
//  for( int ii = 2; ii < status.size(); ii++ )
//    assert( status[ii] == 0 );

  int nextid = 1; // Actually the status value. (so we don't need to add 1)
  // Leaf nodes.
  for( int vd = 0; vd < dom.size(); vd++ )
  {
    valref vr = {
      nextid-1,
      dom[vd]
     };
    vdat.push(vr);

    for(int val = 0; val < dom[vd]; val++)
    {
      node_type.push(N_LEAF);
      node_parents.push();
      node_children.push();
    }
    nextid += dom[vd];
  }

  // Handling a given edge.
  vec<int> node_queue;

  node_queue.push(root>>1);
  status[root>>1] = nextid;
  nextid++;
  
  // Root node.
  node_type.push( (nodes[root>>1]->type == FDNNF_AND) ? N_AND : N_OR );
  node_parents.push();
  node_children.push();
  
  // Build the node->edge and var->edge mappings.
  int qindex = 0;
  while( qindex < node_queue.size() )
  {
    int node = node_queue[qindex];
    int nodeid = status[node]-1;
    
    FDNNFNode nodeptr = nodes[node];
    
    // Edges that are strictly within [lb, ub].
    for(unsigned int jj = 0; jj < nodeptr->sz; jj++)
    {
      _FDNNF child(nodeptr->args[jj]);
      unsigned int dest;
      if(child&1) 
      {
        assert((int) FDNNF_VAL(child) < (int) dom[FDNNF_VAR(child)]);
        dest = vdat[FDNNF_VAR(child)].start + FDNNF_VAL(child);
      } else {
        // Introduce new edge for values [lval,edges[jj].val) from node to ldest.
        if( !status[child>>1] )
        {
          // Initialise the node.
          node_queue.push(child>>1);
          node_type.push( (nodes[child>>1]->type == FDNNF_AND) ? N_AND : N_OR );
          node_children.push();
          node_parents.push();
          
          status[child>>1] = nextid;
          nextid++;
        }
        dest = status[child>>1]-1;
      }
        
      node_children[nodeid].push(dest);
      node_parents[dest].push(nodeid);
    }
    qindex++;
  }

  for(int i = 0; i < node_queue.size(); i++ )
  {
    status[node_queue[i]] = 0;
  }

  // Collapse the structures.
  assert( node_type.size() == node_children.size()
       && node_type.size() == node_parents.size() );
  for( int ii = 0; ii < node_type.size(); ii++ )
  {
    noderefs.push( mk_noderef( node_type[ii] , node_parents[ii], node_children[ii]) );
  }

  for(int vv = 0; vv < vdat.size(); vv++)
  {
    int start = vdat[vv].start;
    for(int val = 0; val < vdat[vv].dom; val++)
      noderefs[start+val]->out_watch = (vv<<16)|val;
  }
}

NNFProp* newNNF(FDNNF r, vec< IntView<> >& xs)
{
  vec<noderef*> nodedata;
  vec<valref> vdat;
  
  vec<int> dom;
  for(int ii = 0; ii < xs.size(); ii++)
    dom.push(xs[ii].getMax()+1);

  NNFCompile(*(r.table), r.val, dom, vdat, nodedata);
  return new NNFProp(xs, vdat, nodedata);
}

void addNNF(vec<IntVar*>& xs, FDNNF r)
{
   vec< IntView<> > ws;

   for (int i = 0; i < xs.size(); i++) xs[i]->specialiseToEL();
   for (int i = 0; i < xs.size(); i++) ws.push(IntView<>(xs[i],1,0));
   

   newNNF(r, ws); 
}
