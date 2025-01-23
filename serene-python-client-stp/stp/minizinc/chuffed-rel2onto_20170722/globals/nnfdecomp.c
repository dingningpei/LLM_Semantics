#include "core/propagator.h"
#include "circuit/FDNNF.h"

enum NodeT { N_AND, N_OR, N_LEAF };

typedef struct {
  int start;
  int dom; 
} valref;

static void nnf_extract(FDNNF r, const vec<int>& dom, vec<valref>& vdat,
      vec<NodeT>& node_type, vec< vec<unsigned int> >& node_parents,
      vec< vec<unsigned int> >& node_children);

static Lit nnf_decompR(vec<IntVar*>& xs, vec<Lit>& cache, std::vector<int>& status, const std::vector<FDNNFNode>& nodes, _FDNNF node);

void nnf_decomp(vec<IntVar*>& xs, FDNNF r)
{
  vec<Lit> cache;
  Lit rv = nnf_decompR(xs, cache, r.table->getStatus(), r.table->getNodes(), r.val);

  r.table->clear_status(r.val);
  sat.enqueue(rv);
}

static Lit nnf_decompR(vec<IntVar*>& xs, vec<Lit>& cache, std::vector<int>& status, const std::vector<FDNNFNode>& nodes, _FDNNF node)
{
  if( node&1 )
  {
    int var = FDNNF_VAR(node);
    int val = FDNNF_VAL(node);
    return xs[var]->getLit(val, (node&2) ? 1 : 0);
  }

  int n_id( node>>1 );
  if( status[n_id] )
    return cache[status[n_id]-1];
  
  FDNNFNode n( nodes[n_id] );
  Lit nv = Lit(sat.newVar(),1);
#if 0
  sat.flags[var(nv)].setUIPable(false);
  sat.flags[var(nv)].setLearnable(false);
#endif

  cache.push(nv);
  status[n_id] = cache.size();

  vec<Lit> cl;
  if( n->type == FDNNF_OR )
  {
    cl.push(~nv);
    for( unsigned int ii = 0; ii < n->sz; ii++ )
    {
      Lit cv = nnf_decompR(xs, cache, status, nodes, n->args[ii]);
//      sat.addClause(nv,~cv);

      cl.push(cv);
    }
    sat.addClause(cl);
  } else if( n->type == FDNNF_AND ) {
//    cl.push(nv);
    for( unsigned int ii = 0; ii < n->sz; ii++ )
    {
      Lit cv = nnf_decompR(xs, cache, status, nodes, n->args[ii]);
      sat.addClause(~nv,cv);

//      cl.push(~cv);
    }
//    sat.addClause(cl);
  }
  return nv;
}

void nnf_decompGAC(vec<IntVar*>& xs, FDNNF r)
{
  vec<NodeT> node_type;
  vec<valref> vdat;
  vec< vec<unsigned int> > node_parents;
  vec< vec<unsigned int> > node_children;

  vec<int> dom;
  for(int ii = 0; ii < xs.size(); ii++)
  {
    dom.push(xs[ii]->getMax()+1);
  }

  // Calculate parent/child information for the graph.  
  nnf_extract(r, dom, vdat, node_type, node_parents, node_children);

  int nleaves(vdat.last().start + vdat.last().dom);

  // Now we construct the decomposition.
  vec<Lit> nodevars; 
  for(int vv = 0; vv < vdat.size(); vv++)
  {
    for(int val = 0; val < vdat[vv].dom; val++)
      nodevars.push(xs[vv]->getLit(val,1));
  }
  assert(nleaves == nodevars.size());

  for(int ii = nleaves; ii < node_type.size(); ii++ )
  {
    nodevars.push(Lit(sat.newVar(),1));
#if 0
    sat.flags[var(nodevars.last())].setUIPable(false);
    sat.flags[var(nodevars.last())].setLearnable(false);
#endif
  }

  // Leaf nodes 
  for(int nn = 0; nn < nleaves; nn++)
  {
    // Parent nodes.
    vec<Lit> par;
    par.push(~nodevars[nn]);
    for(int ii = 0; ii < node_parents[nn].size(); ii++)
      par.push(nodevars[node_parents[nn][ii]]); 
    sat.addClause(par);
  }

  // Root node (only has children)
  vec<Lit> chl;
  unsigned int rn(nleaves);
  if(node_type[rn] == N_AND)
  {
//    chl.push(nodevars[rn]);
    for(int ii = 0; ii < node_children[rn].size(); ii++)
    {
      sat.addClause(~nodevars[rn], nodevars[node_children[rn][ii]]);
//      chl.push(~nodevars[node_children[rn][ii]]);
    }
//    sat.addClause(chl);
  } else {
    assert(node_type[rn] == N_OR);

    chl.push(~nodevars[rn]);
    for(int ii = 0; ii < node_children[rn].size(); ii++)
    {
//      sat.addClause(nodevars[rn], ~nodevars[node_children[rn][ii]]);
      chl.push(nodevars[node_children[rn][ii]]);
    }
    sat.addClause(chl);
  }
 
  // Other nodes.
  for(int nn = nleaves+1; nn < node_type.size(); nn++)
  {
    // Parent nodes.
    assert(node_parents[nn].size() > 0);
    vec<Lit> par;
    par.push(~nodevars[nn]);
    for(int ii = 0; ii < node_parents[nn].size(); ii++)
      par.push(nodevars[node_parents[nn][ii]]); 
    sat.addClause(par);
    
    // Child nodes
    chl.clear();
    if(node_type[nn] == N_AND)
    {
//      chl.push(nodevars[nn]);
      for(int ii = 0; ii < node_children[nn].size(); ii++)
      {
        sat.addClause(~nodevars[nn], nodevars[node_children[nn][ii]]);
//        chl.push(~nodevars[node_children[nn][ii]]);
      }
//      sat.addClause(chl);
    } else {
      assert(node_type[nn] == N_OR);

      chl.push(~nodevars[nn]);
      for(int ii = 0; ii < node_children[nn].size(); ii++)
      {
//        sat.addClause(nodevars[nn], ~nodevars[node_children[nn][ii]]);
        chl.push(nodevars[node_children[nn][ii]]);
      }
      sat.addClause(chl);
    }
  }

  vec<Lit> cl;
  cl.push(nodevars[nleaves]);
  sat.addClause(cl);
}

static void nnf_extract(FDNNF r, const vec<int>& dom,
      vec<valref>& vdat,
      vec<NodeT>& node_type,
      vec< vec<unsigned int> >& node_parents,
      vec< vec<unsigned int> >& node_children)
{
  FDNNFTable& t(*(r.table));
  _FDNNF root(r.val);

  // Assume NNF is not a leaf node.
  assert( !(root&1) );

//  root = t.expand(0, root);
//  t.print_mdd(root);
  // Add code to ensure N = A \/ B => Vars(A) == Vars(B).
  // (Adding redundant x \/ ~x nodes, or additional T(x) terminals).

  const std::vector<FDNNFNode>& nodes(t.getNodes());
  std::vector<int>& status(t.getStatus());

  for( unsigned int ii = 0; ii < status.size(); ii++ )
    assert( status[ii] == 0 );

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
  
  int qindex = 0;
  while( qindex < node_queue.size() )
  {
    int node = node_queue[qindex];
    int nodeid = status[node]-1;
    
    FDNNFNode nodeptr = nodes[node];
    
    for(unsigned int jj = 0; jj < nodeptr->sz; jj++)
    {
      _FDNNF child(nodeptr->args[jj]);
      unsigned int dest;
      if(child&1) 
      {
        assert(FDNNF_VAL(child) < (unsigned int) dom[FDNNF_VAR(child)]);
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

          assert(node_type.size() == nextid);
          
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
}
