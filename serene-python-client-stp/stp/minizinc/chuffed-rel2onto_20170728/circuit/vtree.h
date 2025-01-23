#ifndef __VTREE_H__
#define __VTREE_H__

#include <cassert>
#include <cstdio>
#include <vector>

class VTree {
public:
  typedef struct {
    int parent;
    int left;
    int right;
  } VNode;

  VTree(int _nvars)
      : nvars( _nvars )
  {
    VNode leaf = {
      -1,
      -1,
      -1
     };

    for( int ii = 0; ii < nvars; ii++ )
    {
      nodes.push_back(leaf);
      nodeQ.push_back(ii);
    } 
  }

  VTree(const VTree& other)
      : nvars( other.nvars ), root( other.root ), nodes( other.nodes )
  { }
 
  int pred(int n) const
  {
    return nodes[n].parent;
  }

  int meet(int a, int b) const
  {
    while( a != b )
    {
      if( a < b )
      {
        assert( nodes[a].parent != -1 );
        a = nodes[a].parent>>1;
      } else {
        assert( b < a );
        assert( nodes[b].parent != -1 );
        b = nodes[b].parent>>1;
      }
    }
    return a;
  }

  bool dir(int parent, int child) const
  {
    assert( child < parent );

    while( nodes[child].parent>>1 != parent )
      child = nodes[child].parent>>1;

    return nodes[child].parent&1;
  }

  int merge(int x, int y) {
    assert( nodes[x].parent == -1 && nodes[y].parent == -1 );
    int n_id = nodes.size();
    
    // flag indicates left child.
    nodes[x].parent = n_id<<1|1;
    nodes[y].parent = n_id<<1|0;
    
    VNode n = {
      -1,
      x,
      y
    };
    
    nodes.push_back(n);
    return n_id;
  }
  
  // State
  int nvars;
  int root;
  std::vector<int> nodeQ;

  std::vector<VNode> nodes;

  int left (int x) const { return nodes[x].left; }
  int right (int x) const { return nodes[x].right; }

  void print(void) {
    printVT(root);
    printf("\n");
#if 0
    for( int ii = 0; ii < nodes.size(); ii++ )
    {
      printf("%d: %d| %d, %d\n",ii,nodes[ii].parent, nodes[ii].left, nodes[ii].right);
    }
#endif 
  }

  void printVT(int nid) {
    if( nodes[nid].left == -1 )
    {
      printf(" %d ",nid);
    } else {
      printf("(");
      printVT(nodes[nid].left);
      printVT(nodes[nid].right);
      printf(")");
    }
  }
};

// Class for constructing the VTree.
// VTree construction:
// Process nodes [low, high), inserting output beginning at <start>.
// Returns the index after the last output node.
// <start> should always be <= <low>. Should not touch any nodes >= high.

class Merger {
public:
  virtual int operator()(VTree& vt, std::vector<int>& nodes, int low, int high, int start) = 0;
};

class RightMerger : public Merger {
public:
  RightMerger(void) { }

  int operator()(VTree& vt, std::vector<int>& nodes, int low, int high, int start) {
    int ret = nodes[high-1];

    for( int ii = high-2; ii >= low; ii-- )
    {
      ret = vt.merge(nodes[ii],ret);
    }

    nodes[start] = ret;
    return start+1;
  }
};

class BalMerger : public Merger {
public:
  BalMerger(void) { }
  int operator()(VTree& vt, std::vector<int>& nodes, int low, int high, int start) {
    int ret = merge(vt,nodes,low,high);
    nodes[start] = ret;
    return start+1;
  }

protected:
  int merge(VTree& vt, std::vector<int>& nodes, int low, int high) {
    assert( low < high );
    if( low+1 == high )
      return nodes[low];
    else
      return vt.merge( merge(vt, nodes, low, (low + high)/2),
                        merge(vt, nodes, (low + high)/2, high) );
  }
};

template <class F, class G>
class ComposeMerger : public Merger {
  public:
  ComposeMerger(const F& _f, const G& _g)
    : f( _f ), g( _g )
  {  }

  int operator()(VTree& vt, std::vector<int>& nodes, int low, int high, int start) {
    int end = g(vt,nodes,low,high,start);
    return f(vt,nodes,start,end,start);
  }

protected:
  F f;
  G g;
};

template<class F, class G>
ComposeMerger<F,G> composeMerger(F f, G g)
{
  return ComposeMerger<F,G>(f,g);
}

template <class F>
class KMerger : public Merger {
public:
  KMerger(int _k, const F& _f)
    : k( _k ), f( _f )
  { }
            
  int operator()(VTree& vt, std::vector<int>& nodes, int low, int high, int start) {
    int offset = start;
    for( int ii = low; ii < high; ii += k )
    {
      // Where does this iteration stop?
      int lim = ii + k < high ? ii + k : high;
      
      offset = f(vt, nodes, ii, lim, offset);
    }

    return offset;
  }
protected:
  int k;
  F f;
};

template<class T>
KMerger<T> kMerger(int k, T merger)
{
  return KMerger<T>(k, merger);
}

template <class T>
VTree buildVTree(T merger, int nvars)
{
  VTree vt(nvars);
  
  // Apply the merger to nodes 0..n-1.
  std::vector<int>& nodeQ = vt.nodeQ;
  int out_off = merger(vt, nodeQ, 0, nodeQ.size(), 0);

  assert( out_off == 1 );

  vt.root = nodeQ[0];
  nodeQ.clear();

  return vt;
}
#endif
