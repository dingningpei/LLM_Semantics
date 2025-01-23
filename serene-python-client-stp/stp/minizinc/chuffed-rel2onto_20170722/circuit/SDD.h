#ifndef ___SDD_H__
#define ___SDD_H__

#define USE_MURMURHASH
// #define USE_MAP

#include <climits>
#include <cassert>

#include <map>

#include <ext/hash_map>

#include <vector>

#include "mdd/opcache.h"
#include "vtree.h"

#ifdef USE_MURMURHASH
#include "mdd/MurmurHash3.h"
#endif

typedef unsigned int _SDD;

// _SDD node format: vnode #parts {(p_0, r_0), (p_1, r_1), ..., (p_k, r_k)}
// Leaves are encoded in the _SDD ids.
// leaf: [---------------|xx|1]
//            {vnode}   {flag}
// Flag: { bot = 00, x = 10, ~x = 01, top = 11 }
// Branch: [-----------------|0]
//         {       id        }

// Questions to be resolved:
// - How to represent variables?
// - How to input the v-tree?

typedef struct {
  _SDD left;
  _SDD right; 
} SDDPart;

typedef struct {
  unsigned int vnode;
  unsigned int sz;
  
  SDDPart parts[1];
} SDDNodeEl;

typedef SDDNodeEl* SDDNode;

#define LEAF 1
#define NEG 2
#define POS 4

#define FLAGS (POS|NEG|LEAF)
#define TTT (POS|NEG|LEAF)
#define FFF LEAF

struct sdd_eqnode
{
  bool operator()(const SDDNode a1, const SDDNode a2) const
  {
    if( a1->vnode != a2->vnode )
      return false;
    if( a1->sz != a2->sz )
      return false;

    for( unsigned int ii = 0; ii < a1->sz; ii++ )
    {
      if( a1->parts[ii].left != a2->parts[ii].left || a1->parts[ii].right != a2->parts[ii].right )
        return false;
    }
    return true;
  }
};

// Construct a better hash function. Seriously. Use MurmurHash3.
struct sdd_hashnode
{
  unsigned int operator()(const SDDNode a1) const
  {
#ifdef USE_MURMURHASH
    // Using the vnode as a seed. Probably dubious.
    uint32_t ret;
    MurmurHash3_x86_32(a1->parts, sizeof(SDDPart)*a1->sz, a1->vnode, &ret);
    return ret;
#else
    unsigned int hash = 5381;
    
    hash = ((hash << 5) + hash) + a1->vnode; 
    hash = ((hash << 5) + hash) + a1->sz;

    for(unsigned int ii = 0; ii < a1->sz; ii++)
    {
      hash = ((hash << 5) + hash) + a1->parts[ii].left;
      hash = ((hash << 5) + hash) + a1->parts[ii].right;
    }
    return (hash & 0x7FFFFFFF);
#endif
  }
};

typedef __gnu_cxx::hash_map<const SDDNode, int, sdd_hashnode, sdd_eqnode> NodeCache;

class SDDTable;

class SDD {
public:
  SDD(SDDTable* _table, _SDD _val)
    : table( _table ), val( _val )
  {  }
  
  SDD(void)
    : table(NULL), val(-1)
  {  } 
#if 0
  SDD(const SDD& other)
    : table(other.table), val(other.val)
  {  }

  SDD& operator=(const SDD& other) {
    table = other.table;
    val = other.val;
    return *this;
  }
#endif

  void print_dot(bool reduce = true);

  SDDTable* table;
  _SDD val;
};

class SDDTable
{
public:
  enum SDDOp { OP_AND, OP_OR, OP_NOT, OP_IFF, OP_XOR, OP_EXIST };

protected:
#if 0
  class OpCache
  {
  public:

    OpCache(unsigned int size);
    ~OpCache(void);
    
    unsigned int check(char op, unsigned int a, unsigned int b); // Returns UINT_MAX on failure.
    void insert(char op, unsigned int a, unsigned int b, unsigned int res);
    
    typedef struct {
      unsigned int hash;
      char op;
      unsigned int a;
      unsigned int b;
      unsigned int res;
    } cache_entry;

  private:
    inline unsigned int hash(char op, unsigned int a, unsigned int b);
    
    // Implemented with sparse-array stuff. 
    unsigned int tablesz;

    unsigned int members;
    unsigned int* indices;
    cache_entry* entries;
  };
#endif
public:
  SDDTable(const VTree& vtree);
  ~SDDTable(void);
  
  const std::vector<SDDNode>& getNodes(void)
  {
     return nodes;
  }

  std::vector<int>& getStatus(void)
  {
     return status;
  }
  
  // Convert the SDD to some other circuit. 
  template<class F> F convert(F fff, F ttt, std::vector<F>& vars, _SDD root);
  template<class F> F convertR(F fff, F ttt, std::vector<F>& vars, std::vector<F>& cache, _SDD root);
   
  void clear_status(_SDD r);

  void show_node(_SDD r);
  void print_node(_SDD r);
  void print_nodes(void);   
  void print(_SDD r);
  void pprint(_SDD r);
  void pprint_rec(_SDD r);
  void print_tikz(_SDD r);
  void print_dot(_SDD r, bool reduce = false);

  int sdd_sz(_SDD r, bool reduce = false);
#if 1
  int cache_sz(void)
  {
    return cache.size();
  }
#endif

  _SDD insert(unsigned int vnode, unsigned int start);
  
  SDD ttt(void) { return sdd_true(); } 
  SDD fff(void) { return sdd_false(); } 
  SDD sdd_true(void) { return SDD(this,_sdd_true()); }
  SDD sdd_false(void) { return SDD(this,_sdd_false()); }
  _SDD _sdd_true(void);
  _SDD _sdd_false(void);
  
  SDD var(int var) { return SDD(this, _sdd_var(var)); }
  _SDD _sdd_var(int var);
  _SDD sdd_apply(SDDOp op, _SDD a, _SDD b);

  _SDD normalize(int vnode, _SDD a); // Normalize to a given vtree node.

  _SDD leaf_apply(SDDOp op, _SDD a, _SDD b);
  _SDD sdd_not(_SDD);

  _SDD sdd_exist(_SDD, unsigned int);

  const VTree& vtree;
  
private:
  inline SDDNode allocNode(int sz);
  inline void deallocNode(SDDNode node);
  
  inline int vnode(_SDD r)
  {
    if( r&1 )
      return r>>3;
    else
      return nodes[r>>1]->vnode;  
  }

  int nvars;
  
  OpCache opcache;
  NodeCache cache;
  
  std::vector<SDDPart> stack;
  unsigned int intermed_maxsz;
  SDDNode intermed;

  std::vector<SDDNode> nodes;
  std::vector<int> status;
};

SDD operator|(const SDD& a, const SDD& b);
SDD operator&(const SDD& a, const SDD& b);
SDD operator^(const SDD& a, const SDD& b);
SDD operator~(const SDD& a);
SDD sdd_iff(const SDD& a, const SDD& b);


// Convert the SDD to some other circuit. 
template<class F>
F SDDTable::convert(F fff, F ttt, std::vector<F>& vars, _SDD node)
{
  std::vector<F> cache;
  F ret( convertR(fff,ttt,vars,cache,node) );
  clear_status(node);
  return ret;
}

template<class F>
F SDDTable::convertR(F fff, F ttt, std::vector<F>& vars, std::vector<F>& cache, _SDD node)
{
  if( node&LEAF )
  {
    switch(node&FLAGS)
    {
      case TTT:
        return ttt;
      case FFF:
        return fff;

      case (POS|LEAF):
        return vars[node>>3];
      case (NEG|LEAF):
        return ~vars[node>>3];

      default:
        assert(0);
        break;
    }
  }

  int n_id = node>>1;
  if( status[n_id] != 0 )
  {
    return cache[status[n_id]-1];
  }
  
  F ret = fff;
  for( unsigned int ii = 0; ii < nodes[n_id]->sz; ii++ )
  {
    F left = convertR(fff, ttt, vars, cache, nodes[n_id]->parts[ii].left);
    F right = convertR(fff, ttt, vars, cache, nodes[n_id]->parts[ii].right);
    ret = ret|(left&right);
  }
  cache.push_back(ret);
  status[n_id] = cache.size();

  return ret;
}

#endif
