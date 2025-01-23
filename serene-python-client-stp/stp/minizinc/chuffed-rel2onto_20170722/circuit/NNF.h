#ifndef ___NNF_H__
#define ___NNF_H__

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

#define NNFTRUE UINT_MAX
#define NNFFALSE (NNFTRUE^2)

typedef unsigned int _NNF;

// Leaves are encoded in the _NNF ids.
// leaf: [----------------|x|1]
//            {varid}    {sign}
// Branch: [-----------------|0]
//         {       id        }

enum NNFType { NNF_OR = 0, NNF_AND = 2 };

typedef struct {
  NNFType type;
  unsigned int sz;
  
  _NNF args[1];
} NNFNodeEl;

typedef NNFNodeEl* NNFNode;

struct nnf_eqnode
{
  bool operator()(const NNFNode a1, const NNFNode a2) const
  {
    if( a1->type != a2->type )
      return false;
    if( a1->sz != a2->sz )
      return false;

    for( unsigned int ii = 0; ii < a1->sz; ii++ )
    {
      if( a1->args[ii] != a2->args[ii] )
        return false;
    }
    return true;
  }
};

// Construct a better hash function. Seriously. Use MurmurHash3.
struct nnf_hashnode
{
  unsigned int operator()(const NNFNode a1) const
  {
#ifdef USE_MURMURHASH
    // Using the vnode as a seed. Probably dubious.
    uint32_t ret;
    MurmurHash3_x86_32(a1->args, sizeof(_NNF)*a1->sz, a1->type, &ret);
    return ret;
#else
    unsigned int hash = 5381;
    
    hash = ((hash << 5) + hash) + a1->type; 
    hash = ((hash << 5) + hash) + a1->sz;

    for(unsigned int ii = 0; ii < a1->sz; ii++)
    {
      hash = ((hash << 5) + hash) + a1->args[ii];
    }
    return (hash & 0x7FFFFFFF);
#endif
  }
};


class NNFTable;

class NNF {
public:
  NNF(NNFTable* _table, _NNF _val)
    : table( _table ), val( _val )
  {  }
  
  NNF(void)
    : table( NULL ), val( -1 )
  {  }  

#if 0
  NNF(const NNF& other)
    : table(other.table), val(other.val)
  {  }

  NNF& operator=(const NNF& other) {
    table = other.table;
    val = other.val;
    return *this;
  }
#endif

  void print_dot(void);

  NNFTable* table;
  _NNF val;
};

class NNFTable
{
public:
  typedef __gnu_cxx::hash_map<const NNFNode, int, nnf_hashnode, nnf_eqnode> NodeCache;
  enum NNFOp { OP_AND, OP_OR, OP_NOT, OP_IFF, OP_XOR, OP_EXIST };

  NNFTable(void);
  ~NNFTable(void);
  
  const std::vector<NNFNode>& getNodes(void)
  {
     return nodes;
  }

  std::vector<int>& getStatus(void)
  {
     return status;
  }
  
  void clear_status(_NNF r);

  void print(_NNF r);
  void print_tikz(_NNF r);
  void print_dot(_NNF r);

  int nnf_sz(_NNF r);
#if 1
  int cache_sz(void)
  {
    return cache.size();
  }
#endif

  _NNF insert(NNFType type, unsigned int start);
  
  NNF ttt(void) { return nnf_true(); }
  NNF fff(void) { return nnf_false(); }

  NNF nnf_true(void) { return NNF(this,NNFTRUE); }
  NNF nnf_false(void) { return NNF(this,NNFFALSE); }
  
  NNF var(int var)  { return NNF(this, _nnf_var(var)); }
  _NNF _nnf_var(int var) { return (var<<2)|3; }
  _NNF nnf_apply(NNFOp op, _NNF a, _NNF b);
  _NNF nnf_mknode(NNFType type, _NNF a, _NNF b);

  _NNF nnf_not(_NNF);

  _NNF nnf_exist(_NNF, unsigned int);

private:
  inline NNFNode allocNode(int sz);
  inline void deallocNode(NNFNode node);
  
  int nvars;
  
  OpCache opcache;
  NodeCache cache;
  
  std::vector<_NNF> stack;
  unsigned int intermed_maxsz;
  NNFNode intermed;

  std::vector<NNFNode> nodes;
  std::vector<int> status;
};

NNF operator|(const NNF& a, const NNF& b);
NNF operator&(const NNF& a, const NNF& b);
NNF operator^(const NNF& a, const NNF& b);
NNF operator~(const NNF& a);
NNF nnf_iff(const NNF& a, const NNF& b);

#endif
