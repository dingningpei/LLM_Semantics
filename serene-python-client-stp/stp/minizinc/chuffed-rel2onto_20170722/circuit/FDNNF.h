#ifndef ___FDNNF_H__
#define ___FDNNF_H__

#define USE_MURMURHASH

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

#define FDNNFTRUE UINT_MAX
#define FDNNFFALSE (FDNNFTRUE^2)

typedef unsigned int _FDNNF;

// Leaves are encoded in the _FDNNF ids.
// leaf: [--------|-----|X|1]
//        {varid} {value}^sign
//           16   + 14 + 1+1 = 32
#define FDNNF_VALMASK ((1<<14)-1)
#define FDNNF_SIGN(leaf) (((leaf)>>1)&1)
#define FDNNF_VAL(leaf)  (((leaf)>>2)&FDNNF_VALMASK)
#define FDNNF_VAR(leaf)  ((leaf)>>16)

// Branch: [-----------------|0]
//         {       id        }

enum FDNNFType { FDNNF_OR = 0, FDNNF_AND = 2 };

typedef struct {
  FDNNFType type;
  unsigned int sz;
  
  _FDNNF args[1];
} FDNNFNodeEl;

typedef FDNNFNodeEl* FDNNFNode;

struct fdnnf_eqnode
{
  bool operator()(const FDNNFNode a1, const FDNNFNode a2) const
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
struct fdnnf_hashnode
{
  unsigned int operator()(const FDNNFNode a1) const
  {
#ifdef USE_MURMURHASH
    // Using the vnode as a seed. Probably dubious.
    uint32_t ret;
    MurmurHash3_x86_32(a1->args, sizeof(_FDNNF)*a1->sz, a1->type, &ret);
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


class FDNNFTable;

class FDNNF {
public:
  FDNNF(FDNNFTable* _table, _FDNNF _val)
    : table( _table ), val( _val )
  {  }
  
  FDNNF(void)
    : table( NULL ), val( -1 )
  {  }  

#if 0
  FDNNF(const FDNNF& other)
    : table(other.table), val(other.val)
  {  }

  FDNNF& operator=(const FDNNF& other) {
    table = other.table;
    val = other.val;
    return *this;
  }
#endif

  void print_dot(void);

  FDNNFTable* table;
  _FDNNF val;
};

class FDNNFTable
{
public:
  typedef __gnu_cxx::hash_map<const FDNNFNode, int, fdnnf_hashnode, fdnnf_eqnode> NodeCache;
  enum FDNNFOp { OP_AND, OP_OR, OP_NOT, OP_IFF, OP_XOR, OP_EXIST };

  FDNNFTable(void);
  ~FDNNFTable(void);
  
  const std::vector<FDNNFNode>& getNodes(void)
  {
     return nodes;
  }

  std::vector<int>& getStatus(void)
  {
     return status;
  }
  
  void clear_status(_FDNNF r);

  void print(_FDNNF r);
  void print_tikz(_FDNNF r);
  void print_dot(_FDNNF r);

  int fdnnf_sz(_FDNNF r);
#if 1
  int cache_sz(void)
  {
    return cache.size();
  }
#endif

  _FDNNF insert(FDNNFType type, unsigned int start);
  
  FDNNF ttt(void) { return fdnnf_true(); }
  FDNNF fff(void) { return fdnnf_false(); }

  FDNNF fdnnf_true(void) { return FDNNF(this,FDNNFTRUE); }
  FDNNF fdnnf_false(void) { return FDNNF(this,FDNNFFALSE); }
  
  FDNNF vareq(int var, int val)  { return FDNNF(this, _nnf_vareq(var,val)); }
  _FDNNF _nnf_vareq(int var, int val) { return (_FDNNF) ((var<<16)|(val<<2)|3); }
  _FDNNF nnf_apply(FDNNFOp op, _FDNNF a, _FDNNF b);
  _FDNNF nnf_mknode(FDNNFType type, _FDNNF a, _FDNNF b);

  _FDNNF nnf_not(_FDNNF);

  _FDNNF nnf_exist(_FDNNF, unsigned int);

private:
  inline FDNNFNode allocNode(int sz);
  inline void deallocNode(FDNNFNode node);
  
  int nvars;
  
  OpCache opcache;
  NodeCache cache;
  
  std::vector<_FDNNF> stack;
  unsigned int intermed_maxsz;
  FDNNFNode intermed;

  std::vector<FDNNFNode> nodes;
  std::vector<int> status;
};

FDNNF operator|(const FDNNF& a, const FDNNF& b);
FDNNF operator&(const FDNNF& a, const FDNNF& b);
FDNNF operator^(const FDNNF& a, const FDNNF& b);
FDNNF operator~(const FDNNF& a);
FDNNF nnf_iff(const FDNNF& a, const FDNNF& b);
#endif
