#include <iostream>

#ifdef __APPLE__
#include <memory>
#define MEMCPY std::memcpy
#else
#include <cstring>
#define MEMCPY memcpy
#endif

#include <cassert>
#include <climits>
#include <iostream>
#include "NNF.h"

#define OPCACHE_SZ 100000
#define CACHE_SZ 180000

#define LEAF 1
#define POS 2

static struct NodeSort {
  bool operator()(const _NNF& pa, const _NNF& pb) {
    return pa < pb;
  }
} nodesort;

NNFNode NNFTable::allocNode(int sz)
{
  return ( (NNFNodeEl*) malloc(sizeof(NNFNodeEl) + (sz - 1)*sizeof(_NNF)) );
}

inline void NNFTable::deallocNode(NNFNode node)
{
  free(node);
}

NNFTable::NNFTable(void)
  : opcache( OpCache(OPCACHE_SZ) ),
//      cache(CACHE_SZ),
    cache(),
    stack(),
    intermed_maxsz(2),
    nodes()
{
  // TTT and FFF are represented as leaves; don't need to allocate nodes.

  intermed = allocNode(intermed_maxsz);
}

NNFTable::~NNFTable(void)
{
  deallocNode(intermed);
  for( unsigned int i = 0; i < nodes.size(); i++ )
    deallocNode(nodes[i]);
}

// Insert a node with edges
// stack[start,...].
_NNF NNFTable::insert(NNFType type, unsigned int start)
{
  NodeCache& varcache( cache );
  
  // Ensure there's adequate space in the intermed node.
  if( intermed_maxsz < (stack.size() - start) )
  {
    while( intermed_maxsz < (stack.size() - start) )
      intermed_maxsz *= 2;

    deallocNode(intermed);
    intermed = allocNode(intermed_maxsz);
  }
  
  // Trim the args, so a /\ a = a, a /\ F = F, etc.
  // Can't figure out a nice way to guarantee a /\ ~a -> F.

  // Make sure chunks are ordered.
  std::sort(&stack[start], &stack[stack.size()], nodesort);

  unsigned int last = start;
  unsigned int ii = start+1;
  for( ; ii < stack.size() && stack[ii] < NNFFALSE; ii++ )
  {
    _NNF arg( stack[ii] );

    if( arg == stack[last] )
      continue;
    if( (arg&LEAF) && (arg^POS) == stack[last] )
      continue;

    stack[++last] = arg;
  }
  for( ; ii < stack.size(); ii++ )
  {
    // X /\ F = F.
    // X \/ T = T.
    if( (stack[ii]^type) == NNFTRUE )
    {
      stack.resize(start);
      return NNFTRUE^type;
    }
  }
  
  if( last == start )
  {
    // Constant node.
    // Also works if stack[start] == TTT or FFF.
    _NNF ret(stack[start]);
    stack.resize(start);
    return ret; 
  }

  // Migrate the components to the intermediate state.
  unsigned int jj = 0;
  for(unsigned int kk = start; kk <= last; jj++, kk++)
  {
    intermed->args[jj] = stack[kk];
  }

  // Fill in the rest of intermed, and search in the cache.
  intermed->type = type;
  intermed->sz = jj;

  NodeCache::iterator res = varcache.find(intermed);

  if( res != varcache.end() )
  {
    stack.resize(start);
    return (*res).second;
  }

  NNFNode act = allocNode(intermed->sz);

  MEMCPY(act,intermed,sizeof(NNFNodeEl) + (((int)intermed->sz) - 1)*(sizeof(_NNF)));

  varcache[act] = nodes.size()<<1;
  nodes.push_back(act);
  status.push_back(0);
  
  stack.resize(start); // Remove the current node from the stack.
  return (nodes.size() - 1)<<1;
}

// Assumes commutative operators.
_NNF NNFTable::nnf_apply(NNFOp op, _NNF a, _NNF b)
{
  _NNF res = a < b ? opcache.check(op,a,b)
             : opcache.check(op,b,a);
  
  if( res != UINT_MAX )
     return res;

  switch(op)
  {
    case OP_AND:
      res = nnf_mknode(NNF_AND, a, b);
      break;
    case OP_OR:
      res = nnf_mknode(NNF_OR, a, b);
      break;
    case OP_IFF:
      res = nnf_apply(OP_OR, nnf_apply(OP_AND, a, b), nnf_apply(OP_AND, nnf_not(a), nnf_not(b)));
      break;
    case OP_XOR:     
      res = nnf_apply(OP_OR, nnf_apply(OP_AND, nnf_not(a), b), nnf_apply(OP_AND, a, nnf_not(b)));
      break;
       
    default:
      assert( 0 );
      return NNFFALSE;
  }

  if( a < b )
     opcache.insert(op,a,b,res);
  else
     opcache.insert(op,b,a,res);

  return res;
}

_NNF NNFTable::nnf_mknode(NNFType type, _NNF a, _NNF b)
{
  unsigned int start = stack.size();
  
  if( a == b )
    return a;
  
  // FIXME: Add simplification stuff in here, too.  
  stack.push_back(a);
  stack.push_back(b);
  return insert(type, start);
}

_NNF NNFTable::nnf_not(_NNF root)
{
  // leaf node.
  if( root&LEAF )
  {
    return root^2;
  }
  
  _NNF res = opcache.check(OP_NOT,root,0);
  if( res != UINT_MAX )
    return res;
  
  int rnode = root>>1;
  NNFType type = (NNFType) (nodes[rnode]->type^2); // ~(A /\ B) <=> ~A \/ ~B, etc.
  unsigned int start = stack.size();
  
  for( unsigned int ii = 0; ii < nodes[rnode]->sz; ii++ )
  {
    stack.push_back( nnf_not(nodes[rnode]->args[ii]) );
  }
  res = insert(type, start);
  opcache.insert(OP_NOT,root,0,res);
  return res;
}

void NNFTable::clear_status(_NNF r)
{
   if( r&LEAF )
      return;
    
   unsigned int rnode = r>>1;
   if( !status[rnode] )
      return;
   status[rnode] = 0;

   for( unsigned int ii = 0; ii < nodes[rnode]->sz; ii++ )
   {
      clear_status(nodes[rnode]->args[ii]);
   }
}

void NNFTable::print(_NNF r)
{
#if 0
  if( r&LEAF )
  {
    print_node(r);
    return;
  }

  std::vector<_NNF> queued;
  queued.push_back(r);
  status[r>>1] = 1;
  unsigned int head = 0;

  while( head < queued.size() )
  {
    _NNF n = queued[head];
    print_node(n);
    
    n = n>>1;
    for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ )
    {
      if( (nodes[n]->parts[jj].left&LEAF) == 0 && status[nodes[n]->parts[jj].left>>1] == 0 )
      {
        status[nodes[n]->parts[jj].left>>1] = 1;
        queued.push_back(nodes[n]->parts[jj].left);
      }
      if( (nodes[n]->parts[jj].right&LEAF) == 0 && status[nodes[n]->parts[jj].right>>1] == 0 )
      {
        status[nodes[n]->parts[jj].right>>1] = 1;
        queued.push_back(nodes[n]->parts[jj].right);
      }

    }
    head++;
  }
  for( unsigned int i = 0; i < queued.size(); i++ )
  {
     status[queued[i]>>1] = 0;
  }
#endif
}

void NNFTable::print_tikz(_NNF r)
{
  assert( 0 );
  return;
#if 0
  std::cout << "\\documentclass{article}\n";

  std::cout << "\\usepackage{tikz}\n";
  std::cout << "\\usetikzlibrary{arrows,shapes}\n";
  std::cout << "\\begin{document}\n";
  std::cout << "\\begin{tikzpicture}\n";
  std::cout << "\\tikzstyle{vertex}=[draw,circle,fill=black!25,minimum size=20pt,inner sep=0pt]\n";
  std::cout << "\\tikzstyle{smallvert}=[circle,fill=black!25,minimum size=5pt,inner sep=0pt]\n";
  std::cout << "\\tikzstyle{edge} = [draw,thick,->]\n";
  std::cout << "\\tikzstyle{kdedge} = [draw,thick,=>,color=red]\n";
  std::cout << "\\tikzstyle{kaedge} = [draw,thick,=>,color=blue]\n";
  std::cout << "\\tikzstyle{kbedge} = [draw,thick,=>,color=pinegreen!25]\n";
  

  std::cout << "\\end{tikzpicture}\n";
  std::cout << "\\end{document}\n";
#endif
}

void NNFTable::print_dot(_NNF r)
{
  if( r&LEAF )
    return;

  std::cout << "digraph ingraph { graph [ranksep=\"1.0 equally\"] " << std::endl;
  
  std::vector<int> queued;
  queued.push_back(r>>1);

  status[r>>1] = 1;
  int nextid = 2;
  unsigned int head = 0;
  
  for(head = 0; head < queued.size(); head++ )
  {
    int n_id = queued[head];
    NNFNodeEl* node(nodes[n_id]);
//    printf("  { node [shape=record label=\"{<prefix>%d:%d | {",n_id,nodes[n_id]->type);
    printf("  { node [shape=record label=\"{<prefix>%d:",n_id);
    if(nodes[n_id]->type == NNF_AND )
      printf("/\\\\");
    else
      printf("\\\\/");
    printf(" | {");

    bool first = true;
    for( unsigned int ii = 0; ii < nodes[n_id]->sz; ii++ )
    {
      if( first )
        first = false;
      else
        printf("|");
      
      printf("<p%d>",ii);
      if(node->args[ii]&LEAF)
      {
        if( node->args[ii] == NNFTRUE )
        {
          printf("T");
        } else if( node->args[ii] == NNFFALSE ) {
          printf("F");
        } else {
          if( node->args[ii]&POS )
            printf("+");
          else
            printf("-");
          printf("%d",node->args[ii]>>2);
        }
      } else {
        if(!status[node->args[ii]>>1])
        {
          status[node->args[ii]>>1] = nextid++;
          queued.push_back(node->args[ii]>>1);
        }
        printf("%d",node->args[ii]>>1);
      }
    }
    printf("} }\"] %d };\n", n_id);
  }
  
  for(head = 0; head < queued.size(); head++ )
  {
    int n_id = queued[head];
    NNFNodeEl* node(nodes[n_id]);

    for( unsigned int ii = 0; ii < node->sz; ii++ )
    {
      if( !(node->args[ii]&LEAF) )
      {
        printf("\t%d:p%d -> %d;\n",n_id,ii,node->args[ii]>>1);
      }
    }
  }
  std::cout << "};" << std::endl;
  for( unsigned int ii = 0; ii < queued.size(); ii++ )
    status[queued[ii]] = 0;
}

int NNFTable::nnf_sz(_NNF r)
{
  if( r&LEAF )
  {
    return 0;
  }

  std::vector<_NNF> queued;
  queued.push_back(r);
  status[r>>1] = 1;
  unsigned int head = 0;

  while( head < queued.size() )
  {
    _NNF n = queued[head];
    
    n = n>>1;
    for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ )
    {
      if( (nodes[n]->args[jj]&LEAF) == 0 && status[nodes[n]->args[jj]>>1] == 0 )
      {
        status[nodes[n]->args[jj]>>1] = 1;
        queued.push_back(nodes[n]->args[jj]);
      }
    }
    head++;
  }
  for( unsigned int i = 0; i < queued.size(); i++ )
  {
     status[queued[i]>>1] = 0;
  }
  return queued.size();
}

NNF operator| (const NNF& a, const NNF& b) {
  assert( a.table == b.table );
  return NNF(a.table, a.table->nnf_apply(NNFTable::OP_OR,a.val,b.val));  
}

NNF operator& (const NNF& a, const NNF& b) {
  assert( a.table == b.table);
  return NNF(a.table, a.table->nnf_apply(NNFTable::OP_AND,a.val,b.val));
}

NNF operator^ (const NNF& a, const NNF& b) {
  assert( a.table == b.table);
  return NNF(a.table, a.table->nnf_apply(NNFTable::OP_XOR,a.val,b.val));
}

NNF nnf_iff(const NNF& a, const NNF& b) {
  assert( a.table == b.table);
  return NNF(a.table, a.table->nnf_apply(NNFTable::OP_IFF,a.val,b.val));
}

NNF operator~(const NNF& r) {
  return NNF(r.table, r.table->nnf_not(r.val));
}

void NNF::print_dot(void) {
  table->print_dot(val);
}


