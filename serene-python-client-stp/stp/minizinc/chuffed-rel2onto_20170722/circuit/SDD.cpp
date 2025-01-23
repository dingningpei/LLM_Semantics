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
#include "SDD.h"

#define OPCACHE_SZ 100000
#define CACHE_SZ 180000

#define SDDTRUE(vnode) ((vnode)<<3|TTT)
#define SDDFALSE(vnode) ((vnode)<<3|FFF)

struct PartSort {
  bool operator()(const SDDPart& pa, const SDDPart& pb) {
    return pa.left < pb.left;
  }
} partsort;

static SDDPart mkpart(_SDD left, _SDD right)
{
  SDDPart part = {
    left,
    right
  };
  return part;
}

SDDNode SDDTable::allocNode(int sz)
{
  return ( (SDDNodeEl*) malloc(sizeof(SDDNodeEl) + (sz - 1)*sizeof(SDDPart)) );
}

inline void SDDTable::deallocNode(SDDNode node)
{
  free(node);
}

SDDTable::SDDTable(const VTree& _vtree)
  : vtree( _vtree ),
    opcache( OpCache(OPCACHE_SZ) ),
//      cache(CACHE_SZ),
    cache(),
    stack(),
    intermed_maxsz(2),
    nodes()
{
  // Initialize \ttt and \fff.
  nodes.push_back(NULL); // false node
  nodes.push_back(NULL); // true node
  status.push_back(0);
  status.push_back(0);

  intermed = allocNode(intermed_maxsz);
}

SDDTable::~SDDTable(void)
{
  deallocNode(intermed);
  for( unsigned int i = 2; i < nodes.size(); i++ )
    deallocNode(nodes[i]);
}

// Insert a node with edges
// stack[start,...].
_SDD SDDTable::insert(unsigned int vn, unsigned int start)
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

  // Trim the partition components.
  unsigned int end = start;
  for( unsigned int ii = start; ii < stack.size(); ii++ )
  {
    SDDPart part( stack[ii] );
    
    assert( vnode(part.left) == vtree.left(vn) );
    assert( vnode(part.right) == vtree.right(vn) );
inspart: 
    if( (part.left&FLAGS) == FFF )
      continue;
    
    for( unsigned int kk = start; kk < end; kk++ )
    {
      if( part.right == stack[kk].right )
      {
        part.left = sdd_apply(OP_OR, part.left, stack[kk].left);
        stack[kk] = stack[--end];
        goto inspart;
      }
    }

    stack[end++] = part;
  }
  // Migrate the components to the intermediate state.
  unsigned int jj = 0;
  for(unsigned int kk = start; kk < end; jj++, kk++)
  {
    intermed->parts[jj] = stack[kk];
  }

  for( unsigned int ii = 0; ii < jj; ii++ )
  {
    if( vnode(intermed->parts[ii].left) != vtree.left(vn) )
    {
      std::cout << "AARGH!" << std::endl;
    }
    assert( vnode(intermed->parts[ii].left) == vtree.left(vn) );
    assert( vnode(intermed->parts[ii].right) == vtree.right(vn) );
  }
  
  assert( jj > 0 );
#if 1
  if( jj == 1 )
  {
    // Constant node.
    assert( (intermed->parts[0].left&FLAGS) == TTT );
    if( (intermed->parts[0].right&FLAGS) == FFF )
    {
      stack.resize(start);
      return SDDFALSE(vn);
    } else if( (intermed->parts[0].right&FLAGS) == TTT ) {
      stack.resize(start);
      return SDDTRUE(vn);
    }
  }
#endif

  // Sort the partitions (to ensure canonicity)
  std::sort(intermed->parts, intermed->parts + jj, partsort);

  // Fill in the rest of intermed, and search in the cache.
  intermed->vnode = vn;
  intermed->sz = jj;

  NodeCache::iterator res = varcache.find(intermed);

  if( res != varcache.end() )
  {
    stack.resize(start);
    return (*res).second;
  }

  SDDNode act = allocNode(intermed->sz);

  MEMCPY(act,intermed,sizeof(SDDNodeEl) + (((int)intermed->sz) - 1)*(sizeof(SDDPart)));

  varcache[act] = nodes.size()<<1;
  nodes.push_back(act);
  status.push_back(0);
  
  stack.resize(start); // Remove the current node from the stack.
  return (nodes.size() - 1)<<1;
}

_SDD SDDTable::_sdd_true(void)
{
  return SDDTRUE(vtree.root);
}
_SDD SDDTable::_sdd_false(void)
{
  return SDDFALSE(vtree.root);
}

_SDD SDDTable::_sdd_var(int var)
{
  // {---var---|10|1}
  int vnode = var;
  _SDD res = (var<<3|POS|LEAF);
  while( vnode != vtree.root )
  {
    int parent = vtree.pred(vnode);
    assert( parent != -1 );
    vnode = parent>>1;
    bool dir = parent&1;
    
    int start = stack.size();
    if( dir )
    {
      // Left child.
      stack.push_back(mkpart(res, SDDTRUE(vtree.right(vnode))));
      stack.push_back(mkpart(sdd_not(res), SDDFALSE(vtree.right(vnode))));
    } else {
      // Right child.
      stack.push_back(mkpart(SDDTRUE(vtree.left(vnode)),res));
    }

    res = insert(vnode, start);
  }
  return res;
}

// Constants and shortcutting.
_SDD SDDTable::normalize(int vnode, _SDD a)
{
  assert( 0 );
  return -1;
#if 0
  int anode;
  switch( a&FLAGS )
  {
    case TTT:
    case FFF:
      assert( vnode == ((int) a>>3) ); // TTT/FFF should always be as high as possible.
      return a;
    
    case POS|LEAF:
    case NEG|LEAF:
      anode = a>>3;
      break;

    default:
      anode = nodes[a>>1]->vnode;
  }
  
  assert( anode <= vnode );
  if( anode == vnode )
    return a;

  int start = stack.size();

  if( vtree.dir(vnode, anode) )
  {
    // Left child.
    stack.push_back(mkpart(a, SDDTRUE(vtree.right(vnode))));
    stack.push_back(mkpart(sdd_not(a), SDDFALSE(vtree.right(vnode))));
  } else {
    // Right child.
    stack.push_back(mkpart(SDDTRUE(vtree.left(vnode)),a));
  }

  return insert(vnode, start);
#endif
}

_SDD SDDTable::leaf_apply(SDDOp op, _SDD a, _SDD b)
{
  assert( vnode(a) == vnode(b) );
  if( a == b )
  {
    switch(op) {
      case OP_AND:
      case OP_OR:
        return a;
        break;
      
      case OP_IFF:
        return SDDTRUE(vnode(a));
        break;
      case OP_XOR:
        return SDDFALSE(vnode(a));
        break;

      default:
        assert( 0 );
        break;
    }
  }

  // a == ~b 
  if( ((a^(POS|NEG)) == b) && (a&LEAF) )
  {
    switch(op) {
      case OP_AND:
      case OP_IFF:
        return a&~(POS|NEG); // FFF
      case OP_OR:
      case OP_XOR:
        return a|(POS|NEG); // TTT
      default:
        break;
    }
  }

  switch( a&FLAGS )
  {
    case TTT:
      switch(op) {
        case OP_AND:
          return b;
        case OP_OR:
          return a;
        case OP_IFF:
          return b;
        case OP_XOR:
          return sdd_not(b);
        default:
          break;
      }
      break;

    case FFF:
      switch(op) {
        case OP_AND:
          return a;
        case OP_OR:
          return b;
        case OP_IFF:
          return sdd_not(b);
        case OP_XOR:
          return b; 
        default:
          break;
      }

    default:
      break;
  }

  switch( b&FLAGS )
  {
    case TTT:
      switch(op) {
        case OP_AND:
          return a;
        case OP_OR:
          return b;
        case OP_IFF:
          return a;
        case OP_XOR:
          return sdd_not(a);
        default:
          break;
      }
      break;

    case FFF:
      switch(op) {
        case OP_AND:
          return b;
        case OP_OR:
          return a;
        case OP_IFF:
          return sdd_not(a);
        case OP_XOR:
          return a;        
        default:
          break;
      }

    default:
      break;
  }

  return UINT_MAX;
}

// Assumes commutative operators.
_SDD SDDTable::sdd_apply(SDDOp op, _SDD a, _SDD b)
{
  // Ignoring shortcutting & base cases for now.
  assert( vnode(a) == vnode(b) );

  _SDD res = a < b ? opcache.check(op,a,b)
             : opcache.check(op,b,a);
  if( res == UINT_MAX )
    res = leaf_apply(op, a, b); // Check for early termination cases.
  
  if( res != UINT_MAX )
     return res;
   
  unsigned int start = stack.size();
  assert( vnode(a) == vnode(b) );
  unsigned int vn = vnode(a);
   
  assert( !(a&LEAF) && !(b&LEAF) );
  int an = a>>1;
  int bn = b>>1;
  assert( nodes[an]->vnode == nodes[bn]->vnode );

  for( unsigned int ii = 0; ii < nodes[an]->sz; ii++ )
  {
    _SDD ap = nodes[an]->parts[ii].left;
    _SDD as = nodes[an]->parts[ii].right;

    for( unsigned int jj = 0; jj < nodes[bn]->sz; jj++ )
    {
      _SDD bp = nodes[bn]->parts[jj].left;
      _SDD bs = nodes[bn]->parts[jj].right;

      _SDD p = sdd_apply(OP_AND, ap, bp);
      if( (p&FLAGS) != FFF )
      {
        stack.push_back( mkpart(p, sdd_apply(op, as, bs)) );
      }
    }
  }

  res = insert(vn, start);
  if( a < b )
     opcache.insert(op,a,b,res);
  else
     opcache.insert(op,b,a,res);

  return res;
}

_SDD SDDTable::sdd_exist(_SDD root, unsigned int var)
{
  assert( 0 );
  return SDDFALSE(vtree.root);
#if 0
  if( root == SDDTRUE || root == SDDFALSE )
     return root;

  unsigned int r_var = nodes[root]->vnode;
  if( r_var > var )
     return root;
  
  _SDD res;
  if( (res = opcache.check(OpCache::OP_EXIST,root,var)) != UINT_MAX )
     return res;
  
  if( r_var == var )
  {
    _SDD res = SDDFALSE;
    for( unsigned ii = 0; ii < nodes[root]->sz; ii++ )
    {
      res = mdd_or( res, nodes[root]->edges[ii].dest );
    }
    opcache.insert(OpCache::OP_EXIST,root,var,res);
    return res;
  }

  // r_var < var
  unsigned int start = stack.size();
  unsigned int low = mdd_exist(nodes[root]->low, var);
  for( unsigned int ii = 0; ii < nodes[root]->sz; ii++ )
  {
    stack.push_back( mkedge( nodes[root]->edges[ii].val,
                     mdd_exist(nodes[root]->edges[ii].dest, var) ) );
  }
  res = insert(r_var, low, start);
  opcache.insert(OpCache::OP_EXIST,root,var,res);
  return res;
#endif
}

_SDD SDDTable::sdd_not(_SDD root)
{
  // leaf node.
  if( root&LEAF )
  {
    return root^(POS|NEG);
  }
  
  _SDD res = opcache.check(OP_NOT,root,0);
  if( res != UINT_MAX )
    return res;
  
  int rnode = root>>1;
  unsigned int vnode = nodes[rnode]->vnode;
  unsigned int start = stack.size();
  
  for( unsigned int ii = 0; ii < nodes[rnode]->sz; ii++ )
  {
    stack.push_back( mkpart( nodes[rnode]->parts[ii].left,
                     sdd_not(nodes[rnode]->parts[ii].right) ) );
  }
  res = insert(vnode, start);
  opcache.insert(OP_NOT,root,0,res);
  return res;
}

void SDDTable::clear_status(_SDD r)
{
   if( r&LEAF )
      return;
    
   unsigned int rnode = r>>1;
   if( !status[rnode] )
      return;
   status[rnode] = 0;

   for( unsigned int ii = 0; ii < nodes[rnode]->sz; ii++ )
   {
      clear_status(nodes[rnode]->parts[ii].left);
      clear_status(nodes[rnode]->parts[ii].right);
   }
}

void SDDTable::print_nodes(void)
{
#if 1
  for( unsigned int i = 0; i < nodes.size(); i++ )
  {
    print_node(i);
  }
#else
  std::cout << nodes.size() << std::endl;
#endif
}

void SDDTable::show_node(_SDD r)
{
  if( r&LEAF )
  {
    std::cout << "(" << (r>>3) << "|";
    switch( r&FLAGS )
    {
      case TTT:
        std::cout << "T";
        break;
      case FFF:
        std::cout << "F";
        break;
      case POS|LEAF:
        std::cout << "+";
        break;
      case NEG|LEAF:
        std::cout << "-";
      default:
        break;
    }

    std::cout << ")";
    return;
  } else {
    std::cout << (r>>1);
  }
}

void SDDTable::print_node(_SDD r)
{
  if( r&LEAF )
  {
    std::cout << "(" << (r>>3) << "|";
    switch( r&FLAGS )
    {
      case TTT:
        std::cout << "T";
        break;
      case FFF:
        std::cout << "F";
        break;
      case POS|LEAF:
        std::cout << "+";
        break;
      case NEG|LEAF:
        std::cout << "-";
      default:
        break;
    }
    std::cout << ")" << std::endl;
    return;
  } else {
    r = r>>1;
    std::cout << r << "(" << nodes[r]->vnode << "): ";
    for(unsigned int jj = 0; jj < nodes[r]->sz; jj ++)
    {
       std::cout << " [";
       show_node(nodes[r]->parts[jj].left);
       std::cout << " | ";
       show_node(nodes[r]->parts[jj].right);
       std::cout << "]";
    }
    std::cout << std::endl;
  }
}

void SDDTable::print(_SDD r)
{
  if( r&LEAF )
  {
    print_node(r);
    return;
  }

  std::vector<_SDD> queued;
  queued.push_back(r);
  status[r>>1] = 1;
  unsigned int head = 0;

  while( head < queued.size() )
  {
    _SDD n = queued[head];
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
}

void SDDTable::pprint(_SDD r)
{
  pprint_rec(r);
  std::cout << std::endl;
  clear_status(r);
}

void SDDTable::pprint_rec(_SDD r)
{
  if( r&LEAF )
  {
    show_node(r);
    return;
  }
  
  unsigned int rnode = r>>1;
  if( status[rnode] )
  {
    std::cout << rnode;
    return;
  }
  
  status[rnode] = true;
  
  std::cout << "(" << rnode << "[" << nodes[rnode]->vnode << "]";
  for(unsigned int jj = 0; jj < nodes[rnode]->sz; jj++)
  {
     std::cout << " [";
     pprint_rec(nodes[rnode]->parts[jj].left);
     std::cout << " | ";
     pprint_rec(nodes[rnode]->parts[jj].right);
     std::cout << "]";
  }
  std::cout << ")";
}

void SDDTable::print_tikz(_SDD r)
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

void SDDTable::print_dot(_SDD r, bool reduce)
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
    SDDNodeEl* node(nodes[n_id]);
//    printf("  { node [shape=record label=\"{<prefix>%d:%d | {",status[n_id],nodes[n_id]->vnode);
    printf("  { node [shape=record label=\"{<prefix>%d:%d | {",n_id,nodes[n_id]->vnode);
    bool first = true;
    for( unsigned int ii = 0; ii < nodes[n_id]->sz; ii++ )
    {
      if( reduce && (node->parts[ii].right&FLAGS) == FFF )
        continue;

      if( first )
        first = false;
      else
        printf("|");
      
      printf("<p%d>",ii);
      if(node->parts[ii].left&LEAF)
      {
        switch(node->parts[ii].left&FLAGS)
        {
          case TTT:
            printf("T");
            break;
          case FFF:
            printf("F");
            break;
          case (NEG|LEAF):
            printf("-");
            break;
          case (POS|LEAF): 
            printf("+");
            break;
          default:
            break;
        }
        printf("%d",node->parts[ii].left>>3);
      } else {
        if(!status[node->parts[ii].left>>1])
        {
          status[node->parts[ii].left>>1] = nextid++;
          queued.push_back(node->parts[ii].left>>1);
        }
//        printf("%d",status[node->parts[ii].left>>1]);
        printf("%d",node->parts[ii].left>>1);
      }
      
      printf("|<s%d>",ii);
      if( node->parts[ii].right&LEAF )
      {
        switch(node->parts[ii].right&FLAGS)
        {
          case TTT:
            printf("T");
            break;
          case FFF:
            printf("F");
            break;
          case (NEG|LEAF):
            printf("-");
            break;
          case (POS|LEAF): 
            printf("+");
            break;
          default:
            break;
        }
        printf("%d",node->parts[ii].right>>3);
      } else {
        if( !status[node->parts[ii].right>>1] )
        {
          status[node->parts[ii].right>>1] = nextid++;
          queued.push_back(node->parts[ii].right>>1);
        }
//        printf("%d",status[node->parts[ii].right>>1]);
        printf("%d",node->parts[ii].right>>1);
      }
    }
//    printf("} }\"] %d };\n", status[n_id]);
    printf("} }\"] %d };\n", n_id);
  }
  
  for(head = 0; head < queued.size(); head++ )
  {
    int n_id = queued[head];
    SDDNodeEl* node(nodes[n_id]);

    for( unsigned int ii = 0; ii < node->sz; ii++ )
    {
      if( reduce && (node->parts[ii].right&FLAGS) == FFF )
        continue;

      if( !(node->parts[ii].left&LEAF) )
      {
//        printf("\t%d:p%d -> %d;\n",status[n_id],ii,status[node->parts[ii].left>>1]);
        printf("\t%d:p%d -> %d;\n",n_id,ii,node->parts[ii].left>>1);
      }
      if( !(node->parts[ii].right&LEAF) )
      {
//        printf("\t%d:s%d -> %d;\n",status[n_id],ii,status[node->parts[ii].right>>1]);
        printf("\t%d:s%d -> %d;\n",n_id,ii,node->parts[ii].right>>1);
      }
    }
  }
  std::cout << "};" << std::endl;
  for( unsigned int ii = 0; ii < queued.size(); ii++ )
    status[queued[ii]] = 0;
}

int SDDTable::sdd_sz(_SDD r, bool reduce)
{
  if( r&LEAF )
  {
    return 0;
  }

  std::vector<_SDD> queued;
  queued.push_back(r);
  status[r>>1] = 1;
  unsigned int head = 0;

  while( head < queued.size() )
  {
    _SDD n = queued[head];
    
    n = n>>1;
    for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ )
    {
      if( reduce && (nodes[n]->parts[jj].right&FLAGS) == FFF )
        continue;

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
  return queued.size();
}

SDD operator| (const SDD& a, const SDD& b) {
  assert( a.table == b.table );
  return SDD(a.table, a.table->sdd_apply(SDDTable::OP_OR,a.val,b.val));  
}

SDD operator& (const SDD& a, const SDD& b) {
  assert( a.table == b.table);
  return SDD(a.table, a.table->sdd_apply(SDDTable::OP_AND,a.val,b.val));
}

SDD operator^ (const SDD& a, const SDD& b) {
  assert( a.table == b.table);
  return SDD(a.table, a.table->sdd_apply(SDDTable::OP_XOR,a.val,b.val));
}

SDD sdd_iff(const SDD& a, const SDD& b) {
  assert( a.table == b.table);
  return SDD(a.table, a.table->sdd_apply(SDDTable::OP_IFF,a.val,b.val));
}

SDD operator~(const SDD& r) {
  return SDD(r.table, r.table->sdd_not(r.val));
}

void SDD::print_dot(bool reduce) {
  table->print_dot(val, reduce);
}

#if 0
SDDTable::OpCache::OpCache(unsigned int  sz)
  : tablesz( sz ), members( 0 ),
    indices( (unsigned int*) malloc(sizeof(unsigned int)*sz) ),
    entries( (cache_entry*) malloc(sizeof(cache_entry)*sz) )
{
//    collisions = 0;
}

SDDTable::OpCache::~OpCache(void)
{
  free(indices);
  free(entries);
//    std::cout << members << ", " << collisions << std::endl;
}

typedef struct {
  unsigned int hash;
  unsigned int a;
  unsigned int b;
} cache_sig;
inline unsigned int SDDTable::OpCache::hash(char op, unsigned int a, unsigned int b)
{
#ifndef USE_MURMURHASH
  unsigned int hash = 5381;

  hash = ((hash << 5) + hash) + op;
  hash = ((hash << 5) + hash) + a;
  hash = ((hash << 5) + hash) + b;

  return (hash & 0x7FFFFFFF) % tablesz;
#else
  uint32_t ret;
  cache_sig sig = {
    op,
    a,
    b
   };
  MurmurHash3_x86_32(&sig, sizeof(cache_sig), 5381, &ret);
  return ret % tablesz;
#endif
}

// Returns UINT_MAX on failure.
unsigned int SDDTable::OpCache::check(char op, unsigned int a, unsigned int b)
{
  unsigned int hval = hash(op,a,b);
  unsigned int index = indices[hval];

  if( index < members && entries[index].hash == hval )
  {
    // Something is in the table.
    if( entries[index].op == op && entries[index].a == a && entries[index].b == b )
    {
      return entries[index].res;
    }
  }
  return UINT_MAX;
}

void SDDTable::OpCache::insert(char op, unsigned int a, unsigned int b, unsigned int res)
{
  unsigned int hval = hash(op,a,b);
  unsigned int index = indices[hval];

  if( index >= members || entries[index].hash != hval )
  {
    index = members;
    indices[hval] = index;
    members++;
  }
//   else {
//      collisions++;  
//   }
  
  entries[index].hash = hval; 
  entries[index].op = op; 
  entries[index].a = a;
  entries[index].b = b;
  entries[index].res = res;
}
#endif
