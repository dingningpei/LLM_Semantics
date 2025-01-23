predicate mst(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of bool: endnodes,
                  var int: w, array[int] of int: ws);
predicate cmst(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of bool: endnodes,
                  var int: w, array[int] of int: ws,
                  int: r, int: c);
predicate mst(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of int: endnodes,
                  var int: w, array[int] of int: ws);
predicate cmst(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of int: endnodes,
                  var int: w, array[int] of int: ws,
                  int: r, int: c);
