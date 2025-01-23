predicate biconnected(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of bool: endnodes);
predicate biconnected(array[int] of var bool: vs,array[int] of var bool: es,
                  array[int,int] of bool: adjacency, 
                  array[int,int] of int: endnodes);
predicate wbiconnected(array[int] of var bool: vs,array[int] of var bool: es,
                   array[int,int] of bool: adjacency, 
                   array[int,int] of bool: endnodes,
                   array[int] of int: weights, var int: w);
predicate wbiconnected(array[int] of var bool: vs,array[int] of var bool: es,
                   array[int,int] of bool: adjacency, 
                   array[int,int] of int: endnodes,
                   array[int] of int: weights, var int: w);