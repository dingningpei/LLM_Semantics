predicate steiner_tree(array[int] of var bool: vs,array[int] of var bool: es,
                          array[int,int] of bool: adjacency, 
                          array[int,int] of bool: endnodes,
                          var int: total_weight,
                          array[int] of int: weights);
predicate steiner_tree(array[int] of var bool: vs,array[int] of var bool: es,
                          array[int,int] of bool: adjacency, 
                          array[1..2,int] of int: endnodes,
                          var int: total_weight,
                          array[int] of int: weights);