predicate mdd(array[int] of var int: vs, array[int] of int: shifts,
               int: nb_nodes, array[int] of int: layer_width, 
               array[1..2,int] of int: edges); %Edges: value, dest

predicate wmdd(array[int] of var int: vs, array[int] of int: shifts,
               int: nb_nodes, array[int] of int: layer_width, 
               array[1..2,int] of int: edges, %Edges: value, dest
               array[int] of int: var_idx,
               array[int] of int: val,
               array[int] of int: ecost,
               var int: total_cost); 