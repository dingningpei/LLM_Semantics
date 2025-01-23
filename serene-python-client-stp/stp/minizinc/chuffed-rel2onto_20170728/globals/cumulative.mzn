%-----------------------------------------------------------------------------%
% Requires that a set of tasks given by start times 's', durations 'd', and
% resource requirements 'r', never require more than a global resource bound
% 'b' at any one time.
% Assumptions:
% - forall i, d[i] >= 0 and r[i] >= 0
%-----------------------------------------------------------------------------%

predicate cumulative(array[int] of var int: s,
                     array[int] of var int: d,
                     array[int] of var int: r, var int: b) =
    assert(
        index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
        "cumulative: the 3 array arguments must have identical index sets",
        forall(i in index_set(d))(d[i] >= 0 /\ r[i] >= 0)
	/\  if is_fixed(d) /\ is_fixed(r) /\ is_fixed(b) then
		    chuffed_cumulative(s, fix(d), fix(r), fix(b))
	    else
		    chuffed_cumulative_vars(s, d, r, b)
	    endif
    );


	% Global cumulative propagator
	%
predicate chuffed_cumulative(array[int] of var int: s, array[int] of int: d,
	array[int] of int: r, int: b);

predicate chuffed_cumulative_vars(array[int] of var int: s, array[int] of var int: d,
	array[int] of var int: r, var int: b);

