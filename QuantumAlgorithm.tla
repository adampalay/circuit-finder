-------------------------- MODULE QuantumAlgorithm --------------------------
EXTENDS TLC, Naturals, Integers, FiniteSets


(* --algorithm qm
 
variables S = { << 0, 0, 1, 1 >>, << 0, 1, 0, 1 >> };
Goal = {<<0, 1, 1, 0>>, <<0, 0, 0, 1>>};

define
    nand_elem(bit1, bit2) == 1 - bit1 * bit2
    nand(row1, row2) == <<
        nand_elem(row1[1], row2[1]),
        nand_elem(row1[2], row2[2]),
        nand_elem(row1[3], row2[3]),
        nand_elem(row1[4], row2[4])
    >>
end define;

begin
while TRUE do
    assert ~( Goal \subseteq S /\ S \subseteq Goal);
    with x \in S do
      with y \in S do
        either
          S := S \union {nand(x, y)};
        or 
          S := S \ {x};
        or
          S := S \ {y};
        end either;
      end with;
    end with;
end while;

end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES S, Goal

(* define statement *)
nand_elem(bit1, bit2) == 1 - bit1 * bit2
nand(row1, row2) == <<
    nand_elem(row1[1], row2[1]),
    nand_elem(row1[2], row2[2]),
    nand_elem(row1[3], row2[3]),
    nand_elem(row1[4], row2[4])
>>


vars == << S, Goal >>

Init == (* Global variables *)
        /\ S = { << 0, 0, 1, 1 >>, << 0, 1, 0, 1 >> }
        /\ Goal = {<<0, 1, 1, 0>>, <<0, 0, 0, 1>>}

Next == /\ Assert(~( Goal \subseteq S /\ S \subseteq Goal), 
                  "Failure of assertion at line 22, column 5.")
        /\ \E x \in S:
             \E y \in S:
               \/ /\ S' = (S \union {nand(x, y)})
               \/ /\ S' = S \ {x}
               \/ /\ S' = S \ {y}
        /\ Goal' = Goal

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Jun 21 13:29:38 EDT 2018 by adampalay
\* Created Mon Jun 11 15:52:06 EDT 2018 by adampalay
