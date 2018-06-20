-------------------------- MODULE QuantumAlgorithm --------------------------
EXTENDS TLC, Naturals, Integers


(* --algorithm qm
\* qubit 1's state is 1, 0, meaning that it's a "1" in the 0 basis and "0" in the one
variables S = { << 0, 0, 1, 1 >>, << 0, 1, 0, 1 >> };

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
    assert <<0, 0, 0, 1>> \notin S;
    with x \in S do
      with y \in S do
        S := S \union {nand(x, y)}
      end with;
    end with;
    \* assert <<0, 0, 0, 1>> \notin S;
end while;

end algorithm; *)


\* BEGIN TRANSLATION
VARIABLE S

(* define statement *)
nand_elem(bit1, bit2) == 1 - bit1 * bit2
nand(row1, row2) == <<
    nand_elem(row1[1], row2[1]),
    nand_elem(row1[2], row2[2]),
    nand_elem(row1[3], row2[3]),
    nand_elem(row1[4], row2[4])
>>


vars == << S >>

Init == (* Global variables *)
        /\ S = { << 0, 0, 1, 1 >>, << 0, 1, 0, 1 >> }

Next == /\ Assert(<<0, 0, 0, 1>> \notin S, 
                  "Failure of assertion at line 21, column 5.")
        /\ \E x \in S:
             \E y \in S:
               S' = (S \union {nand(x, y)})

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Jun 20 14:01:15 EDT 2018 by adampalay
\* Created Mon Jun 11 15:52:06 EDT 2018 by adampalay
