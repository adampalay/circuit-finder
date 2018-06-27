----------------------------- MODULE XfromNAND2 -----------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm nand

variables
    CircuitState = << >>;
    Wires = { << "input", << 0, 0, 1, 1 >> >>, << "input", << 0, 1, 0, 1 >> >> };

define
    nand_elem(bit1, bit2) == 1 - bit1 * bit2
    
    nand(row1, row2) == <<
        nand_elem(row1[1], row2[1]),
        nand_elem(row1[2], row2[2]),
        nand_elem(row1[3], row2[3]),
        nand_elem(row1[4], row2[4])
    >>

    RECURSIVE compute(_)
    compute(state) == 
        IF state[1] = "input"
        THEN state[2]
        ELSE nand(compute(state[2]), compute(state[3]))
        
end define;

begin
while TRUE do
    with wirePair \in (Wires \X Wires) do
       CircuitState := << "nand" >> \o wirePair;
       print CircuitState;
       Wires := Wires \union { CircuitState };
    end with;
end while;



end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES CircuitState, Wires

(* define statement *)
nand_elem(bit1, bit2) == 1 - bit1 * bit2

nand(row1, row2) == <<
    nand_elem(row1[1], row2[1]),
    nand_elem(row1[2], row2[2]),
    nand_elem(row1[3], row2[3]),
    nand_elem(row1[4], row2[4])
>>

RECURSIVE compute(_)
compute(state) ==
    IF state[1] = "input"
    THEN state[2]
    ELSE nand(compute(state[2]), compute(state[3]))


vars == << CircuitState, Wires >>

Init == (* Global variables *)
        /\ CircuitState = << >>
        /\ Wires = { << "input", << 0, 0, 1, 1 >> >>, << "input", << 0, 1, 0, 1 >> >> }

Next == \E wirePair \in (Wires \X Wires):
          /\ CircuitState' = << "nand" >> \o wirePair
          /\ PrintT(CircuitState')
          /\ Wires' = (Wires \union { CircuitState' })

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Invariant == (Len(CircuitState) = 0) \/ (compute(CircuitState) /= << 0, 1, 1, 0 >>)


=============================================================================
\* Modification History
\* Last modified Wed Jun 27 16:43:40 EDT 2018 by adampalay
\* Last modified Thu Jun 21 17:18:46 EDT 2018 by emanuel
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
