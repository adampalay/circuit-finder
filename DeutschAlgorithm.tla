-------------------------- MODULE DeutschAlgorithm --------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm qm
\* qubit 1's state is 1, 0, meaning that it's a "1" in the 0 basis and "0" in the one
variables S = << 0, 1, 0, 0 >>,
    actions = << >>;


define
    hadamard_1(s) == <<
        s[1] + s[2],
        s[1] - s[2],
        s[3],
        s[4]
    >>
    
    hadamard_2(s) == <<
        s[1],
        s[2],
        s[3] + s[4],
        s[3] - s[4]
    >>
    
    F(b) == 0
    
    u(f(_),s) == <<
        s[1 + f(0)],
        s[2 - f(0)],
        s[3 + f(1)],
        s[4 - f(1)]
    >>
   
end define;

begin
while TRUE do
    with i \in 1..3 do
       actions := Append(actions, i)
    end with;
    assert actions /= <<1, 3>>
end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES S, actions

(* define statement *)
hadamard_1(s) == <<
    s[1] + s[2],
    s[1] - s[2],
    s[3],
    s[4]
>>

hadamard_2(s) == <<
    s[1],
    s[2],
    s[3] + s[4],
    s[3] - s[4]
>>

F(b) == 0

u(f(_),s) == <<
    s[1 + f(0)],
    s[2 - f(0)],
    s[3 + f(1)],
    s[4 - f(1)]
>>


vars == << S, actions >>

Init == (* Global variables *)
        /\ S = << 0, 1, 0, 0 >>
        /\ actions = << >>

Next == /\ \E i \in 1..3:
             actions' = Append(actions, i)
        /\ Assert(actions' /= <<1, 3>>, 
                  "Failure of assertion at line 42, column 5.")
        /\ S' = S

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Invariant == ~(S[1] = 0 /\ S[2] = 2)


=============================================================================
\* Modification History
\* Last modified Wed Jun 20 16:28:44 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
