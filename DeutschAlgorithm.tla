-------------------------- MODULE DeutschAlgorithm --------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm qm

variables S = << 1, 0, 0, 0 >>,
    CircuitState = << >>;
    Gates = {"hadamard1", "Uf", "swap", "not1"};
    Uf_called = 0;


define
    hadamard1(s) == <<
        s[1] + s[3],
        s[2] + s[4],
        s[1] - s[3],
        s[2] - s[4]
    >>
    
    F(b) == 0
    F2(b) == 1
    F3(b) == b
    F4(b) == ~b
    
    u(f(_),s) == <<
        s[1 + f(0)],
        s[2 - f(0)],
        s[3 + f(1)],
        s[4 - f(1)]
    >>
    
    swap(s) == <<
        s[1],
        s[3],
        s[2],
        s[4]
    >>
    
    not1(s) == <<
        s[3],
        s[4],
        s[1],
        s[2]
    >>
    
    first_qubit_0(s) == (s[3] = 0) /\ (s[4] = 0)
    
    first_qubit_1(s) == (s[1] = 0) /\ (s[2] = 0)
    
    apply(gate, f(_), state) == 
        CASE gate = "hadamard1" -> hadamard1(state)
          [] gate = "Uf" -> u(f, state)
          [] gate = "swap" -> swap(state)
          [] gate = "not1" -> not1(state)
    
    
    RECURSIVE compute(_, _, _)
    compute(circuit, f(_), initial_state) == 
        IF Len(circuit) = 0
        THEN initial_state
        ELSE compute(Tail(circuit), f, apply(Head(circuit), f, initial_state))
        
    check_all(circuit, initial_state) ==
        first_qubit_0(compute(circuit, F, initial_state))
        /\ first_qubit_0(compute(circuit, F2, initial_state))
        /\ first_qubit_1(compute(circuit, F3, initial_state))
        /\ first_qubit_1(compute(circuit, F4, initial_state))
        /\ Uf_called <= 1
        
end define;

begin
while TRUE do
    
    with gate \in Gates do
       CircuitState := Append(CircuitState, gate);
       if gate = "Uf" then
           Gates := {"hadamard1", "swap", "not1"};
           Uf_called := Uf_called + 1;
       end if;
    end with;
    
end while;



end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES S, CircuitState, Gates, Uf_called

(* define statement *)
hadamard1(s) == <<
    s[1] + s[3],
    s[2] + s[4],
    s[1] - s[3],
    s[2] - s[4]
>>

F(b) == 0
F2(b) == 1
F3(b) == b
F4(b) == ~b

u(f(_),s) == <<
    s[1 + f(0)],
    s[2 - f(0)],
    s[3 + f(1)],
    s[4 - f(1)]
>>

swap(s) == <<
    s[1],
    s[3],
    s[2],
    s[4]
>>

not1(s) == <<
    s[3],
    s[4],
    s[1],
    s[2]
>>

first_qubit_0(s) == (s[3] = 0) /\ (s[4] = 0)

first_qubit_1(s) == (s[1] = 0) /\ (s[2] = 0)

apply(gate, f(_), state) ==
    CASE gate = "hadamard1" -> hadamard1(state)
      [] gate = "Uf" -> u(f, state)
      [] gate = "swap" -> swap(state)
      [] gate = "not1" -> not1(state)


RECURSIVE compute(_, _, _)
compute(circuit, f(_), initial_state) ==
    IF Len(circuit) = 0
    THEN initial_state
    ELSE compute(Tail(circuit), f, apply(Head(circuit), f, initial_state))

check_all(circuit, initial_state) ==
    first_qubit_0(compute(circuit, F, initial_state))
    /\ first_qubit_0(compute(circuit, F2, initial_state))
    /\ first_qubit_1(compute(circuit, F3, initial_state))
    /\ first_qubit_1(compute(circuit, F4, initial_state))
    /\ Uf_called <= 1


vars == << S, CircuitState, Gates, Uf_called >>

Init == (* Global variables *)
        /\ S = << 1, 0, 0, 0 >>
        /\ CircuitState = << >>
        /\ Gates = {"hadamard1", "Uf", "swap", "not1"}
        /\ Uf_called = 0

Next == /\ \E gate \in Gates:
             /\ CircuitState' = Append(CircuitState, gate)
             /\ IF gate = "Uf"
                   THEN /\ Gates' = {"hadamard1", "swap", "not1"}
                        /\ Uf_called' = Uf_called + 1
                   ELSE /\ TRUE
                        /\ UNCHANGED << Gates, Uf_called >>
        /\ S' = S

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

\*Invariant == ~(S[1] = 0 /\ S[2] = 2)


=============================================================================
\* Modification History
\* Last modified Thu Jun 21 18:57:38 EDT 2018 by adampalay
\* Last modified Thu Jun 21 17:18:46 EDT 2018 by emanuel
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
