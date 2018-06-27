----------------------------- MODULE LinearFunction -----------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm linear

variables
    AST = << >>;
    SubASTs = { };
    possibleExpr = SubASTs \union {<<"const", x>> :x \in 1..3} \union {<<"var", "x">>};

define

    RECURSIVE compute(_, _)
    compute(expr, x) == 
       CASE expr[1] = "+" -> compute(expr[2], x) + compute(expr[3], x)
        [] expr[1] = "*" -> compute(expr[2], x) * compute(expr[3], x)
        [] expr[1] = "const" -> expr[2]
        [] expr[1] = "var" /\ expr[2] = "x" -> x

end define;

begin
while TRUE do
    with exprPair \in (possibleExpr \X possibleExpr) do
            either
                AST := << "*", exprPair[1], exprPair[2] >>;
                possibleExpr := possibleExpr \union {AST};
            or 
                AST := << "+", exprPair[1], exprPair[2] >>;
                possibleExpr := possibleExpr \union {AST};
           
            end either;
    end with;
end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES AST, SubASTs, possibleExpr

(* define statement *)
RECURSIVE compute(_, _)
compute(expr, x) ==
   CASE expr[1] = "+" -> compute(expr[2], x) + compute(expr[3], x)
    [] expr[1] = "*" -> compute(expr[2], x) * compute(expr[3], x)
    [] expr[1] = "const" -> expr[2]
    [] expr[1] = "var" /\ expr[2] = "x" -> x
    [] expr[1] = "list" -> Tail(expr)
    [] expr[1] = "map" ->
        IF Len(expr[3]) = 1
        THEN << >>
        ELSE <<compute(Head(Tail(expr[3])), expr[2])>>
            \o
            compute(<<"map", expr[2], <<"list">> \o Tail(Tail(expr[3]))>>, x)


vars == << AST, SubASTs, possibleExpr >>

Init == (* Global variables *)
        /\ AST = << >>
        /\ SubASTs = { }
        /\ possibleExpr = (SubASTs \union {<<"const", x>> :x \in 1..3} \union {<<"var", "x">>})

Next == /\ \E exprPair \in (possibleExpr \X possibleExpr):
             \/ /\ AST' = << "*", exprPair[1], exprPair[2] >>
                /\ possibleExpr' = (possibleExpr \union {AST'})
             \/ /\ AST' = << "+", exprPair[1], exprPair[2] >>
                /\ possibleExpr' = (possibleExpr \union {AST'})
        /\ UNCHANGED SubASTs

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Invariant == Len(AST) = 0 \/ ~(compute(AST, 1) = 16 /\ compute(AST, 2) = 20)


=============================================================================
\* Modification History
\* Last modified Wed Jun 27 18:14:14 EDT 2018 by adampalay
\* Last modified Thu Jun 21 17:18:46 EDT 2018 by emanuel
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
