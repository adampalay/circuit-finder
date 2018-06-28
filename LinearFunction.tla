----------------------------- MODULE LinearFunction -----------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm computeFuntion

variables
    AST = << >>;
    SubASTs = { };
    possibleExpr = SubASTs \union {<<"const", x>> :x \in 1..3} \union {<<"var", "x">>};
define

    RECURSIVE compute(_, _)
    compute(expr, x) == 
       CASE Head(expr) = "+" -> compute(expr[2], x) + compute(expr[3], x)
        [] Head(expr) = "*" -> compute(expr[2], x) * compute(expr[3], x)
        [] Head(expr) = "const" -> expr[2]
        [] Head(expr) = "var" /\ expr[2] = "x" -> x 

        
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
   CASE Head(expr) = "+" -> compute(expr[2], x) + compute(expr[3], x)
    [] Head(expr) = "*" -> compute(expr[2], x) * compute(expr[3], x)
    [] Head(expr) = "const" -> expr[2]
    [] Head(expr) = "var" /\ expr[2] = "x" -> x


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

Invariant == \/ Len(AST) = 0
             \/ ~(
                /\ compute(AST, 1) = 3
                /\ compute(AST, 2) = 6
                /\ compute(AST, 3) = 11
                )


=============================================================================
\* Modification History
\* Last modified Wed Jun 27 22:20:38 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
