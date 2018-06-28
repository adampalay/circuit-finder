----------------------------- MODULE LinearFunction -----------------------------

EXTENDS TLC, Naturals, Integers, Sequences

VARIABLES AST, possibleExpr

(* define statement *)
RECURSIVE compute(_, _)
compute(expr, x) ==
   CASE Head(expr) = "+" -> compute(expr[2], x) + compute(expr[3], x)
    [] Head(expr) = "*" -> compute(expr[2], x) * compute(expr[3], x)
    [] Head(expr) = "-" -> compute(expr[2], x) - compute(expr[3], x)
    [] Head(expr) = "const" -> expr[2]
    [] Head(expr) = "var" /\ expr[2] = "x" -> x


vars == << AST, possibleExpr >>

Init == (* Global variables *)
        /\ AST = << >>
        /\ possibleExpr = ({<<"const", x>>: x \in 1..4} \union {<<"var", "x">>})

Next == \E expr1 \in possibleExpr:
          \E expr2 \in possibleExpr:
            \E op \in {"*", "+", "-"}:
              /\ AST' = << op, expr1, expr2 >>
              /\ possibleExpr' = (possibleExpr \union {AST'})

Spec == Init /\ [][Next]_vars


\* can we compute x^2 +x + 1?
Invariant == ~(
    /\ Len(AST) > 0
    /\ compute(AST, 1) = 3
    /\ compute(AST, 2) = 7
    /\ compute(AST, 3) = 13
)


=============================================================================
\* Modification History
\* Last modified Thu Jun 28 12:27:53 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
