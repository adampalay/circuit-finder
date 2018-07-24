----------------------------- MODULE LispFinder -----------------------------

EXTENDS Integers, Sequences, TLC

(*--algorithm LispFinder

variables AST = << >>,
          possibleExpr = ({<<"const", x>>: x \in 1..4}
                          \union {<<"var", "x">>});

define
RECURSIVE evaluate(_, _)
evaluate(expr, x) ==
   CASE Head(expr) = "+" -> evaluate(expr[2], x) + evaluate(expr[3], x)
    [] Head(expr) = "*" -> evaluate(expr[2], x) * evaluate(expr[3], x)
    [] Head(expr) = "-" -> evaluate(expr[2], x) - evaluate(expr[3], x)
    [] Head(expr) = "const" -> expr[2]
    [] Head(expr) = "var" /\ expr[2] = "x" -> x
end define;

begin
while TRUE do
    with expr1 \in possibleExpr do
        with expr2 \in possibleExpr do
            with op \in {"*", "+", "-"} do
                AST := << op, expr1, expr2 >>;
                possibleExpr := (possibleExpr \union {AST});
            end with;
        end with;
    end with;
end while;

end algorithm--*)
\* BEGIN TRANSLATION
VARIABLES AST, possibleExpr

(* define statement *)
RECURSIVE evaluate(_, _)
evaluate(expr, x) ==
   CASE Head(expr) = "+" -> evaluate(expr[2], x) + evaluate(expr[3], x)
    [] Head(expr) = "*" -> evaluate(expr[2], x) * evaluate(expr[3], x)
    [] Head(expr) = "-" -> evaluate(expr[2], x) - evaluate(expr[3], x)
    [] Head(expr) = "const" -> expr[2]
    [] Head(expr) = "var" /\ expr[2] = "x" -> x


vars == << AST, possibleExpr >>

Init == (* Global variables *)
        /\ AST = << >>
        /\ possibleExpr = ({<<"const", x>>: x \in 1..4}
                           \union {<<"var", "x">>})

Next == \E expr1 \in possibleExpr:
          \E expr2 \in possibleExpr:
            \E op \in {"*", "+", "-"}:
              /\ AST' = << op, expr1, expr2 >>
              /\ possibleExpr' = (possibleExpr \union {AST'})

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

\* can we discover x^2 + 1?
Invariant == ~(
    /\ Len(AST) > 0
    /\ evaluate(AST, 0) = 1
    /\ evaluate(AST, 1) = 2
    /\ evaluate(AST, 2) = 5
)

=============================================================================
\* Modification History
\* Last modified Sun Jul 22 11:00:16 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
