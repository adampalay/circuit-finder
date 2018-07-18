----------------------------- MODULE LispFinder -----------------------------

EXTENDS Integers, Sequences, TLC

(*--algorithm LispFinder

variables AST = << >>,
        possibleExpr = ({<<"const", x>>: x \in 1..4} \union {<<"var", "x">>});

define
RECURSIVE compute(_, _)
compute(expr, x) ==
   CASE Head(expr) = "+" -> compute(expr[2], x) + compute(expr[3], x)
    [] Head(expr) = "*" -> compute(expr[2], x) * compute(expr[3], x)
    [] Head(expr) = "-" -> compute(expr[2], x) - compute(expr[3], x)
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

\* END TRANSLATION


\* can we discover x^2 - 9?
Invariant == ~(
    /\ Len(AST) > 0
    /\ compute(AST, 1) = -8
    /\ compute(AST, 2) = -5
    /\ compute(AST, 3) = 0
)


=============================================================================
\* Modification History
\* Last modified Wed Jul 18 13:11:55 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
