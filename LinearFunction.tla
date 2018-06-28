----------------------------- MODULE LinearFunction -----------------------------

EXTENDS TLC, Naturals, Integers, Sequences


(* --algorithm computeFunction

variables
    AST = << >>;
    SubASTs = { };
    possibleExpr = SubASTs \union {<<"const", x>> : x \in 1..3} \union {<<"var", "x">>};
    possibleLists = {<<"nil">>};
define


    RECURSIVE compute(_, _)
    compute(expr, x) == 
       CASE Head(expr) = "+" -> <<"const", compute(expr[2], x)[2] + compute(expr[3], x)[2]>>
        [] Head(expr) = "*" -> <<"const", compute(expr[2], x)[2] * compute(expr[3], x)[2]>>
        [] Head(expr) = "const" -> expr
        [] Head(expr) = "var" /\ expr[2] = "x" -> x
        [] Head(expr) = "nil" -> << "nil" >>
        [] Head(expr) = "cons" -> << "cons", compute(expr[2], x), compute(expr[3], x) >>

        [] Head(expr) = "map" ->
            \* << map, expr, << "nil" >> -> << "nil" >>
            \* << map, expr, << cons, head, body >> -> compute(<< cons, compute(expr, head), << map, expr, body>>)
            \* << map, expr, << map, expr2, list >>
            CASE expr[3] = << "nil" >> -> << "nil" >>
             [] Head(expr[3]) = "cons" -> compute(<<"cons", compute(expr[2], compute(expr[3][2], x)), <<"map", expr[2], expr[3][3] >> >>, x)
             [] Head(expr[3]) = "map" -> compute(<<"map", expr[2], compute(expr[3], x) >>, x)
            
end define;

begin
print compute(<<"map", <<"*", <<"var", "x">>, <<"const", 40>> >>, <<"cons", <<"const", 1>>, <<"cons", <<"const", 2>>, <<"nil">>>>>>>>, 2);
\*print compute(<<"map", <<"var", "x">>, <<"cons", <<"const", 1>>, <<"nil">>>>>>, 1);
while TRUE do
    with exprPair \in (possibleExpr \X possibleExpr) do
        either
            AST := << "*", exprPair[1], exprPair[2] >>;
            possibleExpr := possibleExpr \union {AST};
        or 
            AST := << "+", exprPair[1], exprPair[2] >>;
            possibleExpr := possibleExpr \union {AST}; 
        or
            with list \in possibleLists do
                either
                    AST := << "cons", exprPair[1], list >>;
                    possibleLists := possibleLists \union {AST};
                or
                    AST := << "map", exprPair[1], list >>;
                    possibleLists := possibleLists \union {AST};                
                end either;
            end with;
        end either;
    end with;
end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES AST, SubASTs, possibleExpr, possibleLists, pc

(* define statement *)
RECURSIVE compute(_, _)
compute(expr, x) ==
   CASE Head(expr) = "+" -> <<"const", compute(expr[2], x)[2] + compute(expr[3], x)[2]>>
    [] Head(expr) = "*" -> <<"const", compute(expr[2], x)[2] * compute(expr[3], x)[2]>>
    [] Head(expr) = "const" -> expr
    [] Head(expr) = "var" /\ expr[2] = "x" -> x
    [] Head(expr) = "nil" -> << "nil" >>
    [] Head(expr) = "cons" -> << "cons", compute(expr[2], x), compute(expr[3], x) >>

    [] Head(expr) = "map" ->



        CASE expr[3] = << "nil" >> -> << "nil" >>
         [] Head(expr[3]) = "cons" -> compute(<<"cons", compute(expr[2], compute(expr[3][2], x)), <<"map", expr[2], expr[3][3] >> >>, x)
         [] Head(expr[3]) = "map" -> compute(<<"map", expr[2], compute(expr[3], x) >>, x)


vars == << AST, SubASTs, possibleExpr, possibleLists, pc >>

Init == (* Global variables *)
        /\ AST = << >>
        /\ SubASTs = { }
        /\ possibleExpr = (SubASTs \union {<<"const", x>> : x \in 1..3} \union {<<"var", "x">>})
        /\ possibleLists = {<<"nil">>}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(compute(<<"map", <<"*", <<"var", "x">>, <<"const", 40>> >>, <<"cons", <<"const", 1>>, <<"cons", <<"const", 2>>, <<"nil">>>>>>>>, 2))
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << AST, SubASTs, possibleExpr, possibleLists >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E exprPair \in (possibleExpr \X possibleExpr):
              \/ /\ AST' = << "*", exprPair[1], exprPair[2] >>
                 /\ possibleExpr' = (possibleExpr \union {AST'})
                 /\ UNCHANGED possibleLists
              \/ /\ AST' = << "+", exprPair[1], exprPair[2] >>
                 /\ possibleExpr' = (possibleExpr \union {AST'})
                 /\ UNCHANGED possibleLists
              \/ /\ \E list \in possibleLists:
                      \/ /\ AST' = << "cons", exprPair[1], list >>
                         /\ possibleLists' = (possibleLists \union {AST'})
                      \/ /\ AST' = << "map", exprPair[1], list >>
                         /\ possibleLists' = (possibleLists \union {AST'})
                 /\ UNCHANGED possibleExpr
         /\ pc' = "Lbl_2"
         /\ UNCHANGED SubASTs

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Invariant == \/ Len(AST) = 0
             \/ ~(
                /\ compute(AST, <<"const", 1>>) = <<"const", 4>>
                /\ compute(AST, <<"const", 2>>) = <<"const", 11>>
                /\ compute(AST, <<"const", 3>>) = <<"const", 30>>
                )

testList == << "cons",
                    <<"const", 1>>,
                    <<"cons",
                        <<"const", 2>>,
                        <<"nil">>
                    >>
                >>
\* TODO: `compute` needs to differentiate between x as number vs as list 
\*Invariant == Len(AST) = 0
\*             \/ ~(
\*                compute(AST, testList) =
\*                compute(<<"map", <<"+", <<"const", 1>>, <<"var", "x">> >>, testList>>, <<"const", 11>>)
\*               )

=============================================================================
\* Modification History
\* Last modified Thu Jun 28 01:30:54 EDT 2018 by adampalay
\* Created Wed Jun 20 15:31:47 EDT 2018 by adampalay
