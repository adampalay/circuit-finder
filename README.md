# circuit-finder
use tla+ to synthesize lisp expressions and circuits (classical or quantum)

[TLA+](http://lamport.azurewebsites.net/tla/tla.html) helps you check for bugs in the designs of your systems.
The idea is you use TLA+ to specify your program as a state machine, then check to verify that certain undesireable
states are unreachable. For [example](https://www.learntla.com/introduction/example/), you might want to check that your
algorithm for facilitating intra-bank transfers doesn't change the total amount of money the bank holds.

Circuit-finder is based on an idea that you can think of activity of programming itself as a kind of state machine.
As you construct a program, line by line, you alter the "state" of the program you're writing. If we work with a
restricted programming language and have clear specifications, then presumably we can use TLA+ to construct
programs from their specifications.

This repo contains some examples of these generated programs.

[LispFinder](https://github.com/adampalay/circuit-finder/blob/master/LispFinder.tla) searches a simplified space of Lisp programs of the type `Integer -> Integer` to synthesize programs from specifications. The current version of LispFinder discovers `x^2 + 1` from the specification that the inputs of `0`, `1`, and `2` should return `1`, `2`, and `5`, respectively. LispFinder is a proof of concept that at least simple programs can be generated from specification.

[XfromNAND](https://github.com/adampalay/circuit-finder/blob/master/XfromNAND.tla)
simulates classical chip construction. Starting with two input wires and only using NAND gates, XfromNAND can then
be induced to construct any number of other logic gates. In this case, it implements an adder with a carry. But you can
imagine changing [`Goal`](https://github.com/adampalay/circuit-finder/blob/master/XfromNAND.tla#L8) to the truth table
of an `AND` gate, a `NOT` gate, or any other number of logical gates.

[DeutschAlgorithm](https://github.com/adampalay/circuit-finder/blob/master/DeutschAlgorithm.tla) "discovers" a simple
quantum computing algorithm, [Deutsch's Algorithm](https://en.wikipedia.org/wiki/Deutsch%E2%80%93Jozsa_algorithm#Deutsch's_algorithm),
through specifying [available quantum gates](https://github.com/adampalay/circuit-finder/blob/master/DeutschAlgorithm.tla#L10)
and [the condition we want the algorithm to discover](https://github.com/adampalay/circuit-finder/blob/master/DeutschAlgorithm.tla#L65-L73).

This approach to program generation generally isn't scalable, since TLA+ exhaustively searches the space of
possible programs. But it works very well for these three examples!
