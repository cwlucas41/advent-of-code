# 2022 - Day 01

## Goal
Practice using TLA+/PlusCal for formal verification after reading and working through https://www.learntla.com/ and some of http://lamport.azurewebsites.net/tla/tutorial/intro.html.

## TLA
Wrote specs for both parts (not including input parsing) and learned some things:
* TLC enforcing invariants, action properties, liveness, and termination at the push of a button was great for writing the algorithm and having confidence the PlusCal implementation was correct.
* [using `while` loops considered harmful](https://learntla.com/topics/tips.html#while-loops-considered-harmful) - I didn't realize this until after writing but that's something I learned by experience. Having global index variables for looping was awkward and the state size definitely exploded.
    * Something I struggled with here is having separation between the code in the Liveness property and in the algorithm being verified.
    * Perhaps I indexed too strongly on Lamport saying the following in the abstract [here](https://lamport.azurewebsites.net/pubs/pluscal.pdf) and literally wrote imperative pseudocode for the PlusCal algorithm:
        >  PlusCal is an algorithm language that can be
used right now to replace pseudo-code, for both sequential and concurrent
algorithms
* I found the TLA [CommunityModules](https://github.com/tlaplus/CommunityModules) and would have had a much harder time without them
* I spent most of my time here writing the invariants and properties. Writing the PlusCal imperatively was relatively straightforward, and even describing the invariants and properties wasn't too bad - it was figuring out how to precisely describe the ideas in mathematical language that took time. I think with practice I could get better at that part and that shows me where to focus my time when doing further study of TLA.
* I'd love for someone who knows a thing or two about TLA to rip my code apart and give feedback on what I could have done differently with the invariants and properties I chose to check and how the algorithm could have been written more idiomatically.

## Python
Minimal effort here - file parsing and then directly translating the verified pseudocode into python.
* thoughts here are around how to verify that a spec matches the implementation when the port isn't this direct. How to keep bugs from subtly being introduced through translating to a different language.

## Overall
I think this was a decent first project for working with TLA. I'll want to try a concurrent algorithm next time so I won't be continuing to write TLA for AoC.
