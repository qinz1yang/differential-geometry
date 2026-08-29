# P2AxiomCheck

## Role

This diagnostic module imports the newly completed late-floor and fixed-time
ball-bound chain and asks Lean for the axioms of its public endpoints. It is not
part of the L-geometry umbrella and introduces no declarations.

## Verification

Focused verification is warning-free green. Every printed endpoint depends
only on Lean's standard logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`). No named artifact refresh is needed because this diagnostic
module exports no declarations.
