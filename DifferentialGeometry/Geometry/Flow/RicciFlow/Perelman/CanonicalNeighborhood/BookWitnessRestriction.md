# BookWitnessRestriction

Chapter25 task; claimfa0ebd7d-4a30-47d7-8b75-f18a0eaf4892.
VERIFIED 2026-09-10: saved check2 EMPTY20.96s, named build1 passed49.28s
(including unchanged WindowedWitnessRestriction refresh), fresh four-public
BookWitnessAxioms1 passed19.06s, all standard-only. Receipt:
E:/lean-tools/chapter25-book-20260910/book-limit-completion.json.

The first check exposed only an additive translation order mismatch and an
ambiguous scoped Topology open. Use add_lt_add_right for t+a<t+b in this tree,
and open Topology scope before the nested namespace. Both were corrected.

Book `lem:scn-model-witness-stability`, restriction half. Reuse the verified
`WindowedModelWitness.mono_of_regular`; derive its regular-time condition
from actual backward-window containment and `interior D.carrier <= D.regular`.
The standard half-open interval supplies this inclusion without a new input.
The existing closed-source theorem continues to serve normalization.

The strict norm comparison is retained even when delta=epsilon. The same model,
embedding, pullback, time jets and orientation survive. This is not the openness
half: recentering and perturbing a strict witness remain separate work.

Do not erase the interval qualification in the generic theorem. Native
RealTimeInterval allows its regular set to be strictly smaller than the carrier
interior; IsSolutionOn's smoothness and equation are asserted on that regular
set. The original arbitrary-D oriented_witness_mono remains an unresolved
overgeneralized interface and is not consumed here.

Receipts: E:/lean-tools/chapter25-book-20260910/. Current compiler/claim state:
WORKING_STATUS.md. No earlier-lane edit or new admission.
