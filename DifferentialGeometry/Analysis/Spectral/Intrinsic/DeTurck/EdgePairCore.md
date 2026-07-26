# EdgePairCore

## Purpose

`EdgePairCore.lean` is the acyclic algebraic core required by the closed-edge
Ricci pairing.  It imports only the canonical Palatini-refold, slot-insertion,
and tensor-divergence modules.  In particular, it does not import
`EdgeLowerPairing` or `EdgeRefoldPairing`.

The split is necessary because the current focused check of
`EdgeLowerPairing.lean` fails first at its line 62 binder (`I` is not in the
available local context) and later reaches unfinished addition/Young steps.
Those failures must not sit upstream of the already independent Ricci
pairing identities.

## Public facts

- `pairTrace_refold`: rewrites the moving-metric double trace as the fixed
  background trace after insertion of the relative inverse-metric
  endomorphism.
- `pairSlot2`: inserts a smooth tangent endomorphism into either covariant
  slot of a rank-two tensor.
- `pairSlot2_eval`: gives the pointwise component formula for that insertion.
- `pairProd4`: builds the rank-four product carrier from two rank-two
  covariant tensors.
- `pairProd4_eval`: evaluates that carrier as the product of its first and
  last covariant pairs.

The proofs are the corresponding existing algebraic proofs from
`EdgeRefoldPairing.lean`, with fresh declaration names and only their private
local helper lemmas retained.

## Verification state

- Source implementation: 100%.
- Static extraction comparison: exact after declaration renaming; the only
  harmless textual difference is the `Λ` binder spelling in `pairSlot2`.
- Placeholder audit: no `sorry`, `admit`, or `axiom`.
- Focused Lean verification: GREEN in 77.2 seconds, with no local warning.
- Named short-build export: GREEN, `9434/9434`; the replayed warnings are in
  pre-existing upstream files, not this module.
- Endpoint `ricci_flow_forward_unique`: 0%.  This file is machinery only.

After this file is focused GREEN and its exported `.olean` is refreshed,
`EdgeRicciPairing.lean` can replace its `EdgeRefoldPairing` import and its five
calls with the declarations above.  That downstream edit remains frozen until
the parent task authorizes it.
