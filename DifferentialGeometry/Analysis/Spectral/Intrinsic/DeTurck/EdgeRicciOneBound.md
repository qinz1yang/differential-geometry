# EdgeRicciOneBound

## Current source state

`EdgeRicciOneBound.lean` contains a source-level, placeholder-free proof of the
closed-edge order-one Ricci estimate.  It has not yet received a focused Lean
check because verification is serialized behind the named refresh of
`EdgeRefoldPairing` and the focused check of `EdgeRicciPairing`.

The file exports:

- `ricci1Ker_rfns`: the exact five-arm order-one kernel has fibre norm square
  at most `46` times that of `connDiffContrInsertionField`;
- `ricci1Coeff_rfns`: after the moving four-trace contraction, the concrete
  coefficient is pointwise bounded by a carrier-dependent constant times
  `|nabla P|^2`; and
- `ricci1_path_le`: on `P = s W`, after shrinking a carrier-dependent `C0`
  radius, the signed order-one Ricci energy term costs at most
  `(1/8) * ||nabla W||^2`.

No derivative above `nabla W` occurs.  The proof uses the fixed-metric
connection-difference fibre bound, the order-zero four-trace grid at
derivative order zero, pointwise Cauchy--Schwarz, and spatial integration.

## Why the five-arm split is local

The canonical expansion exists in
`RicciConnDiffOrder1TameEnvelope.lean`, but its theorem
`kernelField_eq_neg_arm_combination` and its sharp arm permutations are
private implementation details.  The public tame-envelope wrapper requires a
high-jet radius and is therefore inadmissible at the closed edge.  This file
reproves only the finite five-arm identity with local permutations; it does
not introduce a new hypothesis or move the frontier behind an opaque
constant.

## Verification and downstream status

- Source placeholders (`sorry`, `admit`, axiom): none.
- Focused Lean check: pending serialized verification.
- Exact `ricci_flow_forward_unique`: **0%** until its unchanged endpoint is
  proved and axiom-checked.
- `extends_of_rmBounded`: unchanged.  This producer removes only the Ricci
  order-one child of the visible closed-edge pairing once verified and
  composed with the order-zero and DeTurck/refold children.
