# Neumann correction of the right parametrix

## Source facts

- `idAdd_isUnit` applies Mathlib's canonical
  `isUnit_one_sub_of_norm_lt_one` to `-B`, identifying `id + B` with
  `1 - (-B)` in the continuous-endomorphism Banach algebra.
- `neumannInv_right` and `neumannInv_left` prove the two exact cancellation
  identities for the canonical ring inverse.
- `splitError_lt_half` packages the intended quantitative split:
  `‖B₂‖ ≤ 1/4` and `‖B₁₀‖ < 1/4` imply
  `‖B₂ + B₁₀‖ < 1/2`.
- `corrected_right_inv` proves that `Q (id + B)⁻¹` is an exact right
  inverse whenever `TQ = id + B`.
- `split_right_inv` combines the exact split identity and the quarter bounds
  in the form needed by the retraction--coretraction parametrix.

The solution space and forcing space may differ.  Only the error acts as an
endomorphism of the complete forcing space, which is precisely where the
Neumann inversion belongs.

## Verification state

Source implementation completed on 2026-07-19.  Lean verification is pending
because the shared named build/export lane currently owns the build lock.  No
Lean process was started for this file, and no `sorry`, `admit`, axiom, opaque
placeholder, or new foundational instance was introduced.

The concrete error compositions and their norm bounds now live in
`RetractionParametrix`, with the fine `B₂` quarter estimate in
`FinePrincipalError`.  The remaining hard analytic input is not an abstract
Neumann assumption: it is the actual zero-trace frozen heat-potential PDE,
the W3p coefficient/jet maps, and their uniform estimates.  The endpoint
`ricci_flow_unif_existence` remains 0% until those inputs instantiate this
correction and the same-horizon geometric output is checked.
