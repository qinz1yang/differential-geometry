# RicciPreservation.lean

## 2026-07-12 — short-time branch alignment

- Pointwise tensor arithmetic now distinguishes real `smul` from natural-number
  `nsmul`; the latter is handled by the new canonical `Tensor0SSpace.nsmul_apply`.
- `scalarMetric1Sec` and `scalarMetric2Sec` were moved before their consumers so the
  proofs reuse the canonical section objects instead of exposing pointwise
  `product_fun` representations.
- Mixed reaction evaluation and the zero-vector branch now use small exact evaluation
  lemmas, including multilinearity at the zero slot tuple, rather than representation
  unfolding through `simp`.
- Focused verification passed without `sorry`; this compatibility repair is complete
  (100%) and has no remaining blocker. The existing Ricci-preservation theorem content
  is unchanged.
- The headline short-time theorem remains complete (100%); branch-alignment integration
  is about 98% pending the Hamilton target rerun. This does not change the separate
  completion percentage of the Hamilton endpoint theorem itself.

## 2026-06-13

Updated the dimension-three algebraic curvature symmetry call to the cleaned
Levi-Civita wrapper, removing the now-obsolete explicit local smoothness
argument.

Verification: focused check passed.  No new `sorry` or `admit`.
