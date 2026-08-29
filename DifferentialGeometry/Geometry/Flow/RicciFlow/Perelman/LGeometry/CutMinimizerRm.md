# Curvature-bounded minimizing L-rays

## Result

`lMinVec_min_rm` is the noncompact fixed-endpoint action-minimality bridge for
a minimizing L-ray. It assumes a uniform norm-square bound for the Riemann
tensor on the relevant regular backward slab, obtains a curve-independent
lower bound from `lRegCosts_bdd_rm`, and applies `lRegCostC1_le_bdd`.

No `CompactSpace`, completeness, or caller-supplied `BddBelow` hypothesis is
used. The cost identity is the same one used by `lMinVec_reg_min`.

## Verification and progress

Focused verification passes without warnings, and the targeted
`CutMinimizerRm` module refresh passes. `lMinVec_min_rm` and its dedicated
curvature-bounded action-minimality machinery are complete (100%). The theorem
is the verified noncompact producer used by `exists_lTail_inj`.
