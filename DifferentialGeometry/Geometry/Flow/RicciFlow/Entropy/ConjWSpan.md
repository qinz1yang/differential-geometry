# Exact-interval Galerkin W comparison

## 2026-07-19 source assembly

`gallim_w_lt` removes the last lifespan shrink from the W comparison at every
strictly interior reverse time.  It uses the already verified local
`gallim_w_cont` only to obtain the right limit at zero, and uses the exact
`IsHeatPotOn` object to invoke `w_rev_antitone` throughout the caller's positive
interior.  Thus the unknown local continuity radius never controls how far W
can be propagated.

The strict upper endpoint is intentional.  Finite propagation can use steps
strictly below the common compact-span radius and retain a positive regular
time buffer; no continuity of the moving gradient at the far Galerkin endpoint
is asserted.

The source contains no local `sorry`.  Static review found and repaired the
final `W 0` normal-form mismatch by simplifying `a + 0` only after proving the
local inequality.  Focused verification is pending the upstream spectral
export refresh, so the theorem remains theorem-level **0%** with approximately
**90%** dedicated source until checked.  Finite Good-set propagation,
`NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level frontiers at
**0%**.

## 2026-07-23 post-merge check

The W comparison span now opens the tensor heat equation and L2 namespaces and
uses the correct right-addition monotonicity direction in the final inequalities.
Focused verification and the module artifact refresh both passed.
