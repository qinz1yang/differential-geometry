# HeatEarlyGlobal

## Proved source boundary

`HeatEarlyGlobal.lean` defines the actual Bochner heat potential on the full
early slab `(0,t/2] x V` and proves a time-uniform source-Carleson bound.

The proof is concrete:

1. split space into shells of width `sqrt t`;
2. cover shell `k` by at most `(5(k+1))^n` balls of radius `sqrt t` using the
   transported De Giorgi quantitative cover;
3. apply `SrcCarl` on each associated parabolic cylinder;
4. use `heatKernel_early` for `exp(-k^2/4)` decay;
5. weaken to `exp(-k/4)` and invoke Mathlib's canonical summability of a
   polynomial times an exponentially decaying sequence.

`earlyHeatC_ne_top` records that the resulting ENNReal constant is finite.
No desired heat estimate is stored as an input field.

## Verification and frontier

Source-written while another agent held the serial Lean slot; focused Lean
verification is pending.  The file contains no `sorry`, `admit`, axiom,
opaque declaration, or heartbeat override.

Together with `HeatPotentialLate.heatLate0_src`, this closes the mathematical
`Y⁰ -> C⁰` heat-potential estimate.  The next analytic arms are the
weighted-gradient supremum and gradient-Carleson estimates for the same heat
potential, followed by the actual rough fixed-point map.  The endpoint
`ricci_flow_forward_unique` remains 0%.
