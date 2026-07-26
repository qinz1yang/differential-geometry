# RadialLaplacian

## Role

This is the comparison-facing assembly for the fixed-first selected inverse
branch.  The intended capstones are the intrinsic `branchLap_eq_mean` theorem
and its raw-model compatibility corollary `radialLap_eq_mean`; the latter must
retain the launch-speed denominator.

## 2026-07-23 source status

- `branchDeriv2_zero` is the first source brick.  It combines the checked local
  affine ray identity `branchRadius_ray` with germ invariance of iterated
  derivatives, and introduces no new geometric assumption.
- `branchHess_radial` consumes the canonical branch-layer
  `branchRadius_open` producer and uses `deriv2_comp_geo_on` to turn that
  ordinary second-derivative identity into the radial Hessian value `0`.
- The transverse entries come from `branchHess_shape`; `trace_eq_line_add` plus
  `lap_eq_hess_on` then own the final trace assembly.
- The endpoint perpendicularity step reuses the canonical
  `intrinsicJacobi_perp`; it does not reproduce the dependent tangent-space
  transport from Gauss's lemma in this consumer.

## Compatibility capstone

- `radialLap_eq_mean` is the raw chart-facing compatibility theorem.  It uses
  `exp_eq_intr_of_c2` to identify the raw radial curve with the intrinsic
  geodesic on the named C2 ball, and it transports the raw radial Jacobi family
  to the intrinsic Jacobi family by germ equality.
- The fixed-first branch is chosen once from the raw endpoint.  The theorem
  then calls `branchLap_eq_mean` for the scaled launch vector `t • x`; it does
  not select a moving inverse branch.
- The conclusion retains the mandatory denominator
  `sqrt (g.inner p x x)`.  No unit-speed normalization, connectedness
  hypothesis, extra agreement radius, or wrapper assumption is introduced.

## Verification

Focused verification passed with no diagnostics, and the exact target artifact
is current.

## Honest accounting

- `branchDeriv2_zero`, `branchHess_radial`, and `branchLap_eq_mean`: theorem
  and dedicated machinery 100%; focused/exact-green.
- `radialLap_eq_mean`: theorem and dedicated source machinery 100%;
  focused/exact-green.
- Dedicated fixed-first radial Laplacian bridge: 100%.
- Route B-prime distance-barrier/cutoff machinery: roughly 50%; the independent
  compact-support maximum-principle and quantitative cutoff estimates remain.
- HCG supporting machinery: roughly 60%; unconditional `compactnessSol`
  remains theorem-level 0%.

## 2026-07-24 `ExpInvBranch` migration

The proof-owning statements `branchDeriv2_zero`, `branchHess_radial`,
`branchLap_eq_mean`, and `radialLap_eq_mean` now consume the canonical
fixed-first `ExpInvBranch`. Existing diagonal applications are recovered by
projecting through `DiagInvBranch.fixed`; no second radius/Hessian/Laplacian
hierarchy remains.

The migrated source is focused green and placeholder-free. The fixed-first
radial Laplacian theorem and its dedicated machinery remain 100%.
`calabiDist_support` itself remains unstated and therefore 0%; Route B-prime
remains about 45%, whole HCG supporting machinery about 60%, and
unconditional `compactnessSol` theorem-level 0%.
