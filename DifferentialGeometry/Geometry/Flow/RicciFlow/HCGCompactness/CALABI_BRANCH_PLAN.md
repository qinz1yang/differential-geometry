# Calabi fixed-first branch plan

## Architecture ruling (2026-07-24)

The approved route fixes the early split at `s₀ = 1 / 4`:

```text
finite-distance minimizing geodesic O → x
  → early point p = γ(1/4)
  → nonconjugacy of the long tail p → x and a short extension past time 1
  → fixed-first inverse branch of expₚ at the nonzero tail vector
  → intrinsic Jacobi/Bishop comparison on the whole tail
  → checked branch Laplacian–mean identity
  → ρ(y) = d(O,p) + branchRadiusₚ(y)
  → local distance upper support
```

The endpoint comparison must use some `b > 1`; the checked
`curveMean_le_hyp` concludes only for `t ∈ Set.Ioo 0 b`.  Dimension one is a
separate `Fin 0` branch and must not be hidden behind `0 < finrank ℝ E - 1`.

## Canonical API

Add `Geometry/Exponential/ExpInvBranch.lean`.

- `ExpInvBranch` is a fixed-first `PartialDiffeomorph` inverse branch for
  `expMapIntrinsic g hEnorm p`.
- `branch_of_not_conj` constructs it at an arbitrary nonconjugate vector.
- `ExpInvBranch.not_conj` reads derivative injectivity back from a selected
  source point.
- `DiagInvBranch.fixed` is the compatibility projection used by existing
  zero-section/moving-base consumers.

`DiagInvBranch` remains unchanged as the stronger zero-section object.  Do not
glue an unrelated zero branch to a nonzero branch, and do not create a second
branch-radius/Hessian hierarchy.

## Dependency order

1. **Fixed-first inverse**
   - `ExpInvBranch`
   - the minimal manifold-derivative/chart-IFT bridge
   - `branch_of_not_conj`
   - `ExpInvBranch.not_conj`
   - `DiagInvBranch.fixed`
2. **Fixed-first calculus migration**
   - `BranchRadius`
   - `EndpointShape`
   - `RadialLaplacian`
   - existing diagonal consumers continue through `.fixed`
3. **Minimizing-tail nonconjugacy**
   - `conjVec_reverse`
   - `tail_not_conj_of_min`
   - `tail_no_conj`
4. **Whole-tail intrinsic comparison**
   - intrinsic Jacobi evaluation and raw pole-germ agreement
   - `exists_intrMean`
   - explicit `finrank ℝ E - 1 = 0` branch
5. **Calabi assembly**
   - `ExpInvBranch.edist_le_radius`
   - `CalabiTailData`
   - `exists_calabiTail`
   - `calabiDist_support`

Only after the fixed-metric support theorem is checked should
`Evolution/DistanceBarrier.lean` add time differentiation and the
solution-generated barrier-cutoff family.

## Constraints

- No `ConnectedSpace M`, endpoint injectivity-radius, cut-time, branch, or
  nonconjugacy assumption in the final support theorem.
- No raw/C²-radius assumption along the long tail.
- No HCG/C4 import below the flow layer.
- Keep the fixed-metric calculation intrinsic away from the pole; raw
  coordinates are used only for the pole germ.
- The branch path only needs to bound distance by its length.  It need not be
  locally minimizing for nearby endpoints.

## Live status

- `ExpInvBranch`, `branch_of_not_conj`, and `ExpInvBranch.not_conj`: theorem
  and dedicated IFT machinery **100%**, focused/exact green.
- `DiagInvBranch.fixed`: theorem **100%**, focused/exact green.
- `minExp_of_ne_top`: theorem and finite-pair Hopf--Rinow machinery **100%**,
  focused/exact green with no `ConnectedSpace M`; the former long theorem is
  now a compatibility wrapper.
- Fixed-first calculus migration: `BranchRadius`,
  `ExpInvBranch.edist_le_radius`, `EndpointShape`, `RadialLaplacian`,
  `DiagInvFixed`, and `CartanLocal` are focused green. The first three
  proof-owning modules are exact-current through the lint-clean
  `BishopIntrinsic` refresh; the final compatibility refreshes remain to be
  coordinated. The underlying radial Hessian/Laplacian mathematics remains
  **100%**.
- `conjVec_reverse`: theorem and dedicated reversal machinery **100%**,
  focused/exact green.
- `not_conj_of_min_len`, `minSeg_edist`, `tail_not_conj_of_min`, and
  `tail_no_conj`: theorem and dedicated minimizing-tail machinery **100%**,
  focused/exact green with no `ConnectedSpace M` or added endpoint hypothesis.
- `exists_intrMean`: theorem and dedicated whole-tail intrinsic comparison
  machinery **100%**, focused/exact green, including the explicit empty
  `Fin 0` branch.  Direct axiom replay reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `CalabiTailData`, `exists_calabiTail`, and `calabiDist_support`: theorem and
  dedicated fixed-metric support machinery **100%**, focused/exact green.
  Direct axiom replay for both minimizing-tail capstones and the final support
  theorem contains only `propext`, `Classical.choice`, and `Quot.sound`.
- The next named theorem is
  `scaledDist_calabiUpperSupport_of_sol` in `Evolution/DistanceBarrier.lean`;
  theorem-level **0%**.  Its remaining seam is to retain the two fixed paths
  from the Calabi construction for the Ricci-flow time derivative, plus the
  separate one-dimensional curvature specialization.
- Selected Route B-prime complete-Shi producer machinery: about **55%**.
- Dedicated P4 consumer/assembly machinery: about **98%**.
- Whole HCG supporting machinery: about **60%**.
- Unconditional `compactnessSol`: theorem-level **0%**.

Update this section after each focused-green producer.  A checked helper does
not change theorem-level completion until the named endpoint itself is stated
and proved.
