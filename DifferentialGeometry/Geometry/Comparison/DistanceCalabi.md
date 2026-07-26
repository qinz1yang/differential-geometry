# DistanceCalabi.lean

## 2026-07-23 — broken paths and the terminal Calabi branch

- This canonical comparison-layer module packages the routine metric and
  inverse-branch facts needed before constructing a Calabi distance support.
- `edistOf_le_arcLength` installs the supplied smooth metric locally and reuses
  the checked geodesic-layer path-length comparison.
- `edistOf_le_two_arcs` combines the one-arc result with the Riemannian extended
  distance triangle inequality at the common endpoint.
- `calabi_tail_of` starts from the finite-distance Hopf–Rinow minimizing
  witness, follows its intrinsic velocity lift, and uses openness of a supplied
  `DiagInvBranch` to choose `0 < s₀ < 1`.  Continuation and spray homogeneity
  prove that the scaled remaining velocity exponentiates to the endpoint;
  `DiagInvBranch.inv_eq_of_exp` then identifies the selected inverse.  The
  theorem also records that the endpoint pair lies in the branch target
  domain, which is the openness seam needed by the later local support.
- The proof uses a private connectivity-free continuity lemma for fiberwise
  scalar multiplication along a continuous total-space curve.
- `exists_calabi_tail` specializes the preceding result to `stdBranch`.
- No Ricci-flow, connectedness, injectivity-radius, or cut-locus hypothesis is
  introduced.  Completeness occurs only in the Hopf–Rinow terminal-tail result;
  the two broken-path estimates remain completeness-free.
- The whole module, including the `stdBranch` corollary, is focused GREEN with
  zero diagnostics, and its exact targeted refresh is GREEN (`3807/3807`).

Accounting: the elementary broken-path metric brick and terminal inverse-branch
selection are 100%; together they are about 10% of the spatial Calabi-support
producer.  The public `scaledDist_calabiUpperSupport_of_sol` theorem remains
0%; Route B-prime producer machinery remains about 35%; unconditional
`compactnessSol` remains 0%; whole HCG support remains about 60%.

## 2026-07-23 — spatial-support audit after `RadialLaplacian`

- The intended next public result is still a fixed-metric
  `calabiDist_support`: choose a suitable interior point of a minimizing
  geodesic, use a selected fixed-first inverse branch there, and take the
  broken-path constant plus `branchRadius`.  The checked
  `branchLap_eq_mean` theorem has exactly the required denominator and does
  not require connectedness.
- The construction itself is componentwise.  No `ConnectedSpace M`
  hypothesis is mathematically needed or permitted at this endpoint.
- The initial audit found that `VolumeComparison.exists_radial_mean` carried a
  stale `[ConnectedSpace M]` requirement inherited through `exists_radial_cmp`,
  `radial_wronsk_zero`, `exists_radialJacobi_zero_radius`, and
  `exists_jacobi_zero`.
- The first owning declaration was `JacobiVariation.jacobi_zero_of_lt`.
  Its proof's only endpoint acceleration input is the already
  connectivity-free `Exponential.exp_radial_d2_zero`; the private
  `clamped_slice_covDeriv_velocity_zero_at_zero` has the same stale
  `ConnectedSpace` binder.  The canonical repair removed that unused binder
  there and weakened the existing public declarations along the chain above,
  without a parallel wrapper or a new support-side assumption.
- The separate `intrinsic_jacobi_d0` theorem also carried a stale
  `ConnectedSpace` binder even though its current proof uses the
  connectivity-free `intrinsicVar_smooth`.  It is not the direct Bishop-chain
  blocker; it was weakened in the same upstream cleanup.
- Dimension one is not a mathematical blocker.  The final support proof should
  split on `0 < finrank ℝ E - 1`: the positive branch uses
  `exists_radial_mean`, while the zero branch uses the empty transverse family,
  for which `curveMean` and hence the branch Laplacian are zero.

## 2026-07-24 — half-segment audit after the assumption cleanup

- The weakest-assumption cleanup is now complete and exact-current throughout
  the Bishop chain.  It therefore no longer blocks this file.
- A deeper length-direction obstruction remains.  The current
  `calabi_tail_of` selects `s₀` near `1`, because its supplied
  `DiagInvBranch` is centered at zero in `TₓM`.  Thus the selected radial
  segment from `q = γ(s₀)` to `x` has length
  `ell = (1 - s₀) * edistOf g O x`, with no positive lower bound in terms of
  the original distance.  Applying `branchLap_eq_mean` and
  `exists_radial_mean` on that segment produces the pole
  `(finrank ℝ E - 1) / ell`; making the terminal tail smaller only makes this
  estimate worse.
- The required endpoint constant
  `2 * (finrank ℝ E - 1) / edistOf g O x` needs a selected subsegment whose
  remaining length is at least half the original distance.  The standard
  choice is an interior half segment, but its launch vector is nonzero in the
  tangent space at its fixed first endpoint.
- No checked producer currently turns minimizing/no-conjugacy data for that
  nonzero launch vector into the required local inverse branch of the
  exponential map.  `MinimalGeodesicNoConjugate.not_conj_of_min` supplies only
  an interior no-conjugacy statement in the current orientation; it neither
  constructs a nonzero-centered exponential branch nor supplies the
  reverse-orientation/conjugate-symmetry bridge needed at the chosen launch
  point.
- The smallest honest next API is therefore a canonical theorem producing a
  fixed-first local inverse branch of `expMap` around a nonzero vector from the
  corresponding minimizing-segment/no-conjugacy fact (including the required
  endpoint orientation transport).  Once that exists, the half-segment
  selection, broken-path support, gradient estimate, and Bishop bound are
  local assembly.

Current blocker classification: genuine missing geometric/API infrastructure,
not a call-site coercion or a mechanical assumption cleanup.  It is a
substantial but standard local-inverse/no-conjugacy bridge.  No new support
theorem was stated here, because an added branch hypothesis or an arbitrary
terminal-tail estimate would hide the missing mathematics and would not prove
the requested constant.

Accounting: `calabiDist_support` is not yet stated or proved (0%); its dedicated
fixed-metric machinery is about 55% after the exact-current inverse-branch and
radial-Laplacian bricks.  The public
`scaledDist_calabiUpperSupport_of_sol` theorem remains 0%; Route B-prime
producer machinery is about 45%; unconditional `compactnessSol` remains 0%;
whole HCG support remains about 60%.
## 2026-07-24 deterministic whole-tail package

`CalabiTailData` is now stated and focused green. It records exactly the
fixed-first data selected at the deterministic split time `1 / 4`: the early
point and long tail vector, the length split and half-length lower bound, one
`ExpInvBranch`, a source point mapping to the endpoint, and nonconjugacy on an
open interval `(0,b)` with `b > 1`.

This is output data, not a new minimizing, radius, or cut-locus assumption.
The producer `exists_calabiTail` is not yet proved because it depends on the
active conjugacy-reversal and shifted-tail theorem. `CalabiTailData` is 100%;
`exists_calabiTail` and `calabiDist_support` remain theorem-level 0%. Route
B-prime remains about 45%, whole HCG supporting machinery about 60%, and
unconditional `compactnessSol` theorem-level 0%.

## 2026-07-24 fixed-metric assembly in progress

- `minSeg_edist` now isolates the exact minimizing-subsegment distance
  calculation used at the deterministic quarter point.  Its proof uses the two
  radial length upper bounds, the endpoint minimizing equality, and ENNReal
  cancellation; it does not add a minimizing predicate.
- Source declarations for `exists_calabiTail` and `calabiDist_support` are now
  present.  They follow the approved architecture literally: quarter split,
  shifted-tail nonconjugacy, `ExpInvBranch`, source openness past time one,
  `exists_intrMean`, `branchLap_eq_mean`, and
  `ExpInvBranch.edist_le_radius`.
- The support proof uses the new neighborhood-local
  `laplacian_add_const` and `gradientFun_mdiffOn`; it does not pretend that
  `branchRadius` is globally smooth.
- These two endpoint declarations are not yet counted as proved.  Their first
  focused elaboration waits on the active arbitrary-length generalization of
  the negative-index-form theorem and the resulting `tail_no_conj` export.

Current blocker classification: routine lower-layer API generalization from
`[0,1]` to `[0,L]`, not a new geometric hypothesis or a new mathematical
frontier.  `conjVec_reverse` and `exists_intrMean` are already checked.  Both
`exists_calabiTail` and `calabiDist_support` remain theorem-level 0% until
focused green; their dedicated fixed-metric machinery is about 75%.  The
evolving-distance support and solution-generated cutoff remain separate 0%
theorems, Route B-prime producer machinery is about 50%, whole HCG supporting
machinery remains about 60%, and unconditional `compactnessSol` remains 0%.

## 2026-07-24 fixed-metric Calabi support closed

`exists_calabiTail` and `calabiDist_support` are now focused- and exact-green.
The deterministic quarter split, endpoint and whole-tail nonconjugacy,
fixed-first inverse branch, intrinsic Bishop comparison, upper-support
inequality, unit-gradient calculation, and branch Laplacian readout all check
without an additional radius, cut-time, minimizing, or connectedness
assumption.

Direct axiom replay for `tail_not_conj_of_min`, `tail_no_conj`, and
`calabiDist_support` reports only `propext`, `Classical.choice`, and
`Quot.sound`; none depends on `sorryAx`.

Theorem accounting: `exists_calabiTail` and `calabiDist_support` are each
**100%**; their dedicated fixed-metric machinery is **100%**.  The next
theorem-level frontier is the evolving Ricci-flow support
`scaledDist_calabiUpperSupport_of_sol`, still **0%**.  Selected Route B-prime
complete-Shi producer machinery is about **55%**, dedicated P4
consumer/assembly machinery about **98%**, whole HCG supporting machinery about
**60%**, and unconditional `compactnessSol` remains theorem-level **0%**.

## 2026-07-24 evolving-support provenance refactor

The fixed-metric proof now has a provenance-preserving public producer,
`exists_calabiData`.  It returns the selected `CalabiTailData` and keeps the
support definition explicit as
`tail.left + branchRadius g tail.branch`.  Its checked output includes smoothness
at the selected point, equality with the distance there, the local upper-support
inequality, neighborhood spatial differentiability, differentiability of the
gradient section, exact unit gradient norm, and the final Laplacian bound.
`calabiDist_support` is now only the compatibility projection that forgets the
tail and the two regularity fields not present in its original statement.

`CalabiTailData` also records `left_pos`; the existing `left_nonneg` field is
retained.  The deterministic quarter-split constructor proves both.  This
positive early length is the fact needed to select a regular first fixed path
for the evolving Ricci-flow support.

The refactored source is focused-green with zero diagnostics and contains no
new `sorry`; no exact refresh was run in this shared write window.  The theorem
accounting is unchanged: `exists_calabiData`, `exists_calabiTail`, and
`calabiDist_support` are theorem-level **100%**, while
`scaledDist_calabiUpperSupport_of_sol` remains theorem-level **0%**.  Its
dedicated Route B-prime producer machinery remains about **55%**; whole HCG
supporting machinery remains about **60%**, and unconditional
`compactnessSol` remains theorem-level **0%**.

The provenance refactor is now exact-current as well as focused-green.  The
refresh also rebuilt the fixed-first conjugacy and inverse-branch dependency
chain successfully.  This changes verification provenance only: the
fixed-metric Calabi theorem and machinery remain 100%, while the evolving
support is still accounted independently until its own module verifies.
