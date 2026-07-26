# Strong reversed conjugate heat

## Completed

`conjA2MR` and `conjA1MR` put the genuine moving-Laplacian and scalar-potential
operators into the literal `a + 2` / `a + 1` exponent normal forms consumed by
maximal regularity.  They precompose with the canonical spectral inclusion,
which is the identity on coefficients and has norm at most one.

`conj_inputs` shrinks the two producer intervals to one positive interval,
transfers continuity and bounds to the adapted operators, and proves the
combined contraction inequality.  The same interval is now also chosen inside
the near-zero genuine A2 graph neighborhood.  `conj_strong_exists` then applies
`nonaut_strong_exists` at `a = r = s = 0` and returns the A2 graph certificate
plus the a.e. identifications of both Duhamel companion fields with
`timeH1.toFun`.  All measurability and norm-bound proofs are existential outputs,
not new consumer assumptions.

`conj_weak_ae` is the first geometric weak-equation consumer.  Almost
everywhere in time it supplies the pointwise Sobolev representatives, the
scalar time derivative against every finite smooth H2 test, the moving-
Laplacian residual in the closed genuine finite-core graph, and the exact A1
multiplier pairing against every finite H1 test.  It selects no measurable
family of core approximants and adds no consumer assumption.  Its A2 conclusion
is deliberately a closed-core graph statement, not yet a test-side
formal-adjoint identity or a classical weak-PDE package.

Focused verification of the current source passes.  The required named
upstream refreshes also pass.  This file has no local warning, `sorry`, or
`admit`.

## Exact remaining frontier

The checked result is now a spectral strong solution together with its a.e.
scalar closed-core weak equation.  It still does not produce the jointly smooth
scalar field required by `IsHeatPotOn`.

The eventual public assembly theorem is `heatpot_of_maxreg` (17 characters),
best placed in a new `Entropy/ConjRegularity.lean` file.  Its generic analytic
engine belongs below Entropy in
`Analysis/Spectral/Intrinsic/HeatSemigroup/ScalarNonautRegularity.lean`.
On every strictly shorter interval it should turn the canonical scalar
maximal-regularity solution with smooth initial data and smooth
metric/potential coefficients into an `IsHeatPotOn` field, without adding a
regularity or realization assumption to the Entropy consumer.  One reconstructed
field should work on all shorter intervals.  The public theorem must accept a
smooth initial scalar field, not arbitrary H2 data, because
`IsHeatPotOn.sliceSmooth` includes time zero.

The finite-core-to-weak-realization issue is now closed in the selector-free
scalar graph normal form.  The producer must still genuinely address three
issues:

1. prove interior regularity for the genuinely second-order non-autonomous A2
   term, without replacing it by a first-order coupling;
2. upgrade all-order spatial/time information to joint spacetime smoothness;
3. upgrade the resulting continuous derivative representative to the pointwise
   `HasDerivAt` equation.

The existing `solField_into_all_tensorHs_interior` route does not close this:
it yields only `L²_t(H^sigma)` and its coupling hypothesis is first order,
whereas A2 is order two.  `PointwiseDeriv.lean` also needs a continuous time
derivative representative that the current strong theorem does not provide.
The exact next frontier is therefore the genuine second-order non-autonomous
bootstrap, not another realization wrapper.

The first missing mathematical producer inside that bootstrap is
`scalar_crit_tame` (16 characters), best placed in
`Analysis/Spectral/Intrinsic/Garding/ScalarNonautTame.lean`.  Its finite-core
normal form must hold uniformly on a shorter interval and at every natural
Sobolev order `k`:

```text
norm (((Delta_(G(T-t)) - Delta_q) + V(T-t)) v) in H^k(q))
  <= delta * norm (v in H^(k+2)(q))
     + C(k) * norm (v in H^(k+1)(q)),   delta < 1.
```

The small highest-order coefficient is `G(T-t)^-1 - q^-1`; time shrinking
absorbs it.  Derivatives of the coefficients, the connection difference, and
the scalar potential belong in the `C(k)` lower-order term.  This is the exact
estimate needed by the cross-scale Galerkin dissipation argument.

Three existing routes do not supply it: the current interior-smoothing theorem
loses only one derivative; the proved critical dissipation/tame theorems are
specialized to DeTurck `(0,2)` tensors; and the rank-generic fixed-background
Garding estimates do not by themselves control the moving principal
coefficient at every order.  Adding a theorem with this conclusion as an
unproved consumer hypothesis would only hide the live analytic frontier, so no
such wrapper was introduced.

## Consult prompt

The local A2/A1 producers and `ConjStrong.lean` may be ahead of the pushed
branch.  Attach those local files to the consultation; use the GitHub branch
below as the project-wide code reference rather than claiming it contains the
unpublished edits.

```text
I am working in a large Lean 4/mathlib differential-geometry project. Do not write code first. Diagnose the analytic/API obstruction and give only the next smallest producer theorem.

Target theorem:
`heatpot_of_maxreg` (new theorem name must stay <= 20 characters), in a new native file
`DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/ScalarNonautRegularity.lean`.

Desired role/statement normal form:
Given the canonical `a = 0` scalar maximal-regularity strong solution produced by
`Entropy.conj_strong_exists`, smooth initial scalar data, and the already-proved smooth
Ricci-flow metric/scalar-potential coefficients, show on every strictly shorter interval
`[0,tau']`, `0 < tau' < tau`, that there exists a jointly smooth scalar field `v` satisfying
`IsHeatPotOn` for the reversed metric and potential, with the prescribed initial field.
Do not add a classical-regularity or geometric-realization hypothesis to the consumer.

Current checked input:
- `conj_strong_exists`: `u : timeH1 H^0`, a companion `L2_t(H^2)` field, trace equality,
  and the time-L2 equation for the genuine adapted A2/A1 continuous-linear maps.
- `lapDiffA20_core` and `scalarPotOp_core`: geometric realization only on finite spectral core.
- A2 is genuinely second order `H^2 -> H^0`; A1 is `H^1 -> H^0`.

Exact obstruction:
- `IsHeatPotOn` requires joint C-infinity, closed-carrier joint continuity, smooth slices,
  and a pointwise `HasDerivAt` equation.
- `solField_into_all_tensorHs_interior` only gives L2-in-time all-order spatial regularity and
  assumes a first-order coupling `H^(d+1) -> H^d`, so it cannot absorb the genuine second-order A2.
- `maxreg_l2deriv_to_pointwise_hasderivwithinat` requires a continuous derivative representative.
- no theorem currently extends the finite-core geometric realization to arbitrary H2/H1 values in
  the weak/distributional equation used by the fixed point.

What was tried/audited:
1. fixed-semigroup interior smoothing: wrong order for A2 and only L2_t regularity;
2. all-scale time-continuity route: specialized to the DeTurck `(0,2)` first-order coupling and still
   does not give joint spacetime smoothness;
3. pointwise derivative bridge: blocked because the RHS has only an L2 representative;
4. pointwise smooth representative selection at each time: not parameter-continuous and not joint smooth.

GitHub reference to inspect before answering:
- Branch: https://github.com/liao9yuan/differential-geometry/tree/short-time-existence
- Nonautonomous engine: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/Nonautonomous.lean
- Solution space: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/SolutionSpace.lean
- Classical interface: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/ScalarTimeDependent.lean
- Existing interior smoothing: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/ParabolicInteriorSmoothing.lean
- Pointwise derivative bridge: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Intrinsic/PointwiseDeriv.lean
- Local changed files to attach: `ConjStrong.lean`, `ConjPotential.lean`, `MetricLapDiffH0.lean`, `MetricLapDiffMeas.lean`, and `ScalarPotential.lean`.

Constraints:
- Work in `DifferentialGeometry/`; do not import or edit RFreference.
- No `HasLocallyConstantChartAt`.
- No new consumer assumptions or regularity wrapper hypotheses.
- Preserve the existing A2/A1 public APIs.
- Avoid whole-tensor/whole-Hom definitional equalities; use applied or weak scalar normal forms.
- Prefer one narrow producer theorem over a broad parabolic refactor.
- Explicitly cite the GitHub files/lines you used.

Tasks:
1. Classify whether the smallest honest next step is weak realization, second-order interior bootstrap,
   joint-smooth reconstruction, or a different statement split.
2. Give the precise Lean statement of the first producer theorem only, with all necessary hypotheses and
   no consumer-facing frontier assumptions.
3. Identify existing project/mathlib lemmas that should prove it, with direct GitHub references.
4. Give the proof architecture and the exact next file to edit.
5. State the failure signal that should make the implementing agent stop and consult again.
```

## Consult result -- 2026-07-13

The Pro consultation is recorded at
<https://chatgpt.com/g/g-p-6a05f8e7fb0881918ae46beec6dcd123-lean-pro-consult-handoff/c/6a55177e-6170-83e8-9ff4-1f55d9ded76c>.
It confirmed the following dependency order:

1. applied A2 graph closure;
2. A1 exact scalar testing;
3. a time-L2 scalar closed-core weak equation;
4. a genuine second-order non-autonomous bootstrap;
5. joint-smooth reconstruction and pointwise time differentiation.

Steps 1--3 are now verified by `lapDiffA20_graph` / `lapDiffA20_test`,
`scalarPotH0_test`, and `conj_weak_ae`.  The stop rule from
the consultation was also respected: no measurable or continuous selector of
finite-core approximants was introduced.  The precise live frontier is step 4.

## Progress accounting

- genuine A2 and A1 input producers: 100%;
- specialized spectral strong-existence theorem: 100%;
- `conj_weak_ae`: proved and focused-verified (100% as this intermediate
  theorem);
- `heatpot_of_maxreg`: not stated/proved (0%); its directly reusable machinery
  is about 35%;
- classical moving conjugate-heat existence theorem: 0%; its dedicated
  analytic machinery is about 77%;
- Perelman no-local-collapsing and `ham3_noncollapse`: 0%; dedicated analytic
  producer machinery is about 40%;
- whole HCG compactness machinery remains about 53%, with endpoint theorems 0%.

## Bootstrap stop -- 2026-07-13

The low-level scalar coefficient route now has genuine moving-trace and
connection-difference fields, fully applied scalar read-offs, generic `appCc`
jet bounds, and rank-generic spectral/jet conversion.  These producers make a
fixed-order estimate feasible with principal coefficient
`A(k) * K2(0)` and a one-derivative remainder independent of spectral support.

That fixed-order normal form does not close the current all-order Galerkin
consumer.  Its absorption hypothesis uses one top coefficient below `2` for
every order, while `A(k)` is order-dependent; one time shrink cannot be assumed
to dominate all `A(k)`.  This is the fifth independent route problem in the
second-order bootstrap audit, after the first-order smoothing mismatch,
DeTurck rank/family specialization, non-isolating fixed-background Gårding, and
the high-order Galerkin projection mismatch.

The next consultation must decide whether to prove a direct covariant
dissipation/commutator theorem with order-zero ellipticity as the uniform top
coefficient, move the full principal operator to the left-hand side, or replace
the all-order consumer by a bootstrap that works on one fixed shorter interval.
No fixed-order estimate has been mislabeled as the completed
`scalar_crit_tame`.

`heatpot_of_maxreg` remains unstated/unproved (0%) with about 35% directly
reusable machinery.  The classical moving conjugate-heat theorem remains 0%
with about 77% dedicated machinery; Perelman no-local-collapsing remains 0%
with about 40% dedicated analytic machinery; whole HCG machinery remains about
53%, with endpoint theorems at 0%.

## Moving dissipation consult -- 2026-07-13

The completed follow-up consultation is at
<https://chatgpt.com/g/g-p-6a05f8e7fb0881918ae46beec6dcd123-lean-pro-consult-handoff/c/6a55679f-4250-83e8-9f44-f3b67243e7ff>.
It was asked to consult the GitHub `short-time-existence` branch.  Only the
published non-autonomous maximal-regularity layer could be verified there; the
post-merge DeTurck and commutator files were unavailable remotely and were
audited from the live worktree instead.

After correcting the raw commutator from order one to order three, the direct
moving-dissipation route remains viable, but only in balanced bilinear form.
The fixed-order `A(k)` estimate and the fixed-scale bootstrap remain rejected:
neither supplies one common all-order interval.  A full variable-coefficient
maximal-regularity refactor is much larger than the scalar route.  The selected
producer chain is therefore flux splitting, principal pairing, balanced
commutator pairing, and moving dissipation; the coefficient-one Dirichlet gap
enters only at final energy assembly.

`appCc_assoc` and `covDiv_appCc` are focused-verified.  The divergence proof is
performance-stable only when it reuses the named associativity theorem; a
consumer-local whole-Hom extensionality proof deterministically times out.  The
next genuine producer is the scalar `trace_slot_flat` metric/cometric
naturality identity for an arbitrary covariant rank-two input.  It then feeds
`trace_retag_eq`, the native coefficient factorization, and
`scalar_flux_split`.

The endpoint accounting does not change: `heatpot_of_maxreg`, the classical
moving conjugate-heat theorem, Perelman no-local-collapsing, and
`ham3_noncollapse` remain 0% as theorems.  Dedicated machinery is about 35%,
77%, and 40% respectively; whole HCG machinery remains about 53%, with its
endpoints at 0%.

## Principal pairing update -- 2026-07-14

The scalar coefficient-to-flux split and the small principal pairing are now
proved and focused-verified.  In particular, `cc_principal_pair` isolates the
order-zero perturbation coefficient `delta / (1 - delta)` without a
spectral-support-dependent constant or a new consumer hypothesis.

The next producer remains the balanced `cc_comm_pair`.  The existing public
raw-commutator theorem is third order, rank-two-specific, and tied to a
resolvent family, so it cannot serve as this producer.  The mathematically
correct transport-and-telescope proof exists privately in the DeTurck energy
pairing file; the current task is to extract its base-rank-generic core and
specialize it to scalars.  Moving dissipation and the final Dirichlet gap remain
downstream of that extraction.

The endpoint accounting is unchanged: `heatpot_of_maxreg`, the classical
moving conjugate-heat theorem, Perelman no-local-collapsing, and
`ham3_noncollapse` remain 0% as theorems.  Dedicated machinery is about 35%,
77%, and 40% respectively; whole HCG machinery remains about 53%, with its
endpoints at 0%.

## Balanced scalar dissipation update -- 2026-07-14

The generic passenger-slot transport and its scalar adapters are now proved
and verified.  In particular, `cc_comm_pair` and `cc_energy_diss` give the
support-independent high-order moving-cometric pairing with sharp top
coefficient `delta / (1 - delta)` and only adjacent covariant-jet windows.

This is machinery progress, not completion of `heatpot_of_maxreg`.  The live
frontier is the rank-generic coefficient-one Dirichlet gap followed by the
finite-core scalar weighted-pairing identification needed by the Galerkin
consumer.  Time smallness can be selected internally from `metric_cp_tendsto`,
so no new convergence assumption is required.

Honest accounting: `heatpot_of_maxreg`, the classical moving conjugate-heat
theorem, Perelman no-local-collapsing, and `ham3_noncollapse` remain 0% as
theorems.  Dedicated machinery is about 35%, 77%, and 40% respectively;
`scalar_crit_tame` remains 0% with about 72% dedicated machinery.  Whole HCG
machinery remains about 53%, with endpoints at 0%.
