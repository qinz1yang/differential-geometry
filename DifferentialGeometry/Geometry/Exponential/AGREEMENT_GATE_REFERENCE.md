# Agreement-gate reference: minimizing => no conjugate => exp local diffeo => injective branch

Route/reference note for the intrinsic lane's declared next target
(`IntrinsicVelocity.md`, "Next target"): ordinary/intrinsic exponential
agreement on the sub-injectivity ball and the canonical injective branch,
feeding `NormalRadiusProfile.le_exp_radius`
(`Flow/RicciFlow/HCGCompactness/C4/MetricCompactnessInputs.lean`).

Source surveyed: frenzymath/Poincare-Conjecture (Apache-2.0), read-only clone,
files under `MorganTian/PoincareLib/Ch01/`.  POLICY: reference only — no
imports, no proof-body copying, no tracking; statement shapes below are short
excerpts for route identification.  The Volume lane's option-1 ledger
(`Comparison/VOLUME_COMPARISON_PLAN.md`, 2026-07-19) flagged this same chain
as shared with our gate.

## Dictionary (their objects -> ours)

| reference | ours |
|---|---|
| `globalGeodesic g hg p v : ℝ → M` (choice, whole-line) | `intrinsicGeodesic g hEnorm p v` (`Exponential/IntrinsicExp.lean`) |
| `expMapGlobal g hg p v = globalGeodesic … 1` | `expMapIntrinsic g hEnorm p v` (same file) |
| `IsConjugatePointAt g γ t₁` (∃ Jacobi pair `(J,DJ)`, `J 0 = 0`, `J t₁ = 0`, `J ≢ 0`; `Ch01/JacobiManifold.lean`) | `IsConjVec g hEnorm p x` = vector-slot `mfderiv` of `expMapIntrinsic` not injective at `x`; Jacobi phrasing via `isConjVec_iff_jacobi` (`Exponential/ConjugatePoint.lean`).  Their def is curve+time; ours is launch-vector-at-parameter-1 — already the shape their chain consumes. |
| `IsMinimizingUpTo g hg p v t` : `dist p (γ_v t) = √g_p(v,v) · t` (`Ch01/CutLocus.lean`) | no named predicate; produced by `hopf_rinow_expMapIntrinsic_surjective_minimizing` (`Exponential/MinimizingGeodesic.lean`) |
| `cutTime`, `segmentDomain U_p = {v | 1 < cutTime v}` (`Ch01/CutLocus.lean`) | `injRadius` (chart-framed, `Comparison/InjectivityRadius.lean`); no cut-time object yet |
| `globalGeodesic_smul : γ_{c•v} = fun s => γ_v (c*s)` | `intrinsicGeodesic_smul : intrinsicGeodesic p (t•u) 1 = intrinsicGeodesic p u t` (`IntrinsicExp.lean:1852`) |

## The reference chain

### Step 1 — minimizing => nonnegative index form (half 2)
`indexForm_nonneg_of_minimizing` (`MinimalGeodesicNoConjugate.lean`).
Hypotheses: geodesic on `[a,b] ⊇ [0,1]`, minimizing on `[0,1]`
(`√speedSq ≤ dist (γ 0) (γ 1)`), parallel ON frame `e`, test field split at a
corner `c ∈ (0,1)` into `C³` halves `W₀ W₁` matching at `c`, vanishing at the
endpoints.  Conclusion: `0 ≤ I_{[0,c]}(W₀,W₀) + I_{[c,1]}(W₁,W₁)`.
Proof route: broken chart variation glued into genuine curves (six files:
`BrokenVariationData/Glue`, `PieceSecondVariation`, `BrokenEnergy`,
`Junction*`), `s = 0` a local min of energy, second-derivative test.
OURS: `indexForm_nonneg_of_minimising_geodesic`
(`Comparison/Variation/SecondVariationMinimiser.lean`) is already proved —
for a single globally SMOOTH perpendicular endpoint-vanishing field, with
minimality stated as `arcLength γ ≤ arcLength η` over `C¹` endpoint-fixed
competitors.  If half 1 delivers its witness smooth (next step), the entire
six-file broken-variation cluster does NOT need porting.

### Step 2 — conjugate point => strictly negative index form (half 1)
`exists_indexForm_neg_smooth_of_isConjugatePointAt`
(`IndexFormNegativeSmooth.lean`, fed by `IndexFormNegative.lean`,
`IndexFormConjugate.lean`).  Interior conjugate time of the frame-coordinate
ODE `y'' + R(t) y = 0` produces a (broken, per-half `C³`) endpoint-vanishing
field with strictly negative index form: truncated Jacobi field = null
direction with a corner, then a corner-smoothing perturbation goes negative.
Entirely abstract (inner-product space + frame coordinates), no manifold.
OURS: not present — this is the hard brick (N-d half 1 in the Volume ledger).
It plugs directly into our frame-coordinate machinery: `parInner_deriv/_d2`,
`jacobi_unique` (`Comparison/Variation/JacobiCoord.lean`), `ode2_pi_zero`,
`forward_ode2_of_bound` (`Analysis/ODE/SecondOrderLinearExistence.lean`),
`gON_expand` (`Metric/FiberExpansion.lean`).  Port target: deliver the witness
fully smooth + perpendicular so step 1's OUR form applies verbatim.
(Perpendicularity is derivable: `⟨J, γ̇⟩` is affine in `t`, zero at both ends.)

### Step 3 — collision: minimizing => no interior conjugate point
`not_isConjugatePointAt_of_minimizing` (`MinimalGeodesicNoConjugate.lean`):
```
(ha : a < 0) (hb : 1 < b) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
(hgeo : IsGeodesicOn g γ (Icc a b)) (hmin : √(speedSq g γ 0) ≤ dist (γ 0) (γ 1))
: ¬ IsConjugatePointAt g γ t₀
```
Two lines: half 1 gives `< 0`, half 2 gives `≥ 0`, `linarith`.  The endpoint
`t₀ = 1` is excluded and MUST stay excluded (sphere antipode).

### Step 4 — rescaling bookkeeping to the radial form
`NoConjugateOfMinimizing.lean` — pure bookkeeping, no new geometry:
`speedSq_globalGeodesic_smul` (speed scales by `c²`),
`minimizing_radial_Ioo_of_minimizing_radial` (minimizing to `r₀` => minimizing
on every sub-segment; triangle inequality + 1-Lipschitz),
`not_isConjugatePointAt_of_minimizing_radial_Ioo` (half-open-interval form:
rescale by an INTERMEDIATE `s' ∈ (s, r₀)` so `s` becomes interior),
`isConjugatePointAt_of_comp_mul_left` (conjugate-point transport out of a
rescaling), and the consumer shape
`not_isConjugatePointAt_one_of_minimizing_radial`: for unit `u`, `0 < c < r₀`,
minimizing on `[0,r₀)` => no conjugate point of `γ_{c•u}` at parameter `1`.
OURS: engine is `intrinsicGeodesic_smul`; because `IsConjVec` is already the
parameter-1 launch-vector shape, our port states `¬ IsConjVec p (c•u)`
directly and needs the transport lemma only through `isConjVec_iff_jacobi`.

### Step 5 — differential singular <=> conjugate; IFT => local diffeo
`expDifferential_injective_iff_not_conjugate` (`ConjugateDifferential.lean`):
given the Jacobi property of the chart-read differential
(`D (DJ 0) = chartVectorRep … J 1`, from
`hasStrictFDerivAt_chartReading_expMapGlobal`, `ExpLocalDiffeo.lean`),
`Function.Injective D ↔ ¬ IsConjugatePointAt g γ_v 1`.  Two supporting facts:
chart reading injective (`tangentCoordChange_injective`) and "Jacobi field
vanishing identically has `DJ a = 0`" + Groenwall uniqueness (`eqOn_zero`).
Then `ExpLocalDiffeo.lean`: `expDifferential_isEquiv_of_not_conjugate`
(finite dimension: injective => `E ≃L[ℝ] E`) and
`expMapGlobal_locallyInjective_of_not_conjugate`
(`HasStrictFDerivAt.toOpenPartialHomeomorph` = IFT).  NO CURVATURE BOUND
anywhere.  Composed with step 4:
`expDifferential_isEquiv_of_minimizing_radial`,
`expMapGlobal_locallyInjective_of_minimizing_radial`
(`NoConjugateOfMinimizing.lean`), and the general-vector normalization
`expMapGlobal_localDiffeo_of_minimizing` (`ExpMinimizingLocalDiffeo.lean`):
minimal on `[0,1]`, `v ≠ 0`, `t₀ < 1` => sub-minimality + differential
isEquiv + local injectivity at `t₀ • v`.
OURS: the differential<->Jacobi bridge is DONE (`isConjVec_iff`,
`isConjVec_iff_jacobi` via `intrinsic_jacobi_one`,
`Exponential/JacobiVariation.lean`); smoothness of the vector slot is DONE and
stronger (`intrinsicFiber_smooth`, `Exponential/IntrinsicVelocity.lean`, C∞
globally).  Missing: N-c endpoint identity `D_t J_w(0) = w`; the
"nontrivial-Jacobi-vanishing-at-both-ends" two-direction bridge (uniqueness
side = `jacobi_unique`); and the mechanical `¬IsConjVec x => mfderiv is a
linear equiv => expMapIntrinsic IsLocalDiffeomorphAt x` IFT wrapper (chart
reading; cf. `Exponential/LocalDiffeomorphism.lean`, currently zero-vector
chart-`expMap` only).

### Step 6 — uniqueness of the minimal geodesic; global injectivity
`MinimalGeodesicUnique.lean`: `dist_eq_speed_mul_of_minimizing` (sub-segments
minimize), `eqOn_of_minimizing_geodesic_of_minimizing_geodesic` /
`minimalGeodesic_restrict_unique` (Part 1: a second minimal geodesic `μ`
meeting `γ` at an INTERIOR `t₀ < 1` coincides on `[0,t₀]`; concatenation +
no-corner), radial consumer `globalGeodesic_eqOn_of_minimizing`.
`SegmentInjective.lean`: `injOn_expMapGlobal_segmentDomain` — exp injective on
`U_p = {v | 1 < cutTime v}`: endpoint meeting upgraded to interior meeting by
rescaling with a common `c ∈ (1, min cutTimes)`, uniqueness, then equal
initial chart velocities => `v = w`; plus `measurableSet_segmentDomain`.
OURS: both engines exist — `broken_minimizer_velocity_match` (no-corner) and
`geo_eqOn_of_init` (uniqueness from equal initial data), both in
`Exponential/MinimizingGeodesic.lean` / `IntrinsicExp.lean`; the Part-1
assembly and the segment-domain injectivity statement are unstated.

### Contrast — the curvature-bound variant
`ExpBallDiffeo.lean` (theirs) reaches the same no-conjugate hypothesis on
`B(0, π/√K)` from `|Rm| ≤ K` via Sturm.  Our
`Comparison/ExpBallDiffeo.lean` (`exists_expBall_diffeo_of_lt`) is the
analogue but capped by `expRadiusGp`; the reference chain shows the cap and
the curvature bound are BOTH removable inside the minimizing radius.

## Mapping to the gate objects

- Agreement today is germ-scale only: `expDiffeoRadius` = min of the
  `exists_expMapIntrinsic_eq_expMap_radius` witness and `expRadiusGp`
  (`Exponential/MinimizingGeodesic.lean`), with `expDiffeo_eq_intr` /
  `expDiffeo_mem_of_lt`.  Beyond the launch chart the chart-fixed `expMap` is
  junk, so the big-ball statement must be about `expMapIntrinsic` itself
  (agreement holds wherever the realized chart object is defined; the
  reference has only ONE exponential and never faces this split).
- `DiagInvBranch` (`Exponential/DiagInvBranch.lean`) is the canonical branch
  container: `OpenPartialHomeomorph (TangentBundle I M) (M × M)`, forward =
  intrinsic `diagExp`, inverse C∞; `inv_eq_normal_lt` already identifies the
  inverse with `normalChartAt` inside `expDiffeoRadius`.  The gate = produce a
  branch whose source covers the sub-injectivity ball, using steps 3–6 for
  injectivity + local diffeo (quantitative radii stay producer data).
- `injRadius` (`Comparison/InjectivityRadius.lean`) is `sSup` of radii on
  which chart-framed `framedExpMap` is injective; relating it to the intrinsic
  ball IS part of the agreement statement (framedExpMap is chart-junk beyond
  `expRadiusGp`, so either re-express `injRadius` intrinsically or state the
  gate against a minimizing/intrinsic radius as the reference does with
  `cutTime`).

## Suggested port order (smallest first)

1. N-c: endpoint identity `D_t J_w(0) = w` for the variation field of
   `intrinsic_jacobi` (check `velocityLift_zero` / IntrinsicVelocity exports
   first).  Routine.
2. Conjugate-bridge closure: `¬IsConjVec p x <=> no nontrivial Jacobi field
   along `intrinsicGeodesic p x` with `J 0 = 0 = J 1`` — assembly of
   `isConjVec_iff_jacobi` + `jacobi_unique` + (1).  Their
   `ConjugateDifferential.lean` shape.  Routine-plus.
3. IFT wrapper: `¬IsConjVec p x` + finite dimension => vector-slot mfderiv is
   a `≃L` => `expMapIntrinsic p` is `IsLocalDiffeomorphAt` at `x` (their
   `ExpLocalDiffeo.lean`).  Mechanical; missing-API risk only.
4. Rescaling bookkeeping (their `NoConjugateOfMinimizing.lean`): sub-segment
   minimality + conjugate transport via `intrinsicGeodesic_smul`.  Cheap.
5. Half 1 (their `IndexFormNegative[Smooth].lean`): interior conjugate time =>
   SMOOTH perpendicular endpoint-vanishing field with `I < 0`, abstract
   frame-ODE level over our `parInner_*`/`jacobi_unique`/`ode2` machinery.
   THE hard brick.
6. Collision (their `MinimalGeodesicNoConjugate.lean` endpoint): minimizing =>
   `¬IsConjVec` interior, via OUR half 2 — needs the dist-minimizing =>
   arcLength-minimizing-among-`C¹`-competitors bridge and the tangential
   split.  Moderate.
7. Part-1 uniqueness + segment injectivity (their `MinimalGeodesicUnique.lean`,
   `SegmentInjective.lean`) from `broken_minimizer_velocity_match` +
   `geo_eqOn_of_init`.  Moderate.
8. Canonical branch on the sub-injectivity ball (`DiagInvBranch` producer) +
   the agreement statement, then the `NormalRadiusProfile.le_exp_radius`
   producer.  Endpoint assembly.

## Already covered by our stack

`intrinsic_jacobi` / `intrinsic_jacobi_one`; `IsConjVec` interface;
`jacobi_unique` + second-order ODE layer; half 2 for smooth fields
(`indexForm_nonneg_of_minimising_geodesic`); Hopf–Rinow minimizing vectors
(`hopf_rinow_expMapIntrinsic_surjective_minimizing`); no-corner + initial-data
uniqueness engines; `intrinsicGeodesic_smul`; C∞ time and vector-slot
regularity; germ agreement + `DiagInvBranch`/readout interface; `injRadius`.

## Genuinely open

Half 1 (item 5) is the only substantial mathematical frontier; items 6–8 are
statement/assembly work with known engines; items 1–4 are small.  The
endpoint (`le_exp_radius` producer) remains 0% until stated — everything here
is machinery FOR it, and this survey changes no endpoint percentage.
