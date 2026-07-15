# VOLUME COMPARISON V1 — executor kickoff prompt (Opus session)

**Paste everything below the line into the new session. Self-contained; the
session has no memory of prior work.  Written 2026-07-05 by the planning lane.**

---

You are implementing **Stage V1 of `DifferentialGeometry/Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`**
in the Lean 4 project at `E:\testdifferential-geometry`.  Read, in this order,
before writing any code: `CLAUDE.md` (workflow rules — they are binding),
`important_lesson.md`, the plan file above (§0 asset audit + §Stage V1), and
the specific asset files named per brick below.  Work only in
`DifferentialGeometry/`; `RFreference/` and `RicciFlow/` are read-only
reference.  Use `./scripts/lake-locked.ps1` for ALL Lake operations (claim your
files before editing, focused `check` per edit, targeted `build +Module` for
verification; never raw `lake`).  Other agents are active in
`Geometry/Flow/RicciFlow/**` — do NOT edit anything under `Flow/`, `Tensor/`,
or `Analysis/Integration/` (consume them read-only).

## Goal (mathematical statement)

Two-sided volume comparability of small geodesic balls under a curvature bound:
there are `r₀ = r₀(n, C₀) > 0` and `0 < c₁ ≤ c₂` (all explicit in `n, C₀`)
such that for a smooth Riemannian metric `g` on a manifold `M` (T2,
σ-compact, `FiniteDimensional ℝ E`, `InnerProductSpace ℝ E` model), a point
`x`, and a scale `s` with `0 < s ≤ r₀` and injectivity radius ≥ `s` at `x`
(`HasInjRadiusAt`-vocabulary, `Geometry/Comparison/InjectivityRadius.lean`),
and a curvature bound of the shape the Grönwall bricks already consume
(match their hypothesis vocabulary exactly — see V1c):

`c₁ * s^n * (unit-ball λ-volume) ≤ riemannianVolumeMeasure g (Metric.ball x s) ≤ c₂ * s^n * (unit-ball λ-volume)`

(`n = Module.finrank ℝ E`; the metric-space structure on `M` in which
`Metric.ball` is taken is the realized Riemannian one — reuse the
`HopfRinowProper.lean` realization vocabulary; if juggling the realized
`MetricSpace` instance gets heavy, it is acceptable to state V1d against the
chart preimage sets first and add the `Metric.ball` form as a corollary).

New files, in `DifferentialGeometry/Geometry/Comparison/Volume/` (new folder):
`NormalChartMeasure.lean` (V1a+V1b) → `JacobianBounds.lean` (V1c) →
`BallVolume.lean` (V1d).  This layer must NOT import anything under
`Geometry/Flow/` (layering: Comparison sits below Flow; in particular do NOT
import `HCGCompactness/C4/StepBInputs.lean` even though it has a similar
`normalCoordMetric` — define your own in V1b, at this layer).

**Statement-audit rule (binding, 2026-07-05):** every public statement gets a
docstring saying (i) why it is mathematically true, (ii) at which scale/under
which cap, (iii) who consumes it — BEFORE you start its proof.

## Bricks

**V1a — evaluate the volume measure in the normal chart.**
Target: for a measurable `A` inside the normal-coordinate patch at `x`
(equivalently `A = expMapDiffeo g x '' B` for measurable `B` inside the
source), `riemannianVolumeMeasure g A = ∫⁻_{B} (normal-chart density) dλ`,
where the density is `√det` of the normal-chart Gram matrix (V1b's object).
Assets: `Analysis/Integration/Measure/Invariance.lean` — the measure is
POU/atlas-independent (`riemannianMeasure_independent_of_atlas`,
`riemannianMeasure_eq_of_pou_independent`, `chartLocalMeasure_apply_of_disjoint_source`)
— and `FamilyDecomposition.lean` (`riemannianVolumeMeasure_eq_finset_sum`).
FIRST search `Invariance.lean`/`FamilyDecomposition.lean` for an
arbitrary-coordinate-patch evaluation lemma before building one; if none
exists, assemble it: canonical-chart local formula + Euclidean change of
variables along the transition maps (Mathlib `MeasureTheory.Function.Jacobian`:
`integral_image_eq_integral_abs_det_fderiv_smul`-family) + POU recombination.
**If this genuinely does not follow from the existing independence layer, STOP
and report — that is an Integration-layer API-gap decision for the planner,
not something to hack around.**

**V1b — normal-chart Gram = Jacobi-field Gram.**
Define (this layer) the pulled-back normal-coordinate metric/Gram
`E → Matrix (Fin n) (Fin n) ℝ` at `x` (value at `w`: entries
`g_{exp(w)}(d(exp)_w e_i, d(exp)_w e_j)` for an orthonormal basis `e`), its
`√det` density, and prove: along the radial ray `t ↦ t•v`, the Gram entries
are `⟨J_i(t), J_j(t)⟩` for the Jacobi fields with `J_i(0)=0`,
`J_i'(0)=e_i`-data.  Assets: `Geometry/Exponential/JacobiVariation.lean`
(exp-variation is Jacobi + the endpoint identity `J(1) = d(exp)·w` — this file
was built exactly for this identification; see also
`HCGCompactness/B0NormalCoordBounds.md` for the blueprint, as prose reference
only), `Geometry/Exponential/GaussLemmaPullback.lean` (chart-pullback
patterns), `Comparison/Variation/JacobiField.lean` (`IsJacobiAlong`).
Also connect V1a's density to this `√det` (they should be definitionally or
lemma-level equal once V1a is stated against the same Gram).

**V1c — two-sided Jacobian bounds at capped scale.**
Target: explicit `r₀(n, C₀)`, and on `‖tv‖ ≤ r₀`:
`(c₁')·tⁿ⁻¹-shaped lower ≤ √det Gram(tv) ≤ (c₂')-shaped upper` — precisely:
two-sided singular-value bounds `a(t)·‖w‖ ≤ ‖d(exp)_{tv}(t·w)‖ ≤ b(t)·‖w‖`
with `a, b` explicit (linear-in-`t` main term ± Grönwall error), then det
bounds via min/max singular values.  Assets:
`Analysis/ODE/SecondOrderGronwall.lean` (`norm_le_gronwall_secondOrder` — the
upper bound), `Comparison/Variation/CovariantGronwall.lean`
(`gronwall_sub_linear` / the keystone family — the quantitative
`‖J(t) − t·J'(0)‖ ≤ err` lower-bound mechanism), parallel ON frames
(`Comparison/Variation/PerpFrame.lean`) if you need frame coordinates, and
`Analysis/Integration/Measure/JacobiFormula.lean` if a derivative-of-det route
is shorter than the singular-value route.  Use the SAME curvature-bound
hypothesis shape those Grönwall files already take (weakest-assumptions rule:
do not invent a new curvature predicate; if their hypothesis is a norm bound on
the curvature term along the geodesic, take exactly that, quantified over the
radial geodesics from `x`).

**V1d — integrate: the two-sided ball-volume bound.**
Lower: `exp(ball 0 s) ⊆ Metric.ball x s` (arc-length: `dist_le_arcLength`
world — see `Geodesic/MaximalInterval.lean` ArcLengthBridge and the
`riemMetric_dist_eq` bridge in `Comparison/HopfRinowProper.lean`) + V1a on the
image + V1c lower + `MeasureTheory.Measure.addHaar_ball`/`addHaar_smul`
scaling.  Upper: `Metric.ball x s ⊆ exp(ball 0 s')` below the injectivity
radius (minimizing geodesics: `Geometry/Exponential/MinimizingGeodesic.lean`,
`IntrinsicExp.lean`; the ball-diffeo producer
`Comparison/ExpBallDiffeo.lean: exists_expBall_diffeo_of_lt` gives the chart
containment discipline) + V1a + V1c upper.  Keep constants explicit enough
that a later consumer can read off `c₁, c₂, r₀` as functions of `(n, C₀)`.

## Do NOT do

- V1e (instantiating the HCG `VolumeComparisonInput`/`PackingBound`) — the
  planner does that together with a guard refinement of those structures.
- Stage V2/V3 material: no cut locus, no polar coordinates
  (`HaarToSphere`), no relative Bishop–Gromov monotonicity, no CGT.
- Any edit outside `Geometry/Comparison/Volume/` (+ its same-name `.md` notes).
  If you believe an upstream file needs a change, STOP and report it as an API
  frontier instead.

## Known project gotchas that WILL bite here

- Enorm/instance diamond on `TangentSpace`: the `Tensor0SBundle` norm
  instances conflict with the `RiemannianBundle` ones.  Distance/arc-length
  lemmas live in the RiemannianBundle world; if a lemma refuses to compose,
  check which enorm its TYPE baked in — the fix pattern
  (`attribute [-instance] Tensor0SBundle.tangentSpace_normed*`, and the bridge
  `tensor0SBundle_enorm_eq_riemannianBundle_enorm` in
  `Comparison/TangentNormDiamond.lean`) is documented in
  `Comparison/CenterOfMass.md`-adjacent notes.
- `letI`-bundle discipline is NOT needed here (you work on a plain `(M, g)`,
  not `PointedRiemannianManifold`) — prefer plain instance binders.
- Heavy-but-not-looping elaborations: `set_option maxHeartbeats 800000 in` on
  a single declaration is acceptable with a one-line comment; do not raise it
  file-wide.
- `lake env lean` success is NOT trustworthy (cached false-green); final
  verification is `./scripts/lake-locked.ps1 build +<your modules>`.
- `λ` is a Lean keyword — never use it in identifiers.
- If instance synthesis times out on tensor-model goals, check
  `important_lesson.md` ("Tensor model aliases and typeclass synthesis")
  before restructuring.

## Acceptance and handback

Each brick: sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`),
green via `lake-locked build +Module`, plus a same-name `.md` note per file
(route taken, what failed, verification status — no build logs).  Then report
back with: the exact public statements proved (names + hypotheses), the
explicit `(r₀, c₁, c₂)` shapes, any deviation from this brick plan and why,
and the honest remaining distance to the V1 goal.  If blocked: classify
(mathematical obstruction / route choice / missing API / typeclass-coercion /
performance / tooling), report the exact goal + error + what you tried, and
stop rather than wrapping the difficulty in new hypotheses.  Do not stop on a
green intermediate tree with an obvious next brick — continue until V1d or a
genuine blocker.  Progress framing for reports: V1 is the first of three
stages of the volume-comparison lane; the lane is item P1a of
`Geometry/Flow/RicciFlow/POINCARE_PLAN.md`, and V1 alone is roughly a third of
Stage-V1-through-V3, itself a few percent of that program — do not let a green
V1 read as "volume comparison done".
