# L6 fill log (DESIGN_C3B brick L6: uniform standard-close windowed witness)

## 2026-09-26 entry 1 (start)

Target, quoted from DESIGN_C3B §4 L6:

```lean
theorem exists_uniform_orientedWitness_of_standard_close {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r : ℝ), 0 < Θ → Θ < 1 → 0 < r →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
      ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
      OrientedWitness S o δ standardModelKappa z T
```

Oleans: none of L1/L23/L4/L5 has an olean yet; all their imports do. Compile method: the
four files concatenated (imports hoisted) into one scratch module outside the repo, compiled to
an olean there, my file compiled against it with LEAN_PATH extended (read-only on the repo).

### FAILURE FIRST: the exact statement is out of reach of the delivered L4

L4 (`WindowedModelWitness.eventually_strict_of_tendsto_flows`) needs
`hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular`, hence `t ∈ D.regular`. For
`RealTimeInterval.closed a b` the regular set is `Ioo a b`
(`Analysis/TimeInterval.lean`, `def closed`), so the witness time must be *interior* to the
common flow interval. In the design's L6, `S` lives on `closed 0 T` and the witness is wanted
at the terminal time `T`: after aligning the counter-sequence at a common time, that time is the
right endpoint of every `Sₙ`'s interval, which is never regular. No re-parametrisation helps
(`Sₙ` is not defined after `Tₙ`). L4's own conclusion also asserts the window of `S n` lies in
`D.regular`, so this is not a slack hypothesis.
Options for the lead: (a) an endpoint (one-sided, `Icc`-carrier) version of L4; (b) the
assembly calls the bridge at a slightly later time so that `S` extends a uniform margin `μ`
past the witness time (in `S`-time the margin is `q·(t' − t)`, `q ≥ qcan/Cbirth`).
Delivered instead (see below): the same theorem with a margin `μ > 0` quantified with `Θ r`:
`S` on `closed 0 T'`, `T + μ ≤ T' ≤ Θ`, closeness on `Icc 0 T'`, witness at `T`. Once (a)
exists, only the construction of the common interval changes.

Other deviations: `0 ≤ T` is kept as a hypothesis (the design's `hT`); the age condition is on
`S`'s scalar exactly as in the design.

## 2026-09-26 entry 2 (progress)

- Scratch deps olean built (L1+L23+L4+L5 concatenated, each file body wrapped in its own
  section, the two anonymous `SigmaCompactSpace` local instances renamed): `lake env lean
  --root=<scratch> -DmaxSynthPendingDepth=3 -o L6Deps.olean`, 1m16s, no output.
- Compiling private helpers against it: orientation dichotomy on a preconnected 3-manifold
  (open agreement sets from `locally_constant`), sign-flip of the model orientation,
  explicit orientation transport through L3's `toRestrictOpen` (L23 proves it only inside an
  `OrientedWitness` existential, which hides the witness whose strictness L4 needs),
  image-radius bound for a witness embedding (`edistOf_map_le_of_metric_upper_on_ball`),
  positive-age producer (copy of `CanonicalWitnessPositiveAge` logic at tolerance δ/4),
  endpoint scalar convergence (triangle with the uniform standard time-Lipschitz bound of
  `standard_metric_bounds_on_shorter_windows`; needed before `T∞ > 0` is known, where L5's
  `0 < a` is unavailable). All compile clean.
- D is chosen explicitly (no second contradiction): `D := r + 2(ρ(δ)+1)√Λ`, `Λ` the uniform
  metric equivalence of standard solutions with `StandardCap.metric` on `[0,Θ]`; the image of
  the δ-buffered ball of the δ/4 standard witness lies in the δ/4-controlled ball
  (`ρ(δ)+1 < ρ(δ/4)` iff `δ < 1`), so its `Q(T)`-distance from `z` is `≤ 2(ρ(δ)+1)/√R ≤
  2(ρ(δ)+1)`, and `StandardCap.radial_difference_le_edist` turns it into a norm bound.

## 2026-09-26 entry 3 (delivered)

File: `Perelman/StandardSolution/StandardClosenessWindowedWitness.lean` (822 lines incl. 13
imports; one public theorem, 13 private helpers). Not registered in the root aggregate; nothing
else edited; no git writes; no `lake build`.

Proved (margin form; see entry 1 for why the endpoint form is out of reach of L4):

```lean
theorem exists_uniform_orientedWitness_of_standard_close {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r μ : ℝ), Θ < 1 → 0 < μ →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T T' : ℝ) (hT' : 0 ≤ T'), 0 ≤ T → T + μ ≤ T' → T' ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T' hT')), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T', ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
      ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
      OrientedWitness S o δ standardModelKappa z T
```

Differences from the design statement: (1) margin `μ` and flow interval `closed 0 T'` with
`T + μ ≤ T' ≤ Θ` (forced, entry 1); with `μ` fixed, `T' = T + μ` recovers "flow up to
`T + μ`". (2) `δ < 1` instead of `δ ≤ 1/4` (weaker; `ρ(δ)+1 < ρ(δ/4)` iff `δ < 1`).
(3) `0 < Θ`, `0 < r` dropped (unused). (4) `0 ≤ T` explicit. `τQ` depends on `δ` only; `D` is
explicit: `r + 2(modelRadius δ + 1)√Λ(Θ)`.

Proof (contradiction over `N = n`, `e = 1/(n+1)` at the fixed `D`): one compact subsequence for
`(Tₙ, zₙ) ∈ [0,Θ] × closedBall 0 r`, then L1 on `Q ∘ φ`; endpoint scalar convergence gives
`τQ ≤ T∞ R∞`, hence `T∞ > 0`, `R∞ ≥ 1`; the standard witness at `δ/4` (producer + positive-age
argument), shifted to time 0 (`orientedWitness_paraSolution_iff`, `A = 1`), monotoned to `δ`
with strictness (L2), restricted to the window (L3, image bound above) and to the common interval
`closed (-b) μ`, `b = 2/(δR∞) < T∞` (the δ/4 window gives `4/(δR∞) ≤ T∞`); each `Sₙ` is shifted
by `Tₙ` (`parabolicSolution … 1`) and restricted to the same interval once `b ≤ Tₙ`; L5 gives
L4's `hconv` (via `T n := Tₙ + μ`) and `hscalar`; L4 transfers the strict witness; the
orientation of the counterexample is `±` the restricted Euclidean one on the connected window,
handled by flipping the model orientation.

Suppliers (file:line): L1 `StandardFamilyCompactness.lean:62`; L2/L3
`WindowedWitnessStrictRestriction.lean:26,162,241,248,255`; L4
`WindowedWitnessPerturbation.lean:764`; L5 `StandardWindowShiftConvergence.lean:24,46,75,103`;
producer `HighCurvatureModels.lean:126`; `StandardCurvatureControl.lean:91`;
`WindowedWitnessRestriction.lean:54` (`mono_of_regular`); `SelectedCountersequenceAdapter.lean:
76,231,249`; `StandardMetricControl.lean:55`; `UniformLifetime.lean:28`;
`Surgery/StandardCap/Distance.lean:134`; `Geometry/Metric/Comparison/
PartialDiffeomorphDistance.lean:57`; `DistanceScaling` (`edistOf_scale`, `le_edistOf_of_quad`).

Compile: scratch module = the new file with `import L6Deps` (the four bricks, entry 2) in
place of the four brick imports, otherwise byte-identical (checked with `diff`):
`lake env lean --root=<scratch> -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`
→ no output. `#lint` appended to a scratch copy: 0 errors, 14 linters. Axioms of the public
theorem: `propext`, `Classical.choice`, `Quot.sound`. Name grep-unique. Lines ≤ 100. In-place
compile: at the end of this lane the oleans of L1, L23, L4 exist, L5's
(`StandardWindowShiftConvergence`) does not yet, so no in-place compile was possible.

Duplication notes (follow-up, outside this file): the positive-age argument copies
`CanonicalWitnessPositiveAge.lean:66`; `nonempty_euclidean_tangentOrientation` copies the private
lemma of `HighCurvatureModels.lean:206`; `toRestrictOpen_preserves` re-proves the explicit form
hidden in L23's `orientedWitness_toRestrictOpen` (L23 could expose it publicly).
