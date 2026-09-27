# B3 — bounded curvature at bounded distance on a slice, first sub-brick (2026-09-26)

New file `Topology/SpatialBoundedCurvatureAtDistance.lean` (321 lines; only file touched besides
this log). Not lake-built, not registered in `DifferentialGeometry.lean` (lead).

## Design statement (DESIGN_CROSSING §2 B3, quoted)

"`∃ ε̄cone : ℝ, 0 < ε̄cone ∧ (ε̄ ≤ ε̄cone → ∀ A : ℝ, 0 < A → ∃ Q : ℝ, ∀ (H : RetainedCoreHistory P₀)
(t …) (y) (qcan : ℝ), 1 ≤ qcan → Λs * qcan ≤ metricScalarAt (H.toHistory.stageMetric _ t) y →
H.SpatiallyCanonicalAt ε̄ C1s C2s (Λs * qcan) t → H.GradientBoundAt Cgrad qcan t →
H.NoncollapsedBefore κ ρ t → PinchedAt phi t → ∀ x ∈ riemannianBallOf (…) y (A / √R(y)),
R(x) ≤ Q * R(y))`" — "stated by contradiction internally: finite escape radius ρ̄, incomplete limit
… cone chart … `solution_cone_terminal_exclusion` gives the contradiction".
The design gives no split; this delivers the witness-only layer the contradiction needs first:
positivity of the escape radius (ρ̄ ≥ √C2/(√C2−1)) and the quadratic blow-up lower bound
`R(z)·d(y,z)² ≥ const` at an escape point (the template's `hlower`), plus the component
alternatives. No flow is used, correctly: a thin metric cone is ε-necklike at every point, so the
slice statement for all `A` is false without the flow (this is why the cone exclusion is needed).

## Delivered (all sorry-free; axioms propext, Classical.choice, Quot.sound)

- `DifferentialGeometry.mem_connectedComponent_of_riemannianEDistOf_lt_top` (general manifold).
- `DifferentialGeometry.exists_riemannianEDistOf_lt_of_lt_add` (`d(x,z) < r₁+r₂`, `r₁ r₂ > 0` ⇒
  `∃ w, d(x,w) < r₁ ∧ d(w,z) < r₂`; path + IVT + `pathELength_add`).
- FiniteHorn: `SpatialCanonicalAlternative.isWholeComponent` (positive/round),
  `.eq_connectedComponent_of_isWholeComponent`; `SpatialCanonicalWitness.scalar_bounds_of_mem_ball`
  (`B(x, R(x)^{-1/2})`: `C2⁻¹R(x) ≤ R ≤ C2 R(x)`); `.scalar_bounds_of_isWholeComponent` (same bound
  at every finite distance: B3 for every `A` with `Q = C2` when the base witness is positive/round).
- `scalar_bounds_of_riemannianEDistOf_lt_of_spatialCanonicalWitness` (chain propagation): with
  `0 ≤ q`, `1 ≤ C2`, witnesses at every `R > q`: `C2^n q < R(y)`,
  `d(y,z) < (∑_{k<n} √C2^{-k})/√R(y)` ⇒ `C2^{-n}R(y) ≤ R(z) ≤ C2^n R(y)`.
- `ofReal_le_riemannianEDistOf_of_scalar_lt_of_spatialCanonicalWitness` (escape lower bound):
  `C2^n q < R(z)`, `C2^n R(y) < R(z)` ⇒ `(∑_{k<n} √C2^{-k})/√R(z) ≤ d(y,z)`.
- `exists_le_sum_range_inv_sqrt_pow`, and the B3-shaped corollary
  `exists_scalar_bound_at_distance_of_spatialCanonicalWitness (hC2 : 1 ≤ C2)
  (hA : A * (√C2 − 1) < √C2) : ∃ Q ≥ 1, ∀ M g eps C1 q, 0 ≤ q → witnesses above q → ∀ y,
  Q*q < R(y) → ∀ z ∈ B(y, A/√R(y)), Q⁻¹R(y) ≤ R(z) ∧ R(z) ≤ Q R(y)`.
- Slab form `OrientedThreeStage.IncomingSlab.scalar_bounds_of_riemannianEDistOf_lt_of_
  spatiallyCanonicalBefore` (F5 hypothesis `G.SpatiallyCanonicalBefore ε C1 C2 q t₀`, `t ∈ Ioo a t₀`).

## Next sub-brick (B3b, the cone part; precise statement)

For `A` beyond `√C2/(√C2−1)`: fix `κ C1s C2s phi Ctime Cgrad` (admissible `phi`); ∃ `ε̄cone > 0`,
∀ `ε̄ ≤ ε̄cone`, ∀ `A > 0`, ∃ `Q Λ ≥ 1`, ∀ `H` (retained-core history), slice `t`, base `y`, `q ≥ 0`:
`Λ·q < R(y,t)`; spatial witnesses (accuracy `ε̄`, constants `C1s C2s`) at every point with `R > q` on
every slice in `[t − Λ/R(y,t), t]` (event slabs via `EventSlabsSpatiallyCanonical`, current slab via
`SpatiallyCanonicalBefore`); `EventSlabsDerivative`/`DerivativeBoundBefore Ctime q`; pinching
`phi`; `NoncollapsedBefore κ ρ t` with `ρ√R(y,t) ≥ Λ` ⇒ `∀ z ∈ B_t(y, A/√R(y,t)), R(z,t) ≤ Q·R(y,t)`.
Proof: contradiction sequence at the least bad radius `ρ̄ ≥ √C2/(√C2−1)` (positive by this file);
`R ≤ C·R(y)` on `B(y, ρ < ρ̄)` + derivative bound ⇒ traced region of depth `c/R(y)` (B2
`isTracedRegion_of_forall_nonempty_backwardPointTrace`, B4) ⇒ survivor flow
(`exists_common_flow_of_isTracedRegion`) ⇒ incomplete limit on `B(ρ̄)` via
`exists_pointed_convergence_of_eventually_compact_inner_balls` (`IncompleteLocal.lean:276`);
escape points are neck centres (this file's escape bound `R·d² ≥ c` excludes caps/components at
the missing point) ⇒ cone chart at the terminal slice (template `NormalizedConeExclusion`,
`ConeChartCoordinates`) ⇒ `solution_cone_terminal_exclusion` (`ConeTerminalExclusion.lean:59`)
with `SecLower 0` from the rescaled pinching ⇒ False. Escape-radius selection to reuse:
`TracedTerminalCompactness.lean:1031/2362`.

## Compile

`LEAN_NUM_THREADS=2 lake env lean <file>`: no output (0 errors, 0 warnings); also clean with
`-Dweak.linter.mathlibStandardSet=true`. Axioms checked on a scratch copy outside the repo.
