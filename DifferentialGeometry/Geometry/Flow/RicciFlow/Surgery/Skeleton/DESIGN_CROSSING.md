# Design: the Crossing leaf (`crossingContinuation`), 2026-09-26

Read-only design. Target: `CrossingContinuation` in
`Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean` (sorry in
`Surgery/Skeleton/PoincareEndgame.lean:47`). Sources read: the leaf and its assembly, `CrossingRoom`,
`BackwardTraceDistortion` (X2, uncommitted), `HistoryParabolicBall`, `TracedTerminalCompactness`,
`IncompleteLocal`, `UniformKappaCanonicalThreshold` / `DeepContinuation`, `HighCurvatureModelBounds`,
`TerminalScalarAncientLimit`, `ConeTerminalExclusion`, `NormalizedBoundedCurvature`,
`AncientCanonicalNeighborhood`, `CanonicalAlternativeComparisonTransport`,
`CapWindowStandardComparison`, `StandardTerminalBlowup`, `SpatialCanonicalContinuation`, digests C
(Q5) and E (items 2, 3, lemma set, decision 5). `DESIGN_28.md` does not exist; item (iii) below is
written against decision 3 of digest E.

## 0. Failures first

F1 (FALSE as briefed) — `θₙ → ∞`. The leaf requires `θcap < 1`
(`CrossingContinuation … θcap < 1`), and `CapWindowPoint` measures age by
`t − T_birth ≤ θcap · scale⁻¹`, i.e. standard-solution time, which lives in `[0, 1)`. The growing
windows are `Dₙ → ∞` and `θcapₙ ↑ 1`, not `θₙ → ∞`. (`θ` is the Deep threshold handed in by the
assembly; it is fixed along the sequence.)

F2 (FALSE as briefed) — "a point captured by a cap at distance `≤ A/√R` contradicts
`¬CapWindowPoint(Dₙ, θcapₙ)` once `Dₙ ≥ D(A)`". Configuration: base inside the core
`‖x‖ < Dₙ + 1` of a cap window whose standard-solution time is `τ' = 0.99`, with `θcapₙ = 0.9`: the
base is spatially captured but is not a `CapWindowPoint(Dₙ, 0.9)`. The capture age must be bounded
too, and the bound depends on the depth `T`, not only on `A`: from
`exists_standard_scalar_lower_bound` (`Perelman/StandardSolution/StandardTerminalBlowup.lean:61`,
`c/(1−τ) ≤ R_std`) and a curvature bound `R ≤ Q·Rₙ` along the base's trace one gets
`τ' ≤ 1 − c/(8·T·Q)` (brick B5). So the window condition is
`Dₙ ≥ D(A,T)` and `θcapₙ ≥ θcap(A,T) := 1 − c/(8·T·Q(A,T))`.

F3 (FALSE as a route) — "iterate X2's dichotomy to get room at every `(A, T)`". X2's own hypotheses
(`exists_parabolicallyRmControlledBall_or_capWindowPoint`, `BackwardTraceDistortion.lean:716`):
`16c² ≤ θcap < 1` forces `c < 1/4`, so it controls only radius `c/√R < 1/(4√R)` and depth
`c²/R < 1/(16R)`. The general form (`exists_cap_capture_of_ball_point_without_trace`, `:409`) needs
a curvature bound `M` on the whole ball at time `t` and `Ctime·M·(t−u) ≤ 1/2`,
`4M(t−u) ≤ θcap`. Nothing in X2 gives `M` on a ball of normalized radius `A` (the gradient bound
gives `R ≤ 4R(y)` only up to radius `1/(4·Cgrad·√R)`), and repeated backward application
accumulates normalized capture age `≥ 4Q·T`, which exceeds `θcap < 1`. Room at every `(A, T)` needs,
in order: bounded curvature at bounded distance on each slice (local cone exclusion, B3), backward
curvature control by the derivative bound in steps `Δ = 1/(8·Ctime·Q)` (B4), and the capture-age
brick B5 at each step.

F4 (FALSE as briefed) — "the backward window `[t − R⁻¹, t]` of the pulled-back witness fits by the
depth `T`". `StrongNeck.time_domain : Icc (t − R⁻¹) t ⊆ D.carrier` is on the SLAB flow `G.flow`
(`FiniteHornGeometry.lean`), not on the survivor flow; so a witness at `(y, t)` needs every neck
centre `z` of the witness to satisfy `R(z)(t − a) ≥ 1`, and the E3 transport
(`CanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn`,
`CanonicalAlternativeComparisonTransport.lean:18`) needs `b ≤ t − 2R(z)⁻¹` with `a < b`. With
`R(z) ≥ C2can⁻¹·R(y)` this holds iff `R(y)(t−a) > 2·C2can`, so Crossing must choose
`τ₀ := 2·C2can(ε/2) + 1` (it may: `τ₀` is its own existential, chosen with `C2₀`). The survivor
depth `T` matters only for the blow-up, never for the witness.

F5 (insufficient interface, with configuration) — decision 3(iii) "Crossing receives the spatial
clause on EARLIER slabs". Configuration: surgeries far from the base at times
`tₙ − k/(n·Rₙ)`, `k = 1..n²` (every slab short; "slabs can all be short", digest C Q5); the base
region is untouched; every point with `R ≥ 2Rₙ` near the base is young (`R·(t − a) < τmin`) in
every slab. Then `CanonicalBefore` / `EventSlabsCanonical` give no witness anywhere near the base,
only derivative and gradient bounds, and the local cone exclusion at the base's own slice (B3)
has no neck structure to work with. Required instead: spatial witnesses at all high-curvature
points of earlier slabs AND of the current slab before `t₀`
(`EventSlabsSpatiallyCanonical` and `G.SpatiallyCanonicalBefore`, as C4 already takes), with
(a) threshold `qs ≤ Λs · max qcan 1`, `Λs` fixed before `q₀` (C4 currently only gives
`qcan ≤ qs`, unbounded — useless along a sequence with `qcanₙ/Rₙ` bounded but `qsₙ/Rₙ → ∞`);
(b) accuracy `≤ ε̄cone` (the cone-exclusion threshold of B3), independent of the target `ε`, i.e. the
assembly runs the joint spatial clause at `min ε ε̄cone`. If the base is old
(`Rₙ(tₙ − a) ≥ τmin`) this is not needed on the current slice (all higher points at the same time
are older), but it is needed on every earlier slice (B3 at depth) and whenever `Rₙ(tₙ − a) → 0`.

F6 (gap, not false) — X2 and `CrossingRoom` assume `DerivativeBoundBefore … t` and the gradient
bound AT `t`. The leaf supplies them only on the open interval `(a, t₀)`; bad points live in
`[t₀, t₀ + η)`. Work on the slice `t₀` (closure, B0) plus a sliver argument (B1). The case
`t₀ = a` (current slab has no "before" data) needs the gradient bound on the post-event slice,
from the previous slab on retained points and from the cap record on cap points (B0b).

F7 (gap) — X2 covers only event slabs (`hi : activeStage t = i.castSucc`); the terminal slab `G`
of the leaf needs the same lemmas on `H.extendHorizon T … (G.closedPrefix …)` (B2c).

F8 (gap) — the E3 transport excludes the positive and round alternatives. A compact limit
(κ-solution on a compact manifold) needs component capture (the whole component of `Hₙ` is the
image of the limit) and a transport of `PositiveComponent` / `RoundComponent` (B8b).

F9 (heaviest gap) — the global curvature bound of the limit (field `globalScalarBound` of
`IsAncientKappaSolution`). The ready local supplier
`exists_complete_nonnegative_bounded_ancient_solution_subsequence_on_terminal_maps_of_scalar_deriv_nonneg_above`
(`TerminalScalarAncientLimit.lean:405`) needs `∂R ≥ 0` at every point above a bounded normalized
threshold (its `_of_strongNeck_above` form needs a strong neck there). That is not supplied at cap
centres, at positive/round points, or at young points. The alternative, the finite-horizon backward
bound `exists_uniform_backward_scalar_bound_on_finite_horizon` (`BackwardScalarBound.lean:22`) with
`exists_cofinal_backwardExtensions_of_scalar_bounds`, is stated on `NormalizedSequence` and uses its
`higher_good : OrientedWitness` field (model closeness, stronger than a `CanonicalWitness`) in 13
files. B6 below takes the Hamilton-Perelman local route; it is the largest single item.

## 1. The contradiction sequence (quantifier layout)

Fix `B ε` (`ε < 1/11`), take `C1₀ = C2₀ = C := max C1can C2can` from `kappa_canonical_neighborhood`
(`AncientCanonicalNeighborhood.lean:146`) at `ε' := min (ε/2) epsCan` (κ-independent, which the
order `∃ C… , ∀ κ` requires), `Ctime₀ = Cgrad₀ = 2C`, `τ₀ = 2C + 1` (F4). Fix
`C1 C2 τmin Ctime Cgrad κ phi θ`. Negate `∃ Dcap θcap q₀ δmax ρmax εcap mcap, …` and instantiate
with `Dₙ = n`, `θcapₙ = 1 − 1/(n+2)`, `q₀ₙ = n`, `δmaxₙ = ρmaxₙ = εcapₙ = 1/n`, `mcapₙ = n`
(legitimate: the negation is `∀`). Obtain `qcanₙ ≥ n`, `p₀ₙ` (with `modelRadius ≥ n`,
`modelAccuracy ≤ 1/n`), `Hₙ`, records, a slab (event `j` or terminal `G`), `t₀ₙ` and the
hypotheses, such that for every `η > 0` some `(y, t)` with `t ∈ [t₀ₙ, t₀ₙ + η)`, `qcanₙ < R`,
`R·(t − a) < θ`, `¬CapWindowPoint(Dₙ, θcapₙ)` violates one of the three clauses of
`CanonicalBoundsOn`. B1 picks `ηₙ` and `(yₙ, tₙ)`; `Rₙ := R(yₙ, tₙ) → ∞`.

## 2. Bricks (dependency order)

Names are proposals (check `NAMING.md`); homes: history-specific glue in `Surgery/Topology/`,
flow-general statements in `Perelman/CanonicalNeighborhood/` or `Compactness/`.

### B0 — closure of the "before" data at `t₀` (≈ 300–500 lines)

```lean
theorem OrientedThreeStage.IncomingSlab.derivativeBound_at_of_before
    (G : P.IncomingSlab a s) {Ctime : ℝ≥0} {qcan t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s)
    (h : G.DerivativeBoundBefore Ctime qcan t₀) (y : P.Carrier) (hy : qcan < G.flow.scalar t₀ y) :
    |derivWithin (fun v => G.flow.scalar v y) (Iic t₀) t₀| ≤ Ctime * G.flow.scalar t₀ y ^ 2

theorem OrientedThreeStage.IncomingSlab.gradientBound_at_of_before  -- same shape, gradient clause
```
Supplier: smoothness of `G.flow` (`IsSolutionOn`), one-sided derivative continuity. B0b
(`t₀ = a`): gradient bound on the post-event slice at retained points from the previous slab's
`GradientBoundBefore (H.time j.succ)` through `TerminalLimitMetric` convergence, and at cap points
from the cap record (`CanonicalStaticInsertionWitness` closeness + standard initial metric
gradient); ≈ 600–1000 lines; X2 must be restated with its `hgrad` restricted to the ball
`riemannianBallOf … y r` (it only uses it there).

### B1 — sliver (≈ 400–700 lines)

```lean
theorem OrientedThreeStage.IncomingSlab.exists_sliver_comparison (G : P.IncomingSlab a s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico a s) (m : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ (∀ t ∈ Icc t₀ (t₀ + η), ∀ y, G.flow.scalar t y * η ≤ ζ) ∧
      ∀ t ∈ Icc t₀ (t₀ + η),
        Nonempty (MetricComparisonOn (fun _ => G.flow.base.metric t₀)
          (fun v => G.flow.base.metric v) (PartialDiffeomorph.refl P.Carrier) univ
          (Icc t₀ t) m ζ)
```
Supplier: `exists_forall_Icc_riemannNorm_le` (`SlabPointPicking.lean:70`, used by Deep) and its
higher-order analogue on the compact carrier. Scale check: for `R ≥ qcan ≥ 1` the normalized
`C^m` distance is at most the unnormalized one, and normalized sliver length is `≤ R·η ≤ ζ`. Use:
for `ζₙ = 1/n`, `mₙ = n`, choose `ηₙ`; the blow-up base is `(yₙ, t₀ₙ)` (all "before" data valid
there by B0), the sliver `[t₀ₙ, tₙ]` disappears in the limit, and B8 composes the limit
comparison with the sliver comparison to land at `tₙ`.

### B2 — traced regions and the common survivor flow (≈ 800–1200 lines)

B2a, predicate generalizing `isParabolicallyRmControlledBall` (radius `r`, depth `r²`, bound
`r⁻²`) to independent radius, depth and bound:
```lean
def ObservedHistory.IsTracedRegion (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (ρ τ K : ℝ) : Prop :=
  0 < ρ ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = t - τ ∧
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
        A.isRmBoundedBy K        -- normSq0S ≤ K ^ 2 along the trace and at every crossing
```
with `isParabolicallyRmControlledBall t p r ↔ IsTracedRegion t p r (r^2) (r^2)⁻¹` (bridge lemma).

B2b, the common flow (copy of `exists_common_flow_of_parabolicallyRmControlledBall`,
`HistoryParabolicBall.lean:737`, whose proof uses the traces only for existence; the curvature
clause becomes `normSq0S ≤ K^2`):
```lean
theorem ObservedHistory.exists_common_flow_of_isTracedRegion (H) (t) (p) {ρ τ K : ℝ}
    (h : H.IsTracedRegion t p ρ τ K) :
    ∃ (a : Icc (0:ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set _) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
        ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
          (∀ j, Function.Injective (f j)) ∧
          (∀ i hi hl x, (H.event i).RegularCrossing (f ⟨i.castSucc, hi, _⟩ x) (f ⟨i.succ, _, hl⟩ x)) ∧
          (∀ x : U, f ⟨H.activeStage t, _, le_rfl⟩ x = x.val) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat),
            IsSolutionOn S ∧
            (∀ j, ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
              S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
            (∀ v ∈ Icc a.val t.val, ∀ x : U, normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2)
```
The survivor flow's time range is exactly `[t − τ, t]`, crossing every event in it with
`RegularCrossing` compatibility. B2c: final-slab versions of B2a–b and of the X2/`CrossingRoom`
lemmas via `extendHorizon`/`closedPrefix` (F7), ≈ 400–700 lines.

### B3 — local bounded curvature at bounded distance on a slice (≈ 4000–7000 lines, new)

```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_spatially_canonical
    {κ ε̄ C1s C2s Λs : ℝ} {Cgrad : ℝ≥0} {phi : ℝ → ℝ} (…positivity, admissible phi…) :
    ∃ ε̄cone : ℝ, 0 < ε̄cone ∧ (ε̄ ≤ ε̄cone →
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ,
    ∀ (H : RetainedCoreHistory P₀) (t : Icc (0:ℝ) H.horizon) (y) (qcan : ℝ), 1 ≤ qcan →
      Λs * qcan ≤ metricScalarAt (H.toHistory.stageMetric _ t) y →
      H.SpatiallyCanonicalAt ε̄ C1s C2s (Λs * qcan) t →        -- spatial witnesses on the slice
      H.GradientBoundAt Cgrad qcan t → H.NoncollapsedBefore κ ρ t → PinchedAt phi t →
      ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric _ t) y (A / √R(y)), R(x) ≤ Q * R(y))
```
(stated by contradiction internally: finite escape radius `ρ̄`, incomplete limit on the ball of
radius `ρ̄` via `exists_pointed_convergence_of_eventually_compact_inner_balls`
(`IncompleteLocal.lean:276`), Ric ≥ 0 from pinching, spatial necks at the escaping points give the
cone chart, `solution_cone_terminal_exclusion` (`ConeTerminalExclusion.lean:59`, already local:
any `SolutionOn`, `SecLower 0` on `U`, cone chart at the terminal slice, nonflat ⇒ False) gives the
contradiction; the short backward flow near the cone points comes from the derivative bound and
B2b). The smooth analogue `exists_boundedAtDistance` (`NormalizedBoundedCurvature.lean:18`) is on
`NormalizedSequence` (complete slices, `higher_good`) and is a proof template only (review:
do not localize `NormalizedSequence`). The collaborator's
`RetainedCoreHistory.exists_compatible_historical_solution_limits_at_scalar_escape_of_scalar_derivative_contact`
(`TracedTerminalCompactness.lean:2362`) already builds the scalar-escape radius limit with traced
buffers for the terminal slab; B3 reuses its escape-radius selection and replaces the contact
hypothesis by the spatial necks. This is where F5's hypotheses enter.

### B4 — backward step: curvature control over depth `Δ` (≈ 600–900 lines)

From `R ≤ Q·R(y)` on `B(y, A/√R)` at time `t` and `EventSlabsDerivative` / current
`DerivativeBoundBefore`, every TRACED point keeps `R ≤ 2Q·R(y)` down to depth
`Δ = 1/(8·Ctime·Q·R(y))` (the computation of `isRmControlled_of_backwardPointTrace_of_derivative_bounds`,
`CrossingRoom.lean:140`, with `M = Q·R(y)`); `|Rm| ≤ K(phi)·Q·R(y)` by
`sqrt_rmNormSq_stageMetric_le_of_pinched`. Output `IsTracedRegion t y (A/√R) (Δ) (K·Q·R)` for the
traced part. Untraced points are handled by B5.

### B5 — per-buffer survival / capping dichotomy with capture age (≈ 1500–2500 lines)

```lean
theorem RetainedCoreHistory.isTracedRegion_or_capWindowPoint
    (records …) (hcan …) (hscale …) (hacc : p.modelAccuracy ≤ ζ₀) (hD : Dstar ≤ p.modelRadius)
    (hbirth : ∀ i b, qcan ≤ Cbirth * ((records i).static b).neck.scale)       -- class supply 28(iv)
    (ha₀ : ∀ i b, 1 ≤ a₀ * ((records i).static b).neck.scale)                 -- class supply 28(iv)
    {A T Q : ℝ} (t) (y) (hQ : ∀ s ∈ [t − T/R, t], base trace curvature ≤ Q·R)  -- from the limit, B7
    (hball : ∀ x ∈ B_t(y, 2A/√R), R(x) ≤ Q·R)                                  -- B3
    (hDwin : D(A,T,Q) < Dcap) (hθ : 1 − c/(8·T·Q) ≤ θcap) (hθ1 : θcap < 1) … :
    H.IsTracedRegion t y (A/√R) (T/R) (K(phi)·2Q·R) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
```
with `D(A,T,Q) := 2·transitionEnd + √(8Q)·exp(9·8√3(1+phi 1+phi 0)·Q·T)·A` (the X2 constant with
`r = A/√R`, `t − u = T/R`, `M = Q·R`). Proof: induction on depth in steps `Δ` (B4). At each step
an untraced ball point gives, by `exists_cap_capture_of_ball_point_without_trace`
(`BackwardTraceDistortion.lean:409`, general `r, M, u`), a trace of `y` into a window point
`‖x‖ < Dcap` of some event `j` with `scale ≤ 4QR`. Capture age: if `τ' := scale·(t − T_j) ≥ θv`,
at `t_v := T_j + θv/scale` the standard comparison `exists_standard_comparison_of_cap_window_trace`
(`CapWindowStandardComparison.lean:20`, needs `hbirth`, `ha₀`, `θv ≤ Θ < 1`) and
`exists_standard_scalar_lower_bound` give `R(y@t_v) ≥ scale·c/(2(1 − θv))`, while `hQ` gives
`R(y@t_v) ≤ Q·R` and `scale ≥ θv·R/T`; so `1 − θv ≥ θv·c/(2TQ)`, false for
`θv = 1 − c/(8TQ)`; hence `τ' < θv ≤ θcap` and `CapWindowPoint` holds (`‖x‖ < Dcap ≤ Dcap + 1`).
In the sequence: for fixed `(A, T)` and `n ≥ n₀(A, T)` we have `Dₙ ≥ D(A,T,Q)`,
`θcapₙ ≥ 1 − c/(8TQ)`, `modelAccuracy ≤ 1/n ≤ ζ₀`, `modelRadius ≥ n ≥ Dstar`, and the base is not a
cap point, so the left branch holds. X2's single step (`16c² ≤ θcap`) is the `T ≤ 1/16`, `A ≤ 1/4`
instance.

### B6 — limit on `M∞ × (−∞, 0]` with the κ-solution properties (≈ 6000–12000 lines)

B6a, spatial compactness at all radii (upgrade of `IncompleteLocal`):
```lean
theorem exists_pointed_convergence_of_eventually_compact_balls_all_radii
    (X : PointedRiemannianSeq I) (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    (hcompact : ∀ R > 0, ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric _ R))
    (hjets : ∀ R > 0, ∀ p, ∃ C ≥ 0, ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) _ R p C)
    (hvol : …as in IncompleteLocal, for all R…) :
    ∃ Lim : MetricCompactLimit X, …capture of every ball, canonical domains…
```
by diagonalizing `exists_pointed_convergence_of_eventually_compact_inner_balls` over `ρ = k`
(compatible because the `rho`-limits nest; `limit_complete` from compactness of all closed balls).

B6b, flows: `X.term n` := the B2b survivor flow on `U(Aₙ, Tₙ)` rescaled parabolically at
`(yₙ, t₀ₙ)` by `Rₙ`, as a `FlowSequence` with `interval n = closed (−Tₙ) 0`, `Aₙ, Tₙ → ∞` slowly
(diagonal choice using B5 for each fixed `(A, T)`). Jets: Shi on the controlled regions (curvature
`≤ K·2Q` in normalized units on `B(A) × [−T, 0]` ⇒ all derivatives on `B(A/2) × [−T/2, 0]`), as in
`exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces`
(`TracedTerminalCompactness.lean:108`). Volume: `NoncollapsedBefore κ ε t₀` (and
`TerminalNoncollapsedBefore` on the terminal slab) on history balls transported to survivor-flow balls
through the maps `f` (a parabolically controlled survivor ball is a controlled history ball: same
traces), scale `ε√Rₙ → ∞`. Compatible flow limits on an exhaustion:
`exists_compatible_historical_solution_limits_of_pointed_convergence`
(`TracedTerminalCompactness.lean:1959`) upgraded from its small window `θ n` (with
`6·C·(A n·θ n) ≤ 1`) to arbitrary depth, fed by B5 instead of `hbuffer`. Output: `ConvergesOn`
(`BlowupConvergence.lean:291` shape) of the rescaled survivor flows to
`S∞ : SolutionOn (M := Lim.limit.M) (RealTimeInterval.infiniteClosed 0 0 le_rfl)`.

B6c, properties:
- `Rm ≥ 0`: rescaled pinching `rescalePinchingFunction Rₙ phi → 0`; supplier: the `hpinch ⇒ hcone`
  step inside `exists_complete_nonnegative_ancient_solution_subsequence_on_terminal_maps_of_scalar_deriv_nonneg_above`
  (`TerminalScalarAncientLimit.lean:281`), extracted.
- completeness of every slice: `t = 0` from B6a; `t < 0` from `Ric ≥ 0` (metric nonincreasing
  forward, so `g(t) ≥ g(0)` and a `g(t)`-Cauchy sequence is `g(0)`-Cauchy) — port of
  `IsAncientKappaSolution.metric_inner_le` (`KappaSolutions/AncientMetricMonotonicity.lean:161`) to a
  flow with nonnegative curvature operator, not assumed ancient-κ.
- bounded curvature (F9): time 0 by the local Hamilton argument (complete, `Rm ≥ 0`, κ-noncollapsed,
  spatial necks at high points; template `terminal_limit_global_bound` /
  `exists_uniform_scalar_bound_outside_terminal_ball`, `BackwardScalarExterior.lean:89`), then
  earlier slices by B3 on the limit slices plus a finite-horizon backward bound (template
  `exists_uniform_backward_scalar_bound_on_finite_horizon`). Largest gap.
- κ at all scales: `ConvergesOn.parabolicallyKappaNoncollapsedBelowScale`
  (`ParabolicNoncollapseLimit.lean:246`, radii `ε√Rₙ → ∞`) then
  `pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative`
  (`Noncollapsing/ParabolicOfSpatialAncient.lean:141`; needs completeness, `Rm ≥ 0`, scalar bound).
- `notFlat`, `scalar = 1` at base: normalization.
Result: `IsAncientKappaSolution (κ / (250·30³)) P∞` with `PointedFlowScalarAtBase P∞ 1` and an
orientation section (limit of the stage orientations through orientation-preserving maps).

### B7 — the depth induction closing B5's `hQ` (≈ 300–600 lines of glue)

Induction on `T` in steps: control at depth `T₁` gives a partial limit on `[−T₁, 0]` whose slices are
complete with bounded curvature (B6c at finite horizon), hence `hQ` and B3's slice hypothesis at
depth `T₁ + Δ` for `n` large; B4 + B5 extend to `T₁ + Δ` with `Δ` depending only on the limit bound.
Where B5 needs `hQ` at `t_v`, `t_v` lies in the already-controlled part when
`(1 − θv)·T₂ ≤ θv·T₁`, true for the chosen `θv`.

### B8 — witness at the base and pullback (≈ 2000–3500 lines)

B8a: `kappa_canonical_neighborhood` at `ε'` gives
`W∞ : CanonicalWitness P∞.S ε' C1can C2can P∞.basepoint 0`.
B8b: transport to `Hₙ` at `(yₙ, tₙ)`: neck/cap by
`CanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn` (window `[b, 0]` of the
limit, `b := −3·C2can`, inside `[−T, 0]`), composed with the parabolic rescaling at `(yₙ, t₀ₙ, Rₙ)`
and the B1 sliver; target flow `S' := G.flow` (the slab flow), which is legitimate because on
`[t − 3C2can/R, t] ⊆ [a, t]` (F4, `τ₀`) the survivor flow on `U` equals `G.flow` restricted to `U`
(`f last = val`), so `MetricComparisonOn` against the survivor flow is one against `G.flow`.
Positive/round (compact `P∞`): component capture + transport of `PositiveComponent`/`RoundComponent`
(F8; candidate supplier `CompactCanonicalAlternative.lean:18`). The scalar, radius, `rm_bound`,
volume, gradient and time-derivative fields transfer by `C^2`-closeness with strict margins
(`ε' ≤ ε/2`, constants `C2can → 2C2can ≤ Ctime₀, Cgrad₀`), then `enlarge_constants`
(`CanonicalStrictBounds.lean:141`) and `canonicalWitness_mono` to `(ε, C1, C2)`; cap-neck charts
(`capTubeHasNeckChart`) as in `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts`.
Young bases (`R(t−a) < τmin`) need only the derivative and gradient fields, which come from `W∞`'s
`time_derivative`/`gradient` fields through the `C^1` space-time convergence at the terminal time.
Contradiction with the choice of `(yₙ, tₙ)`.

## 3. Where young points of earlier slabs enter

1. B3 on every slice at depth (earlier slabs and current slab before `t₀`): spatial witnesses at
   high-curvature young points — F5's hypotheses. The derivative/gradient bounds at young points of
   earlier slabs are already hypotheses (`EventSlabsDerivative`, `EventSlabsGradient`).
2. B4/B5 crossing an event backward: the capture (X2) may be at an earlier event `j < last`; the cap
   comparison there needs `qcan ≤ Cbirth·scale`, `1 ≤ a₀·scale` for EVERY record (class supply,
   decision 3(iv)).
3. B6 κ: `NoncollapsedBefore` is history-level and already covers earlier slabs.
4. Nothing else: the witness itself (B8) lives on the current slab only (F4).
Induction structure needed (for `DESIGN_28` item (iii)): Crossing's hypotheses add
`H.EventSlabsSpatiallyCanonical ε̄ C1s C2s qs k` and `G.SpatiallyCanonicalBefore ε̄ C1s C2s qs t₀`
(event and terminal forms, exactly C4's), quantified `∀ C1s C2s Λs` before `∃ q₀`, with
`qs ≤ Λs · max qcan 1` and `ε̄ ≤ ε̄cone`; the joint continuation (C with C4 at the same `t₀`) is
well-founded because each consumes only the other's `…Before t₀`.

## 4. Size

B0 0.9–1.5k, B1 0.4–0.7k, B2 1.2–1.9k, B3 4–7k, B4 0.6–0.9k, B5 1.5–2.5k, B6 6–12k, B7 0.3–0.6k,
B8 2–3.5k: about 17–31k lines, dominated by B3 and B6c (F9). Parallelizable after B2: {B0, B1},
{B3}, {B4, B5}, {B6a, B6b}, {B8b}; B6c and B7 last.
