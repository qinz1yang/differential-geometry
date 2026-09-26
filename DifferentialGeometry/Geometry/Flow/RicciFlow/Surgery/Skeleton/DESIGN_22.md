# DESIGN 22: history L-geometry through regular crossings (C2 tools)

2026-09-26. Read-only design worker. Worktree `D:\differential-geometry-pc3` at 1682df442. No Lean
edits, no builds, no probes. All paths below are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

Targets: `HistoryReducedVolumeMonotone` and `HistoryReducedVolumeLocalUpperBound`
(`Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean:208,214`). Both are stated for every
`RetainedCoreHistory P₀`, with no cutoff-class hypotheses. I found no configuration that refutes
either statement. Several intermediate formulations in the entry-22 brief are false, though. They
are listed first.

## 0. What fails or is unprovable as briefed

F1. **`Ω_v := {Z | ∃ σ > v, minimizing up to σ}` does not cover `regularMinimizerEndpoints`
up to a null set.** This is the single-flow `lInjDomain` convention. It fails when `T − v²` is an
event time, because of the post-surgery one-sided convention (`activeStage` picks the new stage).
Configuration: event `i` at time `s`, `T ∈ (s, time (i+1))`, `v = √(T − s)`, and a new cap `U ⊆ stage (i+1)`
of positive volume. Minimizers from `p` to points of `U` lie entirely in stages `≥ i+1`, so they
are regular minimizers. But extending one to `σ > v` requires a crossing at event `i` at a point
`oldOutput z`, and cap points are not such images. The missed set is `U`, which has positive
measure. **Repair:** at the larger parameter `v₂`, use the *closed* minimizing domain
`Ω̄_{v₂} := {Z | γ_Z minimizes on [0, v₂]}` together with the *area inequality*, which needs no
injectivity. Use injectivity only at the smaller parameter `v₁ < v₂`, on `Ω̄_{v₂}` (§3, §4).

F2. **`Lexp_v` is not injective on `Ω̄_v`.** Multiple minimizers and a conjugate endpoint at `v`
itself break injectivity. It is injective only at `v₁ < v₂`, on `Ω̄_{v₂}` (brick H5).

F3. **The single-flow theorems do not apply directly.**
- `redVolume_anti_of_rm` (`Perelman/StandardSolution/ReducedVolumeMonotonicity.lean:52`, wrapped at
  `Perelman/LGeometry/ReducedVolume/Monotonicity.lean:23`) needs one manifold `M` carrying all the
  minimizers, plus `RiemannianMetricComplete (S.base.metric T)`, `hRm` on regular slabs, and
  `Icc (T − τ₂) T ⊆ D.regular`.
- `exists_pos_redVolume_le_on_flowMetricBall` (`…/BallEstimate/UniformUpperBound.lean:221`) needs
  `[CompactSpace M] [ConnectedSpace M]`, a `FlowMetricBall` of the same `S`, and
  `Ioc (t − r²) t ⊆ D.regular`.
- No single `M` hosts the history minimizers (C2U log). Only the pieces of these proofs are reusable.

F4. **Closed-end times are not `D.regular`, and both leaves reach them.** `RealTimeInterval.regular`
is open (`Analysis/TimeInterval.lean:93–98`). Two cases are affected:
- Base time `T = horizon` of `finalSlab`, a `ClosedSlab`. `HistoryReducedVolumeMonotone` allows it
  through `T ∈ stageDomain last = Icc`; `HistoryReducedVolumeLocalUpperBound` allows it through
  `t ∈ Icc 0 horizon`.
- Endpoint time `T − v² = time j`, the start of an `IncomingSlab`.

The tree's L-exp needs a regular base time: `zero_mem_lExpDomain` needs `hT : T ∈ D.regular`, and
`exists_lPhaseAt` needs `T − s₀² ∈ D.regular`. This is not a counterexample, because the metric is
`MetricSmoothUpTo` the closed end. It does force brick **G1**: a smooth, non-Ricci, time extension
of a `MetricSmoothUpTo` family past a closed end, so that the L-geodesic ODE and its C¹
dependence on data reach the end. The alternative is an interface change that excludes
`t = horizon`. The assembly could absorb that change, since `TerminalNoncollapsedAboveBefore`
already carries a slab `G` beyond `T`.

F5. **"The seam map is a local isometry of `stageMetric`" is false as a statement about
`stageMetric i.castSucc (time i.succ)`.** That value is `incoming.flow.base.metric` at the open end
`s` of `closedOpen a s`, which is junk. The correct objects are:
- `E.terminal.metric` on `terminalRegularOpen`, related to `outputMetric` by `old_metric_eq`
  (`Surgery/Topology/EventData.lean:324`) and by the metric clause of
  `exists_survivor_partialDiffeomorph` (`EventSurvivorMap.lean:94`);
- the glued flow of `exists_survivor_solution_across_event` (`SurvivorMetricSeam.lean:31`).

Every seam statement below uses these. The stage Lagrangian integrals are over `Ioo`, so the junk
value never enters an action.

F6. **The confinement for (e) does not need `SlabBackwardCurvatureControl` or
`BackwardTraceScalarControl`, and cannot use them.** Both need canonical-neighbourhood / cutoff-class
data, which the leaf does not assume. What the leaf does assume, `isParabolicallyRmControlledBall`,
already yields one smooth common flow `S` on `U = B(p, r)` over `[t − r², t]` with `|Rm| ≤ r⁻²`:
`exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall`
(`Surgery/Topology/HistoryParabolicBall.lean:860`). The local Shi estimate inside `U` supplies
`|∇R|`: `exists_shiFirstDerivative_local_of_solution` (`Estimates/Shi/FirstDerivativeLocal.lean:251`).
No crossings are visible inside `U`. This resolves C2U's (CF) and (VC).

F7. **`σ` independent of `ρ` needs rescaling, not the existing lemma.**
`exists_pos_lRegularizedCurve_mem_ball_of_local_gradient_ricci_bounds`
(`Perelman/LGeometry/Ray/Range.lean:201`) has `b = min B (r / (2(√(AQ)+1)))` with
`Q = exp((1 + 2GB² + 4KB)B)(4R² + 1)`. The `1·B` term is not scale-covariant, so `b ≠ σ r`
uniformly. Apply it to the parabolically rescaled common flow (`r = 1`), which gives brick G6.
The tree's `ρ` in `exists_pos_lRegularizedCurve_mem_ball` (`Ray/FlowBall.lean:447`) is the same
artefact.

F8. **Measurability.** The monotonicity proof integrates over `Ω̄_v`. Its measurability reduces to
Borel measurability of `q ↦ regularizedCost`, which is queue entry 26 (compare
`measurable_regularizedDensity_of_isClosed_regularizedCost_le`, `ReducedVolumeTruncation.lean:216`).
So entry 26 is a prerequisite, not a sibling.

F9. **The scalar floor for an arbitrary `H`.** `reducedVolume` is a `limsup_B`. The only floor in
the tree, `exists_stageMetric_scalar_lower_bound` (`ReducedVolumeTruncation.lean:59`), needs
`GeometricCutoffRecord` for every event. Both leaves quantify over all `H`, so a class-free
per-`H` floor is required. It is easy: each stage is compact (`OrientedThreeStage.compact`), and
`incomingSlab_scalarLowerBarrier_le` / `closedSlab_scalarLowerBarrier_le` apply stage by stage.
This is brick H0.

## 1. Single-flow facts (answers to the survey questions)

- **Monotonicity route: Jacobian.** `redVolume_anti_of_rm` combines three steps:
  - `redVolume_lint_of_rm` (change of variables to `lInjDomain`, with integrand
    `lReducedJacobian · lSourceDensity` against `modelHaar`, via `exists_lExpPartial_full_of_rm`
    `StandardSolution/InjGeometryComplete.lean:140` and `redVolume_lint_of_param`
    `StandardSolution/ReducedVolumeComplete.lean:142`);
  - pointwise `lRedJac_antitoneOn_of_rm` (`StandardSolution/RedJacobian.lean:289`; needs
    `(Z, σ) ∈ lMinDomain`, and gives `AntitoneOn (lReducedJacobian S T x Z) (Ioo 0 σ)`);
  - `lintegral_mono_set` on the nested `lInjDomain`.

  The derivative core is `lReducedJacobian_deriv_le` (`Jacobian/Monotonicity.lean:256`). Its
  frame hypotheses are `P`, `hDP : ∇P = −2s Ric P`, `hON`, and integrability. Behind it,
  `lExpLog_hasDeriv` goes through the Laplacian of `redLength`, which is global cut-locus
  smoothness. The Gram layer is local along the curve: `lGram`, `lGramDeriv`, `lJacobianDensity`
  and `lJacobianDen_hasDeriv` (`Jacobian/Basic.lean:53–113`).
- **Gaussian tail: in velocity space.** `lSourceGaussian S T x Z` (`Jacobian/SourceGaussian.lean:162`)
  has mass 1 (`lSourceGaussian_mass`, line 184). Its tail is uniform over all `S T x`
  (`lSourceGaussian_uniform_tail`, `Jacobian/SourceGaussianTail.lean:89`). The pointwise bound is
  `lReducedJacobian_source_le_of_bdd` (`BallEstimate/SourceTailControl.lean:33`: `(Z, σ) ∈ lMinDomain`,
  `τ < σ`, and `hbdd`). The tail integral is `lReducedJacobian_tail_le` (line 69). The variant for a
  noncompact `M` is `lintegral_redDensity_image_lExp_le_volume_add_gaussian_tail`
  (`ReducedVolume/MinimizingMass.lean:711`): open `U`, `hmin`, `hnconj`, `hinj`, `hbdd`, radius `R`,
  target `Q`, bound `c`.
- **I 7.3 single flow:** `exists_pos_redVolume_le_on_flowMetricBall` (as in F3, with `Q > 1`,
  `rho`, `eta`, `eps₀(rho)`). Its core is `exists_pos_lintegral_lReducedJacobian_le_on_flowMetricBall`
  (`UniformUpperBound.lean:79`): velocities `|Z| ≤ 1/(128√eps)` land in the closed ball `r/32`.
  Volume transfer is `exists_pos_volume_le_on_terminal_ball` (`Noncollapsing/FlowBall/VolumeComparison.lean:21`,
  which needs completeness).
- **Short time:** `tendsto_lReducedJacobian_at_zero_of_bdd` and `lReducedJacobian_le_gaussian_of_bdd`
  (`ShortTime/ReducedJacobianLimit.lean:169,223`).
- **Regularity of minimizers:** `lMinCurve_regularizedGeodesicOn_of_spatial_derivatives`
  (`Action/Minimizer/EulerLagrangeRegularity.lean:99`) gives chart-`H¹` minimizer ⇒
  `IsLRegularizedGeodesicOn` on `Ioo`. The AC bridge is
  `exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval`
  (`Action/ChartPartition/Construction/Sobolev.lean:81`).
- **Index:** `lRegularizedIndex_nonneg` (`Index/MinimizerNonnegativity.lean:57`),
  `lRegularizedIndex_piecewise_nonneg` (`Index/PiecewiseNonnegativity.lean:422`),
  `lRegularizedAction_second_variation_moving_endpoints`
  (`Action/Regularized/MovingEndpointSecondVariation.lean:130`).
- **Change of variables (analysis):** injective case `lintegral_image_eq_lintegral_paramDensity_mul`
  (`Analysis/Integration/Measure/Parametric/Integration.lean:53`); non-injective measure case
  `riemannianVolumeMeasure_image_le` (`AreaFormula.lean:479`); multiplicity
  `lintegral_encard_fiber_eq_lintegral_paramDensity` (`Multiplicity.lean:70`, needs local
  injectivity).
- **The collaborator's history tools have no geodesic theory.** A grep for
  `variation|Jacobi|IsLRegularizedGeodesicOn|lExp|lInjDomain` in `HistoryAction*` returns nothing.
  What exists:
  - costs and dynamic programming (`regularizedCost_dynamic_programming_at_event`,
    `HistoryAction/AbsoluteContinuity.lean:793`; `mem_regularizedActionValues_split_at_event`, `:762`);
  - joins (`HistoryActionJoin.lean:216,314,366`, C¹ values only);
  - common-flow transfer (`action_mem_regularizedC1ActionValues_of_common_curve`, `HistoryAction.lean:964`);
  - the seam flow (`exists_survivor_solution_across_event`);
  - common-flow density lemmas (`HistoryMinimizingDensity.lean:82,158,415`).

## 2. (a) History L-geodesics, the L-exponential map, and surjectivity

Seam relation, which is what the collaborator's structure actually gives. Take a `RegularCrossing`
at event `i` with parameter `w = √(T − time i.succ)` and point `x ∈ interior (val '' old)`
(`mem_interior_old_of_regularCrossing`). `RegularCrossing.exists_survivor_partialDiffeomorph`
(`SurvivorChartMetric.lean:38`) gives `F` with `F x = q`. `exists_survivor_solution_across_event`
gives a smooth Ricci flow on `W ∋ x` over closed `[c, d] ∋ s`: the old metric is
`terminal.extendedMetric` for `t ≤ s`, and for `t > s` it is `G.flow` pulled back by `F`. A regular
minimizer restricted to a neighbourhood of `w` lies in `W` (continuity of `α` at `w`, `W` open) and
minimizes there. Competitors in `W` become history competitors with the same action, crossing at
points of `W ⊆ interior old`. By single-flow regularity it is then a C¹ `IsLRegularizedGeodesicOn`
of the glued flow. Hence the **matching**
`mfderiv F (α_old'(w)) = α_new'(w)`, i.e. `Dψ γ̇₋ = γ̇₊`, with `ψ = F` read in the direction
old → new. Note that `s`-velocity at the seam is one-sided on each stage and two-sided in the
glued flow.

Proposed Lean (new file `Surgery/Topology/HistoryLGeometry/Geodesic.lean`, namespace
`ObservedHistory`):

```lean
structure LWindow (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (T : ℝ) where
  X : Type u
  [top : TopologicalSpace X] [charts : ChartedSpace ThreeSpace X]
  [smooth : IsManifold ThreeModel ∞ X] [t2 : T2Space X] [sigma : SigmaCompactSpace X]
  a b : ℝ
  hab : a < b
  D : RealTimeInterval
  S : SolutionOn (I := ThreeModel) (M := X) D
  hS : IsSolutionOn S
  regular : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular
  f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier
  hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)
  hinj : ∀ j, Function.Injective (f j)
  hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
    T - (Real.sqrt (T - H.time i.succ)) ^ 2 ∈ Icc (T - b ^ 2) (T - a ^ 2) →
    (H.event i).RegularCrossing (f ⟨i.castSucc, hi, _⟩ z) (f ⟨i.succ, _, hl⟩ z)
  hmetric : ∀ j, ∀ s ∈ Ioo a b ∩ Ioo (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T b j.val),
    S.base.metric (T - s ^ 2) = localPullMetric (H.stageMetric j.val (T - s ^ 2)) (f j) (hf j)

def IsHistoryLGeodesicOn (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) : Prop :=
  (∀ i hf hl, (H.event i).RegularCrossing
      (α ⟨i.castSucc, hf, _⟩ (Real.sqrt (T - H.time i.succ)))
      (α ⟨i.succ, _, hl⟩ (Real.sqrt (T - H.time i.succ)))) ∧
  ∀ s ∈ Ioo 0 v, ∃ W : H.LWindow first last T, s ∈ Ioo W.a W.b ∧ ∃ γ : ℝ → W.X,
    IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
    ∀ j, ∀ r ∈ Ioo W.a W.b ∩ Icc (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val), α j r = W.f j (γ r)
```

The window formulation makes stage interiors and seams uniform. A stage-interior window takes
`X` open in one stage with `f` the inclusion. A seam window is the `W` of
`exists_survivor_solution_across_event`, with `f old = val`, `f new = F`. Velocity matching is then
a consequence (`seam_velocity_eq`), not a field.

```lean
theorem isHistoryLGeodesicOn_of_mem_regularMinimizerEndpoints   -- (a) regularity
    (first last) (hle) {T B v : ℝ} (hv : 0 < v) (hT : T ∈ H.stageDomain last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (p : (H.stage last).Carrier) (α) (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hp : α ⟨last, hle, le_rfl⟩ 0 = p) (hcross : ∀ i hf hl, (H.event i).RegularCrossing …)
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v p (α ⟨first, le_rfl, hle⟩ v)) :
    H.IsHistoryLGeodesicOn first last hle T v α ∧
      ∃ Z : TangentSpace ThreeModel p, H.historyInitialVelocity … α = Z

def historyLExpDomain (first last) (hle) (T v : ℝ) (p) : Set (TangentSpace ThreeModel p) :=
  {Z | ∃ α, H.IsHistoryLGeodesicOn first last hle T v α ∧ α ⟨last, hle, le_rfl⟩ 0 = p ∧
      lVelocity (α ⟨last, hle, le_rfl⟩) 0 = 2 • Z}

theorem historyLExp_unique … :        -- ODE uniqueness window by window; regularCrossing_right_unique
    IsHistoryLGeodesicOn … α → IsHistoryLGeodesicOn … β → same p, same Z → ∀ j, EqOn (α j) (β j) …

def historyLExp (first last) (hle) (T v : ℝ) (p) (Z) : (H.stage first).Carrier   -- choice + unique

theorem isOpen_historyLExpDomain_and_contMDiffOn_historyLExp …   -- in Z, for fixed v
    -- requires G1 when T − v² or T is a closed end

def historyMinDomain (first last) (hle) (T B v : ℝ) (p) : Set (TangentSpace ThreeModel p) :=  -- Ω̄_v
  {Z ∈ H.historyLExpDomain first last hle T v p |
    (H.historyAction … Z v : WithTop ℝ) = H.regularizedCost first last hle T B 0 v p (H.historyLExp … Z)}

theorem regularMinimizerEndpoints_subset_image_historyMinDomain … :      -- surjectivity
    H.regularMinimizerEndpoints first last hle T B v p ⊆
      H.historyLExp first last hle T v p '' H.historyMinDomain first last hle T B v p

theorem regularizedDensity_historyLExp_eq … (hZ : Z ∈ H.historyMinDomain …) :
    H.regularizedDensity first last hle T B v p (H.historyLExp … Z) =
      ENNReal.ofReal (Real.exp (-(H.historyAction … Z v) / (2 * v) -
        (3/2) * Real.log (v ^ 2) - (3/2) * Real.log (4 * Real.pi)))
```

(`first = activeStage (projIcc … (T − v²))`, as in `reducedVolume`.) Surjectivity is exactly the
regularity theorem. The density identity follows from `regularizedDensity_eq_exp_of_cost_eq`
(`HistoryReducedDensity.lean:367`) and `hfloor`.

Supply for the proof:
- dynamic programming (`AbsoluteContinuity.lean:762,793`) for stage-wise minimality;
- the AC → chart-`H¹` bridge;
- `lMinCurve_regularizedGeodesicOn_of_spatial_derivatives`, for stage interiors and for the glued
  window at seams;
- `RegularCrossing.exists_survivor_partialDiffeomorph`, `exists_survivor_solution_across_event`;
- a new "window competitor → history competitor" splice (brick H1);
- the initial vector from the single-flow ray/initial-vector theory (`Ray/InitialVector`,
  `CutLocus/Minimizer/Regularity.lean:26`).

Gap: splicing a window curve into an AC history curve. The tree has
`exists_regularizedC1ActionValues_join*` only for C¹ values; use `regularizedCost_eq_regularizedC1Cost`
(`HistoryAction/Density.lean:294`) to move between the two. **Size:** H1 1200, H2a 1200,
H2b 1000, H3a 900, H3b 1400, H4 800.

## 3. (b) Truncation and nesting

```lean
theorem truncate_mem_regularMinimizerEndpoints …   -- truncation of a regular minimizer
    (hα : α witnesses q ∈ H.regularMinimizerEndpoints first last hle T B v₂ p) (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (first' := activeStage (T − v₁²)) :
    (fun j => α ⟨j.val, _, _⟩) witnesses
      α ⟨first', _, _⟩ v₁ ∈ H.regularMinimizerEndpoints first' last _ T B v₁ p

theorem historyMinDomain_antitone (h12 : v₁ ≤ v₂) :
    H.historyMinDomain first₂ last _ T B v₂ p ⊆ H.historyMinDomain first₁ last _ T B v₁ p

theorem injOn_historyLExp_of_lt (h12 : v₁ < v₂) :
    InjOn (H.historyLExp first₁ last _ T v₁ p) (H.historyMinDomain first₂ last _ T B v₂ p)

theorem not_conjugate_of_lt (h12 : v₁ < v₂) (hZ : Z ∈ H.historyMinDomain … v₂ p) :
    0 < H.historyJacobian … Z v₁                         -- nonzero D Lexp at interior times
```

**Proof of truncation.** A cheaper competitor to `α(v₁)` can be spliced with `α|[v₁, v₂]`. Split at
event parameters with `mem_regularizedActionValues_split_at_event`; split inside a stage with an
AC join lemma. The AC analogue of `exists_regularizedC1ActionValues_join_same_stage` is new, about
300 lines. Crossings of the truncation form a subset of the original crossings, so they stay
regular. When `T − v₁²` is an event time, the old-stage part and the crossing at that event are
dropped, which is consistent with the post convention.

**Proof of injectivity (corner argument).** Suppose two minimizers to the same `v₁`-endpoint. The
concatenation of the second with `α|[v₁, v₂]` is again a minimizer, so it is a history L-geodesic
(§2) and is C¹ at `v₁`. By uniqueness (H3a) the two coincide.

**Non-conjugacy.** Derived from the history index nonnegativity on `[0, v₂]` (H6) and the
single-flow `CutLocus/BeforeCutTime` pattern.

**Size:** H5 1400.

## 4. (c) Weighted Jacobian through seams

Definition. The source density is the single-flow `lSourceDensity` of the stage-`last` metric at
`T`. At a closed end, stage `last` is replaced by the base window (G1 or the glued seam window).

```lean
def historyReducedJacobian (first last) (hle) (T v : ℝ) (p) (Z) : ℝ :=
  paramDensity (H.stageMetric first (T - v ^ 2)) (H.historyLExp first last hle T v p) Z /
    lSourceDensity' (H.stageMetric last T) p *
  Real.exp (-(H.historyAction … Z v) / (2 * v) - (3/2) * Real.log (v ^ 2) - (3/2) * Real.log (4 * Real.pi))
```

For the key theorem below, `first` is the `v`-dependent active stage. Write
`first v := activeStage (projIcc … (T − v²))`.

```lean
theorem historyReducedJacobian_antitoneOn (hZ : Z ∈ H.historyMinDomain (first v₂) last _ T B v₂ p) :
    AntitoneOn (fun v => H.historyReducedJacobian (first v) last _ T v p Z) (Ioc 0 v₂)

theorem historyReducedJacobian_le_gaussian (hZ : Z ∈ H.historyMinDomain … v p) :
    ENNReal.ofReal (H.historyReducedJacobian … v p Z * lSourceDensity' …) ≤
      ENNReal.ofReal (lSourceGaussian' (H.stageMetric last T) p Z)
```

Proof layers:

1. **Continuity across a seam.** `paramDensity` is invariant under post-composition with an
   isometric local diffeomorphism. This is new generic brick G2, about 300 lines, from
   `paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt`. `F` is isometric from
   `terminal.metric` to `outputMetric` (`exists_survivor_partialDiffeomorph`, 4th clause). The glued
   flow is jointly `C^∞` across `s` (`exists_survivor_solution_across_event`, clause 8). So
   `v ↦ J` is continuous at the seam from both sides: on the old side as `v ↓ w` using
   `terminal.metric`, and on the new side at `v = w` using `outputMetric = initialMetric (i+1)`
   (`event_output`). The action is continuous in `v`.
2. **Derivative on a window.** `J` is `lJacobianDensity` (`Jacobian/Basic.lean:72`) of the Jacobi
   fields `Y_k = D historyLExp (e_k)`. These are local, so `lJacobianDen_hasDeriv` applies inside
   each `LWindow`: `(log J)' = ½ tr(G⁻¹ G')` with `lGramDeriv`. What is not local is the
   inequality `Σ⟨∇Y, Y⟩ ≤ Σ I(W, W)` for Perelman's adapted fields `W = (s/√τ) P`. It needs a
   **history index form**, the sum over windows of `lRegularizedIndex`, together with:
   - (i) nonnegativity on fields vanishing at `0` and `v`, for `Z ∈ Ω̄_{v₂}`, `v ≤ v₂` (H6: second
     variation of the history action equals the sum of window second variations; boundary terms
     cancel because the glued flow is smooth);
   - (ii) the Jacobi-minimizes-index comparison on `[0, v]` with free end value (G4, single flow on
     intervals);
   - (iii) the adapted-frame trace computation (G5; single-flow `lExpLog_deriv_le` frame
     hypotheses `hDP`, `hON`, `hIint`, `hRint`, restated for an abstract windowed index).
3. Antitone on `(0, v₂)` from 2. It extends to `v₂` by left continuity, since `J ≥ 0` and is
   continuous up to `v₂`; at a closed end this needs G1.
4. **Limit at `0`.** For small `v` the geodesic is in the base window, which is stage `last` or the
   glued window when `T` is an event time. So `J_hist = lReducedJacobian` of that window's flow
   (G2 naturality), and `tendsto_lReducedJacobian_at_zero_of_bdd` gives the Gaussian.

**What cannot be reused.** `lRedLog_hasDeriv` / `lExpTrace_hess` compute the trace through
`laplacian … redLength`, which requires the cost to be smooth near the endpoint. That is cut-locus
theory the history does not have. The history proof must use the Jacobi/index route of layer 2,
not `lReducedJacobian_hasDeriv`.

**Size:** H6 1500, H7a (continuity + definition) 900, H7b (window derivative + antitone) 1400,
H7c (limit) 600; G4 1200, G5 1300.

## 5. (d) Change of variables and `HistoryReducedVolumeMonotone`

For `0 < v₁ < v₂`, set `K := Ω̄_{v₂}` and `f_v := historyLExp … v`. Write `ℓJ(v)` for
`historyReducedJacobian … v p Z · lSourceDensity'`. Then:

- `Ṽ(v₂) = ∫_{regularMinimizerEndpoints(v₂)} dens`
- `≤ ∫_{f_{v₂} '' K} dens`  (surjectivity, §2; `Measure.restrict_mono` needs no measurability)
- `≤ ∫_K ℓJ(v₂)`  (area inequality with multiplicity, G7, plus the density identity of §2)
- `≤ ∫_K ℓJ(v₁)`  (pointwise, §4)
- `= ∫_{f_{v₁} '' K} dens(v₁)`  (injective, `injOn_historyLExp_of_lt`,
  `lintegral_image_eq_lintegral_paramDensity_mul`)
- `≤ Ṽ(v₁)`  (`f_{v₁} '' K ⊆ regularMinimizerEndpoints(v₁)` by truncation, §3).

The case `v₁ = v₂` is trivial. `reducedVolume` is a `limsup_B`, so the chain is run at `B₀ = b(H)`
from H0 and transported by `reducedVolume_eq_of_scalar_lower_bound_le`
(`ReducedVolumeTruncation.lean:294`, which takes `hfloor`, so no class is needed).

```lean
theorem historyReducedVolumeMonotone (P₀ : OrientedThreeStage.{u}) : HistoryReducedVolumeMonotone P₀
```

G7 (generic, `Analysis/Integration/Measure/Parametric/`):

```lean
theorem lintegral_image_le_lintegral_paramDensity_mul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E} (hU : IsOpen U) (hK : MeasurableSet K)
    (hKU : K ⊆ U) (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (h : E → ℝ≥0∞) (hh : Measurable h)
    (φ : M → ℝ≥0∞) (hφ : ∀ x ∈ K, φ (f x) ≤ h x) :
    ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure g ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity g f x) * h x ∂modelHaar
```

Proof sketch for G7: split `K` into the critical set (`paramDensity = 0`, whose image is null by
Mathlib's `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in charts) and the regular part,
which is locally injective by the inverse function theorem. On the regular part use
`exists_partition_injOn` and `riemannianVolumeMeasure_image_eq` as in `Multiplicity.lean:70`.

Gaps: G1 (closed ends), G7, H0, entry 26 (measurability of `Ω̄`). **Size:** G7 600, H0 200,
H8 900.

## 6. (e) `HistoryReducedVolumeLocalUpperBound` (I 7.3 through crossings)

Fix `η`.
- `R := R(η)` from `lSourceGaussian_uniform_tail`, with `eps := η`. That lemma is uniform over all
  flows, so `R` is independent of `H`.
- `σ := σ(R) ≤ 1` from G6: confinement in the rescaled common flow.
- `C₀ := (4π)^{-3/2} e^{C_R/3 + C_V}`, with `C_R`, `C_V` dimension constants from
  `|Rm| ≤ r⁻² ⇒ |R| ≤ C_R r⁻²` and from the volume-form distortion over time `σ² r² ≤ r²`.

Given `H t p r` with the ball hypothesis, take `(a, U, f, S, K, pU)` from
`exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall`. Set `v := σ r`
(`v² ≤ r² ≤ t` by `radius_sq_le_time`) and `Ω̄ := historyMinDomain … v p`. Then
`Ṽ(v) ≤ ∫_{Lexp(Ω̄ ∩ {|Z| ≤ R})} dens + ∫_{Lexp(Ω̄ ∩ {|Z| > R})} dens` (`lintegral_union_le`).

**Core.**
- Confinement: G6 applied to `S` gives `lRegularizedCurve S t pU Z` staying in `K` for
  `|Z| ≤ R`, `s ≤ v`.
- Then `f ∘ γ_S` is a history L-geodesic. It crosses regularly (`hcross` of the common flow) and
  is window-wise L-geodesic via G2. By `historyLExp_unique`, `historyLExp Z = f_first (lExp_S Z)`.
- So the core image lies in `f_first '' K_v`, where `K_v` is the image set at time `t − v²`.
- Density bound: `dens ≤ (4π v²)^{-3/2} e^{C_R σ²/3}` from the action lower bound
  `A ≥ −(2C_R/3) v³/r²`, since `R ≥ −C_R/r²` in `U`.
- Volume: `f_first` is an injective local isometry at `t − v²` (`hmetric`), so
  `μ_first(f_first '' K_v) = μ_S(K_v)`. G8 gives `μ_S(K_v) ≤ e^{C_V} μ_{S,t}(K_v)`, and `K_v ⊆ U`
  gives `≤ e^{C_V} vol_t B(p, r)`, via `hterminal : S.base.metric t = (stageMetric …).restrictOpen U`.

**Tail.** G7 plus `historyReducedJacobian_le_gaussian` give
`∫_{Lexp(tail)} dens ≤ ∫_{|Z|>R} lSourceGaussian' ≤ η`. The Gaussian is computed with
`stageMetric last t` at `p`, the same quadratic form as the tail lemma, which is metric-generic.

Assembly: `ENNReal.ofReal (C₀ / (σ r)³) * vol + ENNReal.ofReal η`, using
`(4π σ² r²)^{-3/2} = (4π)^{-3/2} / (σ r)³`. `σ` depends only on `η`, since `R` does and the
rescaled confinement constant is dimensionless.

```lean
theorem historyReducedVolumeLocalUpperBound (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeLocalUpperBound P₀
```

Brick G6 (single flow, scale-free confinement on a noncomplete open manifold):

```lean
theorem exists_pos_lRegularizedCurve_mem_closedBall_of_parabolic_rm_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ {X} [...] {D} (S : SolutionOn (M := X) D), IsSolutionOn S →
      ∀ (T r : ℝ) (x : X), 0 < r → Ioo (T - r ^ 2) T ⊆ D.regular → T ∈ D.regular →
      IsCompact {y | riemannianEDistOf (S.base.metric T) x y ≤ ENNReal.ofReal (r / 2)} →
      (∀ t ∈ Icc (T - r ^ 2) T, ∀ y, riemannianEDistOf (S.base.metric T) x y < ENNReal.ofReal r →
        r ^ 4 * FlowMetricBall.rmNormSq S t y ≤ 1) →
      ∀ Z : TangentSpace ThreeModel x, (S.base.metric T).inner x Z Z ≤ R ^ 2 →
        σ * r ∈ lRegularizedDomain S T x Z ∧ ∀ s ∈ Icc 0 (σ * r),
          riemannianEDistOf (S.base.metric T) x (lRegularizedCurve S T x Z s) < ENNReal.ofReal (r / 4)
```

Proof: rescale to `r = 1` (`Action/ParabolicScaling`, `Geodesic/Scaling`); local Shi
(`exists_shiFirstDerivative_local_of_solution`) for `G`; `inner_le_exp_mul_inner_of_rmNormSq_le`
(`Noncollapsing/ForwardTransfer.lean:91`) for `A`; the Ricci bound from `|Rm|` for `K`; then
`exists_pos_lRegularizedCurve_mem_ball_of_local_gradient_ricci_bounds`. `T ∈ D.regular` fails at
`t = horizon` (F4, needs G1).

**Size:** G6 700, G8 250, H9 1400.

## 7. Dependency-ordered bricks (each ≤ 1500 lines)

| # | Brick | Home | Kind | Lines | Depends on |
|---|---|---|---|---|---|
| G1 | Closed-end time extension of a `MetricSmoothUpTo` family; L-exp/phase flow up to a closed start or end, C¹ in data | `Perelman/LGeometry/Geodesic/` (+ `Analysis/Calculus/TimeJet`) | single-flow | 900 | — |
| G2 | Naturality under isometric local diffeos / `localPullMetric`: `IsLRegularizedGeodesicOn`, `lGram`, `lJacobianDensity`, `lRegularizedIndex`, `paramDensity` | `Perelman/LGeometry/Geodesic/Naturality`, `Jacobian/` | single-flow | 800 | — |
| G3 | Window solution map of the L-geodesic ODE from arbitrary `(s₀, x, V)`, smooth in data (repackage `exists_lPhaseAt`, `lRegularizedFamily_extend`) | `Perelman/LGeometry/Geodesic/` | single-flow | 1200 | G1 |
| G4 | Interval index comparison: Jacobi field minimizes `lRegularizedIndex` with fixed end values, given nonnegativity on fields vanishing at both ends | `Perelman/LGeometry/Index/` | single-flow | 1200 | — |
| G5 | Adapted-frame trace inequality for `lGramDeriv`, stated against an abstract additive index functional | `Perelman/LGeometry/Jacobian/` | single-flow | 1300 | G4 |
| G6 | Scale-free confinement on a noncomplete open manifold (statement §6) | `Perelman/LGeometry/Ray/` | single-flow | 700 | G1 at closed end |
| G7 | Area inequality with density (statement §5) | `Analysis/Integration/Measure/Parametric/` | generic | 600 | — |
| G8 | Volume of a set under `r⁴|Rm|² ≤ 1` over a time window, noncomplete `M` | `Perelman/Noncollapsing/` | single-flow | 250 | — |
| H0 | Class-free per-history scalar floor `∃ b, ∀ j t x, −b ≤ R` | `Surgery/Topology/ReducedVolumeTruncation` (sibling file) | history | 200 | — |
| 26 | (queue) eventual constancy, finiteness, measurability of cost/endpoints | — | history | — | H0 |
| H1 | `LWindow`; stage and seam windows from `exists_survivor_solution_across_event`; window-competitor ↔ history-competitor splice, AC join inside a stage | `Surgery/Topology/HistoryLGeometry/Window` | history | 1200 | G2 |
| H2a | Regular minimizers: stage-interior L-geodesic and initial vector | `…/Regularity` | history | 1200 | H1 |
| H2b | Seam C¹ matching `mfderiv F (α_old' w) = α_new' w` | `…/Seam` | history | 1000 | H1, H2a |
| H3a | `IsHistoryLGeodesicOn`, `historyLExpDomain`, `historyLExp`, uniqueness | `…/Exponential` | history | 900 | H1, G3 |
| H3b | Openness of domain, smoothness of `historyLExp` in `Z` (composition of G3 maps and seam `F`) | `…/ExponentialSmooth` | history | 1400 | H3a, G1 |
| H4 | `historyMinDomain`, surjectivity, density identity | `…/MinDomain` | history | 800 | H2, H3a, H0 |
| H5 | Truncation, nesting, injectivity at `v₁ < v₂` | `…/Truncation` | history | 1400 | H4 |
| H6 | History index form; second variation; nonnegativity; non-conjugacy | `…/Index` | history | 1500 | H1, H5, G4 |
| H7a | `historyReducedJacobian`; seam continuity | `…/Jacobian` | history | 900 | H3b, G2 |
| H7b | Window derivative inequality; `historyReducedJacobian_antitoneOn` | `…/JacobianMonotone` | history | 1400 | H6, H7a, G5 |
| H7c | Limit at 0; `historyReducedJacobian_le_gaussian` | `…/JacobianLimit` | history | 600 | H7b |
| H8 | Change of variables; `historyReducedVolumeMonotone` | `…/ReducedVolumeMonotone` | history | 900 | H5, H7b, G7, 26 |
| H9 | Common flow + confinement + tail; `historyReducedVolumeLocalUpperBound` | `…/ReducedVolumeUpperBound` | history | 1400 | H7c, G6, G7, G8 |

Totals: single-flow and generic ≈ 7,550 lines; history ≈ 15,300 lines; overall ≈ 23k.

Suggested parallel lanes, subject to `FILL_QUEUE` dispatch:
- G1, G2, G4, G7, G8, H0 have no dependencies and can start at once.
- Then G3, G5, G6, H1.
- H2 through H9 form a mostly serial chain. H6 and H7a can run in parallel after H5 and H3b.

## 8. Which bricks are reusable single-flow generalizations

Pure single-flow or generic, stateable in `Perelman/LGeometry/` or `Analysis/` and reusable
elsewhere: G1, G2, G3, G4, G5, G6, G7, G8. G5 in particular should be stated for an abstract
additive index functional, so that the single-flow `lExpLog_deriv_le` becomes a corollary. G6 also
removes the `rho` artefact from `exists_pos_redVolume_le_on_flowMetricBall`; worth a follow-up
corollary.

History-specific glue: H0–H9. The only genuinely new mathematics among them is H6, the history
second variation and index form. The rest is splicing through `LWindow` and the seam map `F`.

**Interface decision for the lead (F4).** Either build G1 (about 900 lines, covers `t = horizon`
and endpoint times at stage starts), or restrict both leaves to `t < horizon` / `T < horizon` and
route the terminal case through the continuation slab already present in
`TerminalNoncollapsedAboveBefore`. The endpoint-time case at a stage start needs G1 in either case.
The only way to avoid it there would be a continuity-from-below lemma for `reducedVolume`, which
needs the same regularity.
