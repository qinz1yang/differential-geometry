import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Comparison.BallCapture
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_curvDerivNorm_on_compact_of_terminal_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hterminal : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0
      (fun i => (S i).base.metric b) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNormSq 0 ((S i).base.metric t) x ≤ C)
    (K : Set M) (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
      ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b, ∀ x ∈ K,
        curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨R.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨R.inner, R.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  obtain ⟨r, hr, hKr⟩ := hK.exists_isCompact_cthickening
  let K' := Metric.cthickening r K
  have hK' : IsCompact K' := hKr
  have hball (x : M) (hx : x ∈ K) : riemannianClosedBallOf R x r ⊆ K' := by
    intro y hy
    apply Metric.mem_cthickening_of_edist_le y x r K hx
    change riemannianEDistOf R y x ≤ ENNReal.ofReal r
    rw [riemannianEDistOf_comm]
    exact hy
  have hcompactR (x : M) (hx : x ∈ K) : IsCompact (riemannianClosedBallOf R x r) :=
    hK'.of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist R x) continuous_const)
      (hball x hx)
  obtain ⟨C₀, hC₀⟩ := hcurv K' hK'
  let B := Real.sqrt (max C₀ 0) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hC₀B : C₀ ≤ B ^ 2 := by
    dsimp [B]
    nlinarith [Real.sq_sqrt (le_max_right C₀ 0), Real.sqrt_nonneg (max C₀ 0),
      le_max_left C₀ 0]
  let tau := (b - a) / 4
  let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * B * (b - a))
  let C : ℕ → ℝ := fun m =>
    shiLocalUniformBound (Module.finrank ℝ E) m (B * tau)
      (((r / 4) / (4 * L)) * Real.sqrt B /
        (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * B * tau))) *
      B / Real.sqrt tau ^ m
  refine ⟨C, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hB.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  filter_upwards [(hterminal K' hK').eventually_quadratic_bounds hK'
    (show (0 : ℝ) < 1 / 2 by norm_num), hC₀] with i hmetric hcurvi
  have hcapture (x : M) (hx : x ∈ K) :
      riemannianClosedBallOf ((S i).base.metric b) x (r / 4) ⊆ riemannianClosedBallOf R x r := by
    have hcap := Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower
      R ((S i).base.metric b) (PartialDiffeomorph.refl M) x hr
      (show (0 : ℝ) < 2 by norm_num) (show r / 4 < r / 2 by linarith)
      (hcompactR x hx) (fun _ _ => mem_univ _) (fun y hy v => ?_)
    · change riemannianClosedBallOf ((S i).base.metric b) x (r / 4) ⊆
        id '' riemannianClosedBallOf R x r at hcap
      intro z hz
      obtain ⟨y, hy, hyz⟩ := hcap hz
      change y = z at hyz
      exact hyz ▸ hy
    · have hh := (hmetric y (hball x hx hy) v).1
      change R.inner y v v ≤ 2 ^ 2 * ((S i).base.metric b).inner y
        (mfderiv I I id y v) (mfderiv I I id y v)
      rw [mfderiv_id]
      simp only [ContinuousLinearMap.id_apply]
      have hn := metric_inner_self_nonneg ((S i).base.metric b) y v
      nlinarith
  have hcompact (x : M) (hx : x ∈ K) :
      IsCompact (riemannianClosedBallOf ((S i).base.metric b) x (r / 4)) :=
    (hcompactR x hx).of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist ((S i).base.metric b) x)
        continuous_const) (hcapture x hx)
  intro m t ht x hx
  have hh := shi_curvDerivNorm_on_terminal_ball (S i) (hS i) hab hB
    (show 0 < r / 4 by positivity) hcarrier hregular x (hcompact x hx)
    (fun s hs y hy => (hcurvi s hs y (hball x hx (hcapture x hx hy))).trans hC₀B)
    m t ht x (by rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]; exact bot_le)
  exact hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_curvDerivNorm_on_compact_of_eventual_interval
    {D : ℕ → RealTimeInterval} (S : (i : ℕ) → SolutionOn (I := I) (M := M) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b)
    (hcarrier : ∀ᶠ i in atTop, Icc a b ⊆ (D i).carrier)
    (hregular : ∀ᶠ i in atTop, Ioo a b ⊆ (D i).regular)
    (hterminal : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0
      (fun i => (S i).base.metric b) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ K, curvDerivNormSq 0 ((S i).base.metric t) x ≤ C)
    (K : Set M) (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
      ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b, ∀ x ∈ K,
        curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcarrier.and hregular)
  let U : ℕ → SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le) :=
    fun i => (S (max i N)).timeRestrict (RealTimeInterval.closed a b hab.le)
  have hU (i : ℕ) : IsSolutionOn (U i) :=
    isSolutionOn_timeRestrict (hS (max i N))
      (hN (max i N) (le_max_right i N)).1 (hN (max i N) (le_max_right i N)).2
  have hterminalU : ∀ L : Set M, IsCompact L → MetricCPConvergenceOn L 0
      (fun i => (U i).base.metric b) R R := by
    intro L hL ε hε
    obtain ⟨J, hJ⟩ := hterminal L hL ε hε
    exact ⟨J, fun i hi => hJ (max i N) (hi.trans (le_max_left i N))⟩
  have hcurvU : ∀ L : Set M, IsCompact L → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ L, curvDerivNormSq 0 ((U i).base.metric t) x ≤ C := by
    intro L hL
    obtain ⟨C, hC⟩ := hcurv L hL
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hC
    exact ⟨C, eventually_atTop.mpr ⟨J,
      fun i hi => hJ (max i N) (hi.trans (le_max_left i N))⟩⟩
  obtain ⟨C, hC, hb⟩ := exists_eventually_curvDerivNorm_on_compact_of_terminal_convergence
    U hU R hab (fun _ ht => ht) (fun _ ht => ht) hterminalU hcurvU K hK
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop N] with i hi hNi
  change ∀ m : ℕ, ∀ t ∈ Icc ((a + b) / 2) b, ∀ x ∈ K,
    curvDerivNorm m ((S (max i N)).base.metric t) x ≤ C m at hi
  rw [max_eq_left hNi] at hi
  exact hi

end DifferentialGeometry.PDE.RicciFlow
