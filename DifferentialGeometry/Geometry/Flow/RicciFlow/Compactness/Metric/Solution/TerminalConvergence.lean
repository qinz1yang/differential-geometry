import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.EventualTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Window.EventualBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.TimeLipschitz

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem exists_eventually_metric_bounds_on_compact_of_terminal_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ico a b ⊆ D.regular)
    (hterminal : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric b) R R)
    (hequiv : ∀ K : Set M, IsCompact K → ∃ B : ℝ, 1 ≤ B ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
        MetricUniformEquivalentOn K R ((S i).base.metric t) B)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C)
    (K : Set M) (hK : IsCompact K) (N : ℕ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in atTop,
      (∀ q ≤ N, ∀ t ∈ Icc a b, ∀ x ∈ K,
        metricCovDerivNorm q ((S i).base.metric t) R x ≤ C) ∧
      (∀ q ≤ N, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K,
        metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) R x ≤
          L * |s - t|) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K', hK', hKK', _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let U : TopologicalSpace.Opens M := ⟨interior K', isOpen_interior⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hUK' : (U : Set M) ⊆ K' := interior_subset
  obtain ⟨B, hB, heq⟩ := hequiv K' hK'
  have heqU : ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn U R ((S i).base.metric t) B := by
    filter_upwards [heq] with i hi
    exact fun t ht => ⟨hB, fun x hx => (hi t ht).2 x (hUK' hx)⟩
  have hcU : ∀ q ≤ N, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNorm q ((S i).base.metric t) x ≤ C := by
    intro q _
    obtain ⟨C, hC, hb⟩ := hcurv K' hK' q
    exact ⟨C, hC, hb.mono fun i hi t ht x hx => hi t ht x (hUK' hx)⟩
  have hini : ∀ᶠ i in atTop, ∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q ((S i).base.metric b) R x ≤ (1 : ℝ) := by
    obtain ⟨n, hn⟩ := hterminal K' hK' N 1 zero_lt_one
    filter_upwards [eventually_ge_atTop n] with i hi
    intro q hq hqN x hx
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hb := covNorm_le_add (r + 1) ((S i).base.metric b) R R x
    rw [covNorm_self_succ, zero_add] at hb
    exact hb.trans ((derivNorm_le_sup hK' hqN ((S i).base.metric b) R R
      (hUK' hx)).trans (hn i hi).le)
  have hsol : ∀ᶠ i in atTop, ∃ S' : SolutionOn (I := I) (M := U) D,
      IsSolutionOn S' ∧ ∀ t, S'.family.metric t = ((S i).base.metric t).restrictOpen U :=
    Eventually.of_forall fun i => ⟨solutionOnRestrictOpen (S i) U,
      isSolutionOn_restrictOpen (S i) (hS i) U, fun _ => rfl⟩
  obtain ⟨C, L, hC, hL, hb⟩ :=
    exists_eventually_metric_bounds_from_terminal_values_of_local_solutions
      (fun i t => (S i).base.metric t) R U D hab hslab hreg hsol hB heqU N hcU
      (fun _ => 1) (fun _ => zero_le_one) hini
  exact ⟨C, L, hC, hL, hb.mono fun i hi =>
    ⟨fun q hq t ht x hx => hi.1 q hq t ht x (hKK' hx),
      fun q hq s hs t ht x hx => hi.2 q hq s hs t ht x (hKK' hx)⟩⟩

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_eventually_metric_uniform_equivalence_of_terminal_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    (hterminal : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric b) R R)
    (K : Set M) (hK : IsCompact K) {C : ℝ}
    (hcurv : ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
      curvDerivNorm 0 ((S i).base.metric t) x ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn K R ((S i).base.metric t) B := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let epsilon : ℝ := 1 / (2 * n + 2)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  obtain ⟨N, hN⟩ := hterminal K hK 0 epsilon hepsilon
  have hinit : ∀ᶠ i in atTop,
      MetricUniformEquivalentOn K R ((S i).base.metric b) 2 := by
    filter_upwards [eventually_ge_atTop N] with i hi
    rw [show (2 : ℝ) = (1 - (1 / 2 : ℝ))⁻¹ by norm_num]
    apply metricUniformEquivalentOn_of_metricDerivNorm ((S i).base.metric b) R
      (by norm_num) (by norm_num)
    intro x hx
    change n * metricDerivNorm 0 ((S i).base.metric b) R R x ≤ 1 / 2
    have hxnorm : metricDerivNorm 0 ((S i).base.metric b) R R x ≤ epsilon :=
      (derivNorm_le_sup hK (le_refl 0) ((S i).base.metric b) R R hx).trans (hN i hi).le
    calc
      _ ≤ n * epsilon := mul_le_mul_of_nonneg_left hxnorm hn
      _ ≤ 1 / 2 := by
        dsimp only [epsilon]
        rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 2 * n + 2)]
        linarith
  let A : ℝ := n ^ 2 * Real.sqrt (C ^ 2)
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  let B : ℝ := Real.exp (2 * A * (b - a))
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  refine ⟨2 * B, by linarith, ?_⟩
  filter_upwards [hcurv, hinit] with i hi hini
  have hquad := twoTensorQuadBound_of_solutions (fun _ => S i) K a b (C ^ 2)
    (fun _ t ht x hx => by
      have hsq := (Real.sqrt_le_iff.mp (hi t ht x hx)).2
      change curvDerivNormSq 0 ((S i).base.metric t) x ≤ C ^ 2
      exact hsq)
  have htime := metric_uniform_equivalent_on_closed_interval_of_solution
    (S i) (hS i) hab hslab hreg (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
    hA (fun t ht x hx v => hquad.2 0 t ht x hx v)
  intro t ht
  have hfactor : metricEquivalenceFactor 1 A t b ≤ B := by
    simp only [metricEquivalenceFactor, one_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (mul_nonneg (by norm_num) hA)
  exact hini.trans (metricUniformEquivalentOn_of_le (htime 0 t ht) hfactor)

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem exists_metric_subsequence_on_closed_interval_of_terminal_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ico a b ⊆ D.regular)
    (hterminal : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric b) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      g b = R ∧ ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) R < epsilon := by
  have hequiv : ∀ K : Set M, IsCompact K → ∃ B : ℝ, 1 ≤ B ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
        MetricUniformEquivalentOn K R ((S i).base.metric t) B := by
    intro K hK
    obtain ⟨C, _hC, hb⟩ := hcurv K hK 0
    exact exists_eventually_metric_uniform_equivalence_of_terminal_convergence S hS R hab
      hslab (Ioo_subset_Ico_self.trans hreg) hterminal K hK hb
  have hbounds := exists_eventually_metric_bounds_on_compact_of_terminal_convergence
    S hS R hab hslab hreg hterminal hequiv hcurv
  obtain ⟨rho, hrho, g, hg⟩ :=
    exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
      hab.le R (fun i t => (S i).base.metric t)
      (by
        intro i K hK p
        obtain ⟨L, hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S i) (hS i) hab hslab hreg R hK p
        exact ⟨L, hL, fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)
      (by
        intro K hK p
        obtain ⟨C, L, _hC, hL, hb⟩ := hbounds K hK p
        exact ⟨L, hL, hb.mono fun i hi s hs t ht q hq x hx => hi.2 q hq s hs t ht x hx⟩)
      (by
        intro t ht q K hK
        obtain ⟨C, L, _hC, _hL, hb⟩ := hbounds K hK q
        exact ⟨C, hb.mono fun i hi x hx => hi.1 q le_rfl t ht x hx⟩)
      (by
        intro t ht x
        obtain ⟨B, hB, hb⟩ := hequiv {x} isCompact_singleton
        exact ⟨B⁻¹, inv_pos.mpr (zero_lt_one.trans_le hB),
          hb.mono fun i hi v => ((hi t ht).2 x (mem_singleton x) v).1⟩)
  refine ⟨rho, hrho, g, ?_, hg⟩
  apply metricCInf_unique (fun i => (S (rho i)).base.metric b) (g b) R R R
  · intro K hK p epsilon hepsilon
    obtain ⟨N, hN⟩ := hg K hK p epsilon hepsilon
    exact ⟨N, fun i hi => hN i hi b ⟨hab.le, le_rfl⟩⟩
  · intro K hK p epsilon hepsilon
    obtain ⟨N, hN⟩ := hterminal K hK p epsilon hepsilon
    exact ⟨N, fun i hi => hN (rho i) (hi.trans (hrho.id_le i))⟩

end DifferentialGeometry.PDE.RicciFlow

end
