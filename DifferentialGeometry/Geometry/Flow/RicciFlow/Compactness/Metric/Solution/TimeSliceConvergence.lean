import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_eventually_metric_uniform_equivalence_of_time_slice_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    {c : ℝ} (hc : c ∈ Icc a b)
    (K : Set M) (hK : IsCompact K)
    (hconverges : MetricCPConvergenceOn K 0 (fun i => (S i).base.metric c) R R) {C : ℝ}
    (hcurv : ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
      curvDerivNorm 0 ((S i).base.metric t) x ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn K R ((S i).base.metric t) B := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let epsilon : ℝ := 1 / (2 * n + 2)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  obtain ⟨N, hN⟩ := hconverges epsilon hepsilon
  have hinit : ∀ᶠ i in atTop,
      MetricUniformEquivalentOn K R ((S i).base.metric c) 2 := by
    filter_upwards [eventually_ge_atTop N] with i hi
    rw [show (2 : ℝ) = (1 - (1 / 2 : ℝ))⁻¹ by norm_num]
    apply metricUniformEquivalentOn_of_metricDerivNorm ((S i).base.metric c) R
      (by norm_num) (by norm_num)
    intro x hx
    change n * metricDerivNorm 0 ((S i).base.metric c) R R x ≤ 1 / 2
    have hxnorm : metricDerivNorm 0 ((S i).base.metric c) R R x ≤ epsilon :=
      (derivNorm_le_sup hK (le_refl 0) ((S i).base.metric c) R R hx).trans (hN i hi).le
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
    (S i) (hS i) hab hslab hreg hc
    hA (fun t ht x hx v => hquad.2 0 t ht x hx v)
  intro t ht
  have hfactor : metricEquivalenceFactor 1 A t c ≤ B := by
    simp only [metricEquivalenceFactor, one_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith [ht.1, hc.2], by linarith [ht.2, hc.1]⟩)
      (mul_nonneg (by norm_num) hA)
  exact hini.trans (metricUniformEquivalentOn_of_le (htime 0 t ht) hfactor)

end DifferentialGeometry.PDE.RicciFlow
