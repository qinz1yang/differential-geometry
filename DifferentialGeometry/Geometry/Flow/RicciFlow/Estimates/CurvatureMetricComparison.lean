import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem metric_inner_exp_bounds_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C s t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (x : M)
    (hRm : ∀ r ∈ Icc a b,
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (v : TangentSpace I x) :
    Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|)) *
        (S.base.metric t).inner x v v ≤ (S.base.metric s).inner x v v ∧
      (S.base.metric s).inner x v v ≤
        Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) *
          (S.base.metric t).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hpde := metricPDE_Icc S hS hcarrier hregular
  have hd (r : ℝ) (hr : r ∈ Icc a b) :
      ∃ d : ℝ, HasDerivWithinAt (fun u => (S.base.metric u).inner x v v) d (Icc a b) r ∧
        |d| ≤ (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C) *
          (S.base.metric r).inner x v v := by
    refine ⟨_, hpde r hr x v v, ?_⟩
    rw [abs_mul, abs_neg, abs_two]
    have hric := ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hRm r hr)
    nlinarith
  have hst := inner_le_exp_mul_inner_of_abs_deriv_le (fun r => S.base.metric r) x v hd hs ht
  have hts := inner_le_exp_mul_inner_of_abs_deriv_le (fun r => S.base.metric r) x v hd ht hs
  rw [abs_sub_comm t s] at hts
  refine ⟨?_, hst⟩
  calc
    _ ≤ Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|)) *
        (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) *
          (S.base.metric s).inner x v v) :=
      mul_le_mul_of_nonneg_left hts (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

theorem metric_inner_le_reference_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric I M) {θ T A K t : ℝ} (hθT : θ ≤ T)
    (hcarrier : Icc 0 θ ⊆ D.carrier) (hregular : Ioo 0 θ ⊆ D.regular)
    (x : M) (hRm : ∀ r ∈ Icc 0 θ, nablaKRm04NormSqIntrinsic S 0 r x ≤ K)
    (hinit : ∀ v : TangentSpace I x, (S.base.metric 0).inner x v v ≤ A * g.inner x v v)
    (ht : t ∈ Icc 0 θ) (v : TangentSpace I x) :
    (S.base.metric t).inner x v v ≤
      (A * Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * T)) * g.inner x v v := by
  have hsq : ∀ r ∈ Icc 0 θ, normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ K := by
    intro r hr
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm r hr
  have hcmp := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x hsq
    ht ⟨le_rfl, ht.1.trans ht.2⟩ v).2
  rw [sub_zero, abs_of_nonneg ht.1] at hcmp
  have htime : 2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * t ≤
      2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * T :=
    mul_le_mul_of_nonneg_left (ht.2.trans hθT) (by positivity)
  calc
    (S.base.metric t).inner x v v ≤
        Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * t) *
          (S.base.metric 0).inner x v v := hcmp
    _ ≤ Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * T) *
          (S.base.metric 0).inner x v v :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime)
        (metric_inner_self_nonneg (S.base.metric 0) x v)
    _ ≤ Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K * T) *
          (A * g.inner x v v) := mul_le_mul_of_nonneg_left (hinit v) (Real.exp_pos _).le
    _ = _ := by ring

end DifferentialGeometry.PDE.RicciFlow
