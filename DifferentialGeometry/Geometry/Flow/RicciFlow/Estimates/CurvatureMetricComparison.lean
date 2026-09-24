import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

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

end DifferentialGeometry.PDE.RicciFlow
