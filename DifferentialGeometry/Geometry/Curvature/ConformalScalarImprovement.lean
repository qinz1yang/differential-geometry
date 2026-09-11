import DifferentialGeometry.Geometry.Curvature.ConformalScalar
import DifferentialGeometry.Geometry.Operator.ParallelPotential
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]

theorem scalar_conformal_improvement_of_parallel_unit_gradient
    (g h : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hdim : Module.finrank ℝ E = 3)
    (x : M) (ε : ℝ) (hε : ε ≤ 1 / 1000)
    (hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε)
    (hunit : g.inner x (gradFun g u x) (gradFun g u x) = 1)
    (hparallel : ∀ v w : TangentSpace I x, hessFun g u x v w = 0)
    (hR : 0 ≤ metricScalarAt h x) (hf0 : f (u x) ≤ 0)
    (hf1 : |deriv f (u x)| ≤ -deriv (deriv f) (u x))
    (hf2 : (deriv f (u x)) ^ 2 ≤ -deriv (deriv f) (u x) / 100) :
    metricScalarAt h x + 2 * (-deriv (deriv f) (u x)) ≤
      metricScalarAt (conformalMetricOfContDiff h (fun y => f (u y)) (hf.contMDiff.comp hu)) x := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hhalf : ε ≤ 1 / 2 := hε.trans (by norm_num)
  let D := -deriv (deriv f) (u x)
  have hD : 0 ≤ D := (abs_nonneg _).trans hf1
  have hdabs : |deriv (deriv f) (u x)| = D :=
    abs_of_nonpos (neg_nonneg.mp hD)
  have hL := abs_laplacian_comp_sub_le_of_parallel_unit_gradient
    g h u hu f hf x ε hhalf hsmall hunit hparallel
  rw [hdim, hdabs] at hL
  norm_num only [Nat.cast_ofNat] at hL
  have hLp := (abs_le.mp hL).2
  have hpε := mul_le_mul_of_nonneg_left hf1 hε0
  have hΔ : laplacian (LeviCivita h) h (fun y => f (u y)) x ≤ -D + 74 * ε * D := by
    dsimp only [D] at hLp hpε ⊢
    nlinarith only [hLp, hpε]
  have henergy := inner_gradFun_le_two_of_metricDerivNorm_le_half
    g h u x ((hsmall 0 (by norm_num)).trans hhalf)
  rw [hunit, mul_one] at henergy
  have hgrad := gradientFun_comp h ((hf.differentiable (by simp)) (u x))
    ((hu.mdifferentiable (by simp)) x)
  simp only [gradient_eq_gradFun] at hgrad
  have hG : h.inner x (gradFun h (fun y => f (u y)) x)
      (gradFun h (fun y => f (u y)) x) ≤ 2 * (deriv f (u x)) ^ 2 := by
    rw [hgrad, metric_inner_smul_self]
    exact (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)).trans_eq (mul_comm _ _)
  have heD := mul_le_mul_of_nonneg_right hε hD
  have hgain : metricScalarAt h x + 2 * D ≤
      metricScalarAt h x - 4 * laplacian (LeviCivita h) h (fun y => f (u y)) x -
        2 * h.inner x (gradFun h (fun y => f (u y)) x)
          (gradFun h (fun y => f (u y)) x) := by
    change (deriv f (u x)) ^ 2 ≤ D / 100 at hf2
    nlinarith only [hΔ, hG, heD, hf2, hD]
  have hs := metricScalarAt_conformalMetric_three h (fun y => f (u y))
    (hf.contMDiff.comp hu) hdim x
  have hfu : ContMDiff I 𝓘(ℝ) ∞ (fun y => f (u y)) := hf.contMDiff.comp hu
  rw [← laplacian_levi_eq h hfu x] at hs
  rw [hs]
  have ht : 1 ≤ Real.exp (-(2 * f (u x))) := Real.one_le_exp_iff.mpr (by linarith)
  have hnonneg : 0 ≤ metricScalarAt h x -
      4 * laplacian (LeviCivita h) h (fun y => f (u y)) x -
        2 * h.inner x (gradFun h (fun y => f (u y)) x)
          (gradFun h (fun y => f (u y)) x) := by linarith
  exact hgain.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hnonneg)

end DifferentialGeometry.Geometry.Curvature
