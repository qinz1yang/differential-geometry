/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.DifferentialIdentities
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.CoordinateFactorization

open RealInnerProductSpace InnerProductSpace Filter
open scoped Topology

namespace DifferentialGeometry.LiouvilleIntegration

noncomputable section

variable {m : ℕ}

open DifferentialGeometry.LiouvilleRigidity in
theorem differentiableOn_recipPartial (hm : 3 ≤ m) (F : ES m → ES m)
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)}
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) (k : Fin m) :
    DifferentiableOn ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m k)) U := by
  have hE : DifferentiableOn ℝ
      (fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ)) * dc2 hm F k y) U := by
    intro y hy
    have hne : confFactorSq hm F y ≠ 0 := confFactorSq_ne_zero hm F hconf hy
    have h1 : DifferentiableAt ℝ (fun y => (confFactorSq hm F y) ^ (-(3/2 : ℝ))) y :=
      (differentiable_confFactorSq hm F hF y).rpow_const
        (Or.inl hne : confFactorSq hm F y ≠ 0 ∨ 1 ≤ (-(3/2 : ℝ)))
    have h2 : DifferentiableAt ℝ (fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ))) y :=
      h1.const_mul _
    have h3 : DifferentiableAt ℝ (dc2 hm F k) y := differentiable_dc2 hm F hF k y
    exact (h2.mul h3).differentiableWithinAt
  exact hE.congr (fun y hy => dRecip_eq hm F hF hconf hy k)

open DifferentialGeometry.LiouvilleRigidity in
theorem recipPartial_factors (hm : 3 ≤ m) (F : ES m → ES m)
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)}
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) (hU : IsOpen U)
    {c : ES m} (hc : c ∈ U) (k : Fin m) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ U ∧
      ∀ x y : ES m, x ∈ Metric.ball c r → y ∈ Metric.ball c r → x k = y k →
        fderiv ℝ (recipConfFactor hm F) x (stdBasis m k)
          = fderiv ℝ (recipConfFactor hm F) y (stdBasis m k) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  refine ⟨r, hr, hball, fun x y hx hy hxy => ?_⟩
  have hdiff : DifferentiableOn ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m k))
      (Metric.ball c r) :=
    (differentiableOn_recipPartial hm F hF hconf k).mono hball
  have hzero : ∀ z ∈ Metric.ball c r, ∀ j : Fin m, j ≠ k →
      fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m k)) z
        (EuclideanSpace.basisFun (Fin m) ℝ j) = 0 := by
    intro z hz j hjk
    have hzU : z ∈ U := hball hz
    exact recipConfFactor_offdiag hm F hF hconf hU hzU hjk
  exact apply_eq_of_off_partial_eq_zero Metric.isOpen_ball (convex_ball c r)
    hdiff hzero hx hy hxy

end

end DifferentialGeometry.LiouvilleIntegration
