import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem laplacian_eq_zero_of_isometry_antisymmetry
    (g : SmoothRiemannianMetric I M) (Phi : M ≃ₘ⟮I, I⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross g Phi = g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {c : ℝ} (hanti : f ∘ Phi = fun y => c - f y)
    {x : M} (hfix : Phi x = x) : laplacian (LeviCivita g) g f x = 0 := by
  have h := laplacian_pullbackCross g Phi (hf (Phi x))
  rw [hmetric, hanti, hfix] at h
  rw [laplacian_sub _ _ (fun _ => mdifferentiableAt_const)
    (fun y => (hf y).mdifferentiableAt (by norm_num))
    (gradientFun_mdiffAt g contMDiff_const x)
    ((gradientFun_contMDiffAt_one g (hf x)).mdifferentiableAt (by norm_num)),
    laplacian_const] at h
  linarith only [h]

end DifferentialGeometry.Geometry.Operator
