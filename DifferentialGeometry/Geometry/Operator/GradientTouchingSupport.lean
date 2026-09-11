import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradientFun_eq_of_touching_upper_support
    (g : SmoothRiemannianMetric I M) {f phi : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hphi : MDifferentiableAt I 𝓘(ℝ, ℝ) phi x)
    (hcontact : phi x = f x)
    (hupper : ∀ᶠ y in 𝓝 x, f y ≤ phi y) :
    gradientFun g f x = gradientFun g phi x := by
  have hmin : IsLocalMin (fun y => phi y - f y) x := by
    change ∀ᶠ y in 𝓝 x, phi x - f x ≤ phi y - f y
    filter_upwards [hupper] with y hy
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hy
  have hzero := gradientFun_eq_zero_at_spatial_min g hmin (hphi.sub hf)
  rw [gradientFun_sub g hphi hf] at hzero
  exact (sub_eq_zero.mp hzero).symm

end DifferentialGeometry.Geometry.Operator

end
