import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryHessianCorrection

/-!
The actual smooth correction u-Cu² preserves a defining function's sign near its
zero and turns tangent-negative covariant Hessian into a negative-definite Hessian.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

theorem boundary_defining_hessian (g : SmoothRiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (p : M) (hp : u p = 0) (C : ℝ)
    (v w : TangentSpace I p) :
    abstractHessian g (fun y => u y - C * (u y) ^ 2) p v w =
      abstractHessian g u p v w - 2 * C * mvfderiv I u p v * mvfderiv I u p w := by
  let F : M → ℝ := fun y => u y - C * (u y * u y)
  let a : M → ℝ := fun y => 1 - 2 * C * u y
  let D := cotangentCov (LeviCivita g)
  have hdu (y : M) : MDifferentiableAt I 𝓘(ℝ) u y :=
    hu.mdifferentiable (by simp) y
  have hDF : mvfderiv I F = a • mvfderiv I u := by
    funext y
    change mvfderiv I (u - (fun y : M => C) * (u * u)) y = _
    rw [mvfderiv_sub (hdu y) (mdifferentiableAt_const.mul ((hdu y).mul (hdu y))),
      mvfderiv_mul mdifferentiableAt_const ((hdu y).mul (hdu y)),
      mvfderiv_mul (hdu y) (hdu y), mvfderiv_const]
    ext z
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, zero_apply, Pi.smul_apply', a]
    ring
  have ha : ContMDiff I 𝓘(ℝ) ∞ a :=
    contMDiff_const.sub (contMDiff_const.mul hu)
  have hcot : MDiffAtCotangent (mvfderiv I u) p :=
    (cotangentCov_mvfderiv_smooth hu p).mdifferentiableAt (by simp)
  have hD := D.isCovariantDerivativeOnUniv.leibniz hcot
    (ha.mdifferentiable (by simp) p)
  have hDa : mvfderiv I a p = (-2 * C) • mvfderiv I u p := by
    change mvfderiv I ((fun y : M => 1) - (fun y : M => 2 * C) * u) p = _
    rw [mvfderiv_sub mdifferentiableAt_const (mdifferentiableAt_const.mul (hdu p)),
      mvfderiv_const, mvfderiv_mul mdifferentiableAt_const (hdu p), mvfderiv_const]
    ext z
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, zero_apply]
    ring
  change D (mvfderiv I (fun y => u y - C * (u y) ^ 2)) p v w = _
  simp only [pow_two]
  change D (mvfderiv I F) p v w = _
  rw [hDF, hD, hDa]
  simp only [a, hp, mul_zero, sub_zero, one_smul, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change abstractHessian g u p v w + (-2 * C * mvfderiv I u p v) * mvfderiv I u p w = _
  ring

theorem exists_boundary_defining_hessian_correction (g : SmoothRiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u) (p : M) (hp : u p = 0)
    (hneg : ∀ v : TangentSpace I p, mvfderiv I u p v = 0 → v ≠ 0 →
      abstractHessian g u p v v < 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ v : TangentSpace I p, v ≠ 0 →
        abstractHessian g (fun y => u y - C * (u y) ^ 2) p v v < 0) ∧
      ∀ᶠ y in 𝓝 p, (0 ≤ u y - C * (u y) ^ 2 ↔ 0 ≤ u y) := by
  obtain ⟨C, hc, hC⟩ :=
    exists_boundary_hessian_correction (abstractHessian g u p) (mvfderiv I u p) hneg
  refine ⟨C, hc, ?_, ?_⟩
  · intro v hv
    rw [boundary_defining_hessian g u hu p hp C v v]
    nlinarith [hC v hv]
  · have hsmall : ∀ᶠ y in 𝓝 p, C * u y < 1 := by
      apply (continuous_const.mul hu.continuous).continuousAt.eventually
        (isOpen_Iio.mem_nhds ?_)
      change C * u p < 1
      rw [hp, mul_zero]
      exact zero_lt_one
    filter_upwards [hsmall] with y hy
    have hfactor : u y - C * (u y) ^ 2 = u y * (1 - C * u y) := by ring
    rw [hfactor, mul_nonneg_iff_of_pos_right (by linarith : 0 < 1 - C * u y)]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
