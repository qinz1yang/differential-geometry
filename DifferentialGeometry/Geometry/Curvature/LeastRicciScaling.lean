import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Mathlib.LinearAlgebra.Eigenspace.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem least_ricci_eigenpair_of_scaleMetric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    (μ : ℝ) (w : TangentSpace I x)
    (hunit : (scaleMetric c hc g).inner x w w = 1)
    (heigen : ricciSharp (scaleMetric c hc g) x w = μ • w)
    (hmin : ∀ z, (scaleMetric c hc g).inner x z z = 1 →
      μ ≤ ricciTensor (scaleMetric c hc g) x z z)
    (hsimple : Module.End.eigenspace (ricciSharp (scaleMetric c hc g) x).toLinearMap μ =
      Submodule.span ℝ {w}) :
    let u := Real.sqrt c • w
    g.inner x u u = 1 ∧ ricciSharp g x u = (c * μ) • u ∧
      (∀ z, g.inner x z z = 1 → c * μ ≤ ricciTensor g x z z) ∧
      Module.End.eigenspace (ricciSharp g x).toLinearMap (c * μ) = Submodule.span ℝ {u} := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hinv : c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) = 1 := by
    rw [← mul_inv, hsq, mul_inv_cancel₀ hc.ne']
  have he (z : TangentSpace I x) :
      ricciSharp (scaleMetric c hc g) x z = μ • z ↔ ricciSharp g x z = (c * μ) • z := by
    rw [ricciSharp_scaleMetric]
    constructor
    · intro h
      change c⁻¹ • ricciSharp g x z = μ • z at h
      calc
        ricciSharp g x z = c • (c⁻¹ • ricciSharp g x z) := by
          rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
        _ = c • (μ • z) := congrArg (fun v : TangentSpace I x ↦ c • v) h
        _ = (c * μ) • z := by rw [smul_smul]
    · intro h
      change c⁻¹ • ricciSharp g x z = μ • z
      rw [h, smul_smul, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have heu : ricciSharp g x (Real.sqrt c • w) = (c * μ) • (Real.sqrt c • w) := by
    rw [map_smul, (he w).mp heigen, smul_comm]
  refine ⟨?_, heu, ?_, ?_⟩
  · rw [scaleMetric_inner] at hunit
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, hsq]
    exact hunit
  · intro z hz
    have hn : (scaleMetric c hc g).inner x ((Real.sqrt c)⁻¹ • z) ((Real.sqrt c)⁻¹ • z) = 1 := by
      rw [scaleMetric_inner]
      simp only [map_smul, smul_apply, smul_eq_mul, hz, mul_one]
      exact hinv
    have hm := mul_le_mul_of_nonneg_left (hmin _ hn) hc.le
    rw [ricciTensor_scaleMetric] at hm
    simp only [map_smul, smul_apply, smul_eq_mul] at hm
    have hcoeff : c * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * ricciTensor g x z z)) =
        ricciTensor g x z z := by
      calc
        _ = (c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) * ricciTensor g x z z := by ring
        _ = _ := by rw [hinv, one_mul]
    exact hm.trans_eq hcoeff
  · rw [Submodule.span_singleton_smul_eq hs.ne'.isUnit, ← hsimple]
    ext z
    rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
    exact (he z).symm

end DifferentialGeometry.Geometry.Curvature
