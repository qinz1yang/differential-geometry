import DifferentialGeometry.Tensor.LinearAlgebra.PositivePlanarLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem det_fderiv_pos_of_planar_isotopy
    (D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hD : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2))
    (hzero : D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞) (p : ℝ) (z : ℂ) :
    0 < (fderiv ℝ (D p) z).toLinearMap.det := by
  let h : ℝ × ℂ → ℂ := fun q ↦ D q.1 q.2
  let d : ℝ → ℝ := fun t ↦ (fderiv ℝ (D t) z).toLinearMap.det
  have hcol (t : ℝ) (w : ℂ) : fderiv ℝ (D t) z w = fderiv ℝ h (t, z) (0, w) := by
    have hd := ((hD.differentiable (by simp) (t, z)).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))).fderiv
    exact congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L w) hd
  have hcf (w : ℂ) : Continuous (fun t : ℝ ↦ fderiv ℝ h (t, z) (0, w)) :=
    ((hD.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).clm_apply
      continuous_const
  have hdc : Continuous d := by
    have hd (t : ℝ) : d t =
        (fderiv ℝ h (t, z) (0, 1)).re * (fderiv ℝ h (t, z) (0, Complex.I)).im -
        (fderiv ℝ h (t, z) (0, Complex.I)).re * (fderiv ℝ h (t, z) (0, 1)).im := by
      dsimp only [d]
      rw [det_complex_real_linearMap]
      change (fderiv ℝ (D t) z 1).re * (fderiv ℝ (D t) z Complex.I).im -
        (fderiv ℝ (D t) z Complex.I).re * (fderiv ℝ (D t) z 1).im = _
      rw [hcol, hcol]
    simp_rw [show d = _ from funext hd]
    exact ((Complex.continuous_re.comp (hcf 1)).mul (Complex.continuous_im.comp (hcf Complex.I))).sub
      ((Complex.continuous_re.comp (hcf Complex.I)).mul (Complex.continuous_im.comp (hcf 1)))
  have hdnz (t : ℝ) : d t ≠ 0 := by
    let A := fderiv ℝ (D t) z
    let B := fderiv ℝ (D t).symm (D t z)
    have hA : HasFDerivAt (D t) A z :=
      ((D t).contMDiff.contDiff.differentiable (by simp) z).hasFDerivAt
    have hB : HasFDerivAt (D t).symm B (D t z) :=
      ((D t).symm.contMDiff.contDiff.differentiable (by simp) (D t z)).hasFDerivAt
    have hBA : B.comp A = ContinuousLinearMap.id ℝ ℂ := by
      have hc := hB.comp z hA
      have he : (D t).symm ∘ D t = id := funext (D t).symm_apply_apply
      rw [he] at hc
      exact hc.unique (hasFDerivAt_id z)
    have hprod : B.toLinearMap.det * A.toLinearMap.det = 1 := by
      rw [← LinearMap.det_comp]
      change (B.comp A).toLinearMap.det = 1
      rw [hBA]
      simp
    intro hdt
    change A.toLinearMap.det = 0 at hdt
    rw [hdt, mul_zero] at hprod
    exact zero_ne_one hprod
  have hd0 : d 0 = 1 := by
    change (fderiv ℝ (D 0) z).toLinearMap.det = 1
    rw [hzero]
    change (fderiv ℝ (id : ℂ → ℂ) z).toLinearMap.det = 1
    simp
  change 0 < d p
  by_contra hp
  obtain ⟨t, ht⟩ := intermediate_value_univ p 0 hdc
    (show (0 : ℝ) ∈ Icc (d p) (d 0) from ⟨le_of_not_gt hp, by rw [hd0]; norm_num⟩)
  exact hdnz t ht

end DifferentialGeometry.Analysis
