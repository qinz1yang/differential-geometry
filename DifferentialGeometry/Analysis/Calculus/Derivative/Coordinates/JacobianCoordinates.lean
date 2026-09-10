import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem det_fderiv_pos_iff_of_coordinate_conjugacy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hc : IsPreconnected c.source) (f g : E → E) {a : E}
    (ha : a ∈ c.source) (hga : g a ∈ c.source)
    (hf : DifferentiableAt ℝ f (c a)) (hg : DifferentiableAt ℝ g a)
    (heq : f ∘ c =ᶠ[𝓝 a] c ∘ g) :
    0 < (fderiv ℝ f (c a)).toLinearMap.det ↔ 0 < (fderiv ℝ g a).toLinearMap.det := by
  have hca := ((c.contMDiffOn.contDiffOn.contDiffAt
    (c.open_source.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
  have hcga := ((c.contMDiffOn.contDiffOn.contDiffAt
    (c.open_source.mem_nhds hga)).differentiableAt (by simp)).hasFDerivAt
  have hder := ((hf.hasFDerivAt.comp a hca).congr_of_eventuallyEq heq.symm).unique
    (hcga.comp a hg.hasFDerivAt)
  have hprod : (fderiv ℝ f (c a)).toLinearMap.det * (fderiv ℝ c a).toLinearMap.det =
      (fderiv ℝ c (g a)).toLinearMap.det * (fderiv ℝ g a).toLinearMap.det := by
    rw [← LinearMap.det_comp, ← LinearMap.det_comp]
    exact congrArg (fun L : E →L[ℝ] E ↦ L.toLinearMap.det) hder
  have hsign := det_fderiv_pos_iff_of_preconnected c hc ha hga
  have hnza := det_fderiv_ne_zero_of_partialDiffeomorph c ha
  have hnzb := det_fderiv_ne_zero_of_partialDiffeomorph c hga
  rcases lt_or_gt_of_ne hnza with hneg | hpos
  · have hnegb : (fderiv ℝ c (g a)).toLinearMap.det < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun hb ↦ (not_lt_of_gt hneg) (hsign.mpr hb))) hnzb
    constructor
    · intro h
      by_contra hh
      have hleft := mul_neg_of_pos_of_neg h hneg
      have hright := mul_nonneg_of_nonpos_of_nonpos hnegb.le (le_of_not_gt hh)
      linarith
    · intro h
      by_contra hh
      have hleft := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hh) hneg.le
      have hright := mul_neg_of_neg_of_pos hnegb h
      linarith
  · have hposb := hsign.mp hpos
    constructor
    · intro h
      by_contra hh
      have hleft := mul_pos h hpos
      have hright := mul_nonpos_of_nonneg_of_nonpos hposb.le (le_of_not_gt hh)
      linarith
    · intro h
      by_contra hh
      have hleft := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hpos.le
      have hright := mul_pos hposb h
      linarith

theorem det_fderiv_pos_iff_of_equivalent_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F ≃L[ℝ] E) (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (hc : IsPreconnected c.source) (f : F → F) (g : E → E) {a : E}
    (ha : a ∈ c.source) (hga : g a ∈ c.source)
    (hf : DifferentiableAt ℝ f (c a)) (hg : DifferentiableAt ℝ g a)
    (heq : f ∘ c =ᶠ[𝓝 a] c ∘ g) :
    0 < (fderiv ℝ f (c a)).toLinearMap.det ↔ 0 < (fderiv ℝ g a).toLinearMap.det := by
  let C := c.trans L.toDiffeomorph.toPartialDiffeomorph
  have hCs : C.source = c.source := by
    ext x
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_univ _⟩⟩
  let H : E → E := fun x ↦ L (f (L.symm x))
  have hLin : L.symm (C a) = c a := L.symm_apply_apply _
  have hf' : HasFDerivAt f (fderiv ℝ f (c a)) (L.symm (C a)) := by
    rw [hLin]
    exact hf.hasFDerivAt
  have hH : HasFDerivAt H ((L : F →L[ℝ] E).comp
      ((fderiv ℝ f (c a)).comp (L.symm : E →L[ℝ] F))) (C a) :=
    L.hasFDerivAt.comp (C a) (hf'.comp (C a) L.symm.hasFDerivAt)
  have hcomm : H ∘ C =ᶠ[𝓝 a] C ∘ g := by
    filter_upwards [heq] with x hx
    change L (f (L.symm (L (c x)))) = L (c (g x))
    rw [L.symm_apply_apply]
    exact congrArg L hx
  have hi := det_fderiv_pos_iff_of_coordinate_conjugacy C (hCs ▸ hc) H g
    (hCs ▸ ha) (hCs ▸ hga) hH.differentiableAt hg hcomm
  rw [hH.fderiv] at hi
  change 0 < ((L.toLinearEquiv : F →ₗ[ℝ] E).comp
    ((fderiv ℝ f (c a)).toLinearMap.comp (L.symm.toLinearEquiv : E →ₗ[ℝ] F))).det ↔ _ at hi
  have hdet := LinearMap.det_conj (fderiv ℝ f (c a)).toLinearMap L.toLinearEquiv
  change ((L.toLinearEquiv : F →ₗ[ℝ] E).comp
    ((fderiv ℝ f (c a)).toLinearMap.comp (L.symm.toLinearEquiv : E →ₗ[ℝ] F))).det = _ at hdet
  rw [hdet] at hi
  exact hi

end Poincare.Analysis
