import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem det_pos_iff_of_coordinate_linear_square
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F ≃L[ℝ] E) (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (hc : IsPreconnected c.source) {a b : E} (ha : a ∈ c.source) (hb : b ∈ c.source)
    (A : F →L[ℝ] F) (B : E →L[ℝ] E)
    (hsquare : A.comp (fderiv ℝ c a) = (fderiv ℝ c b).comp B) :
    0 < A.toLinearMap.det ↔ 0 < B.toLinearMap.det := by
  let C := c.trans L.toDiffeomorph.toPartialDiffeomorph
  have hCs : C.source = c.source := by
    ext x
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_univ _⟩⟩
  have hCder (x : E) (hx : x ∈ c.source) :
      fderiv ℝ C x = (L : F →L[ℝ] E).comp (fderiv ℝ c x) :=
    (L.hasFDerivAt.comp x (((c.contMDiffOn.contDiffOn.contDiffAt
      (c.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt)).fderiv
  let M := (L : F →L[ℝ] E).comp (A.comp (L.symm : E →L[ℝ] F))
  have hM : M.toLinearMap.det = A.toLinearMap.det :=
    LinearMap.det_conj A.toLinearMap L.toLinearEquiv
  have hcomp : M.comp (fderiv ℝ C a) = (fderiv ℝ C b).comp B := by
    rw [hCder a ha, hCder b hb]
    ext x
    change L (A (L.symm (L (fderiv ℝ c a x)))) = L (fderiv ℝ c b (B x))
    rw [L.symm_apply_apply]
    exact congrArg L (congrArg (fun K : E →L[ℝ] F ↦ K x) hsquare)
  have hprod : M.toLinearMap.det * (fderiv ℝ C a).toLinearMap.det =
      (fderiv ℝ C b).toLinearMap.det * B.toLinearMap.det := by
    rw [← LinearMap.det_comp, ← LinearMap.det_comp]
    exact congrArg (fun K : E →L[ℝ] E ↦ K.toLinearMap.det) hcomp
  have hsign := det_fderiv_pos_iff_of_preconnected C (hCs ▸ hc) (hCs ▸ ha) (hCs ▸ hb)
  have hnza := det_fderiv_ne_zero_of_partialDiffeomorph C (hCs ▸ ha)
  have hnzb := det_fderiv_ne_zero_of_partialDiffeomorph C (hCs ▸ hb)
  have hpos : 0 < (fderiv ℝ C a).toLinearMap.det * (fderiv ℝ C b).toLinearMap.det := by
    rcases lt_or_gt_of_ne hnza with hn | hp
    · exact mul_pos_of_neg_of_neg hn
        (lt_of_le_of_ne (le_of_not_gt (fun h ↦ (not_lt_of_gt hn) (hsign.mpr h))) hnzb)
    · exact mul_pos hp (hsign.mp hp)
  have hsq : 0 < (fderiv ℝ C a).toLinearMap.det * (fderiv ℝ C a).toLinearMap.det :=
    mul_self_pos.mpr hnza
  have heq : M.toLinearMap.det * ((fderiv ℝ C a).toLinearMap.det * (fderiv ℝ C a).toLinearMap.det) =
      B.toLinearMap.det * ((fderiv ℝ C a).toLinearMap.det * (fderiv ℝ C b).toLinearMap.det) := by
    nlinarith [congrArg (fun r : ℝ ↦ r * (fderiv ℝ C a).toLinearMap.det) hprod]
  have hi := congrArg (fun r : ℝ ↦ 0 < r) heq
  rw [mul_pos_iff_of_pos_right hsq, mul_pos_iff_of_pos_right hpos, hM] at hi
  exact Iff.of_eq hi

end Poincare.Analysis
