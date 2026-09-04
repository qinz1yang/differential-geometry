import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem fderiv_eq_of_deriv_eq {f : ℝ → X} {s t : Set ℝ} {x : ℝ}
    (h : derivWithin f s x = derivWithin f t x) :
    fderivWithin ℝ f s x = fderivWithin ℝ f t x := by
  apply DFunLike.ext _ _
  intro r
  rw [show r = r • (1 : ℝ) by simp, map_smul, map_smul,
    fderivWithin_derivWithin, fderivWithin_derivWithin, h]

theorem contDiffOn_Icc_join {f : ℝ → X} {a c b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hl : ContDiffOn ℝ 1 f (Icc a c))
    (hr : ContDiffOn ℝ 1 f (Icc c b))
    (hder : derivWithin f (Icc a c) c = derivWithin f (Icc c b) c) :
    ContDiffOn ℝ 1 f (Icc a b) := by
  let L : Set ℝ := Icc a c
  let R : Set ℝ := Icc c b
  let J : Set ℝ := Icc a b
  let d : ℝ → ℝ →L[ℝ] X := fun x ↦
    Set.piecewise (Iic c) (fderivWithin ℝ f L) (fderivWithin ℝ f R) x
  have hLu : UniqueDiffOn ℝ L := by
    simpa only [L] using uniqueDiffOn_Icc hac
  have hRu : UniqueDiffOn ℝ R := by
    simpa only [R] using uniqueDiffOn_Icc hcb
  have hJu : UniqueDiffOn ℝ J := by
    simpa only [J] using uniqueDiffOn_Icc (hac.trans hcb)
  have hder' : fderivWithin ℝ f L c = fderivWithin ℝ f R c := by
    apply fderiv_eq_of_deriv_eq
    simpa only [L, R] using hder
  have hdl : ContinuousOn (fderivWithin ℝ f L) L := by
    exact (hl.continuousOn_fderivWithin hLu (by norm_num))
  have hdr : ContinuousOn (fderivWithin ℝ f R) R := by
    exact (hr.continuousOn_fderivWithin hRu (by norm_num))
  have hd : ContinuousOn d J := by
    apply ContinuousOn.piecewise (t := Iic c)
    · rintro x ⟨_, hx⟩
      have hxc : x = c := by simpa using hx
      subst x
      exact hder'
    · apply hdl.mono
      rintro x ⟨hxJ, hxc⟩
      have hxc' : x ≤ c := by simpa using hxc
      exact ⟨hxJ.1, hxc'⟩
    · apply hdr.mono
      rintro x ⟨hxJ, hcx⟩
      have hcx' : c ≤ x := by simpa using hcx
      exact ⟨hcx', hxJ.2⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hJu]
  refine ⟨by simp, d, contDiffOn_zero.mpr hd, ?_⟩
  intro x hx
  rcases lt_trichotomy x c with hxc | rfl | hcx
  · have hxL : x ∈ L := ⟨hx.1, hxc.le⟩
    have hleft : HasFDerivWithinAt f (fderivWithin ℝ f L x) L x :=
      (hl.differentiableOn (by norm_num) x hxL).hasFDerivWithinAt
    have hright : HasFDerivWithinAt f (fderivWithin ℝ f L x) R x := by
      apply HasFDerivWithinAt.of_notMem_closure
      rw [isClosed_Icc.closure_eq]
      exact fun hxR ↦ (not_le_of_gt hxc) hxR.1
    have hu := hleft.union hright
    rw [show L ∪ R = J by
      simpa only [L, R, J] using Icc_union_Icc_eq_Icc hac.le hcb.le] at hu
    rw [show d x = fderivWithin ℝ f L x by
      simp only [d, Set.piecewise, if_pos (show x ∈ Iic c from hxc.le)]]
    exact hu
  · have hcL : x ∈ L := ⟨hac.le, le_rfl⟩
    have hcR : x ∈ R := ⟨le_rfl, hcb.le⟩
    have hleft : HasFDerivWithinAt f (fderivWithin ℝ f L x) L x :=
      (hl.differentiableOn (by norm_num) x hcL).hasFDerivWithinAt
    have hright : HasFDerivWithinAt f (fderivWithin ℝ f L x) R x := by
      rw [hder']
      exact (hr.differentiableOn (by norm_num) x hcR).hasFDerivWithinAt
    have hu := hleft.union hright
    rw [show L ∪ R = J by
      simpa only [L, R, J] using Icc_union_Icc_eq_Icc hac.le hcb.le] at hu
    rw [show d x = fderivWithin ℝ f L x by
      simp only [d, Set.piecewise, if_pos (mem_Iic.mpr le_rfl)]]
    exact hu
  · have hxR : x ∈ R := ⟨hcx.le, hx.2⟩
    have hright : HasFDerivWithinAt f (fderivWithin ℝ f R x) R x :=
      (hr.differentiableOn (by norm_num) x hxR).hasFDerivWithinAt
    have hleft : HasFDerivWithinAt f (fderivWithin ℝ f R x) L x := by
      apply HasFDerivWithinAt.of_notMem_closure
      rw [isClosed_Icc.closure_eq]
      exact fun hxL ↦ (not_le_of_gt hcx) hxL.2
    have hu := hleft.union hright
    rw [show L ∪ R = J by
      simpa only [L, R, J] using Icc_union_Icc_eq_Icc hac.le hcb.le] at hu
    rw [show d x = fderivWithin ℝ f R x by
      simp only [d, Set.piecewise, if_neg
        (show x ∉ Iic c from not_le.mpr hcx)]]
    exact hu

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

end
