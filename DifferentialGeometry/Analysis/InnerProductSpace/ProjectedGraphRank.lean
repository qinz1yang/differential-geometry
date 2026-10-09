import DifferentialGeometry.Analysis.InnerProductSpace.AdjointRankMargin

set_option autoImplicit false
open scoped InnerProductSpace
namespace ContinuousLinearMap

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ H]

theorem norm_le_adjoint_of_surjective_norm_le (T : F →L[ℝ] H)
    (hs : Function.Surjective T) (hl : ∀ x, ‖x‖ ≤ ‖T x‖) :
    ∀ y, ‖y‖ ≤ ‖T.adjoint y‖ := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have hinner : ‖T x‖ ^ 2 = ⟪x, T.adjoint (T x)⟫_ℝ := by
    rw [T.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have h := real_inner_le_norm x (T.adjoint (T x))
  rw [← hinner] at h
  have hh := mul_le_mul_of_nonneg_right (hl x) (norm_nonneg (T.adjoint (T x)))
  by_cases hz : ‖T x‖ = 0
  · rw [hz]
    exact norm_nonneg _
  have hp : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  nlinarith

omit [FiniteDimensional ℝ H] in
theorem projected_range_surjective_of_approximation (T : F →L[ℝ] H)
    (L : E →L[ℝ] F) (D : E →L[ℝ] H) {a e b l : ℝ}
    (ha : 0 < a) (he : e < a) (hl : ∀ z, a * ‖z‖ ≤ ‖L.adjoint z‖)
    (hTlower : ∀ z, ‖z‖ ≤ ‖T z‖) (hT : ‖T‖ ≤ b) (hL : ‖L‖ ≤ l)
    (herror : ‖D - T.comp L‖ ≤ e) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  let Q := T.range
  let TQ : F →L[ℝ] Q := T.rangeRestrict
  let P : E →L[ℝ] Q := Q.orthogonalProjectionOnto.comp D
  have hTQ : ∀ z, ‖z‖ ≤ ‖TQ z‖ := hTlower
  have hsTQ : Function.Surjective TQ := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hTadj := TQ.norm_le_adjoint_of_surjective_norm_le hsTQ hTQ
  have htarget : ∀ w, a * ‖w‖ ≤ ‖(TQ.comp L).adjoint w‖ := by
    intro w
    rw [adjoint_comp, comp_apply]
    exact (mul_le_mul_of_nonneg_left (hTadj w) ha.le).trans (hl _)
  have hprojT : Q.orthogonalProjectionOnto.comp T = TQ := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    exact Q.starProjection_mem_subspace_eq_self ⟨T z, ⟨z, rfl⟩⟩
  have hdiff : P - TQ.comp L = Q.orthogonalProjectionOnto.comp (D - T.comp L) := by
    rw [comp_sub, ← comp_assoc, hprojT]
  have herr : ‖P - TQ.comp L‖ ≤ e := by
    rw [hdiff]
    exact ((opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right Q.orthogonalProjectionOnto_norm_le (norm_nonneg _))).trans
        (by simpa only [one_mul] using herror)
  have hsurj := P.surjective_of_adjoint_margin (TQ.comp L) htarget herr he
  have he0 : 0 ≤ e := (norm_nonneg _).trans herror
  have hnormal : ‖D - Q.subtypeL.comp P‖ ≤ e := by
    apply opNorm_le_bound _ he0
    intro v
    change ‖D v - Q.starProjection (D v)‖ ≤ e * ‖v‖
    have h := Metric.infDist_le_dist_of_mem (show T (L v) ∈ Q from ⟨L v, rfl⟩) (x := D v)
    rw [← Q.dist_starProjection_eq_infDist, dist_eq_norm, dist_eq_norm] at h
    exact h.trans (((D - T.comp L).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right herror (norm_nonneg _)))
  have hupper : ‖P‖ ≤ b * l + e := by
    have hP : ‖P‖ ≤ ‖D‖ := ((opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right Q.orthogonalProjectionOnto_norm_le (norm_nonneg D))).trans_eq
        (one_mul _)
    have hd := norm_sub_le (D - T.comp L) (-(T.comp L))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hd
    have hTL := (opNorm_comp_le T L).trans
      (mul_le_mul hT hL (norm_nonneg _) ((norm_nonneg _).trans hT))
    linarith
  exact ⟨hsurj.1, hnormal, fun v hv => ⟨hsurj.2 v hv,
    (P.le_opNorm v).trans (mul_le_mul_of_nonneg_right hupper (norm_nonneg v))⟩⟩

end ContinuousLinearMap
