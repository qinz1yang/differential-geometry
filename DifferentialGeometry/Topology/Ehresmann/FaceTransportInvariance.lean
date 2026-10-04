import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology

namespace DifferentialGeometry.Topology.Ehresmann

private theorem locally_constant_on_Icc_of_derivative_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ U → HasFDerivAt f (0 : ℝ →L[ℝ] F) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htu : t ∈ U) :
    ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) 1, dist u t < δ → f u = f t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds htu)
  let J := Icc (0 : ℝ) 1 ∩ Metric.ball t δ
  have hJ : Convex ℝ J := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).inter (convex_ball t δ)
  have htJ : t ∈ J := ⟨ht, by simpa only [Metric.mem_ball, dist_self] using hδ⟩
  refine ⟨δ, hδ, fun u hu hud => ?_⟩
  have huJ : u ∈ J := ⟨hu, hud⟩
  have hz : ‖f u - f t‖ ≤ 0 := by
    have hle := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun v hv => (hd v hv.1 (hball hv.2)).hasFDerivWithinAt)
      (fun _v _hv => by simp : ∀ v ∈ J, ‖(0 : ℝ →L[ℝ] F)‖ ≤ (0 : ℝ)) hJ htJ huJ
    simpa only [zero_mul] using hle
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

private theorem forall_Icc_of_closed_of_local
    (Z : Set ℝ) (hZ : IsClosed Z)
    (hlocal : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Z →
      ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) 1, dist u t < δ → u ∈ Z)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hsZ : s ∈ Z) :
    ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Z := by
  let J := ↥(Icc (0 : ℝ) 1)
  let S : Set J := Subtype.val ⁻¹' Z
  let : PreconnectedSpace J :=
    Subtype.preconnectedSpace (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) 1))
  have hSc : IsClosed S := hZ.preimage continuous_subtype_val
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨δ, hδ, hδZ⟩ := hlocal t t.2 ht
    have hnb : Subtype.val ⁻¹' Metric.ball (t : ℝ) δ ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (t : ℝ) hδ)
    exact mem_of_superset hnb (fun u hu => hδZ u u.2 hu)
  have hSuniv : S = univ := (show IsClopen S from ⟨hSc, hSo⟩).eq_univ ⟨⟨s, hs⟩, hsZ⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : J) ∈ S := by rw [hSuniv]; trivial
  exact hmem

/-- Open-neighbourhood total derivative equations preserve the actual face and its boundary. -/
theorem face_invariant_on_Icc_of_neighborhood_derivatives
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : ℝ → F) (R : ℝ → ℝ) (hH : Continuous H) (hR : Continuous R)
    (a : F) (c : ℝ) {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1, H t = a → R t ≤ c → t ∈ U)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, H t = a → R t = c → t ∈ V)
    (hDH : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ U → HasFDerivAt H (0 : ℝ →L[ℝ] F) t)
    (hDR : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ V → HasDerivAt R 0 t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (H s = a ∧ R s ≤ c → ∀ t ∈ Icc (0 : ℝ) 1, H t = a ∧ R t ≤ c) ∧
    (H s = a ∧ R s = c → ∀ t ∈ Icc (0 : ℝ) 1, H t = a ∧ R t = c) := by
  have hRzero : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ V → HasFDerivAt R (0 : ℝ →L[ℝ] ℝ) t := by
    intro t ht hv
    simpa using (hDR t ht hv).hasFDerivAt
  have hlocalBoundary : ∀ t ∈ Icc (0 : ℝ) 1, H t = a → R t = c →
      ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) 1, dist u t < δ → H u = a ∧ R u = c := by
    intro t ht hta htc
    obtain ⟨δH, hδH, hconstH⟩ := locally_constant_on_Icc_of_derivative_zero H hU hDH ht
      (htrace t ht hta (le_of_eq htc))
    obtain ⟨δR, hδR, hconstR⟩ := locally_constant_on_Icc_of_derivative_zero R hV hRzero ht
      (hboundary t ht hta htc)
    refine ⟨min δH δR, lt_min hδH hδR, fun u hu hud => ?_⟩
    exact ⟨(hconstH u hu (hud.trans_le (min_le_left _ _))).trans hta,
      (hconstR u hu (hud.trans_le (min_le_right _ _))).trans htc⟩
  constructor
  · intro hstart
    apply forall_Icc_of_closed_of_local {t | H t = a ∧ R t ≤ c}
      ((isClosed_eq hH continuous_const).inter (isClosed_le hR continuous_const))
      ?_ hs hstart
    intro t ht hmem
    by_cases heq : R t = c
    · obtain ⟨δ, hδ, hδmem⟩ := hlocalBoundary t ht hmem.1 heq
      exact ⟨δ, hδ, fun u hu hud => ⟨(hδmem u hu hud).1, le_of_eq (hδmem u hu hud).2⟩⟩
    · have hlt : R t < c := lt_of_le_of_ne hmem.2 heq
      obtain ⟨δH, hδH, hconstH⟩ := locally_constant_on_Icc_of_derivative_zero H hU hDH ht
        (htrace t ht hmem.1 hmem.2)
      obtain ⟨δR, hδR, hball⟩ := Metric.mem_nhds_iff.mp
        ((isOpen_lt hR continuous_const).mem_nhds hlt)
      refine ⟨min δH δR, lt_min hδH hδR, fun u hu hud => ?_⟩
      exact ⟨(hconstH u hu (hud.trans_le (min_le_left _ _))).trans hmem.1,
        le_of_lt (hball (hud.trans_le (min_le_right _ _)))⟩
  · intro hstart
    exact forall_Icc_of_closed_of_local {t | H t = a ∧ R t = c}
      ((isClosed_eq hH continuous_const).inter (isClosed_eq hR continuous_const))
      (fun t ht hmem => hlocalBoundary t ht hmem.1 hmem.2) hs hstart

end DifferentialGeometry.Topology.Ehresmann
