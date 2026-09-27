import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Separation.Regular

open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ContDiffOn

theorem exists_lipschitzOnWith_of_isCompact
    {f : E → F} {U K : Set E} (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L, s, hs, hL⟩ :=
    (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
  exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩

theorem exists_norm_le_mul_sub_of_comp_eq_zero
    {f : E → F} {P : E → E} {U K : Set E} (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hP : ContinuousOn P K) (hPU : Set.MapsTo P K U) :
    ∃ L : ℝ≥0, ∀ x ∈ K, f (P x) = 0 → ‖f x‖ ≤ L * ‖x - P x‖ := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_of_isCompact hU
    (hK.union (hK.image_of_continuousOn hP)) (Set.union_subset hKU hPU.image_subset)
  refine ⟨L, fun x hx hzero => ?_⟩
  have h := hL.norm_sub_le (Set.mem_union_left _ hx)
    (Set.mem_union_right _ (Set.mem_image_of_mem P hx))
  simpa only [hzero, sub_zero] using h

theorem exists_open_norm_le_mul_sub_of_comp_eq_zero [LocallyCompactSpace E]
    {f : E → F} {P : E → E} {U V K : Set E} (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKV : K ⊆ V) (hP : ContinuousOn P V)
    (hPU : Set.MapsTo P K U) :
    ∃ (L : ℝ≥0) (W : Set E), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∩ V ∧
      Set.MapsTo P W U ∧
      ∀ x ∈ W, f (P x) = 0 → ‖f x‖ ≤ L * ‖x - P x‖ := by
  have hO : IsOpen (U ∩ (V ∩ P ⁻¹' U)) :=
    hU.inter (hP.isOpen_inter_preimage hV hU)
  have hKO : K ⊆ U ∩ (V ∩ P ⁻¹' U) :=
    fun x hx => ⟨hKU hx, hKV hx, hPU hx⟩
  obtain ⟨C, hC, hKC, hCO⟩ := exists_compact_between hK hO hKO
  obtain ⟨L, hL⟩ := hf.exists_norm_le_mul_sub_of_comp_eq_zero hU hC
    (fun x hx => (hCO hx).1) (hP.mono (fun x hx => (hCO hx).2.1))
    (fun x hx => (hCO hx).2.2)
  refine ⟨L, interior C, isOpen_interior, hKC, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hCO (interior_subset hx)).1, (hCO (interior_subset hx)).2.1⟩
  · intro x hx
    exact (hCO (interior_subset hx)).2.2
  · intro x hx
    exact hL x (interior_subset hx)

theorem exists_norm_le_mul_sub_of_time_comp_eq_zero
    {f : ℝ × E → F} {P : E → E} {U : Set (ℝ × E)} {K : Set (ℝ × E)}
    (hf : ContDiffOn ℝ 1 f U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hP : ContinuousOn P (Prod.snd '' K))
    (hPU : ∀ x ∈ K, (x.1, P x.2) ∈ U) :
    ∃ L : ℝ≥0, ∀ x ∈ K, f (x.1, P x.2) = 0 →
      ‖f x‖ ≤ L * ‖x.2 - P x.2‖ := by
  let Q : ℝ × E → ℝ × E := fun x => (x.1, P x.2)
  have hQ : ContinuousOn Q K := by
    apply ContinuousOn.prodMk continuousOn_fst
    exact hP.comp continuousOn_snd (fun _ hx => Set.mem_image_of_mem Prod.snd hx)
  have hQK : Set.MapsTo Q K U := by
    intro x hx
    exact hPU x hx
  obtain ⟨L, hL⟩ := hf.exists_norm_le_mul_sub_of_comp_eq_zero hU hK hKU hQ hQK
  refine ⟨L, fun x hx hzero => ?_⟩
  have h := hL x hx hzero
  simpa [Q, Prod.norm_def, max_eq_right (norm_nonneg _)] using h

theorem exists_norm_le_mul_sum_of_fderiv_comp_eq_zero
    {f : ℝ × E × E → F} {P : E → E} {U K : Set (ℝ × E × E)} {V : Set E}
    (hf : ContDiffOn ℝ 1 f U) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKU : K ⊆ U) (hKV : ∀ x ∈ K, x.2.1 ∈ V)
    (hP : ContDiffOn ℝ 1 P V)
    (hPU : ∀ x ∈ K, (x.1, P x.2.1, fderiv ℝ P x.2.1 x.2.2) ∈ U) :
    ∃ L : ℝ≥0, ∀ x ∈ K, f (x.1, P x.2.1, fderiv ℝ P x.2.1 x.2.2) = 0 →
      ‖f x‖ ≤ L * (‖x.2.1 - P x.2.1‖ + ‖x.2.2 - fderiv ℝ P x.2.1 x.2.2‖) := by
  let Q : ℝ × E × E → ℝ × E × E :=
    fun x => (x.1, P x.2.1, fderiv ℝ P x.2.1 x.2.2)
  have hpos : ContinuousOn (fun x : ℝ × E × E => x.2.1) K :=
    continuous_fst.comp continuous_snd |>.continuousOn
  have hvel : ContinuousOn (fun x : ℝ × E × E => x.2.2) K :=
    continuous_snd.comp continuous_snd |>.continuousOn
  have hQ : ContinuousOn Q K :=
    continuousOn_fst.prodMk ((hP.continuousOn.comp hpos hKV).prodMk
      (((hP.continuousOn_fderiv_of_isOpen hV le_rfl).comp hpos hKV).clm_apply hvel))
  obtain ⟨L, hL⟩ := hf.exists_norm_le_mul_sub_of_comp_eq_zero hU hK hKU hQ hPU
  refine ⟨L, fun x hx hzero => ?_⟩
  have h := hL x hx hzero
  have hnorm : ‖x - Q x‖ ≤
      ‖x.2.1 - P x.2.1‖ + ‖x.2.2 - fderiv ℝ P x.2.1 x.2.2‖ := by
    simp only [Q, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
    exact max_le (by positivity) (max_le
      (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)))
  exact h.trans (mul_le_mul_of_nonneg_left hnorm L.coe_nonneg)

end ContDiffOn
