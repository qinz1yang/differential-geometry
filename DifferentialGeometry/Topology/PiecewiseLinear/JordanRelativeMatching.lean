/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalOrderExtension
import DifferentialGeometry.Topology.PiecewiseLinear.InteriorAccess
import DifferentialGeometry.Topology.Homeomorph.JordanDiskMove
import DifferentialGeometry.Topology.PlanarJordan.Crosscut
import DifferentialGeometry.External.Schoenflies.TwoArcs

open Set Topology Schoenflies unitInterval

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_isArcBetween_sdiff_subset_inside {K : Set Plane} (hK : IsJordanCurve K)
    {p q : Plane} (hp : p ∈ K) (hq : q ∈ K) (hpq : p ≠ q) :
    ∃ P : Set Plane, IsArcBetween P p q ∧ P \ {p, q} ⊆ inside K := by
  obtain ⟨e, he, -⟩ := Homeomorph.exists_isPLSphere_image_eqOn_compl_of_isJordanCurve hK
    isOpen_univ (subset_univ K)
  have hD := PiecewiseLinear.isPLBall_closure_inside_of_isPLSphere_one he
  have hfr : frontier (closure (inside (e '' K))) = e '' K :=
    frontier_closure_inside (isJordanCurve_image e hK)
  have hep : e p ∈ frontier (closure (inside (e '' K))) := by
    rw [hfr]
    exact mem_image_of_mem e hp
  have heq : e q ∈ frontier (closure (inside (e '' K))) := by
    rw [hfr]
    exact mem_image_of_mem e hq
  obtain ⟨A, hA⟩ := hD.exists_isCrosscut hep heq (e.injective.ne hpq)
  refine ⟨e.symm '' A, ?_, ?_⟩
  · simpa only [Homeomorph.symm_apply_apply] using isArcBetween_image e.symm hA.arc
  · rintro _ ⟨⟨z, hz, rfl⟩, hzpq⟩
    have hz' : z ∈ A \ {e p, e q} := by
      refine ⟨hz, ?_⟩
      rintro (h | h)
      · exact hzpq (Or.inl (by rw [h, Homeomorph.symm_apply_apply]))
      · exact hzpq (Or.inr (mem_singleton_iff.mpr
          (by rw [mem_singleton_iff.mp h, Homeomorph.symm_apply_apply])))
    have hin := hA.sdiff_subset hz'
    rw [hfr, ← image_inside] at hin
    obtain ⟨w, hw, hwz⟩ := hin
    rw [← hwz, Homeomorph.symm_apply_apply]
    exact hw

theorem isCutPair_of_isLoop {f : ℝ → Plane} (hf : IsLoop f) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    IsCutPair (f '' I) (f 0) (f q) (f '' Icc 0 q) (f '' Icc 0 0 ∪ f '' Icc q 1) := by
  have hqI : q ∈ I := ⟨hq0.le, hq1.le⟩
  exact ⟨hf.middle_IsArcBetween zero_mem_I hqI hq1.ne hq0,
    (hf.outside_IsArcBetween zero_mem_I hqI zero_ne_one hq1.ne hq0).reverse,
    IsLoop.pieces_cover zero_mem_I hqI,
    hf.pieces_meet_at_ends zero_mem_I hqI zero_ne_one hq1.ne hq0⟩

theorem false_of_isCutPair_of_inside_subset {S J S₁ S₂ A₁ A₂ : Set Plane}
    {y₁ y₂ y₃ y₄ : Plane} (hS : IsJordanCurve S) (hJ : IsJordanCurve J)
    (hSJ : inside S ⊆ inside J) (hcutS : IsCutPair S y₁ y₂ S₁ S₂)
    (hcutJ : IsCutPair J y₁ y₂ A₁ A₂) (h₃S : y₃ ∈ S₁) (h₄S : y₄ ∈ S₁)
    (h₃ : y₃ ∈ A₁ \ {y₁, y₂}) (h₄ : y₄ ∈ A₂ \ {y₁, y₂}) : False := by
  have h₁₂ : y₁ ≠ y₂ := by
    obtain ⟨f, -, hi, -, hf0, hf1⟩ := hcutS.fst
    intro h
    exact zero_ne_one (hi zero_mem_I one_mem_I (hf0.trans (h.trans hf1.symm)))
  have h₃₄ : y₃ ≠ y₄ := by
    rintro rfl
    exact h₃.2 (hcutJ.inter_eq.subset ⟨h₃.1, h₄.1⟩)
  obtain ⟨P, hP, hPS⟩ := exists_isArcBetween_sdiff_subset_inside hS
    (hcutS.fst_subset hcutS.fst.left_mem) (hcutS.fst_subset hcutS.fst.right_mem) h₁₂
  obtain ⟨hcover, -, -, -⟩ := crosscut_regions hS hP hcutS hPS
  obtain ⟨Q, hQ, hQK⟩ := exists_isArcBetween_sdiff_subset_inside
    (isJordanCurve_cut_arc_union hP hcutS hPS) (Or.inl h₃S) (Or.inl h₄S) h₃₄
  have hQS : Q \ {y₃, y₄} ⊆ inside S \ P := fun z hz => by
    rw [hcover]
    exact Or.inl (hQK hz)
  have hQJ : Q \ {y₃, y₄} ⊆ inside J \ P := fun z hz => ⟨hSJ (hQS hz).1, (hQS hz).2⟩
  have hPJ : P \ {y₁, y₂} ⊆ inside J := hPS.trans hSJ
  have hside₂ := arc_diff_subset_crosscut_side hJ hP hcutJ.symm hPJ hQ hQJ h₄
  have hQJ' : Q \ {y₄, y₃} ⊆ inside J \ P := by
    rw [pair_comm]
    exact hQJ
  have hside₁ := arc_diff_subset_crosscut_side hJ hP hcutJ hPJ hQ.reverse hQJ' h₃
  obtain ⟨-, hdis, -, -⟩ := crosscut_regions hJ hP hcutJ hPJ
  obtain ⟨z, hzQ, hz⟩ := not_subset.mp hQ.not_subset_pair
  have hz' : z ∉ ({y₄, y₃} : Set Plane) := by
    rw [pair_comm]
    exact hz
  exact disjoint_left.mp hdis (hside₁ ⟨hzQ, hz'⟩) (hside₂ ⟨hzQ, hz⟩)

theorem not_lt_lt_of_isLoop_of_inside_subset {γ τ : ℝ → Plane} (hγ : IsLoop γ)
    (hτ : IsLoop τ) (hSJ : inside (γ '' I) ⊆ inside (τ '' I)) (h0 : γ 0 = τ 0)
    {q c d q' c' d' : ℝ} (hc : 0 < c) (hcq : c < q) (hqd : q < d) (hd : d < 1)
    (hq' : q' ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) (hd' : d' ∈ Ioo (0 : ℝ) 1)
    (heq : γ q' = τ q) (hec : γ c' = τ c) (hed : γ d' = τ d) :
    ¬ (c' < q' ∧ d' < q') ∧ ¬ (q' < c' ∧ q' < d') := by
  have hS : IsJordanCurve (γ '' I) := ⟨γ, hγ, rfl⟩
  have hJ : IsJordanCurve (τ '' I) := ⟨τ, hτ, rfl⟩
  have hcutJ := isCutPair_of_isLoop hτ (hc.trans hcq) (hqd.trans hd)
  have hcutS := isCutPair_of_isLoop hγ hq'.1 hq'.2
  rw [h0, heq] at hcutS
  have hne : ∀ {x y : ℝ}, x ∈ Ico (0 : ℝ) 1 → y ∈ Ico (0 : ℝ) 1 → x ≠ y → τ x ≠ τ y :=
    fun hx hy hxy h => hxy (hτ.injOn hx hy h)
  have h₃ : τ c ∈ τ '' Icc 0 q \ {τ 0, τ q} := by
    refine ⟨⟨c, ⟨hc.le, hcq.le⟩, rfl⟩, ?_⟩
    rintro (h | h)
    · exact hne ⟨hc.le, by linarith⟩ ⟨le_rfl, zero_lt_one⟩ hc.ne' h
    · exact hne ⟨hc.le, by linarith⟩ ⟨by linarith, by linarith⟩ hcq.ne (mem_singleton_iff.mp h)
  have h₄ : τ d ∈ (τ '' Icc 0 0 ∪ τ '' Icc q 1) \ {τ 0, τ q} := by
    refine ⟨Or.inr ⟨d, ⟨hqd.le, hd.le⟩, rfl⟩, ?_⟩
    rintro (h | h)
    · exact hne ⟨by linarith, hd⟩ ⟨le_rfl, zero_lt_one⟩ (show (0 : ℝ) < d by linarith).ne' h
    · exact hne ⟨by linarith, hd⟩ ⟨by linarith, by linarith⟩ hqd.ne' (mem_singleton_iff.mp h)
  constructor
  · rintro ⟨h1, h2⟩
    have e3 : τ c ∈ γ '' Icc 0 q' := by
      rw [← hec]
      exact ⟨c', ⟨hc'.1.le, h1.le⟩, rfl⟩
    have e4 : τ d ∈ γ '' Icc 0 q' := by
      rw [← hed]
      exact ⟨d', ⟨hd'.1.le, h2.le⟩, rfl⟩
    exact false_of_isCutPair_of_inside_subset hS hJ hSJ hcutS hcutJ e3 e4 h₃ h₄
  · rintro ⟨h1, h2⟩
    have e3 : τ c ∈ γ '' Icc 0 0 ∪ γ '' Icc q' 1 := by
      rw [← hec]
      exact Or.inr ⟨c', ⟨h1.le, hc'.2.le⟩, rfl⟩
    have e4 : τ d ∈ γ '' Icc 0 0 ∪ γ '' Icc q' 1 := by
      rw [← hed]
      exact Or.inr ⟨d', ⟨h2.le, hd'.2.le⟩, rfl⟩
    exact false_of_isCutPair_of_inside_subset hS hJ hSJ hcutS.symm hcutJ e3 e4 h₃ h₄

theorem invFunOn_isLoop {τ : ℝ → Plane} (hτ : IsLoop τ) {x : Plane} (hx : x ∈ τ '' I) :
    Function.invFunOn τ (Ico 0 1) x ∈ Ico (0 : ℝ) 1 ∧
      τ (Function.invFunOn τ (Ico 0 1) x) = x := by
  obtain ⟨u, hu, hu1, rfl⟩ := hτ.parameter_before_finish hx
  have hex : ∃ a ∈ Ico (0 : ℝ) 1, τ a = τ u := ⟨u, ⟨hu.1, hu.2.lt_of_ne hu1⟩, rfl⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

theorem invFunOn_isLoop_apply {τ : ℝ → Plane} (hτ : IsLoop τ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) : Function.invFunOn τ (Ico 0 1) (τ t) = t := by
  have h := invFunOn_isLoop hτ ⟨t, Ico_subset_Icc_self ht, rfl⟩
  exact hτ.injOn h.1 ht h.2

theorem continuousOn_image_of_continuousOn_comp {X : Type*} [TopologicalSpace X]
    {γ : ℝ → Plane} (hγ : ContinuousOn γ I) {g : Plane → X} (hg : ContinuousOn (g ∘ γ) I) :
    ContinuousOn g (γ '' I) := by
  rw [continuousOn_iff_isClosed]
  intro K hK
  refine ⟨γ '' (I ∩ (g ∘ γ) ⁻¹' K), ?_, ?_⟩
  · have hc : IsCompact (I ∩ (g ∘ γ) ⁻¹' K) :=
      isCompact_Icc.of_isClosed_subset (hg.preimage_isClosed_of_isClosed isClosed_Icc hK)
        inter_subset_left
    exact (hc.image_of_continuousOn (hγ.mono inter_subset_left)).isClosed
  · ext x
    constructor
    · rintro ⟨hxK, t, ht, rfl⟩
      exact ⟨⟨t, ⟨ht, hxK⟩, rfl⟩, ⟨t, ht, rfl⟩⟩
    · rintro ⟨⟨t, ⟨ht, htK⟩, rfl⟩, -⟩
      exact ⟨htK, t, ht, rfl⟩

theorem isLoop_comp_one_sub {τ : ℝ → Plane} (hτ : IsLoop τ) : IsLoop fun s => τ (1 - s) where
  continuousOn := by
    have hmaps : MapsTo (fun s : ℝ => 1 - s) I I := by
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact hτ.continuousOn.comp (by fun_prop : ContinuousOn (fun s : ℝ => 1 - s) I) hmaps
  closes := by
    simp only [sub_zero, sub_self]
    exact hτ.closes.symm
  injOn := by
    intro s hs t ht hst'
    have hst : τ (1 - s) = τ (1 - t) := hst'
    have key : ∀ u ∈ Ico (0 : ℝ) 1, 0 < u → τ (1 - u) ≠ τ 1 := by
      intro u hu hu0 h
      have h' : 1 - u = 0 :=
        hτ.injOn ⟨by linarith [hu.2], by linarith⟩ ⟨le_rfl, zero_lt_one⟩ (h.trans hτ.closes.symm)
      linarith [hu.2]
    rcases eq_or_lt_of_le hs.1 with e | hs0 <;> rcases eq_or_lt_of_le ht.1 with e' | ht0
    · rw [← e, ← e']
    · rw [← e, sub_zero] at hst
      exact absurd hst.symm (key t ht ht0)
    · rw [← e', sub_zero] at hst
      exact absurd hst (key s hs hs0)
    · have h := hτ.injOn ⟨by linarith [hs.2], by linarith⟩ ⟨by linarith [ht.2], by linarith⟩ hst
      linarith

theorem image_comp_one_sub (τ : ℝ → Plane) : (fun s => τ (1 - s)) '' I = τ '' I := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp only [sub_sub_cancel]⟩

theorem exists_isLoop_image_eq_zero {J : Set Plane} (hJ : IsJordanCurve J) {x : Plane}
    (hx : x ∈ J) : ∃ τ : ℝ → Plane, IsLoop τ ∧ τ '' I = J ∧ τ 0 = x := by
  obtain ⟨u, hu, v, hv, huv⟩ := hJ.exists_ne
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ J, x ≠ y := by
    by_cases hxu : x = u
    · refine ⟨v, hv, ?_⟩
      rw [hxu]
      exact huv
    · exact ⟨u, hu, hxu⟩
  obtain ⟨A, B, hcut⟩ := exists_isCutPair hJ hx hy hxy
  obtain ⟨a, hac, hai, ha, ha0, ha1⟩ := hcut.fst
  obtain ⟨b, hbc, hbi, hb, hb0, hb1⟩ := hcut.snd.reverse
  have hmid : a 1 = b 0 := by rw [ha1, hb0]
  refine ⟨concatenate a b, IsLoop.concatenate hac hai hbc hbi hmid (by rw [hb1, ha0]) ?_,
    ?_, ?_⟩
  · intro z hza hzb
    rw [ha] at hza
    rw [hb] at hzb
    have hz := hcut.inter_eq.subset ⟨hza, hzb⟩
    rw [ha0, ha1]
    exact hz
  · rw [image_concatenate hmid, ha, hb, hcut.union_eq]
  · rw [concatenate_zero, ha0]

theorem continuousOn_injOn_image_of_isLoop_of_strictMonoOn {γ τ : ℝ → Plane} (hγ : IsLoop γ)
    (hτ : IsLoop τ) {H : ℝ → ℝ} (hHc : ContinuousOn H I) (hHm : StrictMonoOn H I)
    (hHI : H '' I = I) (hH0 : H 0 = 0) (hH1 : H 1 = 1) :
    ContinuousOn (fun x => τ (H (Function.invFunOn γ (Ico 0 1) x))) (γ '' I) ∧
      InjOn (fun x => τ (H (Function.invFunOn γ (Ico 0 1) x))) (γ '' I) ∧
      (fun x => τ (H (Function.invFunOn γ (Ico 0 1) x))) '' (γ '' I) = τ '' I := by
  have hmapsH : MapsTo H I I := fun t ht => hHI ▸ mem_image_of_mem H ht
  have hcomp : EqOn ((fun x => τ (H (Function.invFunOn γ (Ico 0 1) x))) ∘ γ) (τ ∘ H) I := by
    intro t ht
    rcases eq_or_ne t 1 with rfl | ht1
    · change τ (H (Function.invFunOn γ (Ico 0 1) (γ 1))) = τ (H 1)
      rw [← hγ.closes, invFunOn_isLoop_apply hγ ⟨le_rfl, zero_lt_one⟩, hH0, hH1, hτ.closes]
    · change τ (H (Function.invFunOn γ (Ico 0 1) (γ t))) = τ (H t)
      rw [invFunOn_isLoop_apply hγ ⟨ht.1, ht.2.lt_of_ne ht1⟩]
  have hlt1 : ∀ t ∈ Ico (0 : ℝ) 1, H t ∈ Ico (0 : ℝ) 1 := by
    intro t ht
    have h := hHm (Ico_subset_Icc_self ht) one_mem_I ht.2
    rw [hH1] at h
    exact ⟨(hmapsH (Ico_subset_Icc_self ht)).1, h⟩
  refine ⟨?_, ?_, ?_⟩
  · exact continuousOn_image_of_continuousOn_comp hγ.continuousOn
      ((hτ.continuousOn.comp hHc hmapsH).congr hcomp)
  · intro x hx y hy hxy
    obtain ⟨t, ht, ht1, rfl⟩ := hγ.parameter_before_finish hx
    obtain ⟨s, hs, hs1, rfl⟩ := hγ.parameter_before_finish hy
    have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.lt_of_ne ht1⟩
    have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1, hs.2.lt_of_ne hs1⟩
    simp only [invFunOn_isLoop_apply hγ ht', invFunOn_isLoop_apply hγ hs'] at hxy
    have h := hτ.injOn (hlt1 t ht') (hlt1 s hs') hxy
    rw [hHm.injOn.eq_iff ht hs] at h
    rw [h]
  · rw [← image_comp, hcomp.image_eq, image_comp, hHI]

theorem exists_matching_of_isLoop_of_strictMono {γ τ : ℝ → Plane} (hγ : IsLoop γ)
    (hτ : IsLoop τ) (h0 : γ 0 = τ 0)
    (hmono : ∀ t₁ ∈ Ioo (0 : ℝ) 1, γ t₁ ∈ τ '' I → ∀ t₂ ∈ Ioo (0 : ℝ) 1, γ t₂ ∈ τ '' I →
      t₁ < t₂ → Function.invFunOn τ (Ico 0 1) (γ t₁) < Function.invFunOn τ (Ico 0 1) (γ t₂)) :
    ∃ f : Plane → Plane, ContinuousOn f (γ '' I) ∧ InjOn f (γ '' I) ∧
      f '' (γ '' I) = τ '' I ∧ ∀ x ∈ γ '' I ∩ τ '' I, f x = x := by
  set k := Function.invFunOn τ (Ico 0 1) with hk
  set G : Set ℝ := I ∩ γ ⁻¹' (τ '' I) with hG
  set hh : ℝ → ℝ := fun t => if t = 1 then 1 else k (γ t) with hhh
  have hJc : IsClosed (τ '' I) := (isCompact_Icc.image_of_continuousOn hτ.continuousOn).isClosed
  have hSc : IsClosed (γ '' I) := (isCompact_Icc.image_of_continuousOn hγ.continuousOn).isClosed
  have hGc : IsClosed G := hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hJc
  have hGI : G ⊆ Icc 0 1 := inter_subset_left
  have hγ1 : γ 1 = γ 0 := hγ.closes.symm
  have hτ1 : τ 1 = τ 0 := hτ.closes.symm
  have h0G : (0 : ℝ) ∈ G :=
    ⟨zero_mem_I, by rw [mem_preimage, h0]; exact mem_image_of_mem τ zero_mem_I⟩
  have h1G : (1 : ℝ) ∈ G :=
    ⟨one_mem_I, by rw [mem_preimage, hγ1, h0]; exact mem_image_of_mem τ zero_mem_I⟩
  have hkey : ∀ t ∈ G, t ≠ 1 → hh t ∈ Ico (0 : ℝ) 1 ∧ τ (hh t) = γ t := by
    intro t ht ht1
    simp only [hhh, ite_eq_right ht1]
    exact invFunOn_isLoop hτ ht.2
  have hh0 : hh 0 = 0 := by
    have e := hkey 0 h0G zero_ne_one
    exact hτ.injOn e.1 ⟨le_rfl, zero_lt_one⟩ (e.2.trans h0)
  have hh1 : hh 1 = 1 := by simp [hhh]
  have hinner : ∀ t ∈ G, t ∈ Ioo (0 : ℝ) 1 → hh t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht ht'
    obtain ⟨e1, e2⟩ := hkey t ht ht'.2.ne
    refine ⟨lt_of_le_of_ne e1.1 fun e => ?_, e1.2⟩
    have h : γ t = γ 0 := by rw [← e2, ← e, h0]
    exact ht'.1.ne' (hγ.injOn ⟨ht'.1.le, ht'.2⟩ ⟨le_rfl, zero_lt_one⟩ h)
  have hstrict : StrictMonoOn hh G := by
    intro t₁ ht₁ t₂ ht₂ hlt
    rcases eq_or_lt_of_le ht₁.1.1 with e | hpos₁
    · subst e
      rw [hh0]
      rcases eq_or_lt_of_le ht₂.1.2 with e' | hlt₂
      · rw [e', hh1]
        exact zero_lt_one
      · exact (hinner t₂ ht₂ ⟨hlt, hlt₂⟩).1
    · rcases eq_or_lt_of_le ht₂.1.2 with e' | hlt₂
      · rw [e', hh1]
        exact (hinner t₁ ht₁ ⟨hpos₁, hlt.trans_le ht₂.1.2⟩).2
      · have ht₁' : t₁ ∈ Ioo (0 : ℝ) 1 := ⟨hpos₁, hlt.trans hlt₂⟩
        have ht₂' : t₂ ∈ Ioo (0 : ℝ) 1 := ⟨hpos₁.trans hlt, hlt₂⟩
        simp only [hhh, ite_eq_right ht₁'.2.ne, ite_eq_right hlt₂.ne]
        exact hmono t₁ ht₁' ht₁.2 t₂ ht₂' ht₂.2 hlt
  have himage : hh '' G = I ∩ τ ⁻¹' (γ '' I) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases eq_or_ne t 1 with rfl | ht1
      · rw [hh1]
        refine ⟨one_mem_I, ?_⟩
        rw [mem_preimage, hτ1, ← h0]
        exact mem_image_of_mem γ zero_mem_I
      · obtain ⟨e1, e2⟩ := hkey t ht ht1
        refine ⟨Ico_subset_Icc_self e1, ?_⟩
        rw [mem_preimage, e2]
        exact mem_image_of_mem γ ht.1
    · rintro ⟨hs, hsS⟩
      rcases eq_or_ne s 1 with rfl | hs1
      · exact ⟨1, h1G, hh1⟩
      · have hsS' : τ s ∈ γ '' I := hsS
        obtain ⟨t, ht, ht1, hts⟩ := hγ.parameter_before_finish hsS'
        have htG : t ∈ G := ⟨ht, by rw [mem_preimage, hts]; exact mem_image_of_mem τ hs⟩
        obtain ⟨e1, e2⟩ := hkey t htG ht1
        exact ⟨t, htG, hτ.injOn e1 ⟨hs.1, hs.2.lt_of_ne hs1⟩ (e2.trans hts)⟩
  have hGc' : IsClosed (hh '' G) := by
    rw [himage]
    exact hτ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hSc
  obtain ⟨H, hHm, hHI, hHeq, hHc⟩ :=
    exists_strictMonoOn_Icc_extension hGc hGI h0G h1G hstrict hh0 hh1 hGc'
  have hH0 : H 0 = 0 := (hHeq h0G).trans hh0
  have hH1 : H 1 = 1 := (hHeq h1G).trans hh1
  obtain ⟨hc, hi, himg⟩ :=
    continuousOn_injOn_image_of_isLoop_of_strictMonoOn hγ hτ hHc hHm hHI hH0 hH1
  refine ⟨_, hc, hi, himg, ?_⟩
  rintro x ⟨hxS, hxJ⟩
  obtain ⟨t, ht, ht1, rfl⟩ := hγ.parameter_before_finish hxS
  have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.lt_of_ne ht1⟩
  have htG : t ∈ G := ⟨ht, hxJ⟩
  change τ (H (Function.invFunOn γ (Ico 0 1) (γ t))) = γ t
  rw [invFunOn_isLoop_apply hγ ht', hHeq htG]
  exact (hkey t htG ht1).2

theorem exists_matching_of_inside_subset {S J : Set Plane} (hS : IsJordanCurve S)
    (hJ : IsJordanCurve J) (hSJ : inside S ⊆ inside J) :
    ∃ f : Plane → Plane, ContinuousOn f S ∧ InjOn f S ∧ f '' S = J ∧
      ∀ x ∈ S ∩ J, f x = x := by
  by_cases hF : (S ∩ J).Nonempty
  · obtain ⟨x₀, hx₀S, hx₀J⟩ := hF
    obtain ⟨γ, hγ, hγS, hγ0⟩ := exists_isLoop_image_eq_zero hS hx₀S
    obtain ⟨τ, hτ, hτJ, hτ0⟩ := exists_isLoop_image_eq_zero hJ hx₀J
    subst hγS hτJ
    have h0 : γ 0 = τ 0 := hγ0.trans hτ0.symm
    set k := Function.invFunOn τ (Ico 0 1) with hk
    set T : Set ℝ := Ioo 0 1 ∩ γ ⁻¹' (τ '' I) with hT
    have hparam : ∀ t ∈ T, k (γ t) ∈ Ioo (0 : ℝ) 1 ∧ τ (k (γ t)) = γ t := by
      intro t ht
      obtain ⟨e1, e2⟩ := invFunOn_isLoop hτ ht.2
      refine ⟨⟨lt_of_le_of_ne e1.1 fun e => ?_, e1.2⟩, e2⟩
      have h : γ t = γ 0 := e2.symm.trans ((congrArg τ e.symm).trans h0.symm)
      exact ht.1.1.ne' (hγ.injOn ⟨ht.1.1.le, ht.1.2⟩ ⟨le_rfl, zero_lt_one⟩ h)
    have hinj : InjOn (fun t => k (γ t)) T := by
      intro t₁ h₁ t₂ h₂ he
      have h : γ t₁ = γ t₂ :=
        (hparam t₁ h₁).2.symm.trans ((congrArg τ he).trans (hparam t₂ h₂).2)
      exact hγ.injOn ⟨h₁.1.1.le, h₁.1.2⟩ ⟨h₂.1.1.le, h₂.1.2⟩ h
    have P4 : ∀ {q c d q' c' d' : ℝ}, 0 < c → c < q → q < d → d < 1 →
        q' ∈ Ioo (0 : ℝ) 1 → c' ∈ Ioo (0 : ℝ) 1 → d' ∈ Ioo (0 : ℝ) 1 → γ q' = τ q →
          γ c' = τ c → γ d' = τ d → ¬ (c' < q' ∧ d' < q') ∧ ¬ (q' < c' ∧ q' < d') :=
      fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        not_lt_lt_of_isLoop_of_inside_subset hγ hτ hSJ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    have hbtw : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a < b → b < c →
        (k (γ a) < k (γ b) ∧ k (γ b) < k (γ c)) ∨
          (k (γ c) < k (γ b) ∧ k (γ b) < k (γ a)) := by
      intro a ha b hb c hc hab hbc
      obtain ⟨pa, ea⟩ := hparam a ha
      obtain ⟨pb, eb⟩ := hparam b hb
      obtain ⟨pc, ec⟩ := hparam c hc
      have hne_ab : k (γ a) ≠ k (γ b) := fun e => hab.ne (hinj ha hb e)
      have hne_bc : k (γ b) ≠ k (γ c) := fun e => hbc.ne (hinj hb hc e)
      have hne_ac : k (γ a) ≠ k (γ c) := fun e => (hab.trans hbc).ne (hinj ha hc e)
      have hx1 : ¬ (k (γ b) < k (γ a) ∧ k (γ b) < k (γ c)) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hne_ac with h3 | h3
        · exact (P4 pb.1 h1 h3 pc.2 ha.1 hb.1 hc.1 ea.symm eb.symm ec.symm).2
            ⟨hab, hab.trans hbc⟩
        · exact (P4 pb.1 h2 h3 pa.2 hc.1 hb.1 ha.1 ec.symm eb.symm ea.symm).1
            ⟨hbc, hab.trans hbc⟩
      have hx2 : ¬ (k (γ a) < k (γ b) ∧ k (γ c) < k (γ b)) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hne_ac with h3 | h3
        · exact (P4 pa.1 h3 h2 pb.2 hc.1 ha.1 hb.1 ec.symm ea.symm eb.symm).1
            ⟨hab.trans hbc, hbc⟩
        · exact (P4 pc.1 h3 h1 pb.2 ha.1 hc.1 hb.1 ea.symm ec.symm eb.symm).2
            ⟨hab.trans hbc, hab⟩
      rcases lt_or_gt_of_ne hne_ab with h1 | h1 <;> rcases lt_or_gt_of_ne hne_bc with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · exact absurd ⟨h1, h2⟩ hx2
      · exact absurd ⟨h1, h2⟩ hx1
      · exact Or.inr ⟨h2, h1⟩
    rcases strictMonoOn_or_strictAntiOn_of_between hinj hbtw with hmono | hanti
    · exact exists_matching_of_isLoop_of_strictMono hγ hτ h0
        fun t₁ h₁ h₁' t₂ h₂ h₂' hlt => hmono ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ hlt
    · have hτ' : IsLoop fun s => τ (1 - s) := isLoop_comp_one_sub hτ
      have hτ'I : (fun s => τ (1 - s)) '' I = τ '' I := image_comp_one_sub τ
      have hk' : ∀ t ∈ T,
          Function.invFunOn (fun s => τ (1 - s)) (Ico 0 1) (γ t) = 1 - k (γ t) := by
        intro t ht
        obtain ⟨p, e⟩ := hparam t ht
        have hmem : γ t ∈ (fun s => τ (1 - s)) '' I := by
          rw [hτ'I]
          exact ht.2
        obtain ⟨e1, e2⟩ := invFunOn_isLoop hτ' hmem
        refine hτ'.injOn e1 ⟨by linarith [p.2], by linarith [p.1]⟩ (e2.trans ?_)
        show γ t = τ (1 - (1 - k (γ t)))
        rw [sub_sub_cancel, e]
      have h0' : γ 0 = (fun s => τ (1 - s)) 0 := by
        change γ 0 = τ (1 - 0)
        rw [sub_zero, h0, hτ.closes]
      obtain ⟨f, hf⟩ := exists_matching_of_isLoop_of_strictMono hγ hτ' h0'
        (by
          intro t₁ h₁ h₁' t₂ h₂ h₂' hlt
          rw [hτ'I] at h₁' h₂'
          rw [hk' t₁ ⟨h₁, h₁'⟩, hk' t₂ ⟨h₂, h₂'⟩]
          have h : k (γ t₂) < k (γ t₁) := hanti ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ hlt
          linarith)
      rw [hτ'I] at hf
      exact ⟨f, hf⟩
  · rw [not_nonempty_iff_eq_empty] at hF
    obtain ⟨γ, hγ, rfl⟩ := hS
    obtain ⟨τ, hτ, rfl⟩ := hJ
    obtain ⟨hc, hi, himg⟩ := continuousOn_injOn_image_of_isLoop_of_strictMonoOn hγ hτ (H := id)
      continuousOn_id strictMonoOn_id (image_id I) rfl rfl
    refine ⟨_, hc, hi, himg, ?_⟩
    intro x hx
    rw [hF] at hx
    simp at hx

end DifferentialGeometry.Topology.PlanarJordan
