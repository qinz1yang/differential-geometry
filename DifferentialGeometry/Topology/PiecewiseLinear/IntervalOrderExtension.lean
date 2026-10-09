/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity

open Set

namespace DifferentialGeometry.Topology

theorem exists_strictMonoOn_Icc_extension {G : Set ℝ} (hG : IsClosed G) (hGI : G ⊆ Icc 0 1)
    (h0 : (0 : ℝ) ∈ G) (h1 : (1 : ℝ) ∈ G) {h : ℝ → ℝ} (hmono : StrictMonoOn h G)
    (hh0 : h 0 = 0) (hh1 : h 1 = 1) (hcl : IsClosed (h '' G)) :
    ∃ H : ℝ → ℝ, StrictMonoOn H (Icc 0 1) ∧ H '' Icc 0 1 = Icc 0 1 ∧ EqOn H h G ∧
      ContinuousOn H (Icc 0 1) := by
  set lo : ℝ → ℝ := fun t => sSup (G ∩ Iic t) with hlo_def
  set hi : ℝ → ℝ := fun t => sInf (G ∩ Ici t) with hhi_def
  set H : ℝ → ℝ := fun t =>
    h (lo t) + (t - lo t) * (h (hi t) - h (lo t)) / (hi t - lo t) with hH_def
  have hmonoG : MonotoneOn h G := hmono.monotoneOn
  have hbddA : ∀ t : ℝ, BddAbove (G ∩ Iic t) := fun t => ⟨t, fun _ hs => hs.2⟩
  have hbddB : ∀ t : ℝ, BddBelow (G ∩ Ici t) := fun t => ⟨t, fun _ hs => hs.2⟩
  have hlo_mem : ∀ t ∈ Icc (0 : ℝ) 1, lo t ∈ G ∧ lo t ≤ t := fun t ht =>
    (hG.inter isClosed_Iic).csSup_mem ⟨0, h0, ht.1⟩ (hbddA t)
  have hhi_mem : ∀ t ∈ Icc (0 : ℝ) 1, hi t ∈ G ∧ t ≤ hi t := fun t ht =>
    (hG.inter isClosed_Ici).csInf_mem ⟨1, h1, ht.2⟩ (hbddB t)
  have hlo_ge : ∀ t : ℝ, ∀ s ∈ G, s ≤ t → s ≤ lo t := fun t s hs hst =>
    le_csSup (hbddA t) ⟨hs, hst⟩
  have hhi_le : ∀ t : ℝ, ∀ s ∈ G, t ≤ s → hi t ≤ s := fun t s hs hst =>
    csInf_le (hbddB t) ⟨hs, hst⟩
  have hH_of_mem : ∀ t ∈ G, H t = h t := by
    intro t ht
    have htI := hGI ht
    have hl : lo t = t := le_antisymm (hlo_mem t htI).2 (hlo_ge t t ht le_rfl)
    have hr : hi t = t := le_antisymm (hhi_le t t ht le_rfl) (hhi_mem t htI).2
    simp only [hH_def, hl, hr, sub_self, zero_mul, zero_div, add_zero]
  have hgap : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ G →
      lo t < t ∧ t < hi t ∧ ∀ s ∈ G, s ≤ lo t ∨ hi t ≤ s := by
    intro t ht htG
    have hl := hlo_mem t ht
    have hr := hhi_mem t ht
    refine ⟨lt_of_le_of_ne hl.2 fun he => htG (he ▸ hl.1),
      lt_of_le_of_ne hr.2 fun he => htG (he.symm ▸ hr.1), fun s hs => ?_⟩
    rcases le_total s t with hst | hst
    · exact Or.inl (hlo_ge t s hs hst)
    · exact Or.inr (hhi_le t s hs hst)
  have hH_between : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ G → h (lo t) < H t ∧ H t < h (hi t) := by
    intro t ht htG
    obtain ⟨hlt, hth, -⟩ := hgap t ht htG
    have hd : 0 < hi t - lo t := by linarith
    have hc : 0 < h (hi t) - h (lo t) :=
      sub_pos.mpr (hmono (hlo_mem t ht).1 (hhi_mem t ht).1 (hlt.trans hth))
    have hpos : 0 < (t - lo t) * (h (hi t) - h (lo t)) / (hi t - lo t) :=
      div_pos (mul_pos (by linarith) hc) hd
    have hlt1 : (t - lo t) * (h (hi t) - h (lo t)) / (hi t - lo t) < h (hi t) - h (lo t) := by
      rw [div_lt_iff₀ hd]
      nlinarith
    constructor
    · change h (lo t) < h (lo t) + _
      linarith
    · change h (lo t) + _ < h (hi t)
      linarith
  have hsame : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ G → ∀ t' ∈ Ioo (lo t) (hi t),
      lo t' = lo t ∧ hi t' = hi t := by
    intro t ht htG t' ht'
    obtain ⟨-, -, hsep⟩ := hgap t ht htG
    have hloG := (hlo_mem t ht).1
    have hhiG := (hhi_mem t ht).1
    have ht'I : t' ∈ Icc (0 : ℝ) 1 :=
      ⟨(hGI hloG).1.trans ht'.1.le, ht'.2.le.trans (hGI hhiG).2⟩
    have h1 := hlo_mem t' ht'I
    have h2 := hhi_mem t' ht'I
    constructor
    · rcases hsep (lo t') h1.1 with h3 | h3
      · exact le_antisymm h3 (hlo_ge t' (lo t) hloG ht'.1.le)
      · exact absurd (h3.trans h1.2) (not_le.mpr ht'.2)
    · rcases hsep (hi t') h2.1 with h3 | h3
      · exact absurd (h3.trans_lt ht'.1) (not_lt.mpr h2.2)
      · exact le_antisymm (hhi_le t' (hi t) hhiG ht'.2.le) h3
  have hstrict : StrictMonoOn H (Icc 0 1) := by
    intro t₁ ht₁ t₂ ht₂ hlt
    by_cases g₁ : t₁ ∈ G <;> by_cases g₂ : t₂ ∈ G
    · rw [hH_of_mem t₁ g₁, hH_of_mem t₂ g₂]
      exact hmono g₁ g₂ hlt
    · calc H t₁ = h t₁ := hH_of_mem t₁ g₁
        _ ≤ h (lo t₂) := hmonoG g₁ (hlo_mem t₂ ht₂).1 (hlo_ge t₂ t₁ g₁ hlt.le)
        _ < H t₂ := (hH_between t₂ ht₂ g₂).1
    · calc H t₁ < h (hi t₁) := (hH_between t₁ ht₁ g₁).2
        _ ≤ h t₂ := hmonoG (hhi_mem t₁ ht₁).1 g₂ (hhi_le t₁ t₂ g₂ hlt.le)
        _ = H t₂ := (hH_of_mem t₂ g₂).symm
    · by_cases hin : t₂ < hi t₁
      · obtain ⟨hlt₁, hth₁, -⟩ := hgap t₁ ht₁ g₁
        obtain ⟨hl, hh⟩ := hsame t₁ ht₁ g₁ t₂ ⟨hlt₁.trans hlt, hin⟩
        have hd : 0 < hi t₁ - lo t₁ := by linarith
        have hc : 0 < h (hi t₁) - h (lo t₁) :=
          sub_pos.mpr (hmono (hlo_mem t₁ ht₁).1 (hhi_mem t₁ ht₁).1 (hlt₁.trans hth₁))
        change h (lo t₁) + (t₁ - lo t₁) * (h (hi t₁) - h (lo t₁)) / (hi t₁ - lo t₁) <
          h (lo t₂) + (t₂ - lo t₂) * (h (hi t₂) - h (lo t₂)) / (hi t₂ - lo t₂)
        rw [hl, hh]
        have hmul : (t₁ - lo t₁) * (h (hi t₁) - h (lo t₁)) <
            (t₂ - lo t₁) * (h (hi t₁) - h (lo t₁)) :=
          mul_lt_mul_of_pos_right (by linarith) hc
        have := div_lt_div_of_pos_right hmul hd
        linarith
      · rw [not_lt] at hin
        calc H t₁ < h (hi t₁) := (hH_between t₁ ht₁ g₁).2
          _ ≤ h (lo t₂) := hmonoG (hhi_mem t₁ ht₁).1 (hlo_mem t₂ ht₂).1
              (hlo_ge t₂ (hi t₁) (hhi_mem t₁ ht₁).1 hin)
          _ < H t₂ := (hH_between t₂ ht₂ g₂).1
  have hmaps : MapsTo H (Icc 0 1) (Icc 0 1) := by
    intro t ht
    by_cases htG : t ∈ G
    · rw [hH_of_mem t htG]
      exact ⟨hh0 ▸ hmonoG h0 htG (hGI htG).1, hh1 ▸ hmonoG htG h1 (hGI htG).2⟩
    · obtain ⟨hlow, hup⟩ := hH_between t ht htG
      have hloG := (hlo_mem t ht).1
      have hhiG := (hhi_mem t ht).1
      have e1 : 0 ≤ h (lo t) := hh0 ▸ hmonoG h0 hloG (hGI hloG).1
      have e2 : h (hi t) ≤ 1 := hh1 ▸ hmonoG hhiG h1 (hGI hhiG).2
      exact ⟨by linarith, by linarith⟩
  have hsurj : SurjOn H (Icc 0 1) (Icc 0 1) := by
    intro y hy
    have hbA : BddAbove (h '' G ∩ Iic y) := ⟨y, fun _ hs => hs.2⟩
    have hbB : BddBelow (h '' G ∩ Ici y) := ⟨y, fun _ hs => hs.2⟩
    have hc := (hcl.inter isClosed_Iic).csSup_mem ⟨0, ⟨0, h0, hh0⟩, hy.1⟩ hbA
    have hd := (hcl.inter isClosed_Ici).csInf_mem ⟨1, ⟨1, h1, hh1⟩, hy.2⟩ hbB
    set c := sSup (h '' G ∩ Iic y) with hc_def
    set d := sInf (h '' G ∩ Ici y) with hd_def
    have hcge : ∀ z ∈ h '' G, z ≤ y → z ≤ c := fun z hz hzy => le_csSup hbA ⟨hz, hzy⟩
    have hdle : ∀ z ∈ h '' G, y ≤ z → d ≤ z := fun z hz hzy => csInf_le hbB ⟨hz, hzy⟩
    obtain ⟨α, hαG, hαc⟩ := hc.1
    obtain ⟨β, hβG, hβd⟩ := hd.1
    by_cases hyc : c = y
    · exact ⟨α, hGI hαG, by rw [hH_of_mem α hαG, hαc, hyc]⟩
    by_cases hyd : d = y
    · exact ⟨β, hGI hβG, by rw [hH_of_mem β hβG, hβd, hyd]⟩
    have hcy : c < y := lt_of_le_of_ne hc.2 hyc
    have hyd' : y < d := lt_of_le_of_ne hd.2 (Ne.symm hyd)
    have hαβ : α < β := (hmono.lt_iff_lt hαG hβG).mp (by rw [hαc, hβd]; linarith)
    have hnone : ∀ s ∈ G, s ≤ α ∨ β ≤ s := by
      intro s hs
      by_contra hcon
      rw [not_or, not_le, not_le] at hcon
      have e1 : c < h s := hαc ▸ hmono hαG hs hcon.1
      have e2 : h s < d := hβd ▸ hmono hs hβG hcon.2
      rcases le_total (h s) y with hsy | hsy
      · exact absurd (hcge (h s) ⟨s, hs, rfl⟩ hsy) (not_le.mpr e1)
      · exact absurd (hdle (h s) ⟨s, hs, rfl⟩ hsy) (not_le.mpr e2)
    have hdc : 0 < d - c := by linarith
    have hβα : 0 < β - α := by linarith
    set t := α + (y - c) * (β - α) / (d - c) with ht_def
    have hfrac : 0 < (y - c) * (β - α) / (d - c) :=
      div_pos (mul_pos (by linarith) hβα) hdc
    have hfrac' : (y - c) * (β - α) / (d - c) < β - α := by
      rw [div_lt_iff₀ hdc]
      nlinarith
    have hαt : α < t := by linarith
    have htβ : t < β := by linarith
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨(hGI hαG).1.trans hαt.le, htβ.le.trans (hGI hβG).2⟩
    have htG : t ∉ G := fun htG => (hnone t htG).elim (fun e => absurd e (not_le.mpr hαt))
      (fun e => absurd e (not_le.mpr htβ))
    have hlo : lo t = α := by
      have e1 : α ≤ lo t := hlo_ge t α hαG hαt.le
      have e2 := hlo_mem t htI
      rcases hnone (lo t) e2.1 with e3 | e3
      · exact le_antisymm e3 e1
      · exact absurd (e3.trans e2.2) (not_le.mpr htβ)
    have hhi : hi t = β := by
      have e1 : hi t ≤ β := hhi_le t β hβG htβ.le
      have e2 := hhi_mem t htI
      rcases hnone (hi t) e2.1 with e3 | e3
      · exact absurd (e2.2.trans e3) (not_le.mpr hαt)
      · exact le_antisymm e1 e3
    refine ⟨t, htI, ?_⟩
    change h (lo t) + (t - lo t) * (h (hi t) - h (lo t)) / (hi t - lo t) = y
    rw [hlo, hhi, hαc, hβd]
    have hta : t - α = (y - c) * (β - α) / (d - c) := by rw [ht_def]; ring
    rw [hta]
    field_simp
    ring
  have himage : H '' Icc 0 1 = Icc 0 1 := Subset.antisymm hmaps.image_subset hsurj
  refine ⟨H, hstrict, himage, hH_of_mem, ?_⟩
  let Hs : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t => ⟨H t, hmaps t.2⟩
  have hHs : StrictMono Hs := fun a b hab => hstrict a.2 b.2 hab
  have hHsurj : Function.Surjective Hs := by
    intro y
    obtain ⟨t, ht, hty⟩ := hsurj y.2
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  have hcont : Continuous Hs := (StrictMono.orderIsoOfSurjective Hs hHs hHsurj).continuous
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hcont

theorem strictMonoOn_or_strictAntiOn_of_between {T : Set ℝ} {g : ℝ → ℝ} (hinj : InjOn g T)
    (hbtw : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a < b → b < c →
      (g a < g b ∧ g b < g c) ∨ (g c < g b ∧ g b < g a)) :
    StrictMonoOn g T ∨ StrictAntiOn g T := by
  have tri : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, u < v → v < w →
      (g u < g v ↔ g u < g w) ∧ (g v < g w ↔ g u < g w) := by
    intro u hu v hv w hw huv hvw
    rcases hbtw u hu v hv w hw huv hvw with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨iff_of_true e1 (e1.trans e2), iff_of_true e2 (e1.trans e2)⟩
    · exact ⟨iff_of_false (not_lt.mpr e2.le) (not_lt.mpr (e1.trans e2).le),
        iff_of_false (not_lt.mpr e1.le) (not_lt.mpr (e1.trans e2).le)⟩
  have extL : ∀ u ∈ T, ∀ v ∈ T, ∀ u' ∈ T, u' ≤ u → u < v → (g u < g v ↔ g u' < g v) := by
    intro u hu v hv u' hu' hle hlt
    rcases eq_or_lt_of_le hle with rfl | hlt'
    · exact Iff.rfl
    · exact (tri u' hu' u hu v hv hlt' hlt).2
  have extR : ∀ u ∈ T, ∀ v ∈ T, ∀ v' ∈ T, v ≤ v' → u < v → (g u < g v ↔ g u < g v') := by
    intro u hu v hv v' hv' hle hlt
    rcases eq_or_lt_of_le hle with rfl | hlt'
    · exact Iff.rfl
    · exact (tri u hu v hv v' hv' hlt hlt').1
  have key : ∀ a ∈ T, ∀ b ∈ T, ∀ x ∈ T, ∀ y ∈ T, a < b → x < y →
      (g a < g b ↔ g x < g y) := by
    intro a ha b hb x hx y hy hab hxy
    have hL : min a x ∈ T := by
      rcases min_choice a x with e | e <;> rw [e] <;> assumption
    have hR : max b y ∈ T := by
      rcases max_choice b y with e | e <;> rw [e] <;> assumption
    have e1 := extL a ha b hb (min a x) hL (min_le_left a x) hab
    have e2 := extR (min a x) hL b hb (max b y) hR (le_max_left b y)
      ((min_le_left a x).trans_lt hab)
    have e3 := extL x hx y hy (min a x) hL (min_le_right a x) hxy
    have e4 := extR (min a x) hL y hy (max b y) hR (le_max_right b y)
      ((min_le_right a x).trans_lt hxy)
    exact (e1.trans e2).trans (e3.trans e4).symm
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnm, hna⟩ := hcon
  simp only [StrictMonoOn, StrictAntiOn, not_forall, not_lt] at hnm hna
  obtain ⟨a, ha, b, hb, hab, hba⟩ := hnm
  obtain ⟨x, hx, y, hy, hxy, hxy'⟩ := hna
  have hba' : g b < g a := lt_of_le_of_ne hba fun e => (ne_of_lt hab) (hinj ha hb e.symm)
  have hxy'' : g x < g y := lt_of_le_of_ne hxy' fun e => (ne_of_lt hxy) (hinj hx hy e)
  exact (not_lt.mpr hba'.le) ((key a ha b hb x hx y hy hab hxy).mpr hxy'')

end DifferentialGeometry.Topology
