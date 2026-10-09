/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open Set Topology

namespace DifferentialGeometry.Topology

private theorem exists_interval_between_finite_marks {M : Set ℝ} (hM : M.Finite)
    {t : ℝ} (ht : t ∈ Ioo 0 1) (htM : t ∉ M) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < t ∧ t < b ∧ b ≤ 1 ∧
      (a ∈ M ∨ a = 0) ∧ (b ∈ M ∨ b = 1) ∧ Disjoint (Ioo a b) M := by
  let L := insert (0 : ℝ) {s ∈ M | s < t}
  let H := insert (1 : ℝ) {s ∈ M | t < s}
  have hL : L.Finite := (hM.subset (sep_subset _ _)).insert 0
  have hH : H.Finite := (hM.subset (sep_subset _ _)).insert 1
  have ha := (insert_nonempty (0 : ℝ) {s ∈ M | s < t}).csSup_mem hL
  have hb := (insert_nonempty (1 : ℝ) {s ∈ M | t < s}).csInf_mem hH
  have hLo : ∀ s ∈ L, s ≤ sSup L := fun s hs => le_csSup hL.bddAbove hs
  have hHi : ∀ s ∈ H, sInf H ≤ s := fun s hs => csInf_le hH.bddBelow hs
  have hat : sSup L < t := by
    rcases ha with ha | ha
    · rw [ha]
      exact ht.1
    · exact ha.2
  have htb : t < sInf H := by
    rcases hb with hb | hb
    · rw [hb]
      exact ht.2
    · exact hb.2
  refine ⟨sSup L, sInf H, hLo 0 (Or.inl rfl), hat, htb, hHi 1 (Or.inl rfl),
    ha.elim Or.inr (fun h => Or.inl h.1), hb.elim Or.inr (fun h => Or.inl h.1), ?_⟩
  apply Set.disjoint_left.mpr
  intro s hs hsM
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hs.1.not_ge (hLo s (Or.inr ⟨hsM, hst⟩))
  · exact htM (hst ▸ hsM)
  · exact hs.2.not_ge (hHi s (Or.inr ⟨hsM, hts⟩))

theorem exists_subinterval_of_finite_boundary_preimage
    {X : Type*} [TopologicalSpace X] {η : ℝ → X} {T D J : Set X}
    (hη : ContinuousOn η (Icc 0 1)) (hηT : MapsTo η (Icc 0 1) T) (hD : IsClosed D)
    (hboundary : D ∩ closure (T \ D) = J)
    (hfinite : (Icc (0 : ℝ) 1 ∩ η ⁻¹' J).Finite)
    (h0 : η 0 ∈ J ∨ η 0 ∉ D) (h1 : η 1 ∈ J ∨ η 1 ∉ D)
    {t : ℝ} (ht : t ∈ Ioo 0 1) (hηt : η t ∈ D \ J) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < t ∧ t < b ∧ b ≤ 1 ∧ η a ∈ J ∧ η b ∈ J ∧
      MapsTo η (Ioo a b) (D \ J) := by
  obtain ⟨a, b, ha0, hat, htb, hb1, haM, hbM, hfree⟩ :=
    exists_interval_between_finite_marks hfinite ht (fun h => hηt.2 h.2)
  have hab : a < b := hat.trans htb
  have hIoo : Ioo a b ⊆ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨ha0.trans hs.1.le, hs.2.le.trans hb1⟩
  have hIcc : Icc a b ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨ha0.trans hs.1, hs.2.trans hb1⟩
  let Y := η '' Ioo a b
  have hY : IsPreconnected Y := isPreconnected_Ioo.image η (hη.mono hIoo)
  have hYT : Y ⊆ T := by
    rintro x ⟨s, hs, rfl⟩
    exact hηT (hIoo hs)
  have hYJ : Disjoint Y J := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hxJ
    exact Set.disjoint_left.mp hfree hs ⟨hIoo hs, hxJ⟩
  have hcover : Y ⊆ D ∪ closure (T \ D) := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hYT hx, hxD⟩)
  have hdis : Y ∩ (D ∩ closure (T \ D)) = ∅ := by
    rw [hboundary]
    exact hYJ.inter_eq
  have hYD : Y ⊆ D := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (T \ D))
        hD isClosed_closure hcover hdis with h | h
    · exact h
    · exact (hηt.2 (hboundary.subset ⟨hηt.1, h ⟨t, ⟨hat, htb⟩, rfl⟩⟩)).elim
  have hcl : ∀ s ∈ Icc a b, η s ∈ D := by
    intro s hs
    have hscl : s ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hs
    have hηcl := ((hη s (hIcc hs)).mono hIoo).mem_closure_image hscl
    exact closure_minimal hYD hD hηcl
  have haD : η a ∈ D := hcl a ⟨le_rfl, hab.le⟩
  have hbD : η b ∈ D := hcl b ⟨hab.le, le_rfl⟩
  refine ⟨a, b, ha0, hat, htb, hb1, ?_, ?_, fun s hs => ?_⟩
  · rcases haM with haM | ha
    · exact haM.2
    · rw [ha] at haD ⊢
      exact h0.resolve_right (fun h => h haD)
  · rcases hbM with hbM | hb
    · exact hbM.2
    · rw [hb] at hbD ⊢
      exact h1.resolve_right (fun h => h hbD)
  · exact ⟨hYD ⟨s, hs, rfl⟩, fun hsJ => Set.disjoint_left.mp hYJ ⟨s, hs, rfl⟩ hsJ⟩

end DifferentialGeometry.Topology
