/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.GeneralCrosscut
import DifferentialGeometry.External.Schoenflies.Graph.VertexSquares

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_isCutPair_inter_closed_eq_singleton {C F : Set Plane} {v : Plane}
    (hC : IsJordanCurve C) (hF : IsClosed F) (hCF : (C ∩ F).Nonempty)
    (hv : v ∈ C) (hvF : v ∉ F) :
    ∃ p ∈ F, ∃ A B, IsCutPair C v p A B ∧ A ∩ F = {p} := by
  obtain ⟨q, hqC, hqF⟩ := hCF
  have hvq : v ≠ q := fun heq => hvF (heq ▸ hqF)
  obtain ⟨A, B, hcut⟩ := exists_isCutPair hC hv hqC hvq
  obtain ⟨f, hf, hi, himage, hf0, hf1⟩ := hcut.fst
  obtain ⟨t, ht, _, htF, hbefore⟩ := exists_first_mem hf hF
    one_mem_I (hf1.symm ▸ hqF)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    apply hvF
    simpa only [← heq, hf0] using htF)
  let P := f '' Icc 0 t
  let T := f '' Icc t 1
  have hPI : Icc 0 t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
  have hTI : Icc t 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht.1 le_rfl
  have hPA : P ⊆ A := himage ▸ image_mono hPI
  have hTA : T ⊆ A := himage ▸ image_mono hTI
  have hfirst : P ∩ F = {f t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hsF⟩
      have hst : s = t := le_antisymm hs.2 (not_lt.mp (fun hlt => hbefore s (hPI hs) hlt hsF))
      exact congrArg f hst
    · exact singleton_subset_iff.mpr ⟨⟨t, ⟨ht.1, le_rfl⟩, rfl⟩, htF⟩
  by_cases ht1 : t = 1
  · subst t
    refine ⟨q, hqF, A, B, hcut, ?_⟩
    simpa only [P, himage, hf1] using hfirst
  have htt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have harcP : IsArcBetween P v (f t) := by
    simpa only [uIcc_of_le htpos.le, hf0] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I ht htpos.ne
  have harcT : IsArcBetween T (f t) q := by
    simpa only [uIcc_of_le ht.2, hf1] using
      isArcBetween_subarc_of_injOn_I hf hi ht one_mem_I ht1
  have hBT : ∀ x ∈ B, x ∈ T → x = q := by
    intro x hxB hxT
    have hx := hcut.inter_eq.subset ⟨hTA hxT, hxB⟩
    rcases hx with rfl | rfl
    · obtain ⟨s, hs, hsf⟩ := hxT
      have hs0 : s = 0 := hi (hTI hs) zero_mem_I (hsf.trans hf0.symm)
      exact (not_le_of_gt htpos (hs0 ▸ hs.1)).elim
    · rfl
  have hinterPB : P ∩ B = {v} := by
    apply Subset.antisymm
    · intro x hx
      rcases hcut.inter_eq.subset ⟨hPA hx.1, hx.2⟩ with rfl | rfl
      · rfl
      · obtain ⟨s, hs, hsf⟩ := hx.1
        have hs1 : s = 1 := hi (hPI hs) one_mem_I (hsf.trans hf1.symm)
        exact (not_le_of_gt htt (hs1 ▸ hs.2)).elim
    · exact singleton_subset_iff.mpr ⟨harcP.left_mem, hcut.snd.left_mem⟩
  have hinterPT : P ∩ T = {f t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, ⟨u, hu, hus⟩⟩
      have hsu : s = u := hi (hPI hs) (hTI hu) hus.symm
      exact congrArg f (le_antisymm hs.2 (hsu ▸ hu.1))
    · exact singleton_subset_iff.mpr ⟨harcP.right_mem, harcT.left_mem⟩
  have hcover : P ∪ T = A := by
    change f '' Icc 0 t ∪ f '' Icc t 1 = A
    rw [← image_union, Icc_union_Icc_eq_Icc ht.1 ht.2]
    exact himage
  refine ⟨f t, htF, P, B ∪ T, ⟨harcP, hcut.snd.concatenate harcT.reverse hBT, ?_, ?_⟩, hfirst⟩
  · calc
      P ∪ (B ∪ T) = (P ∪ T) ∪ B := by ac_rfl
      _ = C := by rw [hcover, hcut.union_eq]
  · rw [inter_union_distrib_left, hinterPB, hinterPT]
    ext x
    simp [or_comm]

end DifferentialGeometry.Topology.PlanarJordan
