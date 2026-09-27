/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set Topology

namespace Schoenflies

theorem IsArcBetween.mem_nhdsWithin_of_subarc {A B : Set Plane} {p q r : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p r) (hBA : B ⊆ A) :
    B ∈ 𝓝[A] p := by
  obtain ⟨f, hfc, hfi, hfA, hf0, _⟩ := hA
  obtain ⟨t, ht, hft⟩ := hfA.symm ▸ hBA hB.right_mem
  have hpr : p ≠ r := by
    obtain ⟨g, _, hgi, _, hg0, hg1⟩ := hB
    exact fun h => zero_ne_one (hgi zero_mem_I one_mem_I (hg0.trans (h.trans hg1.symm)))
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (fun heq => hpr (hf0.symm.trans (heq ▸ hft)))
  have hsub : f '' Icc 0 t ⊆ A := by
    rw [← hfA]
    exact image_mono (Icc_subset_Icc le_rfl ht.2)
  have harc : IsArcBetween (f '' Icc 0 t) p r := by
    simpa only [uIcc_of_le htpos.le, hf0, hft] using
      isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I ht htpos.ne
  have heq := hB.eq_of_subset_arc harc ⟨f, hfc, hfi, hfA, hf0, rfl⟩ hBA hsub
  obtain ⟨ε, hε, hball⟩ := exists_ball_inter_subset_image hfc hfi
    (U := Iio t) isOpen_Iio ⟨0, ⟨htpos, zero_mem_I⟩, hf0⟩
  apply Filter.mem_of_superset (inter_mem_nhdsWithin A (Metric.ball_mem_nhds p hε))
  intro x hx
  rw [heq]
  obtain ⟨s, hs, rfl⟩ := hball ⟨hx.2, hfA.symm ▸ hx.1⟩
  exact mem_image_of_mem f ⟨hs.2.1, hs.1.le⟩

theorem exists_polygonal_subarcs_of_polygonal_subsets
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {P Q : Set Plane} {p q : Plane}
    (hpArc : IsArcBetween P (f 0) p) (hqArc : IsArcBetween Q (f 1) q)
    (hpPoly : IsPolygonal P) (hqPoly : IsPolygonal Q)
    (hpSub : P ⊆ f '' unitInterval) (hqSub : Q ⊆ f '' unitInterval) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      IsPolygonal (f '' Icc 0 a) ∧ IsPolygonal (f '' Icc b 1) := by
  have hp : f 0 ≠ p := by
    obtain ⟨g, _, hgi, _, hg0, hg1⟩ := hpArc
    exact fun heq => zero_ne_one (hgi zero_mem_I one_mem_I (hg0.trans (heq.trans hg1.symm)))
  have hq : f 1 ≠ q := by
    obtain ⟨g, _, hgi, _, hg0, hg1⟩ := hqArc
    exact fun heq => zero_ne_one (hgi zero_mem_I one_mem_I (hg0.trans (heq.trans hg1.symm)))
  have hA : IsArcBetween (f '' unitInterval) (f 0) (f 1) := ⟨f, hf, hi, rfl, rfl, rfl⟩
  obtain ⟨u, hu, hfu⟩ := hpSub hpArc.right_mem
  obtain ⟨v, hv, hfv⟩ := hqSub hqArc.right_mem
  have hu0 : 0 < u := lt_of_le_of_ne hu.1 fun h => hp (h ▸ hfu)
  have hv1 : v < 1 := lt_of_le_of_ne hv.2 fun h => hq (h ▸ hfv)
  have hL : f '' Icc 0 u = P := by
    have hLA : IsArcBetween (f '' Icc 0 u) (f 0) p := by
      simpa only [uIcc_of_le hu.1, hfu] using
        isArcBetween_subarc_of_injOn_I hf hi zero_mem_I hu hu0.ne
    exact hLA.eq_of_subset_arc hpArc hA
      (image_mono (Icc_subset_Icc_right hu.2)) hpSub
  have hR : f '' Icc v 1 = Q := by
    have hRA : IsArcBetween (f '' Icc v 1) q (f 1) := by
      simpa only [uIcc_of_le hv.2, hfv] using
        isArcBetween_subarc_of_injOn_I hf hi hv one_mem_I hv1.ne
    exact hRA.reverse.eq_of_subset_arc hqArc hA
      (image_mono (Icc_subset_Icc_left hv.1)) hqSub
  let a := u / 3
  let b := (v + 2) / 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have hab : a < b := by dsimp [a, b]; linarith [hu.2, hv.1]
  have haI : a ∈ unitInterval := ⟨ha.le, hab.le.trans hb.le⟩
  have hbI : b ∈ unitInterval := ⟨ha.le.trans hab.le, hb.le⟩
  have hau : a ≤ u := by dsimp [a]; linarith
  have hvb : v ≤ b := by dsimp [b]; linarith [hv.2]
  have hla : IsArcBetween (f '' Icc 0 a) (f 0) (f a) := by
    simpa only [uIcc_of_le ha.le] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I haI ha.ne
  have hrb : IsArcBetween (f '' Icc b 1) (f b) (f 1) := by
    simpa only [uIcc_of_le hb.le] using
      isArcBetween_subarc_of_injOn_I hf hi hbI one_mem_I hb.ne
  refine ⟨a, b, ha, hab, hb, ?_, ?_⟩
  · exact hla.isPolygonal_of_subset_arc hpArc hpPoly
      ((image_mono (Icc_subset_Icc_right hau)).trans hL.subset)
  · exact hrb.isPolygonal_of_subset_arc hqArc hqPoly
      ((image_mono (Icc_subset_Icc_left hvb)).trans hR.subset)

theorem exists_polygonal_subarcs_of_segment_subsets
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {p q : Plane} (hp : f 0 ≠ p) (hq : f 1 ≠ q)
    (hl : segment ℝ (f 0) p ⊆ f '' unitInterval)
    (hr : segment ℝ (f 1) q ⊆ f '' unitInterval) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      IsPolygonal (f '' Icc 0 a) ∧ IsPolygonal (f '' Icc b 1) :=
  exists_polygonal_subarcs_of_polygonal_subsets hf hi
    (isArcBetween_segment hp) (isArcBetween_segment hq)
    (isPolygonal_segment _ _) (isPolygonal_segment _ _) hl hr

end Schoenflies
