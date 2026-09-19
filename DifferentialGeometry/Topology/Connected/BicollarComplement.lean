/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.ClosedCover
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Connected complements of bicollars of nonseparating sets
-/

open Set

namespace DifferentialGeometry.Topology

theorem isConnected_complement_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {N S W R : Set X} {ρ : X × ℝ → X}
    (hS : IsConnected S) (hSc : IsCompact S) (hR : IsClosed R)
    (hcover : R ∪ W = N) (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (hnonsep : IsPreconnected (N \ S)) : IsConnected R := by
  let P := ρ '' (S ×ˢ Icc (-1 : ℝ) 0)
  let Q := ρ '' (S ×ˢ Icc (0 : ℝ) 1)
  have hneg : S ×ˢ Icc (-1 : ℝ) 0 ⊆ S ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans zero_le_one⟩
  have hpos : S ×ˢ Icc (0 : ℝ) 1 ⊆ S ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hx.2.1, hx.2.2⟩
  have hends : S ×ˢ {(-1 : ℝ), 1} ⊆ S ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hzS, ht⟩
    rcases ht with ht | ht
    · exact ⟨hzS, ht.symm ▸ ⟨le_rfl, by norm_num⟩⟩
    · exact ⟨hzS, ht.symm ▸ ⟨by norm_num, le_rfl⟩⟩
  have hP : IsClosed P := ((hSc.prod isCompact_Icc).image_of_continuousOn (hρ.mono hneg)).isClosed
  have hQ : IsClosed Q := ((hSc.prod isCompact_Icc).image_of_continuousOn (hρ.mono hpos)).isClosed
  have hPQ : P ∪ Q = W := by
    rw [show P = ρ '' (S ×ˢ Icc (-1 : ℝ) 0) from rfl,
      show Q = ρ '' (S ×ˢ Icc (0 : ℝ) 1) from rfl, ← image_union, ← prod_union,
      Icc_union_Icc_eq_Icc (by norm_num : (-1 : ℝ) ≤ 0) zero_le_one, hbij.image_eq]
  have hmeet : P ∩ Q = S := by
    rw [show P = ρ '' (S ×ˢ Icc (-1 : ℝ) 0) from rfl,
      show Q = ρ '' (S ×ˢ Icc (0 : ℝ) 1) from rfl, ← hbij.injOn.image_inter hneg hpos]
    have hdom : (S ×ˢ Icc (-1 : ℝ) 0) ∩ (S ×ˢ Icc (0 : ℝ) 1) = S ×ˢ {(0 : ℝ)} := by
      ext z
      simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
      constructor
      · exact fun hz => ⟨hz.1.1, le_antisymm hz.1.2.2 hz.2.2.1⟩
      · rintro ⟨hz, ht⟩
        rw [ht]
        exact ⟨⟨hz, by norm_num, le_rfl⟩, hz, le_rfl, zero_le_one⟩
    rw [hdom]
    apply Subset.antisymm
    · rintro x ⟨z, ⟨hz, ht⟩, rfl⟩
      change z.2 = 0 at ht
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hzero z.1 hz]
      exact hz
    · exact fun x hx => ⟨(x, 0), ⟨hx, rfl⟩, hzero x hx⟩
  have hinter (T : Set ℝ) (hT : T ⊆ Icc (-1 : ℝ) 1) :
      R ∩ ρ '' (S ×ˢ T) = ρ '' (S ×ˢ ({(-1 : ℝ), 1} ∩ T)) := by
    have hTW : ρ '' (S ×ˢ T) ⊆ W :=
      (image_mono (prod_mono Subset.rfl hT)).trans hbij.image_eq.subset
    calc
      R ∩ ρ '' (S ×ˢ T) = (R ∩ W) ∩ ρ '' (S ×ˢ T) := by
        ext x
        exact ⟨fun hx => ⟨⟨hx.1, hTW hx.2⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
      _ = ρ '' (S ×ˢ {(-1 : ℝ), 1}) ∩ ρ '' (S ×ˢ T) := by rw [htrace]
      _ = ρ '' ((S ×ˢ {(-1 : ℝ), 1}) ∩ (S ×ˢ T)) :=
        (hbij.injOn.image_inter hends (prod_mono Subset.rfl hT)).symm
      _ = ρ '' (S ×ˢ ({(-1 : ℝ), 1} ∩ T)) := by rw [prod_inter_prod, inter_self]
  have hRP : R ∩ P = ρ '' (S ×ˢ {(-1 : ℝ)}) := by
    have h := hinter (Icc (-1 : ℝ) 0) (Icc_subset_Icc le_rfl zero_le_one)
    have heq : {(-1 : ℝ), 1} ∩ Icc (-1 : ℝ) 0 = {(-1 : ℝ)} := by
      ext t
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_Icc]
      constructor
      · rintro ⟨ht | ht, hlo, hhi⟩
        · exact ht
        · linarith
      · rintro rfl
        norm_num
    rwa [heq] at h
  have hRQ : R ∩ Q = ρ '' (S ×ˢ {(1 : ℝ)}) := by
    have h := hinter (Icc (0 : ℝ) 1) (Icc_subset_Icc (by norm_num) le_rfl)
    have heq : {(-1 : ℝ), 1} ∩ Icc (0 : ℝ) 1 = {(1 : ℝ)} := by
      ext t
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_Icc]
      constructor
      · rintro ⟨ht | ht, hlo, hhi⟩
        · linarith
        · exact ht
      · rintro rfl
        norm_num
    rwa [heq] at h
  have hRdis : Disjoint R S := by
    apply disjoint_left.mpr
    intro x hxR hxS
    have hxW : x ∈ W := (hzero x hxS) ▸ hbij.mapsTo ⟨hxS, by norm_num, by norm_num⟩
    obtain ⟨z, hz, hzx⟩ := htrace.subset ⟨hxR, hxW⟩
    have heq := hbij.injOn (hends hz) ⟨hxS, by norm_num, by norm_num⟩
      (hzx.trans (hzero x hxS).symm)
    have ht := congrArg Prod.snd heq
    have hzends := hz.2
    rw [ht] at hzends
    norm_num at hzends
  have hRU : R ⊆ N \ S := fun x hx =>
    ⟨hcover.subset (Or.inl hx), fun hxS => disjoint_left.mp hRdis hx hxS⟩
  have hRPconn : IsConnected (R ∩ P) := by
    rw [hRP]
    exact (hS.prod isConnected_singleton).image ρ
      (hρ.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩))
  have hRQconn : IsConnected (R ∩ Q) := by
    rw [hRQ]
    exact (hS.prod isConnected_singleton).image ρ
      (hρ.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩))
  let U := N \ S
  let A := ((↑) : U → X) ⁻¹' R
  let B := ((↑) : U → X) ⁻¹' P
  let C := ((↑) : U → X) ⁻¹' Q
  have hA : IsClosed A := hR.preimage continuous_subtype_val
  have hB : IsClosed B := hP.preimage continuous_subtype_val
  have hC : IsClosed C := hQ.preimage continuous_subtype_val
  have hpreimage (T : Set X) (hTU : T ⊆ U) :
      IsPreconnected (((↑) : U → X) ⁻¹' T) ↔ IsPreconnected T := by
    rw [← _root_.Topology.IsInducing.subtypeVal.isPreconnected_image,
      Subtype.image_preimage_coe, inter_eq_right.mpr hTU]
  have hAB : IsPreconnected (A ∩ B) := by
    change IsPreconnected ((((↑) : U → X) ⁻¹' R) ∩ (((↑) : U → X) ⁻¹' P))
    rw [← preimage_inter]
    exact (hpreimage (R ∩ P) (inter_subset_left.trans hRU)).mpr hRPconn.isPreconnected
  have hAC : IsPreconnected (A ∩ C) := by
    change IsPreconnected ((((↑) : U → X) ⁻¹' R) ∩ (((↑) : U → X) ⁻¹' Q))
    rw [← preimage_inter]
    exact (hpreimage (R ∩ Q) (inter_subset_left.trans hRU)).mpr hRQconn.isPreconnected
  have hBC : Disjoint B C := disjoint_left.mpr fun x hxB hxC =>
    x.property.2 (hmeet.subset ⟨hxB, hxC⟩)
  have hcoverU : A ∪ B ∪ C = univ := by
    change (((↑) : U → X) ⁻¹' R) ∪ (((↑) : U → X) ⁻¹' P) ∪
      (((↑) : U → X) ⁻¹' Q) = univ
    rw [union_assoc, ← preimage_union, hPQ, ← preimage_union, hcover]
    exact eq_univ_of_forall fun x => x.property.1
  have hconnU : IsPreconnected (A ∪ B ∪ C) := by
    rw [hcoverU]
    let _ : PreconnectedSpace U := Subtype.preconnectedSpace hnonsep
    exact isPreconnected_univ
  have hconnAB : IsPreconnected (A ∪ B) :=
    isPreconnected_left_of_isClosed_union (hA.union hB) hC hconnU (by
      rw [union_inter_distrib_right, hBC.inter_eq, union_empty]
      exact hAC)
  have hconnA := isPreconnected_left_of_isClosed_union hA hB hconnAB hAB
  exact ⟨hRPconn.nonempty.mono inter_subset_left, (hpreimage R hRU).mp hconnA⟩

end DifferentialGeometry.Topology
