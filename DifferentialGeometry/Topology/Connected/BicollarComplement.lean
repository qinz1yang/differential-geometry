/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.Connected.BicollarSeparation
import Mathlib.Topology.Instances.Real.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology

private theorem exists_closed_pair_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {S W R : Set X} {ρ : X × ℝ → X}
    (hS : IsConnected S) (hSc : IsCompact S)
    (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    ∃ P Q : Set X, IsClosed P ∧ IsClosed Q ∧ P ∪ Q = W ∧ P ∩ Q = S ∧
      Disjoint R S ∧ IsConnected (R ∩ P) ∧ IsConnected (R ∩ Q) := by
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
  have hRPconn : IsConnected (R ∩ P) := by
    rw [hRP]
    exact (hS.prod isConnected_singleton).image ρ
      (hρ.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩))
  have hRQconn : IsConnected (R ∩ Q) := by
    rw [hRQ]
    exact (hS.prod isConnected_singleton).image ρ
      (hρ.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩))
  exact ⟨P, Q, hP, hQ, hPQ, hmeet, hRdis, hRPconn, hRQconn⟩

theorem connectedComponentIn_complement_inter_eq_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {N S W R : Set X} {ρ : X × ℝ → X}
    (hS : IsConnected S) (hSc : IsCompact S) (hR : IsClosed R)
    (hcover : R ∪ W = N) (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    {x : X} (hx : x ∈ R) :
    connectedComponentIn (N \ S) x ∩ R = connectedComponentIn R x := by
  obtain ⟨P, Q, hP, hQ, hPQ, hmeet, hRdis, hRPconn, hRQconn⟩ :=
    exists_closed_pair_of_bicollar hS hSc htrace hρ hbij hzero
  have hRU : R ⊆ N \ S := fun y hy =>
    ⟨hcover.subset (Or.inl hy), fun hyS => disjoint_left.mp hRdis hy hyS⟩
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
  have hBC : Disjoint B C := disjoint_left.mpr fun y hyB hyC =>
    y.property.2 (hmeet.subset ⟨hyB, hyC⟩)
  have hcoverU : A ∪ B ∪ C = univ := by
    change (((↑) : U → X) ⁻¹' R) ∪ (((↑) : U → X) ⁻¹' P) ∪
      (((↑) : U → X) ⁻¹' Q) = univ
    rw [union_assoc, ← preimage_union, hPQ, ← preimage_union, hcover]
    exact eq_univ_of_forall fun y => y.property.1
  let y : U := ⟨x, hRU hx⟩
  have hyA : y ∈ A := hx
  have hbig := connectedComponentIn_union_inter_eq (hA.union hB) hC
    (by rw [union_inter_distrib_right, hBC.inter_eq, union_empty]; exact hAC)
    (show y ∈ A ∪ B from Or.inl hyA)
  rw [hcoverU, connectedComponentIn_univ] at hbig
  have hsmall := connectedComponentIn_union_inter_eq hA hB hAB hyA
  have hcomp : connectedComponent y ∩ A = connectedComponentIn A y := by
    calc
      connectedComponent y ∩ A = (connectedComponent y ∩ (A ∪ B)) ∩ A := by
        ext z
        simp only [mem_inter_iff, mem_union]
        tauto
      _ = connectedComponentIn (A ∪ B) y ∩ A := congrArg (· ∩ A) hbig
      _ = connectedComponentIn A y := hsmall
  have hconn : IsPreconnected (connectedComponentIn (N \ S) x ∩ R) := by
    rw [connectedComponentIn_eq_image (hRU hx), ← image_inter_preimage]
    change IsPreconnected (((↑) : U → X) '' (connectedComponent y ∩ A))
    rw [hcomp]
    exact isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
  apply Subset.antisymm
  · exact hconn.subset_connectedComponentIn ⟨mem_connectedComponentIn (hRU hx), hx⟩
      inter_subset_right
  · exact fun z hz => ⟨connectedComponentIn_mono x hRU hz, connectedComponentIn_subset R x hz⟩

theorem isConnected_complement_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {N S W R : Set X} {ρ : X × ℝ → X}
    (hS : IsConnected S) (hSc : IsCompact S) (hR : IsClosed R)
    (hcover : R ∪ W = N) (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (hnonsep : IsPreconnected (N \ S)) : IsConnected R := by
  obtain ⟨P, -, -, -, -, -, hRdis, hRPconn, -⟩ :=
    exists_closed_pair_of_bicollar hS hSc htrace hρ hbij hzero
  obtain ⟨x, hxR, -⟩ := hRPconn.nonempty
  have hRU : R ⊆ N \ S := fun y hy =>
    ⟨hcover.subset (Or.inl hy), fun hyS => disjoint_left.mp hRdis hy hyS⟩
  have heq := connectedComponentIn_complement_inter_eq_of_bicollar hS hSc hR
    hcover htrace hρ hbij hzero hxR
  rw [hnonsep.connectedComponentIn (hRU hxR), inter_eq_right.mpr hRU] at heq
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hxR

theorem exists_mem_complement_connectedComponentIn_of_bicollar
    {X : Type*} [TopologicalSpace X] {N S W R : Set X} {ρ : X × ℝ → X}
    (hcover : R ∪ W = N) (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    {x : X} (hx : x ∈ N \ S) :
    ∃ y ∈ R, connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) y := by
  by_cases hxR : x ∈ R
  · exact ⟨x, hxR, rfl⟩
  have hxW : x ∈ W := (hcover.symm.subset hx.1).resolve_left hxR
  obtain ⟨z, hz, hzx⟩ := hbij.surjOn hxW
  have hz0 : z.2 ≠ 0 := by
    intro ht
    have heq : ρ z = z.1 := by
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hzero z.1 hz.1]
    exact hx.2 ((heq.symm.trans hzx) ▸ hz.1)
  have hfinish (T : Set ℝ) (hT : IsPreconnected T) (hTsub : T ⊆ Icc (-1 : ℝ) 1)
      (hTzero : ∀ t ∈ T, t ≠ 0) (hzT : z.2 ∈ T)
      (t : ℝ) (ht : t ∈ T) (htend : t = -1 ∨ t = 1) :
      ∃ y ∈ R, connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) y := by
    let f : ℝ → X := fun t => ρ (z.1, t)
    have hdom : MapsTo (fun t : ℝ => (z.1, t)) T (S ×ˢ Icc (-1 : ℝ) 1) :=
      fun _ hs => ⟨hz.1, hTsub hs⟩
    have hf : ContinuousOn f T := hρ.comp
      (continuous_const.prodMk continuous_id).continuousOn hdom
    have hmap : MapsTo f T (N \ S) := by
      intro u hu
      refine ⟨hcover.subset (Or.inr (hbij.mapsTo (hdom hu))), ?_⟩
      intro hfS
      have heq := hbij.injOn (hdom hu) ⟨hfS, by norm_num, by norm_num⟩
        (hzero (f u) hfS).symm
      exact hTzero u hu (congrArg Prod.snd heq)
    have hximage : x ∈ f '' T := ⟨z.2, hzT, hzx⟩
    have hsub := (hT.image f hf).subset_connectedComponentIn hximage hmap.image_subset
    have hyR : f t ∈ R := (htrace.symm.subset ⟨(z.1, t), ⟨hz.1, htend⟩, rfl⟩).1
    exact ⟨f t, hyR, connectedComponentIn_eq (hsub (mem_image_of_mem f ht))⟩
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · exact hfinish (Ico (-1 : ℝ) 0) isPreconnected_Ico
      (fun _ ht => ⟨ht.1, ht.2.le.trans zero_le_one⟩)
      (fun _ ht => ht.2.ne) ⟨hz.2.1, hneg⟩ (-1) ⟨le_rfl, by norm_num⟩ (Or.inl rfl)
  · exact hfinish (Ioc (0 : ℝ) 1) isPreconnected_Ioc
      (fun _ ht => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans ht.1.le, ht.2⟩)
      (fun _ ht => ht.1.ne') ⟨hpos, hz.2.2⟩ 1 ⟨by norm_num, le_rfl⟩ (Or.inr rfl)

theorem isConnected_complement_iff_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {N S W R : Set X} {ρ : X × ℝ → X}
    (hS : IsConnected S) (hSc : IsCompact S) (hR : IsClosed R)
    (hcover : R ∪ W = N) (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1}))
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    IsConnected R ↔ IsPreconnected (N \ S) := by
  refine ⟨?_, isConnected_complement_of_bicollar hS hSc hR hcover htrace hρ hbij hzero⟩
  intro hRc
  obtain ⟨-, -, -, -, -, -, hRdis, -, -⟩ :=
    exists_closed_pair_of_bicollar hS hSc htrace hρ hbij hzero
  have hRU : R ⊆ N \ S := fun y hy =>
    ⟨hcover.subset (Or.inl hy), fun hyS => disjoint_left.mp hRdis hy hyS⟩
  obtain ⟨a, ha⟩ := hRc.nonempty
  have hRsub := hRc.isPreconnected.subset_connectedComponentIn ha hRU
  have hUsub : N \ S ⊆ connectedComponentIn (N \ S) a := by
    intro x hx
    obtain ⟨y, hyR, hxy⟩ :=
      exists_mem_complement_connectedComponentIn_of_bicollar hcover htrace hρ hbij hzero hx
    have heq := hxy.trans (connectedComponentIn_eq (hRsub hyR)).symm
    exact heq ▸ mem_connectedComponentIn hx
  rw [Subset.antisymm hUsub (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn

theorem exists_connectedComponentIn_pair_complement_of_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {N S W R : Set X} {ρ : X × ℝ → X}
    [LocallyConnectedSpace N] (hN : IsPreconnected N) (hS : IsConnected S)
    (hSc : IsCompact S) (hR : IsClosed R) (hcover : R ∪ W = N)
    (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1})) (hW : W ∈ 𝓝ˢ[N] S)
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    ∃ a ∈ R, ∃ b ∈ R, ∀ x ∈ R,
      connectedComponentIn R x = connectedComponentIn R a ∨
      connectedComponentIn R x = connectedComponentIn R b := by
  obtain ⟨-, -, -, -, -, -, hRdis, -, -⟩ :=
    exists_closed_pair_of_bicollar hS hSc htrace hρ hbij hzero
  have hRU : R ⊆ N \ S := fun y hy =>
    ⟨hcover.subset (Or.inl hy), fun hyS => disjoint_left.mp hRdis hy hyS⟩
  obtain ⟨u, hu, v, hv, hpair⟩ := exists_connectedComponentIn_pair_sdiff_of_bicollar
    hN hS hSc.isClosed (subset_union_right.trans hcover.subset) hW hρ hbij hzero
  obtain ⟨a, ha, hua⟩ :=
    exists_mem_complement_connectedComponentIn_of_bicollar hcover htrace hρ hbij hzero hu
  obtain ⟨b, hb, hvb⟩ :=
    exists_mem_complement_connectedComponentIn_of_bicollar hcover htrace hρ hbij hzero hv
  have hcomp {x : X} (hx : x ∈ R) :=
    connectedComponentIn_complement_inter_eq_of_bicollar hS hSc hR hcover htrace hρ hbij hzero hx
  refine ⟨a, ha, b, hb, fun x hx => ?_⟩
  rcases hpair x (hRU hx) with hxu | hxv
  · exact Or.inl ((hcomp hx).symm.trans
      ((congrArg (· ∩ R) (hxu.trans hua)).trans (hcomp ha)))
  · exact Or.inr ((hcomp hx).symm.trans
      ((congrArg (· ∩ R) (hxv.trans hvb)).trans (hcomp hb)))

end DifferentialGeometry.Topology
