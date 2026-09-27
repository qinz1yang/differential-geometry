/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.InteriorAccess
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalArcBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem mem_closure_crosscut_inter_side {Q A C R : Set Plane} {x : Plane}
    (hR : IsPLBall 2 R) (hCR : C ⊆ frontier R)
    (hRQ : frontier R ⊆ frontier Q ∪ C) (hx : x ∈ interior Q)
    (hcross : HasPLCurveCrossingOnAt univ A C x) :
    x ∈ closure (A ∩ interior R) := by
  obtain ⟨q, hq⟩ := hR
  have hb : q '' stdSimplexBoundary 2 = frontier R := hq.image_stdSimplexBoundary
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ q '' stdSimplexBoundary 2 ↔ y ∈ C := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [hb]
    exact ⟨fun hyR => (hRQ hyR).resolve_left (fun hyQ => hyQ.2 hy), fun hyC => hCR hyC⟩
  have h := hcross.mem_closure_inter_diskInterior hq (subset_univ R) hlocal
  rwa [hb, self_sdiff_frontier] at h

private theorem exists_crosscut_bypass_of_ordered_intersections
    {Q A C : Set Plane} {a b c d : Plane} (hQ : IsPLBall 2 Q)
    (hA : Schoenflies.IsCrosscut (frontier Q) A a b)
    (hC : Schoenflies.IsCrosscut (frontier Q) C c d)
    (γ : ℝ → Plane) (hγ : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγA : γ '' Icc 0 1 = A) (hγ0 : γ 0 = a) (hγ1 : γ 1 = b)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs : s < 1)
    (hAC : A ∩ C = {γ r, γ s})
    (hcr : HasPLCurveCrossingOnAt univ A C (γ r))
    (hcs : HasPLCurveCrossingOnAt univ A C (γ s)) :
    ∃ A' : Set Plane, IsPLBall 1 A' ∧
      Schoenflies.IsCrosscut (frontier Q) A' a b ∧ Disjoint A' C := by
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.le, (hrs.trans hs).le⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨(hr.trans hrs).le, hs.le⟩
  have hγint : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ interior Q := by
    intro t ht
    rw [hQ.interior_eq_inside_frontier]
    apply hA.sdiff_subset
    refine ⟨hγA ▸ mem_image_of_mem γ ⟨ht.1.le, ht.2.le⟩, ?_⟩
    intro he
    rcases he with he | he
    · have ht0 := hγi ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hγ0.symm)
      exact ht.1.ne' ht0
    · have ht1 := hγi ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ (he.trans hγ1.symm)
      exact ht.2.ne ht1
  have hCball : IsPLBall 1 C :=
    isPLBall_one_of_isArcBetween_of_isPolygonal hC.arc hC.polygonal
  obtain ⟨U, V, hU, hV, hUV, hiUV, hfU, hfV, hCU, hCV, -⟩ :=
    exists_isPLBall_pair_of_isCrosscut hQ hCball hC
  have hUQ : U ⊆ Q := hUV ▸ subset_union_left
  have hVQ : V ⊆ Q := hUV ▸ subset_union_right
  have hUIV : Disjoint U (interior V) := by
    refine disjoint_left.mpr fun x hxU hxV => ?_
    exact (hCV (hiUV ▸ ⟨hxU, interior_subset hxV⟩)).2 hxV
  have hVIU : Disjoint V (interior U) := by
    refine disjoint_left.mpr fun x hxV hxU => ?_
    exact (hCU (hiUV ▸ ⟨interior_subset hxU, hxV⟩)).2 hxU
  have hdis : Disjoint (interior U) (interior V) := hUIV.mono_left interior_subset
  have hcover : interior Q \ C ⊆ interior U ∪ interior V := by
    rintro x ⟨hxQ, hxC⟩
    have hxUV : x ∈ U ∪ V := hUV.symm ▸ interior_subset hxQ
    have hnotU : x ∉ frontier U := fun hx =>
      (hfU hx).elim (fun h => h.2 hxQ) hxC
    have hnotV : x ∉ frontier V := fun hx =>
      (hfV hx).elim (fun h => h.2 hxQ) hxC
    exact hxUV.elim (fun hx => Or.inl ((mem_interior_iff_notMem_frontier hx).mpr hnotU))
      (fun hx => Or.inr ((mem_interior_iff_notMem_frontier hx).mpr hnotV))
  have hside : ∀ i j : ℝ, Ioo i j ⊆ Ioo 0 1 →
      (∀ t ∈ Ioo i j, t ≠ r ∧ t ≠ s) →
      γ '' Ioo i j ⊆ interior U ∨ γ '' Ioo i j ⊆ interior V := by
    intro i j hij hoff
    have hconn : IsPreconnected (γ '' Ioo i j) :=
      isPreconnected_Ioo.image γ (hγ.mono (hij.trans Ioo_subset_Icc_self))
    apply hconn.subset_or_subset isOpen_interior isOpen_interior hdis
    rintro _ ⟨t, ht, rfl⟩
    apply hcover
    refine ⟨hγint t (hij ht), ?_⟩
    intro htC
    have hp : γ t ∈ ({γ r, γ s} : Set Plane) :=
      hAC ▸ ⟨hγA ▸ mem_image_of_mem γ (Ioo_subset_Icc_self (hij ht)), htC⟩
    rcases hp with hp | hp
    · exact (hoff t ht).1 (hγi (Ioo_subset_Icc_self (hij ht)) hrI hp)
    · exact (hoff t ht).2 (hγi (Ioo_subset_Icc_self (hij ht)) hsI hp)
  have hleft := hside 0 r (fun _ ht => ⟨ht.1, ht.2.trans (hrs.trans hs)⟩)
    (fun t ht => ⟨ht.2.ne, (ht.2.trans hrs).ne⟩)
  have hmiddle := hside r s (fun _ ht => ⟨hr.trans ht.1, ht.2.trans hs⟩)
    (fun t ht => ⟨ht.1.ne', ht.2.ne⟩)
  have hright := hside s 1 (fun _ ht => ⟨(hr.trans hrs).trans ht.1, ht.2⟩)
    (fun t ht => ⟨(hrs.trans ht.1).ne', ht.1.ne'⟩)
  have hclosedSub : ∀ {R : Set Plane}, IsClosed R → ∀ {i j : ℝ}, i < j →
      Icc i j ⊆ Icc 0 1 → γ '' Ioo i j ⊆ R → γ '' Icc i j ⊆ R := by
    intro R hR i j hij hI hsub
    rintro _ ⟨t, ht, rfl⟩
    apply closure_minimal hsub hR
    apply ((hγ t (hI ht)).mono (Ioo_subset_Icc_self.trans hI)).mem_closure_image
    rw [closure_Ioo hij.ne]
    exact ht
  have hclU : γ r ∈ closure (A ∩ interior U) ∧ γ s ∈ closure (A ∩ interior U) :=
    ⟨mem_closure_crosscut_inter_side hU hCU hfU (hγint r ⟨hr, hrs.trans hs⟩) hcr,
      mem_closure_crosscut_inter_side hU hCU hfU (hγint s ⟨hr.trans hrs, hs⟩) hcs⟩
  have hclV : γ r ∈ closure (A ∩ interior V) ∧ γ s ∈ closure (A ∩ interior V) :=
    ⟨mem_closure_crosscut_inter_side hV hCV hfV (hγint r ⟨hr, hrs.trans hs⟩) hcr,
      mem_closure_crosscut_inter_side hV hCV hfV (hγint s ⟨hr.trans hrs, hs⟩) hcs⟩
  have hopposite : ∀ R S : Set Plane, IsClosed R → Disjoint R (interior S) →
      γ r ∈ closure (A ∩ interior S) → γ s ∈ closure (A ∩ interior S) →
      γ '' Ioo r s ⊆ interior R →
      (¬ γ '' Ioo 0 r ⊆ interior R) ∧ (¬ γ '' Ioo s 1 ⊆ interior R) := by
    intro R S hR hRS hclR hclS hmid
    have hm := hclosedSub hR hrs (fun _ ht => ⟨hr.le.trans ht.1, ht.2.trans hs.le⟩)
      (hmid.trans interior_subset)
    constructor
    · intro hl
      have hl' := hclosedSub hR hr (fun _ ht => ⟨ht.1, ht.2.trans hrI.2⟩)
        (hl.trans interior_subset)
      have htailc : IsClosed (γ '' Icc s 1) :=
        (isCompact_Icc.image_of_continuousOn (hγ.mono
          (fun _ ht => ⟨hsI.1.trans ht.1, ht.2⟩))).isClosed
      have htail : A ∩ interior S ⊆ γ '' Icc s 1 := by
        rintro x ⟨hxA, hxS⟩
        obtain ⟨t, ht, rfl⟩ := hγA.symm ▸ hxA
        by_cases hts : s ≤ t
        · exact ⟨t, ⟨hts, ht.2⟩, rfl⟩
        · exfalso
          apply disjoint_left.mp hRS _ hxS
          by_cases htr : t ≤ r
          · exact hl' ⟨t, ⟨ht.1, htr⟩, rfl⟩
          · exact hm ⟨t, ⟨(not_le.mp htr).le, (not_le.mp hts).le⟩, rfl⟩
      obtain ⟨t, ht, htr⟩ := closure_minimal htail htailc hclR
      have htr' := hγi ⟨hsI.1.trans ht.1, ht.2⟩ hrI htr
      exact (not_le_of_gt hrs) (htr' ▸ ht.1)
    · intro hright'
      have hr' := hclosedSub hR hs (fun _ ht => ⟨hsI.1.trans ht.1, ht.2⟩)
        (hright'.trans interior_subset)
      have htailc : IsClosed (γ '' Icc 0 r) :=
        (isCompact_Icc.image_of_continuousOn (hγ.mono
          (fun _ ht => ⟨ht.1, ht.2.trans hrI.2⟩))).isClosed
      have htail : A ∩ interior S ⊆ γ '' Icc 0 r := by
        rintro x ⟨hxA, hxS⟩
        obtain ⟨t, ht, rfl⟩ := hγA.symm ▸ hxA
        by_cases htr : t ≤ r
        · exact ⟨t, ⟨ht.1, htr⟩, rfl⟩
        · exfalso
          apply disjoint_left.mp hRS _ hxS
          by_cases hts : s ≤ t
          · exact hr' ⟨t, ⟨hts, ht.2⟩, rfl⟩
          · exact hm ⟨t, ⟨(not_le.mp htr).le, (not_le.mp hts).le⟩, rfl⟩
      obtain ⟨t, ht, hts⟩ := closure_minimal htail htailc hclS
      have hts' := hγi ⟨ht.1, ht.2.trans hrI.2⟩ hsI hts
      exact (not_le_of_gt hrs) (hts' ▸ ht.2)
  have hends : (a ∈ U ∧ b ∈ U) ∨ (a ∈ V ∧ b ∈ V) := by
    have hendpoints : ∀ R : Set Plane, IsClosed R →
        γ '' Ioo 0 r ⊆ interior R → γ '' Ioo s 1 ⊆ interior R → a ∈ R ∧ b ∈ R := by
      intro R hR hl hr'
      have hl' := hclosedSub hR hr (fun _ ht => ⟨ht.1, ht.2.trans hrI.2⟩)
        (hl.trans interior_subset)
      have hr'' := hclosedSub hR hs (fun _ ht => ⟨hsI.1.trans ht.1, ht.2⟩)
        (hr'.trans interior_subset)
      exact ⟨hγ0 ▸ hl' ⟨0, ⟨le_rfl, hr.le⟩, rfl⟩,
        hγ1 ▸ hr'' ⟨1, ⟨hs.le, le_rfl⟩, rfl⟩⟩
    rcases hmiddle with hmidU | hmidV
    · obtain ⟨hl, hr'⟩ := hopposite U V hU.isPolyhedron.isClosed hUIV hclV.1 hclV.2 hmidU
      exact Or.inr (hendpoints V hV.isPolyhedron.isClosed
        (hleft.resolve_left hl) (hright.resolve_left hr'))
    · obtain ⟨hl, hr'⟩ := hopposite V U hV.isPolyhedron.isClosed hVIU hclU.1 hclU.2 hmidV
      exact Or.inl (hendpoints U hU.isPolyhedron.isClosed
        (hleft.resolve_right hl) (hright.resolve_right hr'))
  have haC : a ∉ C := by
    intro ha
    have hae : a ∈ ({γ r, γ s} : Set Plane) := hAC ▸ ⟨hA.arc.left_mem, ha⟩
    rcases hae with hae | hae
    · exact hA.left_mem.2 (hae.symm ▸ hγint r ⟨hr, hrs.trans hs⟩)
    · exact hA.left_mem.2 (hae.symm ▸ hγint s ⟨hr.trans hrs, hs⟩)
  have hbC : b ∉ C := by
    intro hb
    have hbe : b ∈ ({γ r, γ s} : Set Plane) := hAC ▸ ⟨hA.arc.right_mem, hb⟩
    rcases hbe with hbe | hbe
    · exact hA.right_mem.2 (hbe.symm ▸ hγint r ⟨hr, hrs.trans hs⟩)
    · exact hA.right_mem.2 (hbe.symm ▸ hγint s ⟨hr.trans hrs, hs⟩)
  have hbuild : ∀ R : Set Plane, IsPLBall 2 R → R ⊆ Q → C ⊆ frontier R →
      a ∈ R → b ∈ R → ∃ A' : Set Plane, IsPLBall 1 A' ∧
        Schoenflies.IsCrosscut (frontier Q) A' a b ∧ Disjoint A' C := by
    intro R hR hRQ hCR ha hb
    have haF : a ∈ frontier R := by
      rw [hR.isPolyhedron.isClosed.frontier_eq]
      exact ⟨ha, fun hai => hA.left_mem.2 (interior_mono hRQ hai)⟩
    have hbF : b ∈ frontier R := by
      rw [hR.isPolyhedron.isClosed.frontier_eq]
      exact ⟨hb, fun hbi => hA.right_mem.2 (interior_mono hRQ hbi)⟩
    obtain ⟨A', hA'⟩ := hR.exists_isCrosscut haF hbF hA.arc.ne
    have hcore : A' \ {a, b} ⊆ interior R := by
      rw [hR.interior_eq_inside_frontier]
      exact hA'.sdiff_subset
    refine ⟨A', isPLBall_one_of_isArcBetween_of_isPolygonal hA'.arc hA'.polygonal,
      ⟨hA.curve, hA'.arc, hA'.polygonal, hA.left_mem, hA.right_mem, ?_⟩, ?_⟩
    · rw [← hQ.interior_eq_inside_frontier]
      exact hcore.trans (interior_mono hRQ)
    · refine disjoint_left.mpr fun x hxA hxC => ?_
      by_cases hxe : x ∈ ({a, b} : Set Plane)
      · rcases hxe with rfl | rfl
        · exact haC hxC
        · exact hbC hxC
      · exact (hCR hxC).2 (hcore ⟨hxA, hxe⟩)
  exact hends.elim (fun h => hbuild U hU hUQ hCU h.1 h.2)
    (fun h => hbuild V hV hVQ hCV h.1 h.2)

theorem exists_isCrosscut_disjoint_of_two_crossings
    {Q A C : Set Plane} {a b c d p q : Plane} (hQ : IsPLBall 2 Q)
    (hA : Schoenflies.IsCrosscut (frontier Q) A a b)
    (hC : Schoenflies.IsCrosscut (frontier Q) C c d)
    (hAC : A ∩ C = {p, q}) (hpq : p ≠ q)
    (hpQ : p ∈ interior Q) (hqQ : q ∈ interior Q)
    (hcp : HasPLCurveCrossingOnAt univ A C p)
    (hcq : HasPLCurveCrossingOnAt univ A C q) :
    ∃ A' : Set Plane, IsPLBall 1 A' ∧
      Schoenflies.IsCrosscut (frontier Q) A' a b ∧ Disjoint A' C := by
  obtain ⟨γ, hγ, hγi, hγA, hγ0, hγ1⟩ := hA.arc
  have hpA : p ∈ A := (hAC.symm ▸ (mem_insert p {q})).1
  have hqA : q ∈ A := (hAC.symm ▸ (mem_insert_of_mem p (mem_singleton q))).1
  obtain ⟨r, hrI, hγr⟩ := hγA.symm ▸ hpA
  obtain ⟨s, hsI, hγs⟩ := hγA.symm ▸ hqA
  have hparam : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ interior Q → t ∈ Ioo 0 1 := by
    intro t ht hti
    constructor
    · by_contra hle
      have ht0 : t = 0 := le_antisymm (not_lt.mp hle) ht.1
      exact hA.left_mem.2 (by simpa only [ht0, hγ0] using hti)
    · by_contra hle
      have ht1 : t = 1 := le_antisymm ht.2 (not_lt.mp hle)
      exact hA.right_mem.2 (by simpa only [ht1, hγ1] using hti)
  have hr := hparam r hrI (hγr.symm ▸ hpQ)
  have hs := hparam s hsI (hγs.symm ▸ hqQ)
  have hrs : r ≠ s := fun hrs => hpq (hγr.symm.trans ((congrArg γ hrs).trans hγs))
  have hAC' : A ∩ C = {γ r, γ s} := by rw [hγr, hγs]; exact hAC
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · exact exists_crosscut_bypass_of_ordered_intersections hQ hA hC γ hγ hγi hγA hγ0 hγ1
      r s hr.1 hrs hs.2 hAC' (hγr.symm ▸ hcp) (hγs.symm ▸ hcq)
  · apply exists_crosscut_bypass_of_ordered_intersections hQ hA hC γ hγ hγi hγA hγ0 hγ1
      s r hs.1 hsr hr.2
    · rw [pair_comm]
      exact hAC'
    · exact hγs.symm ▸ hcq
    · exact hγr.symm ▸ hcp

end DifferentialGeometry.Topology.PiecewiseLinear
