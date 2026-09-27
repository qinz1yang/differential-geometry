/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSphereImageSplitRim
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatesOfLocallyEventuallyEq
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceSubsetOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.EdgeCollarFamily
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.InitialSurfaceSeparates
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionBallPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.ReducedDiskPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerExists
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalDescentSequence
import DifferentialGeometry.Topology.PiecewiseLinear.Section26ThreeSurfaces
import DifferentialGeometry.Topology.PiecewiseLinear.Section28Annuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section30Separation
import DifferentialGeometry.Topology.PiecewiseLinear.Section30Torus
import DifferentialGeometry.Topology.PiecewiseLinear.Section31CanonicalConfiguration

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

end Leaves

section Assemblies

open Classical in
theorem moise322_of_moise307 (h307 : Moise307) : Moise322 := by
  intro K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub hWfr hWK
  set P' : E3 := h (({u, v} : Finset E3).centroid ℝ id) with hP'
  have hcard : ({u, v} : Finset E3).card = 2 := Finset.card_pair huv
  obtain ⟨Bu, hBuc, hBucon, hBuu, hBuC, hBuD, hBuF⟩ :=
    exists_compact_connected_to_freeFace ht hu he hcard (Finset.mem_insert_self u {v})
  obtain ⟨Bv, hBvc, hBvcon, hBvv, hBvC, hBvD, hBvF⟩ :=
    exists_compact_connected_to_freeFace ht hv he hcard
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  obtain ⟨φ, Pt, Dp, Dpint, J, A, S, T, S'', T'', htw, hZ⟩ :=
    exists_canonicalTower ht hu hv huv he hP' hW hWint hWsub hWfr hWK h307
      (hBuc.isClosed.union hBvc.isClosed) (Disjoint.union_left hBuD hBvD)
  have havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3) := fun i =>
    (hZ i).mono_right (insert_subset_iff.mpr
      ⟨mem_union_left _ hBuu, singleton_subset_iff.mpr (mem_union_right _ hBvv)⟩)
  obtain ⟨hcl₁, hsep₁⟩ := separates_initialSurface ht hu hv huv he hP' htw havoid
  obtain ⟨H, B, Jlo, Jhi, M, hch, -, hMcl, hMsep, hMP, hLcl, hloc⟩ :=
    exists_descentSequence ht hu hv huv he hP' htw havoid hcl₁ hsep₁ moise303 moise286 moise267
      moise314
  have hP'U : P' ∈ annularChain H B P' := by
    change P' ∈ (⋃ i, H i ∪ B i) ∪ {P'}
    exact mem_union_right _ (mem_singleton _)
  have hsing : ∀ y : E3,
      IsPreconnected (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {y}) := by
    intro y
    refine Set.Subsingleton.isPreconnected ?_
    intro a ha b hb
    exact Subtype.ext ((mem_singleton_iff.mp (mem_preimage.mp ha)).trans
      (mem_singleton_iff.mp (mem_preimage.mp hb)).symm)
  have hsepU : Separates
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' annularChain H B P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}) := by
    have : LocallyPathConnectedSpace (interior (h '' C u ∪ h '' C v)) :=
      isOpen_interior.locallyPathConnectedSpace
    refine separates_of_locally_eventually_eq (p := ⟨P', htw.centerMemInterior⟩) hMcl hMsep
      (fun n => hMP n) (hsing (h u)) (hsing (h v)) hLcl hP'U ?_
    rintro ⟨x, hxI⟩ hxp
    have hxP : x ≠ P' := fun hx => hxp (Subtype.ext hx)
    obtain ⟨U, hU, n₀, hn⟩ := hloc x hxI hxP
    refine ⟨((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' U,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU, n₀, fun n hn' => ?_⟩
    simp only [← preimage_inter, hn n hn']
  obtain ⟨hcell, hlp, hclos, hpairs⟩ :=
    isOpenTopologicalCell_annularChain ht hu hv huv he hP' htw hch hsepU
  have hsph : IsTopologicalSphere 1 (h '' Dbd {u, v}) :=
    isTopologicalSphere_image_splitRim ht he hcard
  have hmid : ({u, v} : Finset E3).centroid ℝ id ∈ D {u, v} ∩ K.space := by
    rw [ht.splitMidpoint he hcard]
    exact mem_singleton _
  have hP'K : P' ∈ h '' K.space := ⟨_, hmid.2, hP'.symm⟩
  have hP'D : P' ∈ h '' D {u, v} := ⟨_, hmid.1, hP'.symm⟩
  have hP'W : P' ∈ W := by
    have hmem : P' ∈ W ∩ h '' K.space := by
      rw [hWK]
      exact mem_singleton _
    exact hmem.1
  have hDbdD : h '' Dbd {u, v} ⊆ h '' D {u, v} := by
    refine image_mono ?_
    rw [← ht.splitProper _ he hcard]
    exact inter_subset_left
  have hDbdfr : h '' Dbd {u, v} ⊆ frontier (h '' C u ∪ h '' C v) := by
    rw [← hWfr]
    exact inter_subset_right
  have hUI : annularChain H B P' ⊆ interior (h '' C u ∪ h '' C v) := by
    change (⋃ i, H i ∪ B i) ∪ {P'} ⊆ _
    refine union_subset (iUnion_subset fun i => union_subset ?_ ?_)
      (singleton_subset_iff.mpr htw.centerMemInterior)
    · exact (hch.halfSubsetTorus i).trans (htw.subsetInterior _)
    · exact (hch.bridgeSubset i).trans (union_subset
        (union_subset (htw.subsetInterior _) (htw.subsetInterior _)) (htw.subsetInterior _))
  have hUW : annularChain H B P' ∪ h '' Dbd {u, v} ⊆ W := by
    refine union_subset ?_ ?_
    · change (⋃ i, H i ∪ B i) ∪ {P'} ⊆ W
      refine union_subset (iUnion_subset fun i => union_subset ?_ ?_)
        (singleton_subset_iff.mpr hP'W)
      · exact (hch.halfSubsetTorus i).trans (htw.subsetW _)
      · exact (hch.bridgeSubset i).trans (union_subset
          (union_subset (htw.subsetW _) (htw.subsetW _)) (htw.subsetW _))
    · rw [← hWfr]
      exact inter_subset_left
  have hEK : (annularChain H B P' ∪ h '' Dbd {u, v}) ∩ h '' K.space = {P'} := by
    refine Subset.antisymm (fun x hx => ?_)
      (singleton_subset_iff.mpr ⟨mem_union_left _ hP'U, hP'K⟩)
    rw [← hWK]
    exact ⟨hUW hx.1, hx.2⟩
  have hE : IsPseudoCell (annularChain H B P' ∪ h '' Dbd {u, v}) (annularChain H B P')
      (h '' Dbd {u, v}) P' :=
    ⟨rfl, hcell, hsph, disjoint_interior_frontier.mono hUI hDbdfr, hclos, hP'U, hlp⟩
  have hdisjE : ∀ Bx : Set E3, Bx ⊆ Bu ∪ Bv → Disjoint Bx (h '' D {u, v}) →
      Disjoint Bx (annularChain H B P' ∪ h '' Dbd {u, v}) := by
    intro Bx hBx hBxD
    have hBxS : ∀ i, Disjoint Bx (φ '' S i) := fun i => ((hZ i).mono_right hBx).symm
    refine disjoint_union_right.mpr ⟨?_, hBxD.mono_right hDbdD⟩
    change Disjoint Bx ((⋃ i, H i ∪ B i) ∪ {P'})
    refine disjoint_union_right.mpr ⟨disjoint_iUnion_right.mpr fun i => ?_,
      disjoint_singleton_right.mpr fun hP => disjoint_left.mp hBxD hP hP'D⟩
    refine disjoint_union_right.mpr ⟨(hBxS _).mono_right (hch.halfSubsetTorus i), ?_⟩
    exact Disjoint.mono_right (hch.bridgeSubset i) (disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hBxS _, hBxS _⟩, hBxS _⟩)
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hd, hcover, hpre, hf₁, hf₂, hF₁, hF₂⟩ :=
    exists_twoComponents_of_pseudoCell ht hu hv huv he hP' hWsub hWfr hE rfl hUW hsepU hpairs
      ⟨hBuc, hBucon, hBuu, hBuC, hdisjE Bu subset_union_left hBuD, hBuF⟩
      ⟨hBvc, hBvcon, hBvv, hBvC, hdisjE Bv subset_union_right hBvD, hBvF⟩
  exact ⟨_, _, _, U₁, U₂, hE, rfl, hUW, hsepU, hEK, hU₁, hU₂, hc₁, hc₂, hd, hcover, hpre,
    hf₁, hf₂, hF₁, hF₂⟩

theorem moise321_of_moise307 (h307 : Moise307) : Moise321 := by
  intro K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub hWfr hWK
  obtain ⟨Ec, Eint, Ebd, -, -, hpc, hbd, hsub, hsep, hK, -⟩ :=
    moise322_of_moise307 h307 K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub
      hWfr hWK
  exact ⟨Ec, Eint, Ebd, hpc, hbd, hsub, hsep, hK⟩

open Classical in
theorem moise323_of_moise307 (h307 : Moise307) : Moise323 := by
  intro K N C D Dbd h N' ht V hV
  obtain ⟨W, hW⟩ := exists_edgeCollarFamily ht V hV
  have hall : ∀ e : Finset E3, ∃ Ec Eint Ebd : Set E3, e ∈ K.faces → e.card = 2 →
      ∃ u v : E3, u ∈ K.vertices ∧ v ∈ K.vertices ∧ u ≠ v ∧ e = {u, v} ∧
        SplitsDualCellsAlong K N C Dbd h (W e) Ec Eint Ebd u v := by
    intro e
    by_cases hedge : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨he, hc⟩ := hedge
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
      have hu : u ∈ K.vertices := K.down_closed he
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self u {v}))
        (Finset.singleton_nonempty u)
      have hv : v ∈ K.vertices := K.down_closed he
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)))
        (Finset.singleton_nonempty v)
      obtain ⟨hWcl, hWint, hWK, hWpair, -, -⟩ := hW _ he hc
      obtain ⟨hWsub, hWfr⟩ := hWpair u (Finset.mem_insert_self u {v}) v
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) huv
      obtain ⟨Ec, Eint, Ebd, hS⟩ :=
        (moise322_of_moise307 h307).exists_splitsDualCellsAlong ht hu hv huv he hWcl
          hWint hWsub hWfr hWK
      exact ⟨Ec, Eint, Ebd, fun _ _ => ⟨u, v, hu, hv, huv, rfl, hS⟩⟩
    · exact ⟨∅, ∅, ∅, fun he hc => absurd ⟨he, hc⟩ hedge⟩
  choose Ec Eint Ebd hE using hall
  obtain ⟨hone, hcover, hedge, hnonedge⟩ := isHandleDecomposition_of_edgeCollars ht hW hE
  have hsub := handlePiece_subset_of_edgeCollars ht hW hE
  refine ⟨Ec, Eint, Ebd, handlePiece K N' Ec h,
    ⟨ht, ?_, ?_, ?_, ?_, ?_, hone, hcover, fun _ _ => rfl, hedge, hnonedge⟩, ?_⟩
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.1
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.2.1
  · intro e he hc
    obtain ⟨u, v, hu, hv, huv, rfl, hS⟩ := hE e he hc
    obtain ⟨-, -, -, hWpair, -, -⟩ := hW _ he hc
    obtain ⟨hWsub, hWfr⟩ := hWpair u (Finset.mem_insert_self u {v}) v
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) huv
    have hY : h '' C u ∪ h '' C v ⊆ N' := by
      rw [ht.imageEq, ← image_union]
      exact image_mono (union_subset (ht.dualCell_subset hu) (ht.dualCell_subset hv))
    refine Subset.antisymm ?_ ?_
    · intro x hx
      have hxW : x ∈ W {u, v} := hS.2.2.1 hx.1
      have hxY : x ∈ h '' C u ∪ h '' C v := hWsub hxW
      have hxc : x ∈ closure (h '' C u ∪ h '' C v)ᶜ :=
        closure_mono (compl_subset_compl.mpr hY)
          (frontier_eq_closure_inter_closure.subset hx.2).2
      have hxfr : x ∈ frontier (h '' C u ∪ h '' C v) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hxY, hxc⟩
      rw [hS.2.1, ← hWfr]
      exact ⟨hxW, hxfr⟩
    · intro x hx
      have hxE : x ∈ Ec {u, v} := by
        rw [hS.1.carrierEq]
        exact Or.inr hx
      have hxN' : x ∈ N' := hY (hWsub (hS.2.2.1 hxE))
      have hN'cl : IsClosed N' := by
        rw [ht.imageEq]
        exact (ht.isCompact.image_of_continuousOn ht.continuousOn).isClosed
      refine ⟨hxE, ?_⟩
      rw [frontier, hN'cl.closure_eq]
      refine ⟨hxN', fun hint => ?_⟩
      rw [hS.2.1] at hx
      exact disjoint_left.mp (ht.disjoint_image_rim_interior he hc) hx hint
  · intro e he hc
    obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
    exact hS.2.2.2.2.1
  · intro e he hc f hf hfc hef
    obtain ⟨-, -, -, -, -, hdisj⟩ := hW e he hc
    refine (hdisj f hf hfc hef).mono ?_ ?_
    · obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE e he hc
      exact hS.2.2.1
    · obtain ⟨u, v, -, -, -, rfl, hS⟩ := hE f hf hfc
      exact hS.2.2.1
  · intro v hv
    refine (hsub v hv).trans (union_subset (subset_of_mem_nhdsSet (hV v hv))
      (iUnion₂_subset fun e he => ?_))
    obtain ⟨he₁, he₂, he₃⟩ := he
    obtain ⟨-, -, -, -, hVe, -⟩ := hW e he₁ he₂
    exact (hVe v he₃).2

theorem moise324 : Moise324 := by
  intro Ec Eint Ebd P hE δ hδ
  obtain ⟨Bl, Dc, Dcint, hBl, hBδ, hPB, hDc, hDcE, hDcδ, hPDc, hBE, hgp⟩ :=
    exists_generalPosition_ball_pseudoCell hE hδ
  obtain ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩ :=
    exists_reducedDisk_of_crossesPseudoCell hE hBl hPB hDc hDcE hPDc hBE hgp
      Metric.isOpen_ball hBδ hDcδ
  exact ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩

theorem moise322 : Moise322 :=
  moise322_of_moise307 moise307

theorem moise321 : Moise321 :=
  moise321_of_moise307 moise307

theorem moise323 : Moise323 :=
  moise323_of_moise307 moise307

end Assemblies

end DifferentialGeometry.Topology.PiecewiseLinear
