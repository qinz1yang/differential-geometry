/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellBallPush
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitLocalTrace
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_disk_push_of_coincident_patch {Ec Eint Ebd Γ D T Ω : Set E3}
    {P : E3} (hpc : IsPseudoCell Ec Eint Ebd P) {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ)
    (hD : IsPLBall 2 D) (hDΓ : D ⊆ r '' openSimplex (stdVertices 1))
    (hDE : D ⊆ Eint \ {P}) (hT : IsClosed T) (hDT : Disjoint D T)
    (hΓE : Γ ∩ Ec ⊆ D ∪ T) (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω) :
    ∃ (Γ' : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ' ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      Γ' ⊆ Ω ∧ Γ' ∩ Ec = (Γ \ D) ∩ Ec := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hΓ : IsPLBall 2 Γ := ⟨r, hr⟩
  let J := r '' stdSimplexBoundary 2
  have hJ : IsClosed J := hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed
  have hDsub : D ⊆ Γ := hDΓ.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hr.image_eq.subset)
  have hDJ : Disjoint D J := by
    apply disjoint_left.mpr
    intro x hx hxJ
    have := hDΓ hx
    rw [hr.image_openSimplex_stdVertices] at this
    exact this.2 hxJ
  let W := (Ω ∩ Tᶜ) ∩ Jᶜ
  have hW : IsOpen W := (hΩ.inter hT.isOpen_compl).inter hJ.isOpen_compl
  have hDW : D ⊆ W := fun x hx =>
    ⟨⟨hΓΩ (hDsub hx), disjoint_left.mp hDT hx⟩, disjoint_left.mp hDJ hx⟩
  obtain ⟨M, s, hs, hME, hMW, hDM, hag⟩ :=
    hpc.exists_disk_neighborhood hD hDE hW hDW
  have hM : IsPLBall 2 M := ⟨s, hs⟩
  have hDsubM : D ⊆ M := hDM.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hs.image_eq.subset)
  have hMEc : M ⊆ Ec := fun x hx => hpc.carrierEq.symm ▸ Or.inl (hME hx).1
  have hΓM : Γ ∩ M = D := by
    apply Subset.antisymm
    · intro x hx
      exact (hΓE ⟨hx.1, hMEc hx.2⟩).resolve_right (hMW hx.2).1.2
    · exact subset_inter hDsub hDsubM
  let V := {x | ∀ᶠ y in 𝓝 x, y ∈ M ↔ y ∈ Ec} ∩ W
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds.inter hW
  have hDV : D ⊆ V := fun x hx => ⟨hag x hx, hDW hx⟩
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  obtain ⟨F, hF, hFcard, hFM⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (hΓ.isPolyhedron.isCompact.union hM.isPolyhedron.isCompact).isBounded
  let K := simplexComplex F hF
  let _ : Finite K.faces := (simplexComplex_faces_finite F hF).to_subtype
  have hKspace : K.space = convexHull ℝ (F : Set E3) :=
    simplexComplex_space F hF (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent F hF hFcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex F := by
    rw [hKspace, interior_convexHull_eq_openSimplex hF (by omega)]
  have hΓint : Γ ⊆ interior K.space :=
    (subset_union_left.trans hFM).trans hint.symm.subset
  have hMint : M ⊆ interior K.space :=
    (subset_union_right.trans hFM).trans hint.symm.subset
  have hDint : D ⊆ interior K.space := hDsub.trans hΓint
  have hUnhds : V ∩ interior K.space ∈ 𝓝ˢ[K.space] D :=
    mem_nhdsSetWithin.mpr ⟨V ∩ interior K.space, hV.inter isOpen_interior,
      subset_inter hDV hDint, inter_subset_left⟩
  have hUdis : Disjoint (V ∩ interior K.space) (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact disjoint_interior_frontier.mono_left inter_subset_right
  have hlocal : Γ ∪ M ∈ 𝓝ˢ[Γ ∪ M] D :=
    mem_nhdsSetWithin.mpr ⟨univ, isOpen_univ, subset_univ D, inter_subset_right⟩
  obtain ⟨N, B, g, q₁, A₁, Δ₁, C', hBfin, -, hB, hDN, -, -,
      hNnhds, -, hg, -, -, -, hΔ₁, -, hfront, hinter, -, -, -, -, -, hΓB, -, -, -, -, -⟩ :=
    hK.exists_surface_split_local_traces_with_side_trace hD hr hs hDΓ hDM
      hDsub hDsubM hΓM (hΓint.trans interior_subset) (hMint.trans interior_subset)
      subset_union_left subset_union_right hlocal hUnhds hUdis
  let _ : Finite B.faces := hBfin.to_subtype
  have hNnhds' : ∀ x ∈ D, N ∈ 𝓝 x := by
    intro x hx
    have h := hNnhds x hx
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hDint hx))] at h
  have hDΔ₁ : Disjoint D Δ₁ := by
    apply disjoint_left.mpr
    intro x hx hxΔ₁
    have hxg : x ∈ g '' stdSimplexBoundary 2 :=
      hinter.subset ⟨⟨hDsubM hx, hDN hx⟩, hxΔ₁⟩
    apply hg.notMem_image_stdSimplexBoundary_of_mem_nhdsWithin hpc.isOpenCell
      (hDE hx).1 ?_ hxg
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨N ∩ {y | y ∈ M ↔ y ∈ Ec}, Filter.inter_mem (hNnhds' x hx) (hag x hx), ?_⟩
    rintro y ⟨⟨hyN, hy⟩, hyE⟩
    exact ⟨hy.mpr (hpc.carrierEq.symm ▸ Or.inl hyE), hyN⟩
  let O := (interior N ∩ V) \ Δ₁
  have hO : IsOpen O := (isOpen_interior.inter hV).sdiff hΔ₁.isPolyhedron.isClosed
  have hDO : D ⊆ O := fun x hx =>
    ⟨⟨mem_interior_iff_mem_nhds.mpr (hNnhds' x hx), hDV hx⟩,
      disjoint_left.mp hDΔ₁ hx⟩
  have hOV : O ⊆ V := inter_subset_left.trans inter_subset_right
  have hON : O ⊆ N := (inter_subset_left.trans inter_subset_left).trans interior_subset
  have hfrontO : O ∩ Ec = O ∩ frontier B.space := by
    rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim B
      hB.isCombinatorialManifoldWithBoundary, hfront]
    ext x
    constructor
    · rintro ⟨hxO, hxE⟩
      exact ⟨hxO, Or.inl ⟨(hOV hxO).1.self_of_nhds.mpr hxE, hON hxO⟩⟩
    · rintro ⟨hxO, hx | hx⟩
      · exact ⟨hxO, hMEc hx.1⟩
      · exact (hxO.2 hx).elim
  have hΓC : Γ ∩ O ⊆ B.space := fun x hx =>
    (hΓB.symm.subset ⟨hx.1, hON hx.2⟩).2
  have hΓD : Γ ∩ O ∩ Ec ⊆ D := fun x hx =>
    (hΓE ⟨hx.1.1, hx.2⟩).resolve_right (hOV hx.1.2).2.1.2
  have hJO : Disjoint (r '' stdSimplexBoundary 2) O :=
    disjoint_left.mpr fun x hxJ hxO => (hOV hxO).2.2 hxJ
  obtain ⟨Γ', q, hq, hqb, hΓ'sub, htrace⟩ :=
    hpc.exists_disk_push_of_ball_frontier hB hD.isPolyhedron.isCompact hDE hO hDO
      hfrontO hr hΓC hΓD hJO
  refine ⟨Γ', q, hq, hqb, hΓ'sub.trans (union_subset hΓΩ ?_), ?_⟩
  · exact hOV.trans (fun _ hx => hx.2.1.1)
  · rw [htrace]
    ext x
    constructor
    · rintro ⟨⟨hxΓ, hxO⟩, hxE⟩
      exact ⟨⟨hxΓ, fun hxD => hxO (hDO hxD)⟩, hxE⟩
    · rintro ⟨⟨hxΓ, hxD⟩, hxE⟩
      exact ⟨⟨hxΓ, fun hxO => hxD (hΓD ⟨⟨hxΓ, hxO⟩, hxE⟩)⟩, hxE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
