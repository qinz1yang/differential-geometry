/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import DifferentialGeometry.Topology.Connected.BicollarComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_component_pair_of_separating_annulus
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hKc : IsPreconnected K.space)
    {J W : Set E} (hJ : IsPLSphere 1 J) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hWnhds : W ∈ 𝓝ˢ[K.space] J)
    (hcover : W ∪ R.space = K.space)
    (htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hboundary : (boundaryComplex 2 R).space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ A B : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧ B.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsCombinatorialManifoldWithBoundary 2 B ∧
      IsConnected A.space ∧ IsConnected B.space ∧ Disjoint A.space B.space ∧
      A.space ∪ B.space = R.space ∧
      (boundaryComplex 2 A).space = ρ '' (J ×ˢ {(-1 : ℝ)}) ∧
      (boundaryComplex 2 B).space = ρ '' (J ×ˢ {(1 : ℝ)}) := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  have hρc := hρ.isPiecewiseAffineOn.continuousOn
  obtain ⟨a, ha, b, hb, hpair⟩ := Topology.exists_connectedComponentIn_pair_complement_of_bicollar
    hKc hJ.isConnected hJ.isPolyhedron.isCompact (isPolyhedron_space R).isClosed
    (by rwa [union_comm]) (by rwa [inter_comm]) hWnhds hρc hρ.bijOn hzero
  have hRnot : ¬ IsPreconnected R.space := fun hc => hsep
    ((Topology.isConnected_complement_iff_of_bicollar hJ.isConnected hJ.isPolyhedron.isCompact
      (isPolyhedron_space R).isClosed (by rwa [union_comm]) (by rwa [inter_comm])
      hρc hρ.bijOn hzero).mp ⟨⟨a, ha⟩, hc⟩)
  let A := restrict R (connectedComponentIn R.space a)
  let B := restrict R (connectedComponentIn R.space b)
  have hAfin : A.faces.Finite := restrict_faces_finite R _
  have hBfin : B.faces.Finite := restrict_faces_finite R _
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hA := hR.restrict_connectedComponentIn a
  have hB := hR.restrict_connectedComponentIn b
  have hAspace : A.space = connectedComponentIn R.space a := restrict_connectedComponentIn_space R a
  have hBspace : B.space = connectedComponentIn R.space b := restrict_connectedComponentIn_space R b
  have hAc : IsConnected A.space := hAspace.symm ▸ isConnected_connectedComponentIn_iff.mpr ha
  have hBc : IsConnected B.space := hBspace.symm ▸ isConnected_connectedComponentIn_iff.mpr hb
  have hAB : A.space ∪ B.space = R.space := by
    rw [hAspace, hBspace]
    apply Subset.antisymm (union_subset (connectedComponentIn_subset _ _)
      (connectedComponentIn_subset _ _))
    intro x hx
    rcases hpair x hx with hxa | hxb
    · exact Or.inl (hxa ▸ mem_connectedComponentIn hx)
    · exact Or.inr (hxb ▸ mem_connectedComponentIn hx)
  have hne : connectedComponentIn R.space a ≠ connectedComponentIn R.space b := by
    intro heq
    apply hRnot
    rw [← hAB, hAspace, hBspace, heq, union_self]
    exact isPreconnected_connectedComponentIn
  have hdis : Disjoint A.space B.space := by
    rw [hAspace, hBspace]
    exact disjoint_left.mpr fun _ hx hy =>
      hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm)
  have hAR : A.space ⊆ R.space := subset_union_left.trans hAB.subset
  have hBR : B.space ⊆ R.space := subset_union_right.trans hAB.subset
  have hAbd : (boundaryComplex 2 A).space = (boundaryComplex 2 R).space ∩ A.space :=
    (boundaryComplex_space_restrict_connectedComponentIn 2 R a).trans
      (congrArg ((boundaryComplex 2 R).space ∩ ·) hAspace.symm)
  have hBbd : (boundaryComplex 2 B).space = (boundaryComplex 2 R).space ∩ B.space :=
    (boundaryComplex_space_restrict_connectedComponentIn 2 R b).trans
      (congrArg ((boundaryComplex 2 R).space ∩ ·) hBspace.symm)
  have hRsub : R.space ⊆ K.space := subset_union_right.trans hcover.subset
  have hWclosed : IsClosed W := hρ.image_eq ▸
    ((hJ.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn hρc).isClosed
  have hcontact (M N : Set E) (hM : IsClosed M) (hN : IsClosed N)
      (hMne : M.Nonempty) (hNne : N.Nonempty) (hMN : Disjoint M N)
      (hMNcover : M ∪ N = R.space) : (M ∩ W).Nonempty := by
    have hMK : M ⊆ K.space := subset_union_left.trans (hMNcover.subset.trans hRsub)
    have hNK : N ⊆ K.space := subset_union_right.trans (hMNcover.subset.trans hRsub)
    obtain ⟨m, hm⟩ := hMne
    obtain ⟨n, hn⟩ := hNne
    have hcoverK : K.space ⊆ M ∪ (N ∪ W) := by
      rw [← union_assoc, hMNcover, union_comm, hcover]
    obtain ⟨z, -, hzM, hzNW⟩ := isPreconnected_closed_iff.mp hKc M (N ∪ W)
      hM (hN.union hWclosed) hcoverK ⟨m, hMK hm, hm⟩ ⟨n, hNK hn, Or.inl hn⟩
    exact ⟨z, hzM, hzNW.resolve_left (fun hzN => disjoint_left.mp hMN hzM hzN)⟩
  have hAW := hcontact A.space B.space (isPolyhedron_space A).isClosed
    (isPolyhedron_space B).isClosed hAc.nonempty hBc.nonempty hdis hAB
  have hBW := hcontact B.space A.space (isPolyhedron_space B).isClosed
    (isPolyhedron_space A).isClosed hBc.nonempty hAc.nonempty hdis.symm (by rwa [union_comm])
  let J₀ := ρ '' (J ×ˢ {(-1 : ℝ)})
  let J₁ := ρ '' (J ×ˢ {(1 : ℝ)})
  have hends : J₀ ∪ J₁ = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by
    rw [show J₀ = ρ '' (J ×ˢ {(-1 : ℝ)}) from rfl,
      show J₁ = ρ '' (J ×ˢ {(1 : ℝ)}) from rfl, ← image_union, ← prod_union, singleton_union]
  have hJ₀c : IsPreconnected J₀ := (hJ.isConnected.prod isConnected_singleton).image ρ
    (hρc.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩)) |>.isPreconnected
  have hJ₁c : IsPreconnected J₁ := (hJ.isConnected.prod isConnected_singleton).image ρ
    (hρc.mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩)) |>.isPreconnected
  have hendsR : J₀ ∪ J₁ ⊆ R.space := hends.subset.trans
    (htrace.symm.subset.trans inter_subset_right)
  have hside {T : Set E} (hTc : IsPreconnected T) (hTR : T ⊆ R.space) :
      T ⊆ A.space ∨ T ⊆ B.space :=
    isPreconnected_iff_subset_of_disjoint_closed.mp hTc A.space B.space
      (isPolyhedron_space A).isClosed (isPolyhedron_space B).isClosed
      (hTR.trans hAB.symm.subset) (by rw [hdis.inter_eq, inter_empty])
  have hside₀ := hside hJ₀c (subset_union_left.trans hendsR)
  have hside₁ := hside hJ₁c (subset_union_right.trans hendsR)
  have hnotBoth {M N : Set E} (hMN : Disjoint M N) (hNR : N ⊆ R.space)
      (hNW : (N ∩ W).Nonempty) (h₀ : J₀ ⊆ M) (h₁ : J₁ ⊆ M) : False := by
    obtain ⟨z, hzN, hzW⟩ := hNW
    have hz := hends.symm.subset (htrace.subset ⟨hzW, hNR hzN⟩)
    exact disjoint_left.mp hMN (hz.elim (fun h => h₀ h) (fun h => h₁ h)) hzN
  rcases hside₀ with h₀A | h₀B
  · have h₁B := hside₁.resolve_left (hnotBoth hdis hBR hBW h₀A)
    refine ⟨A, B, hAfin, hBfin, hA, hB, hAc, hBc, hdis, hAB, ?_, ?_⟩
    · rw [hAbd, hboundary, ← hends, union_inter_distrib_right, inter_eq_left.mpr h₀A,
        (hdis.symm.mono_left h₁B).inter_eq, union_empty]
    · rw [hBbd, hboundary, ← hends, union_inter_distrib_right,
        (hdis.mono_left h₀A).inter_eq, empty_union, inter_eq_left.mpr h₁B]
  · have h₁A := hside₁.resolve_right (fun h₁B => hnotBoth hdis.symm hAR hAW h₀B h₁B)
    refine ⟨B, A, hBfin, hAfin, hB, hA, hBc, hAc, hdis.symm, ?_, ?_, ?_⟩
    · rwa [union_comm]
    · rw [hBbd, hboundary, ← hends, union_inter_distrib_right, inter_eq_left.mpr h₀B,
        (hdis.mono_left h₁A).inter_eq, union_empty]
    · rw [hAbd, hboundary, ← hends, union_inter_distrib_right,
        (hdis.symm.mono_left h₀B).inter_eq, empty_union, inter_eq_left.mpr h₁A]

end DifferentialGeometry.Topology.PiecewiseLinear
