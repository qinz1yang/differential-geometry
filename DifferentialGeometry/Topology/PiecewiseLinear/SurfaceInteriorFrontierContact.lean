/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_surface_interior_frontier_contact
    (M : Fin 3 → Geometry.SimplicialComplex ℝ E3)
    (hfin : ∀ i, (M i).faces.Finite)
    (hM : ∀ i, IsCombinatorialManifoldWithBoundary 2 (M i))
    (hconn : ∀ i, IsConnected (M i).space)
    (hboundary : ∀ i j, (boundaryComplex 2 (M i)).space =
      (boundaryComplex 2 (M j)).space)
    (hne : (boundaryComplex 2 (M 0)).space.Nonempty)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint ((M i).space \ (boundaryComplex 2 (M i)).space)
        ((M j).space \ (boundaryComplex 2 (M j)).space))
    {x : E3} (hx : x ∉ ⋃ i, (M i).space) :
    ∃ i, ∃ z ∈ (M i).space \ (boundaryComplex 2 (M i)).space,
      z ∈ frontier (connectedComponentIn (⋃ i, (M i).space)ᶜ x) := by
  have hd : (inferInstance : DecidableEq E3) = (fun a b => Classical.propDecidable (a = b)) := by
    ext a b
    exact Subsingleton.elim _ _
  have hB (i : Fin 3) : (boundaryComplex 2 (M i)).space =
      (@boundaryComplex E3 _ _ (fun a b => Classical.propDecidable (a = b)) 2 (M i)).space :=
    congrArg (fun d : DecidableEq E3 => (@boundaryComplex E3 _ _ d 2 (M i)).space) hd
  let _ : ∀ i, Finite (M i).faces := fun i => (hfin i).to_subtype
  have hpoly (i : Fin 3) : IsPolyhedron (M i).space := isPolyhedron_space (M i)
  have hclosed : IsClosed (⋃ i, (M i).space) :=
    isClosed_iUnion_of_finite fun i => (hpoly i).isClosed
  let U := (⋃ i, (M i).space)ᶜ
  have hUopen : IsOpen U := hclosed.isOpen_compl
  let C := connectedComponentIn U x
  have hCopen : IsOpen C := hUopen.connectedComponentIn
  have hxU : x ∈ U := hx
  have hxC : x ∈ C := mem_connectedComponentIn hxU
  have hCsubU : C ⊆ U := connectedComponentIn_subset U x
  have hfront_sub_S : frontier C ⊆ ⋃ i, (M i).space := by
    rw [frontier, hCopen.interior_eq]
    intro z ⟨hzcl, hznotC⟩
    by_contra hzS
    have hzU : z ∈ U := hzS
    have hmeet : (C ∩ connectedComponentIn U z).Nonempty := by
      have h := mem_closure_iff_nhds.mp hzcl (connectedComponentIn U z)
        (hUopen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hzU))
      rwa [inter_comm] at h
    obtain ⟨y, hyC, hyz⟩ := hmeet
    have heq : connectedComponentIn U z = C :=
      (connectedComponentIn_eq hyz).trans (connectedComponentIn_eq hyC).symm
    exact hznotC (heq ▸ mem_connectedComponentIn hzU)
  have hBS (i : Fin 3) : (boundaryComplex 2 (M i)).space ⊆ (M i).space :=
    boundaryComplex_space_subset 2 (M i)
  have hinter (i j : Fin 3) (hij : i ≠ j) :
      (M i).space ∩ (M j).space = (boundaryComplex 2 (M i)).space := by
    apply Subset.antisymm _ (subset_inter (hBS i) ((hboundary i j).symm ▸ hBS j))
    rintro z ⟨hzi, hzj⟩
    by_contra hzB
    exact disjoint_left.mp (hdisjoint i j hij) ⟨hzi, hzB⟩ ⟨hzj, (hboundary i j) ▸ hzB⟩
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hbd0 : (M 0).space ∩ (M 1).space = (boundaryComplex 2 (M 0)).space := hinter 0 1 h01
  have hbd1 : (M 0).space ∩ (M 1).space = (boundaryComplex 2 (M 1)).space := by
    rw [hbd0, hboundary 0 1]
  have hbd0_class : (M 0).space ∩ (M 1).space =
      (@boundaryComplex E3 _ _ (fun a b => Classical.propDecidable (a = b)) 2 (M 0)).space := by
    rw [← hB 0]
    exact hbd0
  have hbd1_class : (M 0).space ∩ (M 1).space =
      (@boundaryComplex E3 _ _ (fun a b => Classical.propDecidable (a = b)) 2 (M 1)).space := by
    rw [← hB 1]
    exact hbd1
  obtain ⟨K01, hK01fin, hK01, hK01space⟩ :=
    exists_isCombinatorialManifold_space_union (M 0) (M 1) (hM 0) (hM 1) hbd0_class hbd1_class
  let _ : Finite K01.faces := hK01fin.to_subtype
  have hmeet01 : ((M 0).space ∩ (M 1).space).Nonempty := by
    rw [hbd0]
    exact hne
  have hK01conn : IsConnected K01.space := by
    rw [hK01space]
    exact IsConnected.union hmeet01 (hconn 0) (hconn 1)
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have hx01 : x ∈ K01.spaceᶜ := by
    rw [hK01space]
    intro hxmem
    rcases hxmem with h0 | h1
    · exact hx (mem_iUnion.mpr ⟨0, h0⟩)
    · exact hx (mem_iUnion.mpr ⟨1, h1⟩)
  let X := connectedComponentIn K01.spaceᶜ x
  have hXconn : IsConnected X := isConnected_connectedComponentIn_iff.mpr hx01
  have hxX : x ∈ X := mem_connectedComponentIn hx01
  obtain ⟨a, -, b, -, -, hunion, -, -, hfrontA, hfrontB⟩ :=
    hK01.exists_connectedComponentIn_pair_compl K01 hdim hK01conn
  have hfrontX : frontier X = K01.space := by
    rcases hunion.symm.subset hx01 with hxA | hxB
    · have heq : connectedComponentIn K01.spaceᶜ a = X := connectedComponentIn_eq hxA
      rw [← heq]
      exact hfrontA
    · have heq : connectedComponentIn K01.spaceᶜ b = X := connectedComponentIn_eq hxB
      rw [← heq]
      exact hfrontB
  have hUX : U ⊆ K01.spaceᶜ := by
    intro y hy
    rw [hK01space]
    intro hy01
    rcases hy01 with hy0 | hy1
    · exact hy (mem_iUnion.mpr ⟨0, hy0⟩)
    · exact hy (mem_iUnion.mpr ⟨1, hy1⟩)
  have hCX : C ⊆ X := connectedComponentIn_mono x hUX
  by_cases hX2 : (X ∩ (M 2).space).Nonempty
  · have hCneX : C ≠ X := by
      obtain ⟨y, hyX, hy2⟩ := hX2
      intro heq
      have hyC : y ∈ C := heq ▸ hyX
      exact (hCsubU hyC) (mem_iUnion.mpr ⟨2, hy2⟩)
    have hCclopenX : ¬ (closure C ∩ X ⊆ C) := by
      intro hclosedX
      let S_sub : Set ↥X := Subtype.val ⁻¹' C
      have hS_open : IsOpen S_sub := hCopen.preimage continuous_subtype_val
      have hcl_sub : closure S_sub ⊆ Subtype.val ⁻¹' (closure C) :=
        closure_minimal (preimage_mono subset_closure)
          (isClosed_closure.preimage continuous_subtype_val)
      have hS_closed : IsClosed S_sub := by
        rw [← closure_eq_iff_isClosed]
        apply Subset.antisymm _ subset_closure
        rintro ⟨w, hwX⟩ hwcl
        exact hclosedX ⟨hcl_sub hwcl, hwX⟩
      let _ : PreconnectedSpace ↥X := Subtype.preconnectedSpace hXconn.isPreconnected
      have hS_univ : S_sub = univ :=
        (show IsClopen S_sub from ⟨hS_closed, hS_open⟩).eq_univ ⟨⟨x, hxX⟩, hxC⟩
      have hXsubC : X ⊆ C := by
        intro w hw
        have : (⟨w, hw⟩ : ↥X) ∈ S_sub := by rw [hS_univ]; exact mem_univ _
        exact this
      exact hCneX (Subset.antisymm hCX hXsubC)
    obtain ⟨z, ⟨hzcl, hzX⟩, hznotC⟩ := not_subset.mp hCclopenX
    have hzfront : z ∈ frontier C := ⟨hzcl, fun hzint => hznotC (hCopen.interior_eq.symm ▸ hzint)⟩
    have hzS : z ∈ ⋃ i, (M i).space := hfront_sub_S hzfront
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzS
    have hzi2 : i = 2 := by
      by_contra hne2
      have hzK : z ∈ K01.space := by
        rw [hK01space]
        rcases i with ⟨_ | _ | _ | n, hn⟩
        · exact Or.inl hzi
        · exact Or.inr hzi
        · have hi2 : (⟨2, hn⟩ : Fin 3) = 2 := Fin.ext rfl
          exact (hne2 hi2).elim
        · omega
      exact (connectedComponentIn_subset K01.spaceᶜ x hzX) hzK
    subst hzi2
    have hznotB : z ∉ (boundaryComplex 2 (M 2)).space := by
      intro hzB
      have hzB0 : z ∈ (boundaryComplex 2 (M 0)).space := by rwa [← hboundary 2 0]
      have hzK : z ∈ K01.space := by
        rw [hK01space]
        exact Or.inl (hBS 0 hzB0)
      exact (connectedComponentIn_subset K01.spaceᶜ x hzX) hzK
    refine ⟨2, z, ⟨hzi, hznotB⟩, hzfront⟩
  · have hXsub2c : X ⊆ ((M 2).space)ᶜ := by
      intro y hyX hy2
      exact hX2 ⟨y, hyX, hy2⟩
    have hXsubU : X ⊆ U := by
      intro y hyX hyS
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyS
      rcases i with ⟨_ | _ | _ | n, hn⟩
      · have hyK : y ∈ K01.space := hK01space.symm ▸ Or.inl hyi
        exact (connectedComponentIn_subset K01.spaceᶜ x hyX) hyK
      · have hyK : y ∈ K01.space := hK01space.symm ▸ Or.inr hyi
        exact (connectedComponentIn_subset K01.spaceᶜ x hyX) hyK
      · exact hXsub2c hyX hyi
      · omega
    have hXC : X ⊆ C := hXconn.isPreconnected.subset_connectedComponentIn hxX hXsubU
    have hCEqX : C = X := Subset.antisymm hCX hXC
    have hfrontC : frontier C = K01.space := by rw [hCEqX, hfrontX]
    have h0ne : ((M 0).space \ (boundaryComplex 2 (M 0)).space).Nonempty := by
      by_contra he
      rw [nonempty_iff_ne_empty, not_not] at he
      have hsub := (hM 0).space_subset_closure_sdiff_boundaryComplex_space (K := M 0)
      rw [he, closure_empty] at hsub
      have hBne : ((boundaryComplex 2 (M 0)).space).Nonempty := hne
      obtain ⟨p, hp⟩ := hBne
      exact (hsub (hBS 0 hp)).elim
    obtain ⟨z, hz0, hznotB⟩ := h0ne
    refine ⟨0, z, ⟨hz0, hznotB⟩, ?_⟩
    rw [hfrontC, hK01space]
    exact Or.inl hz0

end DifferentialGeometry.Topology.PiecewiseLinear
