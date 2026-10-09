/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CollarBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_surface_prod_Icc
    (K H : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite H.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space) {a b : ℝ} (hab : a < b) :
    ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      IsPolyhedron W ∧ W ⊆ K.space ∧ IsPLHomeomorphOn ρ (H.space ×ˢ Icc a b) W ∧
      (∀ x ∈ H.space, ρ (x, a) = x) ∧ W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a b) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  let V := {v : E // ({v} : Finset E) ∈ H.faces}
  let _ : Finite V :=
    (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite H.faces)).to_subtype
  let _ : Fintype V := Fintype.ofFinite V
  let D : V → Geometry.SimplicialComplex ℝ E := fun v => dualCell H {v.1} v.2
  let _ (v : V) : Finite (D v).faces := (dualCell_faces_finite H v.2).to_subtype
  let P : Finset V → Set E := fun d => ⋃ v ∈ d, (D v).space
  have hD : ∀ v : V, IsPLBall 2 (D v).space := fun v =>
    hH.isPLBall_dualCell H v.2 (k := 0) (Finset.card_singleton v.1) (by norm_num)
  have hDB : ∀ v : V, (D v).space ⊆ (boundaryComplex 3 K).space := by
    intro v x hx
    apply hHK
    rw [← iUnion_dualCell_singleton_space H]
    exact mem_iUnion.mpr ⟨v, hx⟩
  have hPempty : P ∅ = ∅ := by simp [P]
  have hPinsert : ∀ (v : V) (d : Finset V), P (insert v d) = P d ∪ (D v).space := by
    intro v d
    simp [P, union_comm]
  have hP : ∀ d : Finset V, IsPolyhedron (P d) := by
    intro d
    induction d using Finset.induction_on with
    | empty => rw [hPempty]; exact IsPolyhedron.empty
    | @insert v d hv ih => rw [hPinsert]; exact ih.union (hD v).isPolyhedron
  have hind : ∀ d : Finset V,
      ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
        IsPolyhedron W ∧ W ⊆ K.space ∧ IsPLHomeomorphOn ρ (P d ×ˢ Icc a b) W ∧
        (∀ x ∈ P d, ρ (x, a) = x) ∧ W ∩ (boundaryComplex 3 K).space = P d ∧
        R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
        R.space = closure (K.space \ W) ∧
        W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
        (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
        ∀ v ∉ d, (D v).space ∪ ρ '' (((D v).space ∩ P d) ×ˢ Icc a b) ⊆
          (boundaryComplex 3 R).space := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
      refine ⟨∅, fun _ => 0, K, IsPolyhedron.empty, empty_subset _, ?_, ?_, ?_,
        Set.toFinite K.faces, hK, ?_, ?_, ?_, ?_⟩
      · rw [hPempty, empty_prod]
        exact ⟨by simp [BijOn, MapsTo, InjOn, SurjOn], fun _ hx => hx.elim, fun _ hx => hx.elim⟩
      · simp only [hPempty, mem_empty_iff_false, false_implies, implies_true]
      · simp [hPempty]
      · simp only [sdiff_empty, (isPolyhedron_space K).isClosed.closure_eq]
      · simp only [empty_inter, empty_subset]
      · exact inter_subset_left
      · intro v _
        simpa only [hPempty, inter_empty, empty_prod, image_empty, union_empty] using hDB v
    | @insert v d hv ih =>
      obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, hWB, hRfin, hR, hRspace,
        hWR, hBR, hfuture⟩ := ih
      let _ : Finite R.faces := hRfin.to_subtype
      obtain ⟨e, -, hE, hcover⟩ :=
        hH.exists_boundary_arcs_cover_inter_dualCell_iUnion H d hv
      obtain ⟨C, σ, R', hC, hCR, -, hσ, hσρ, hbase, htrace, -, hR'fin, hR', hR'space,
        hWR', hBR', hσC, hCtrace, hCB, hWC⟩ :=
        exists_collar_extension_of_boundary_arcs (D v) R (hD v) hR (hP d) (hDB v) hab
          hρ hbottom hWB e (fun w => (D v).space ∩ (D w).space)
          (fun w hw => (hE w hw).1) (fun w hw => (hE w hw).2) hcover
          (hfuture v hv) hWR hBR (U := univ) Filter.univ_mem
      let _ : Finite R'.faces := hR'fin.to_subtype
      have hRK : R.space ⊆ K.space := by
        rw [hRspace]
        exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
      have hR'global : R'.space = closure (K.space \ (W ∪ C)) := by
        rw [hR'space, hRspace]
        have heq : closure (closure (K.space \ W) \ C) = closure ((K.space \ W) \ C) := by
          apply Subset.antisymm
          · apply closure_minimal _ isClosed_closure
            have h := closure_sdiff (s := K.space \ W) (t := C)
            rwa [hC.isPolyhedron.isClosed.closure_eq] at h
          · exact closure_mono (sdiff_subset_sdiff_left subset_closure)
        rw [heq, sdiff_sdiff]
      refine ⟨W ∪ C, σ, R', hW.union hC.isPolyhedron, union_subset hWK (hCR.trans hRK),
        ?_, ?_, ?_, hR'fin, hR', hR'global, hWR', hBR', ?_⟩
      · rwa [hPinsert]
      · rwa [hPinsert]
      · rwa [hPinsert]
      · intro u hu
        have hud : u ∉ d := fun hud => hu (Finset.mem_insert_of_mem hud)
        have huv : u ≠ v := fun heq => hu (heq ▸ Finset.mem_insert_self v d)
        have huv' : u.1 ≠ v.1 := fun heq => huv (Subtype.ext heq)
        have hJD : IsPLBall 1 ((D u).space ∩ (D v).space) ∨
            Disjoint (D u).space (D v).space := by
          by_cases hface : ({u.1, v.1} : Finset E) ∈ H.faces
          · exact Or.inl (hH.isPLBall_inter_dualCell_singleton H u.2 v.2 huv' hface)
          · exact Or.inr (disjoint_dualCell_space H u.2 v.2 (by
              simpa only [Finset.singleton_union] using hface))
        have hJDb : (D u).space ∩ (D v).space ⊆ (boundaryComplex 2 (D v)).space := by
          rcases hJD with hball | hdis
          · have hface := union_mem_faces_of_nonempty_dualCell_inter H u.2 v.2 hball.nonempty
            rw [inter_comm]
            exact hH.inter_dualCell_singleton_subset_boundaryComplex H v.2 u.2 huv'.symm
              (by simpa only [Finset.singleton_union, Finset.pair_comm] using hface)
          · rw [hdis.inter_eq]
            exact empty_subset _
        obtain ⟨e', -, hE', hcover'⟩ :=
          hH.exists_boundary_arcs_cover_inter_dualCell_iUnion H d hud
        obtain ⟨G, hGfin, hGspace⟩ := hC.isPolyhedron.exists_simplicialComplex
        let _ : Finite G.faces := hGfin.to_subtype
        have hpersist := collar_disk_subset_boundaryComplex_complement (D v) R G R'
          (hD v) hR (hGspace.symm ▸ hCR) hR' (hGspace.symm ▸ hR'space)
          (hP d) (hD u) (hDB u) hJD hJDb
          (hH.finite_inter_dualCell_singleton_iUnion H d huv hud hv)
          e' (fun w => (D u).space ∩ (D w).space) (fun w hw => (hE' w hw).1) hcover'
          hab hρ (hGspace.symm ▸ hσC) hσρ (hfuture u hud)
          (hGspace.symm ▸ hCtrace) (hGspace.symm ▸ hCB) (hGspace.symm ▸ hWC)
        rwa [hPinsert]
  have hPall : P Finset.univ = H.space := by
    simp only [P, Finset.mem_univ, iUnion_true]
    exact iUnion_dualCell_singleton_space H
  obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, hWB, hRfin, hR, hRspace, hWR, hBR, -⟩ :=
    hind Finset.univ
  rw [hPall] at hρ hbottom hWB
  refine ⟨W, ρ, R, hW, hWK, hρ, hbottom, hWB, ?_, hRfin, hR, hRspace, hWR, hBR⟩
  intro z hz
  have hzW := hρ.bijOn.mapsTo ⟨hz.1, hz.2.1.le, hz.2.2⟩
  refine ⟨hWK hzW, ?_⟩
  intro hzB
  have hxbase : ρ z ∈ H.space := hWB ▸ ⟨hzW, hzB⟩
  have heq : z = (ρ z, a) := hρ.bijOn.injOn ⟨hz.1, hz.2.1.le, hz.2.2⟩
    ⟨hxbase, le_rfl, hab.le⟩ (hbottom (ρ z) hxbase).symm
  exact hz.2.1.ne' (congrArg Prod.snd heq)

end DifferentialGeometry.Topology.PiecewiseLinear
