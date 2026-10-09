/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestrictionE
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellSurface
import DifferentialGeometry.Topology.PiecewiseLinear.DiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphMarkedPoints
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_boundary
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    IsPLBall 2 ((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) := by
  let _ : Finite (boundaryComplex 3 K).faces :=
    (boundaryComplex_faces_finite 3 K).to_subtype
  rw [graphDualCell_space_inter_subcomplex K (boundaryComplex 3 K) L
    (boundaryComplex_faces_subset 3 K) (hL hv)]
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  exact hB.isPLBall_graphDualCell_two _ _ hL hcard hv

open Classical in
theorem IsCombinatorialManifoldWithBoundary.splittingDisk_subset_boundary_graphDualCell
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} {e : Finset E}
    (he : e ∈ L.faces) (hecard : e.card = 2) (hv : v ∈ e) :
    (splittingDisk K e (hL he)).space ⊆
      (boundaryComplex 3 (graphDualCell K L v)).space := by
  classical
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ e, w ≠ v := by
    by_contra h
    have hsub : e ⊆ {v} := by
      intro w hw
      simp only [Finset.mem_singleton]
      by_contra hwv
      exact h ⟨w, hw, hwv⟩
    have := Finset.card_le_card hsub
    simp only [hecard, Finset.card_singleton] at this
    omega
  let Cv := graphDualCell K L v
  let Cw := graphDualCell K L w
  let _ : Finite Cv.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite Cw.faces := (graphDualCell_faces_finite K L w).to_subtype
  have hvL := L.down_closed he (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)
  have hwL := L.down_closed he (Finset.singleton_subset_iff.mpr hw)
    (Finset.singleton_nonempty w)
  have hCv := hK.isPLBall_graphDualCell K L hL hcard hvL
  have hCw := hK.isPLBall_graphDualCell K L hL hcard hwL
  have hinter := graphDualCell_space_inter_of_mem K L hL hcard he hv hw hwv.symm
  have hI : IsPLBall 2 (Cv.space ∩ Cw.space) := by
    rw [hinter]
    exact hK.isPLBall_splittingDisk K (hL he) hecard (by omega)
  have hsub := PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall
    (PiecewiseLinear.secondDerived K) Cv Cw hK.secondDerived hCv hCw
    ((graphDualCell_faces_subset K L v).trans (derivedNeighborhood_faces_subset K L))
    ((graphDualCell_faces_subset K L w).trans (derivedNeighborhood_faces_subset K L)) hI
  rw [hinter] at hsub
  exact hsub

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_boundary_contact
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces)
    (d : Finset {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}) :
    IsPLBall 2 (((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) ∪
      ⋃ e ∈ d, (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hL e.2.1))).space) := by
  classical
  let C := graphDualCell K L v
  let B := boundaryComplex 3 C
  let A := C.space ∩ (boundaryComplex 3 K).space
  let hLK := hL.trans (boundaryComplex_faces_subset 3 K)
  let D := fun e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e} =>
    (splittingDisk K e.1 (hLK e.2.1)).space
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 C).to_subtype
  let _ : Finite (boundaryComplex 3 K).faces :=
    (boundaryComplex_faces_finite 3 K).to_subtype
  have hC := hK.isPLBall_graphDualCell K L hLK hcard hv
  have hA : IsPLBall 2 A := hK.isPLBall_graphDualCell_inter_boundary K L hL hcard hv
  have hAB : A ⊆ B.space := inter_boundaryComplex_space_subset_of_subset K C hK
    hC.isCombinatorialManifoldWithBoundary
    ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L))
  have hDB (e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}) : D e ⊆ B.space :=
    hK.splittingDisk_subset_boundary_graphDualCell K L hLK hcard e.2.1 e.2.2.1 e.2.2.2
  have hI (e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}) :
      IsPLBall 1 (A ∩ D e) := by
    have hDC : D e ⊆ C.space := (hDB e).trans (boundaryComplex_space_subset 3 C)
    have heq : A ∩ D e = D e ∩ (boundaryComplex 3 K).space := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hDC hx.1, hx.2⟩, hx.1⟩⟩
    rw [heq, splittingDisk_space_inter_subcomplex K (boundaryComplex 3 K)
      (boundaryComplex_faces_subset 3 K) (hL e.2.1)]
    have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
    exact hB.isPLBall_splittingDisk _ (hL e.2.1) e.2.2.1 (by omega)
  have hB₀ : IsCombinatorialManifold 2 B :=
    isCombinatorialManifold_boundaryComplex C hC.isCombinatorialManifoldWithBoundary
  have hB := hB₀.isCombinatorialManifoldWithBoundary
  have h := hB.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface hA hAB d D
      (fun e _ => hK.isPLBall_splittingDisk _ (hLK e.2.1) e.2.2.1 (by omega))
      (fun e _ => hDB e) (fun e _ => hI e) (fun e _ f _ hef =>
        disjoint_splittingDisk_space K (hLK e.2.1) (hLK f.2.1)
          (fun heq => hef (Subtype.ext heq)) (e.2.2.1.trans f.2.2.1.symm))
  exact h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_free_boundary
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces)
    (d : Finset {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}) :
    IsPLBall 2 (closure ((boundaryComplex 3 (graphDualCell K L v)).space \
      (((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) ∪
        ⋃ e ∈ d, (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hL e.2.1))).space))) := by
  let C := graphDualCell K L v
  let hLK := hL.trans (boundaryComplex_faces_subset 3 K)
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  have hC := hK.isPLBall_graphDualCell K L hLK hcard hv
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall C hC
  have hD := hK.isPLBall_graphDualCell_boundary_contact K L hL hcard hv d
  apply hS.isPLBall_closure_sdiff hD
  refine union_subset ?_ (iUnion₂_subset fun e _ => ?_)
  · exact inter_boundaryComplex_space_subset_of_subset K C hK
      hC.isCombinatorialManifoldWithBoundary
      ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L))
  · exact hK.splittingDisk_subset_boundary_graphDualCell K L hLK hcard e.2.1 e.2.2.1 e.2.2.2

end DifferentialGeometry.Topology.PiecewiseLinear
