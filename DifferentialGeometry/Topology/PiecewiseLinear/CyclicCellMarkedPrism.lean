/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeMarkedPrism
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellTrace
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def dualFaceCrossing (s t : Finset E) : E :=
  ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id

theorem dualFaceCrossing_comm (s t : Finset E) : dualFaceCrossing s t = dualFaceCrossing t s := by
  classical
  simp only [dualFaceCrossing, Finset.pair_comm]

variable [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_graphCell_prism_marked
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {s t u : Finset E}
    (hs : s ∈ L.faces) (ht : t ∈ L.faces) (hu : u ∈ L.faces)
    (hsB : s ∉ (boundaryComplex 3 K).faces) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hcompT : s ⊆ t ∨ t ⊆ s) (hcompU : s ⊆ u ∨ u ⊆ s)
    (hneighbors : ∀ r ∈ L.faces, r ≠ s → (s ⊆ r ∨ r ⊆ s) → r = t ∨ r = u)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P)
    {g : EuclideanSpace ℝ (Fin 2) → E}
    (hg : IsPLHomeomorphOn g P
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space))
    (hga : g a = dualFaceCrossing s t) :
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → E,
      IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (derivedNeighborhoodCell K s).space ∧
      (∀ x ∈ P, G (x, 0) = g x) ∧
      G '' (P ×ˢ ({1} : Set ℝ)) =
        (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K u).space ∧
      G (a, 1) = dualFaceCrossing s u ∧
      G '' ({a} ×ˢ Icc (0 : ℝ) 1) = (derivedNeighborhoodCell K s).space ∩ L.space := by
  classical
  let B := upperLink (barycentricSubdivision K) {s.centroid ℝ id}
  let D := upperLink (barycentricSubdivision K) {s.centroid ℝ id, u.centroid ℝ id}
  let _ : Finite B.faces := (upperLink_faces_finite _ _).to_subtype
  let _ : Finite D.faces := (upperLink_faces_finite _ _).to_subtype
  have hB : IsConeBase (s.centroid ℝ id) B := isConeBase_centroid_upperLink K (hLK hs)
  have hS : IsPLSphere 2 B.space :=
    hK.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex (hLK hs) hsB
  have hD : IsConeBase (dualFaceCrossing s u) D :=
    isConeBase_upperLink _
      (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K (hLK hs) (hLK hu) hcompU)
  have hSd : IsPLSphere 1 D.space :=
    hK.isPLSphere_upperLink_pair_centroid_of_interior_face (hLK hs) (hLK hu) hsB hsu hcompU
  have hcapT := derivedNeighborhoodCell_inter_eq_coneSet K (hLK hs) (hLK ht) hcompT
  have hcapU := derivedNeighborhoodCell_inter_eq_coneSet K (hLK hs) (hLK hu) hcompU
  have hTsub : (derivedNeighborhoodCell K s).space ∩
      (derivedNeighborhoodCell K t).space ⊆ B.space := by
    rw [hcapT]
    exact coneSet_pair_centroid_subset_upperLink K (hLK hs) (hLK ht) hst hcompT
  have hUsub : coneSet (dualFaceCrossing s u) D.space ⊆ B.space :=
    coneSet_pair_centroid_subset_upperLink K (hLK hs) (hLK hu) hsu hcompU
  have hdis : Disjoint
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space)
      (coneSet (dualFaceCrossing s u) D.space) := by
    change Disjoint _
      (coneSet (({s.centroid ℝ id, u.centroid ℝ id} : Finset E).centroid ℝ id)
        (upperLink (barycentricSubdivision K) {s.centroid ℝ id, u.centroid ℝ id}).space)
    rw [← hcapU]
    exact (disjoint_derivedNeighborhoodCell_inter_of_card_le_two K L hLK hcard
      hs ht hu hst hsu htu).mono subset_rfl inter_subset_right
  obtain ⟨q, hq, hqa⟩ := hD.exists_stdSimplex_homeomorph_apex hSd
  obtain ⟨G, hG, hG0, -, hG1, hGa, hGaxis⟩ :=
    exists_isPLHomeomorphOn_prism_cone_marked hP ha hB hS hTsub hUsub hdis hg hq
  have hcell : (derivedNeighborhoodCell K s).space = coneSet (s.centroid ℝ id) B.space :=
    derivedNeighborhoodCell_space_eq_coneSet K (hLK hs)
  have htrace : (derivedNeighborhoodCell K s).space ∩ L.space =
      coneSet (s.centroid ℝ id) {dualFaceCrossing s t, dualFaceCrossing s u} := by
    rw [derivedNeighborhoodCell_inter_space_eq_coneSet K L hLK hcard hs]
    congr 1
    ext c
    constructor
    · rintro ⟨r, hr, hrs, hcomp, rfl⟩
      rcases hneighbors r hr hrs hcomp with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    · intro hc
      rcases mem_insert_iff.mp hc with rfl | hc
      · exact ⟨t, ht, hst.symm, hcompT, rfl⟩
      · exact ⟨u, hu, hsu.symm, hcompU, mem_singleton_iff.mp hc⟩
  refine ⟨G, hcell.symm ▸ hG, hG0, hG1.trans hcapU.symm, hGa.trans hqa, ?_⟩
  rw [hGaxis, hga, hqa, htrace]

open Classical in
theorem exists_isPLHomeomorphOn_circleCell_prism_marked
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) {n : ℕ} (e : Fin (n + 3) ≃ L.faces)
    (hadj : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j ↔
      e i ≠ e j ∧ ((e i).val ⊆ (e j).val ∨ (e j).val ⊆ (e i).val))
    (hinterior : ∀ s ∈ L.faces, s ∉ (boundaryComplex 3 K).faces)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P) (i : Fin (n + 3))
    {g : EuclideanSpace ℝ (Fin 2) → E}
    (hg : IsPLHomeomorphOn g P ((derivedNeighborhoodCell K (e i).val).space ∩
      (derivedNeighborhoodCell K (e (i - 1)).val).space))
    (hga : g a = dualFaceCrossing (e i).val (e (i - 1)).val) :
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → E,
      IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (derivedNeighborhoodCell K (e i).val).space ∧
      (∀ x ∈ P, G (x, 0) = g x) ∧
      G '' (P ×ˢ ({1} : Set ℝ)) = (derivedNeighborhoodCell K (e i).val).space ∩
        (derivedNeighborhoodCell K (e (i + 1)).val).space ∧
      G (a, 1) = dualFaceCrossing (e i).val (e (i + 1)).val ∧
      G '' ({a} ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell K (e i).val).space ∩ L.space := by
  have hprev : (SimpleGraph.cycleGraph (n + 3)).Adj i (i - 1) := by
    change i - 1 ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet i
    rw [SimpleGraph.cycleGraph_neighborSet]
    exact mem_insert _ _
  have hnext : (SimpleGraph.cycleGraph (n + 3)).Adj i (i + 1) := by
    change i + 1 ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet i
    rw [SimpleGraph.cycleGraph_neighborSet]
    exact mem_insert_of_mem _ (mem_singleton _)
  have hpn : i - 1 ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  refine exists_isPLHomeomorphOn_graphCell_prism_marked K L hK hLK
    (fun s hs => hL.card_le L hs) (e i).property (e (i - 1)).property
    (e (i + 1)).property (hinterior _ (e i).property)
    (fun h => (hadj i (i - 1)).mp hprev |>.1 (Subtype.ext h))
    (fun h => (hadj i (i + 1)).mp hnext |>.1 (Subtype.ext h))
    (fun h => hpn (e.injective (Subtype.ext h)))
    ((hadj i (i - 1)).mp hprev).2 ((hadj i (i + 1)).mp hnext).2 ?_ hP ha hg hga
  intro r hr hrs hcomp
  obtain ⟨j, hj⟩ := e.surjective ⟨r, hr⟩
  have hv : (e j).val = r := congrArg Subtype.val hj
  have hij : (SimpleGraph.cycleGraph (n + 3)).Adj i j :=
    (hadj i j).mpr ⟨fun h => hrs (hv.symm.trans (congrArg Subtype.val h).symm), hv ▸ hcomp⟩
  change j ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet i at hij
  rw [SimpleGraph.cycleGraph_neighborSet] at hij
  rcases mem_insert_iff.mp hij with rfl | hij
  · exact Or.inl hv.symm
  · rw [mem_singleton_iff.mp hij] at hv
    exact Or.inr hv.symm

open Classical in
theorem exists_isPLHomeomorphOn_cellInterface_marked
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hsB : s ∉ (boundaryComplex 3 K).faces)
    (hst : s ≠ t) (hcomp : s ⊆ t ∨ t ⊆ s)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPLHomeomorphOn g P
        ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) ∧
      g a = dualFaceCrossing s t := by
  let D := upperLink (barycentricSubdivision K) {s.centroid ℝ id, t.centroid ℝ id}
  let _ : Finite D.faces := (upperLink_faces_finite _ _).to_subtype
  have hD : IsConeBase (dualFaceCrossing s t) D :=
    isConeBase_upperLink _
      (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hcomp)
  have hSd : IsPLSphere 1 D.space :=
    hK.isPLSphere_upperLink_pair_centroid_of_interior_face hs ht hsB hst hcomp
  obtain ⟨q, hq, hqa⟩ := hD.exists_stdSimplex_homeomorph_apex hSd
  have hPball : IsPLBall 2 P := by simpa using hP.isPLBall ⟨a, ha⟩
  obtain ⟨r, hr, hra⟩ := hPball.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq ha
  refine ⟨q ∘ Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)), ?_, ?_⟩
  · rw [derivedNeighborhoodCell_inter_eq_coneSet K hs ht hcomp]
    exact hr.symm.trans hq
  · change q (Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) a) = _
    rw [← hra, hr.bijOn.invOn_invFunOn.1
      (openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)), hqa]

end DifferentialGeometry.Topology.PiecewiseLinear
