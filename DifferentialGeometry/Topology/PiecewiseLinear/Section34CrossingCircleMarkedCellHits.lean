import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleMarkedCellParameters
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorSurfaceCaps
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleSheets

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem interior_derived_cap_center_not_mem_rim
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) {s t : Finset E}
    (hs : s ∈ R.faces) (ht : t ∈ R.faces) (hsB : s ∉ (boundaryComplex 3 R).faces)
    (hne : s ≠ t) (hcomp : s ⊆ t ∨ t ⊆ s) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space)) :
    ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id ∉
      q '' stdSimplexBoundary 2 := by
  let e : Finset E := {s.centroid ℝ id, t.centroid ℝ id}
  have he : e ∈ (barycentricSubdivision R).faces :=
    pair_centroid_mem_barycentricSubdivision_of_subset_or_subset R hs ht hcomp
  let C := dualCell (barycentricSubdivision R) e he
  let _ : Finite C.faces := (dualCell_faces_finite _ he).to_subtype
  let _ : Finite (upperLink (barycentricSubdivision R) e).faces :=
    (upperLink_faces_finite _ _).to_subtype
  have hC : C.space =
      (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space :=
    (derivedNeighborhoodCell_space_inter R hs ht hcomp).symm
  have hqb := hq.image_stdSimplexBoundary_eq_boundaryComplex C hC
  have hS : IsPLSphere 1 (upperLink (barycentricSubdivision R) e).space :=
    hR.isPLSphere_upperLink_pair_centroid_of_interior_face hs ht hsB hne hcomp
  have hCb : (boundaryComplex 2 C).space =
      (upperLink (barycentricSubdivision R) e).space :=
    (isConeBase_upperLink (barycentricSubdivision R) he).boundaryComplex_space_of_isPLSphere hS
  rw [hqb, hCb]
  exact (isConeBase_upperLink (barycentricSubdivision R) he).notMem_space

open Classical in
theorem exists_marked_arcs_of_interior_derived_cell
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) (hsB : s ∉ (boundaryComplex 3 R).faces)
    {t : Fin 2 → Finset E} (ht : ∀ j, t j ∈ Γ.faces)
    (hne : ∀ j, s ≠ t j) (hcomp : ∀ j, s ⊆ t j ∨ t j ⊆ s)
    {D : Fin 2 → Set E} (hD : ∀ j, D j =
      (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R (t j)).space)
    {qcap : Fin 2 → (Fin 3 → ℝ) → E}
    (hcap : ∀ j, IsPLHomeomorphOn (qcap j) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D j))
    (hDS : ∀ j, D j ⊆ (derivedNeighborhoodCellBase R s).space)
    (hdis : Disjoint (D 0) (D 1)) {y : Fin 2 → E}
    (hy : ∀ j, y j = ({s.centroid ℝ id, (t j).centroid ℝ id} : Finset E).centroid ℝ id)
    {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    {W : Set E} (hbd : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hstar : (⋃ v ∈ s, closedStar R v) ⊆ W) {γ : Fin 4 → ℝ → E}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1)
      ((derivedNeighborhoodCellBase R s).space ∩ P i))
    (hzero : ∀ i, γ i 0 = y 0) (hone : ∀ i, γ i 1 = y 1) :
    ∃ δ : Fin 4 → ℝ → E,
      (∀ i, IsPLHomeomorphOn (δ i) (Icc 0 1)
        ((derivedNeighborhoodCellBase R s).space ∩ P i)) ∧
      (∀ i, δ i 0 = y 0) ∧ (∀ i, δ i 1 = y 1) ∧
      (∀ i, qcap 0 '' stdSimplexBoundary 2 ∩
        ((derivedNeighborhoodCellBase R s).space ∩ P i) = {δ i (1 / 4)}) ∧
      (∀ i, qcap 1 '' stdSimplexBoundary 2 ∩
        ((derivedNeighborhoodCellBase R s).space ∩ P i) = {δ i (3 / 4)}) ∧
      (∀ i, D 0 ∩ P i = segment ℝ (y 0) (δ i (1 / 4))) ∧
      ∀ i, D 1 ∩ P i = segment ℝ (y 1) (δ i (3 / 4)) := by
  have hsP (i : Fin 4) := comparable_circle_face_mem_page_boundary R Γ hΓR hs
    hq hPR hbd hstar hs (Or.inl Finset.Subset.rfl) i
  have htP (j : Fin 2) (i : Fin 4) := comparable_circle_face_mem_page_boundary R Γ hΓR hs
    hq hPR hbd hstar (ht j) (hcomp j) i
  have hraw : ∀ j i, ∃ x : E, qcap j '' stdSimplexBoundary 2 ∩
      ((derivedNeighborhoodCellBase R s).space ∩ P i) = {x} ∧
      D j ∩ P i = segment ℝ (y j) x := by
    intro j i
    let L := PiecewiseLinear.restrict R (P i)
    let _ : Finite L.faces := (restrict_faces_finite R _).to_subtype
    have hLsp : L.space = P i := hPR i
    have hL : IsPLBall 2 L.space := hLsp.symm ▸ ⟨q i, hq i⟩
    obtain ⟨x, hx, harm⟩ := exists_singleton_interior_cap_boundary_inter_surface R L hR
      hL.isCombinatorialManifoldWithBoundary (restrict_faces_subset R _) (hsP i) (htP j i)
      hsB (hne j) (hcomp j) ((hD j) ▸ hcap j)
    exact ⟨x, by simpa only [hLsp] using hx,
      by simpa only [← hD j, ← hy j, hLsp] using harm⟩
  choose x hx harm using hraw
  have hnot (j : Fin 2) : y j ∉ qcap j '' stdSimplexBoundary 2 := by
    rw [hy j]
    exact interior_derived_cap_center_not_mem_rim R hR (hΓR hs) (hΓR (ht j)) hsB
      (hne j) (hcomp j) ((hD j) ▸ hcap j)
  have hyD (j : Fin 2) : y j ∈ D j := by
    rw [hD j, hy j, derivedNeighborhoodCell_inter_eq_coneSet R
      (hΓR hs) (hΓR (ht j)) (hcomp j)]
    exact apex_mem_coneSet _ _
  have hS := hR.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex (hΓR hs) hsB
  choose δ hδ hδ0 hδ1 hδq hδt using fun i =>
    exists_arc_parametrization_marking_disjoint_caps hS (hγ i) inter_subset_left
      (hcap 0) (hcap 1) (hDS 0) hdis (hzero i ▸ hyD 0)
      (hzero i ▸ hnot 0) (hone i ▸ hnot 1) (hx 0 i) (hx 1 i)
  exact ⟨δ, hδ, fun i => (hδ0 i).trans (hzero i), fun i => (hδ1 i).trans (hone i),
    fun i => by rw [hx 0 i, hδq i], fun i => by rw [hx 1 i, hδt i],
    fun i => by rw [harm 0 i, hδq i], fun i => by rw [harm 1 i, hδt i]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
