import DifferentialGeometry.Topology.PiecewiseLinear.InteriorManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem closure_sdiff_topology_of_regular_closed
    {E : Type*} [TopologicalSpace E] {P R : Set E}
    (hR : IsClosed R) (hreg : closure (interior R) = R)
    {x : E} (hx : x ∈ interior P) :
    (x ∈ closure (P \ R) ↔ x ∉ interior R) ∧
      (x ∈ interior (closure (P \ R)) ↔ x ∉ R) ∧
      (x ∈ frontier (closure (P \ R)) ↔ x ∈ frontier R) := by
  have hsub : closure (P \ R) ⊆ (interior R)ᶜ := by
    rw [← closure_compl]
    exact closure_mono (fun _ h => h.2)
  have hmem : x ∈ closure (P \ R) ↔ x ∉ interior R := by
    refine ⟨fun h => hsub h, fun h => ?_⟩
    have hxcl : x ∈ closure Rᶜ := by rwa [closure_compl]
    exact closure_mono (inter_subset_inter_left Rᶜ interior_subset)
      (isOpen_interior.inter_closure ⟨hx, hxcl⟩)
  have hint : x ∈ interior (closure (P \ R)) ↔ x ∉ R := by
    constructor
    · intro h
      have hh := interior_mono hsub h
      rwa [interior_compl, hreg] at hh
    · intro h
      apply interior_mono (subset_closure (s := P \ R))
      rw [sdiff_eq, interior_inter, interior_compl, hR.closure_eq]
      exact ⟨hx, h⟩
  refine ⟨hmem, hint, ?_⟩
  rw [frontier, isClosed_closure.closure_eq, mem_sdiff, hmem, hint,
    frontier, hR.closure_eq, mem_sdiff]
  tauto

open Classical in
theorem exists_section34_filling_exterior_model
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hRP : R.space ⊆ interior P) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 K ∧
      K.space = closure (P \ R.space) ∧ K.space ⊆ P ∧
      frontier R.space ⊆ frontier K.space ∧
      ∀ x ∈ interior P,
        (x ∈ K.space ↔ x ∉ interior R.space) ∧
        (x ∈ interior K.space ↔ x ∉ R.space) ∧
        (x ∈ frontier K.space ↔ x ∈ frontier R.space) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨B, hBfin, hBspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsCombinatorialManifoldWithBoundary 3 B :=
    (hBspace.symm ▸ hP).isCombinatorialManifoldWithBoundary
  have hRclosed := (isPolyhedron_space R).isClosed
  have hregR : closure (interior R.space) = R.space :=
    (closure_minimal interior_subset hRclosed).antisymm
      (hR.subset_closure_interior_space (by simp))
  have hdis : Disjoint R.space (boundaryComplex 3 B).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (by simp) B hB, hBspace]
    exact disjoint_interior_frontier.mono_left hRP
  obtain ⟨K, hKfin, hK, hKspace⟩ :=
    hB.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary hR
      (hBspace.symm ▸ hRP.trans interior_subset) hdis
  let _ : Finite K.faces := hKfin.to_subtype
  rw [hBspace] at hKspace
  have hread (x) (hx : x ∈ interior P) :
      (x ∈ K.space ↔ x ∉ interior R.space) ∧
      (x ∈ interior K.space ↔ x ∉ R.space) ∧
      (x ∈ frontier K.space ↔ x ∈ frontier R.space) := by
    rw [hKspace]
    exact closure_sdiff_topology_of_regular_closed hRclosed hregR hx
  refine ⟨K, hKfin, hK, hKspace, ?_, ?_, hread⟩
  · rw [hKspace]
    exact closure_minimal sdiff_subset hP.isPolyhedron.isClosed
  · intro x hx
    exact (hread x (hRP (hRclosed.frontier_subset hx))).2.2.mpr hx

end DifferentialGeometry.Topology.PiecewiseLinear
