/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_iUnion_isPLSphere_one
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) :
    ∃ (n : ℕ) (C : Fin n → Set E), (∀ i, IsPLSphere 1 (C i)) ∧
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧ K.space = ⋃ i, C i := by
  classical
  let _ : Finite (ConnectedComponents K.space) := finite_connectedComponents_space K
  let _ := Fintype.ofFinite (ConnectedComponents K.space)
  let e := (Fintype.equivFin (ConnectedComponents K.space)).symm
  refine ⟨_, fun i => (PiecewiseLinear.connectedComponentComplex K (e i)).space, ?_, ?_, ?_⟩
  · intro i
    let _ : Finite (PiecewiseLinear.connectedComponentComplex K (e i)).faces :=
      (connectedComponentComplex_faces_finite K (e i)).to_subtype
    exact isPLSphere_one_of_edgeGraph_connected _ (hK.connectedComponentComplex (e i))
      (edgeGraph_connected_of_isConnected_space _
        (isConnected_connectedComponentComplex_space K (e i)))
  · intro i j hij
    exact pairwise_disjoint_connectedComponentComplex_space K
      (fun heq => hij (e.injective heq))
  · change K.space = ⋃ i, (PiecewiseLinear.connectedComponentComplex K (e i)).space
    exact (iUnion_connectedComponentComplex_space K).symm.trans
      (e.surjective.iUnion_comp
        (fun c => (PiecewiseLinear.connectedComponentComplex K c).space)).symm

theorem IsCombinatorialManifold.exists_compact_subsurface_neighborhood
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {C U : Set E}
    (hC : IsCompact C) (hCK : C ⊆ K.space) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (_ : L.faces.Finite)
      (n : ℕ) (G : Fin n → Set E), IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ K.space ∩ U ∧ (∀ x ∈ C, L.space ∈ 𝓝[K.space] x) ∧
      (∀ i, IsPLSphere 1 (G i)) ∧ (Pairwise fun i j => Disjoint (G i) (G j)) ∧
      L.space ∩ closure (K.space \ L.space) = ⋃ i, G i := by
  classical
  obtain ⟨K', L, hK', hK'fin, hLK', hL, hLU, hLC⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood hC hCK hU hCU
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hLfin := hK'fin.subset hLK'
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite (boundaryComplex 2 L).faces := (boundaryComplex_faces_finite 2 L).to_subtype
  obtain ⟨n, G, hG, hGdis, hGeq⟩ :=
    (isCombinatorialManifold_boundaryComplex L hL).exists_iUnion_isPLSphere_one
  refine ⟨L, hLfin, n, G, hL, ?_, hLC, hG, hGdis, ?_⟩
  · refine subset_inter ?_ hLU
    rw [← hK'.space_eq]
    exact space_mono_of_faces_subset hLK'
  · rw [← hK'.space_eq,
      inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold K' L
        (hK.of_isSubdivision hK') hL hLK', hGeq]

end DifferentialGeometry.Topology.PiecewiseLinear
