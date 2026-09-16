import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.LocallyPathConnected

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

theorem locallyPathConnectedSpace_geometricSpace (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : LocallyPathConnectedSpace K.space := by
  let _ : ∀ s : K.faces, CompactSpace (convexHull ℝ (s.1 : Set E)) := fun s =>
    isCompact_iff_compactSpace.mp (s.1.finite_toSet.isCompact_convexHull ℝ)
  let _ : ∀ s : K.faces, LocallyPathConnectedSpace (convexHull ℝ (s.1 : Set E)) := fun s =>
    (convex_convexHull ℝ (s.1 : Set E)).locallyPathConnectedSpace
  let f : (Σ s : K.faces, convexHull ℝ (s.1 : Set E)) → K.space := fun p =>
    ⟨p.2, K.convexHull_subset_space p.1.2 p.2.2⟩
  have hf : Continuous f := continuous_sigma fun _ => continuous_subtype_val.subtype_mk _
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp x.2
    exact ⟨⟨⟨s, hs⟩, ⟨x, hxs⟩⟩, rfl⟩
  exact (hf.isClosedMap.isQuotientMap hf hsurj).locallyPathConnectedSpace

theorem isPathConnected_geometricSpace (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsConnected K.space) : IsPathConnected K.space := by
  let _ := locallyPathConnectedSpace_geometricSpace K
  let _ := isConnected_iff_connectedSpace.mp hK
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (PathConnectedSpace.of_locallyPathConnectedSpace (X := K.space))

end DifferentialGeometry.Topology.SimplicialComplex
