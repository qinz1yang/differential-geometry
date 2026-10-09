/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.FinitePartition
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBicollar

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem IsPolyhedralSphere.isCompact {m : ℕ} {S : Set M}
    (hS : IsPolyhedralSphere (n := n) m S) : IsCompact S := by
  obtain ⟨T, hT⟩ := hS
  rw [← T.piece.bijOn.image_eq]
  exact hT.isPolyhedron.isCompact.image_of_continuousOn T.piece.continuousOn

open Classical in
theorem IsPolyhedralSphere.eq_of_subset [T2Space M] {m : ℕ} {S T : Set M}
    (hS : IsPolyhedralSphere (n := n) (m + 1) S)
    (hT : IsPolyhedralSphere (n := n) (m + 1) T) (hST : S ⊆ T) : S = T := by
  obtain ⟨A, hA⟩ := hS
  obtain ⟨B, hB⟩ := hT
  let g := Function.invFunOn B.piece.map B.piece.complex.space ∘ A.piece.map
  have hright : ∀ y ∈ T, B.piece.map (Function.invFunOn B.piece.map
      B.piece.complex.space y) = y := fun y hy => B.piece.bijOn.invOn_invFunOn.2 hy
  have hmaps : MapsTo A.piece.map A.piece.complex.space T :=
    fun x hx => hST (A.piece.bijOn.mapsTo hx)
  have hinv : ContinuousOn (Function.invFunOn B.piece.map B.piece.complex.space) T := by
    exact (continuousOn_invFunOn_image_of_isCompact hB.isPolyhedron.isCompact
      B.piece.continuousOn B.piece.bijOn.injOn).mono B.piece.bijOn.image_eq.symm.subset
  have hgcont : ContinuousOn g A.piece.complex.space :=
    hinv.comp A.piece.continuousOn hmaps
  have hginj : InjOn g A.piece.complex.space := by
    intro x hx y hy hxy
    apply A.piece.bijOn.injOn hx hy
    rw [← hright _ (hmaps hx), ← hright _ (hmaps hy)]
    exact congrArg B.piece.map hxy
  have hgmap : MapsTo g A.piece.complex.space B.piece.complex.space :=
    fun x hx => B.piece.bijOn.surjOn.mapsTo_invFunOn (hmaps hx)
  have hsurj := hA.surjOn_of_continuousOn_injOn hB hgcont hginj hgmap
  refine Subset.antisymm hST fun y hy => ?_
  obtain ⟨z, hz, hzy⟩ := B.piece.bijOn.surjOn hy
  obtain ⟨x, hx, hxz⟩ := hsurj hz
  have hxy : A.piece.map x = y := by
    rw [← hright _ (hmaps hx)]
    change B.piece.map (g x) = y
    rw [hxz, hzy]
  exact hxy ▸ A.piece.bijOn.mapsTo hx

theorem setOf_isPolyhedralSphere_one_subset_sUnion_eq [T2Space M]
    {C : Set (Set M)} (hC : C.Finite)
    (hCsphere : ∀ S ∈ C, IsPolyhedralSphere (n := n) 1 S)
    (hdisjoint : C.PairwiseDisjoint id) :
    {S | IsPolyhedralSphere (n := n) 1 S ∧ S ⊆ ⋃₀ C} = C := by
  ext S
  constructor
  · rintro ⟨hS, hSC⟩
    obtain ⟨T, ⟨hTC, hST⟩, -⟩ := existsUnique_subset_of_isConnected_of_finite_closed_partition
      hS.isConnected hC (fun T hT => (hCsphere T hT).isCompact.isClosed) hdisjoint hSC
    exact hS.eq_of_subset (hCsphere T hTC) hST ▸ hTC
  · intro hS
    exact ⟨hCsphere S hS, subset_sUnion_of_mem hS⟩

end DifferentialGeometry.Topology.PiecewiseLinear
