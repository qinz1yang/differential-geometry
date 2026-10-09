/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeExhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private structure ManifoldPieceWithInteriorCore (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] (U : Set X) where
  support : Set X
  piece : PLPiece (m + 1) X support
  core : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin piece.ambientDim))
  manifold : IsCombinatorialManifoldWithBoundary (m + 1) piece.piece.complex
  subset : support ⊆ U
  core_le : core.faces ⊆ piece.piece.complex.faces
  regularNeighborhood_subset : piece.piece.map ''
    (regularNeighborhoodIn piece.piece.complex core.space).space ⊆ interior support

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] [SecondCountableTopology X]
  [Nonempty X] [HasGroupoid X (plGroupoid (m + 1))]

theorem exists_locallyFinitePieceTower_of_isOpen {U : Set X} (hU : IsOpen U) :
    ∃ T : LocallyFinitePieceTower (m + 1) X U,
      ∀ i, IsCombinatorialManifoldWithBoundary (m + 1) (T.piece i).piece.complex := by
  classical
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (m + 1)))
      X
  have := hU.locallyCompactSpace
  let C : ℕ → Set X := fun i => ((↑) : U → X) '' compactCovering U i
  have hC : ∀ i, IsCompact (C i) := fun i =>
    (isCompact_compactCovering U i).image continuous_subtype_val
  have hCU : ∀ i, C i ⊆ U := by
    rintro i x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ x ∈ U, ∃ i, x ∈ C i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩
  let S := ManifoldPieceWithInteriorCore m X U
  let start : S := {
    support := ∅
    piece := ⟨0, PLPieceIn.empty (EuclideanSpace ℝ (Fin 0))⟩
    core := ⊥
    manifold := by intro v hv; exact False.elim hv
    subset := empty_subset _
    core_le := fun _ hs => False.elim hs
    regularNeighborhood_subset := by
      rintro _ ⟨x, hx, rfl⟩
      have hxK := space_regularNeighborhoodIn_subset _ _ hx
      change x ∈ (⊥ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 0))).space at hxK
      simp only [space_bot, Set.mem_empty_iff_false] at hxK }
  have hstep : ∀ i (P : S), ∃ Q : S,
      ∃ A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin Q.piece.ambientDim)),
        ∃ φ : EuclideanSpace ℝ (Fin P.piece.ambientDim) → EuclideanSpace ℝ (Fin Q.piece.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin Q.piece.ambientDim) → EuclideanSpace ℝ (Fin
              P.piece.ambientDim),
            P.support ∪ C i ⊆ Q.piece.piece.map '' Q.core.space ∧
              P.support ∪ C i ⊆ interior Q.support ∧ A.faces ⊆ Q.core.faces ∧
                IsGlueIso P.core A φ φ' ∧ ∀ x ∈ P.core.space,
                  Q.piece.piece.map (simplicialMap P.core φ x) = P.piece.piece.map x := by
    intro i P
    obtain ⟨Y, T, L, A, φ, φ', hman, hYU, hL, hcover, hinterior, hdeep, hA, hiso, hmap⟩ :=
      P.piece.exists_manifold_neighborhood_with_core P.core P.core_le P.regularNeighborhood_subset
        (hC i) hU P.subset (hCU i)
    exact ⟨⟨Y, T, L, hman, hYU, hL, hdeep⟩, A, φ, φ', hcover, hinterior, hA, hiso, hmap⟩
  choose f A φ φ' hcore hinterior hA hiso hmap using hstep
  let seq : ℕ → S := Nat.rec start (fun i P => f i P)
  let T : LocallyFinitePieceTower (m + 1) X U := {
    N := fun i => (seq i).support
    piece := fun i => (seq i).piece
    subset_nhdsWithin := fun i x hx => mem_nhdsWithin_of_mem_nhds
      (mem_interior_iff_mem_nhds.mp (hinterior i (seq i) (Or.inl hx)))
    iUnion_eq := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact (seq i).subset hi
      · intro x hx
        obtain ⟨i, hi⟩ := hcover x hx
        exact mem_iUnion.mpr ⟨i + 1, interior_subset (hinterior i (seq i) (Or.inr hi))⟩
    core := fun i => (seq i).core
    core_le := fun i => (seq i).core_le
    subset_core := fun i _ hx => hcore i (seq i) (Or.inl hx)
    coreImage := fun i => A i (seq i)
    coreImage_le := fun i => hA i (seq i)
    embed := fun i => φ i (seq i)
    embedInv := fun i => φ' i (seq i)
    embed_isGlueIso := fun i => hiso i (seq i)
    map_embed := fun i => hmap i (seq i) }
  exact ⟨T, fun i => (seq i).manifold⟩

theorem isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) U :=
  exists_locallyFinitePieceTower_of_isOpen hU

end DifferentialGeometry.Topology.PiecewiseLinear
