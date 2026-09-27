/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodMaximalCell
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellAttachment

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_derivedNeighborhood_maximal_attachment
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hmax : ∀ t ∈ K.faces, s ⊆ t → s = t)
    (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    let D := stdSimplex ℝ (Fin (n + 3))
    let A : Set D := {z | z.val ∈ stdSimplexBoundary (n + 2)}
    let N := derivedNeighborhood K L
    IsCombinatorialManifoldWithBoundary (n + 2) N ∧
      ∃ g : (Fin (n + 3) → ℝ) → E,
        IsPLHomeomorphOn g D (derivedNeighborhoodCell K s).space ∧
        IsPLHomeomorphOn g (stdSimplexBoundary (n + 2))
          ((derivedNeighborhoodCell K s).space ∩ N.space) ∧
        ∃ φ : A → N.space, IsClosedEmbedding φ ∧
          (∀ z, (φ z : E) = g z.val.val) ∧
          (∀ z, (φ z : E) ∈ (boundaryComplex (n + 2) N).space) ∧
          ∃ e : AdjunctionSpace (Subtype.val : A → D) φ ≃ₜ
              (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space,
            (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
            ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  classical
  dsimp only
  let D := stdSimplex ℝ (Fin (n + 3))
  let A : Set D := {z | z.val ∈ stdSimplexBoundary (n + 2)}
  obtain ⟨g, hg, hgs⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_maximal
    K L hK hLK hs hmax hsL hproper
  have hset : (fun z : D => g z.val) '' A = g '' stdSimplexBoundary (n + 2) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1⟩, hz, rfl⟩
  have htrace := hset.trans hgs.image_eq
  exact ⟨hK.isCombinatorialManifoldWithBoundary.derivedNeighborhood L, g, hg, hgs,
    exists_derivedNeighborhoodCell_attachment K L hK.isCombinatorialManifoldWithBoundary
      hLK hs hsL hproper A hg htrace⟩

open Classical in
theorem exists_derivedNeighborhood_tetrahedron_attachment
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 4) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    let D := stdSimplex ℝ (Fin 4)
    let A : Set D := {z | z.val ∈ stdSimplexBoundary 3}
    let N := derivedNeighborhood K L
    IsCombinatorialManifoldWithBoundary 3 N ∧
      ∃ g : (Fin 4 → ℝ) → E,
        IsPLHomeomorphOn g D (derivedNeighborhoodCell K s).space ∧
        IsPLHomeomorphOn g (stdSimplexBoundary 3)
          ((derivedNeighborhoodCell K s).space ∩ N.space) ∧
        ∃ φ : A → N.space, IsClosedEmbedding φ ∧
          (∀ z, (φ z : E) = g z.val.val) ∧
          (∀ z, (φ z : E) ∈ (boundaryComplex 3 N).space) ∧
          ∃ e : AdjunctionSpace (Subtype.val : A → D) φ ≃ₜ
              (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space,
            (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
            ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  apply exists_derivedNeighborhood_maximal_attachment K L hK hLK hs ?_ hsL hproper
  intro t ht hst
  apply Finset.eq_of_subset_of_card_le hst
  rw [hcard]
  exact hK.card_le K ht

end DifferentialGeometry.Topology.PiecewiseLinear
