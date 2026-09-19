/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTriangle
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellAttachment

/-! Actual two-handle attachments in derived neighborhoods of closed three-manifolds. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_derivedNeighborhood_triangle_attachment
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    let D := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
    let A : Set D := {z | z.val.1 ∈ stdSimplexBoundary 2}
    let N := derivedNeighborhood K L
    IsCombinatorialManifoldWithBoundary 3 N ∧
      ∃ g : (Fin 3 → ℝ) × ℝ → E,
        IsPLHomeomorphOn g D (derivedNeighborhoodCell K s).space ∧
        IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc 0 1)
          ((derivedNeighborhoodCell K s).space ∩ N.space) ∧
        ∃ φ : A → N.space, IsClosedEmbedding φ ∧
          (∀ z, (φ z : E) = g z.val.val) ∧
          (∀ z, (φ z : E) ∈ (boundaryComplex 3 N).space) ∧
          ∃ e : AdjunctionSpace (Subtype.val : A → D) φ ≃ₜ
              (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space,
            (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
            ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  classical
  dsimp only
  let D := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
  let A : Set D := {z | z.val.1 ∈ stdSimplexBoundary 2}
  obtain ⟨g, hg, hgs⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_triangle
    K L hK hLK hL hs hcard hsL hproper
  have hset : (fun z : D => g z.val) '' A = g '' (stdSimplexBoundary 2 ×ˢ Icc 0 1) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.val, ⟨hz, z.property.2⟩, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨z, ⟨hz.1.1, hz.2⟩⟩, hz.1, rfl⟩
  have htrace := hset.trans hgs.image_eq
  exact ⟨hK.isCombinatorialManifoldWithBoundary.derivedNeighborhood L, g, hg, hgs,
    exists_derivedNeighborhoodCell_attachment K L hK.isCombinatorialManifoldWithBoundary
      hLK hs hsL hproper A hg htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
