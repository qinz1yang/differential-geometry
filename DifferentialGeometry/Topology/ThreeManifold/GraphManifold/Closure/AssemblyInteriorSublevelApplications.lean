import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInteriorSublevel

/-!
# Consumer of B1-interior and B1-complement: the two sides of one rounding function

The common rounding of the assembly design (§0 decision 1, `CircleRegion`) uses ONE function on
both sides: the rounded region `{x ∈ U | f x ≤ c}` (B1-interior) and the ball–handle side
`W \ {x ∈ U | f x < c}` (B1-complement). `exists_pieces_of_interior_sublevel_pair` records both
families of pieces together: they cover `W`, they meet exactly along the common level
`{x ∈ U | f x = c}`, the region pieces have boundary exactly that level, and the complementary
pieces have boundary `∂W` together with that level.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Both sides of one rounding function.** -/
theorem exists_pieces_of_interior_sublevel_pair (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hK : IsCompact {x | x ∈ U ∧ f x ≤ c}) :
    ∃ (m n : ℕ) (P : Fin m → PieceEmbedding W) (Q : Fin n → PieceEmbedding W),
      (⋃ k, range (P k).map) ∪ (⋃ l, range (Q l).map) = univ ∧
      (⋃ k, range (P k).map) ∩ (⋃ l, range (Q l).map) = {x | x ∈ U ∧ f x = c} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      Pairwise (fun l l' => Disjoint (range (Q l).map) (range (Q l').map)) ∧
      (∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔ f ((P k).map q) = c) ∧
      ∀ l q, (𝓡∂ 3).IsBoundaryPoint q ↔
        (W.model.IsBoundaryPoint ((Q l).map q) ∨ ((Q l).map q ∈ U ∧ f ((Q l).map q) = c)) := by
  obtain ⟨m, P, hP, hPd, hPb⟩ := exists_pieces_of_interior_sublevel W U hU f c hf hreg hK
  obtain ⟨n, Q, hQ, hQd, hQb⟩ := exists_pieces_of_interior_superlevel W U hU f c hf hreg hK
  refine ⟨m, n, P, Q, ?_, ?_, hPd, hQd, hPb, hQb⟩
  · rw [hP, hQ]
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    by_cases hx : x ∈ U
    · rcases le_total (f x) c with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl hx)
  · rw [hP, hQ]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, h1⟩, hx' | h2⟩
      · exact absurd hx hx'
      · exact ⟨hx, le_antisymm h1 h2⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, h.le⟩, Or.inr h.ge⟩

end GC.GraphManifold.Assembly
