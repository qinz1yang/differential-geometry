import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_one_space_iff_degree_eq_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) (v : K.vertices) :
    (v : E) ∈ (boundaryComplex 1 K).space ↔
      ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 1 := by
  rw [mem_boundaryComplex_one_space_iff K (fun s hs => hK.card_le K hs),
    SimplicialComplex.ncard_neighborSet_edgeGraph, Set.ncard_eq_one]
  exact and_iff_right v.property

open Classical in
theorem IsCombinatorialManifoldWithBoundary.even_ncard_boundaryComplex_one_space
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) :
    Even (boundaryComplex 1 K).space.ncard := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  let _ : Fintype K.vertices := Fintype.ofFinite _
  let G := SimplicialComplex.edgeGraph K
  have hdegree (v : K.vertices) : (G.neighborSet v).ncard = 1 ∨
      (G.neighborSet v).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    rcases (isCombinatorialManifoldWithBoundary_one_iff K).mp hK |>.2 v v.property with h | h
    · exact Or.inl (Set.ncard_eq_one.mpr h)
    · exact Or.inr (Set.ncard_eq_two.mpr h)
  have hodd (v : K.vertices) : Odd (G.degree v) ↔
      (v : E) ∈ (boundaryComplex 1 K).space := by
    rw [hK.mem_boundaryComplex_one_space_iff_degree_eq_one K,
      ← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    rcases hdegree v with h | h <;> rw [h] <;> decide
  have himage : ((↑) : K.vertices → E) '' {v | Odd (G.degree v)} =
      (boundaryComplex 1 K).space := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hodd v).mp hv
    · intro hx
      have hxv : x ∈ K.vertices :=
        ((mem_boundaryComplex_one_space_iff K (fun s hs => hK.card_le K hs)).mp hx).1
      exact ⟨⟨x, hxv⟩, (hodd ⟨x, hxv⟩).mpr hx, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using G.even_card_odd_degree_vertices

open Classical in
theorem IsCombinatorialManifoldWithBoundary.boundaryComplex_one_space_ne_singleton
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) (x : E) :
    (boundaryComplex 1 K).space ≠ {x} := by
  intro h
  have heven := hK.even_ncard_boundaryComplex_one_space K
  rw [h, Set.ncard_singleton] at heven
  exact (by decide : ¬Even (1 : ℕ)) heven

end DifferentialGeometry.Topology.PiecewiseLinear
