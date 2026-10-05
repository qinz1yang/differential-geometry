import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryComponent.SurfaceNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSystem

open Classical in
theorem vertexCollisionPairs_subset_of_factorization
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E → F) (g : E → G) (p : G → F)
    (factorization : ∀ v ∈ K.vertices, p (g v) = f v) :
    vertexCollisionPairs K g ⊆ vertexCollisionPairs K f := by
  intro s hs
  rw [mem_vertexCollisionPairs] at hs ⊢
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro injective
  apply hs.2.2
  intro v hv w hw hgw
  apply injective hv hw
  calc
    f v = p (g v) := (factorization v (hs.1 hv)).symm
    _ = p (g w) := congrArg p hgw
    _ = f w := factorization w (hs.1 hw)

open Classical in
theorem simplicialComplexity_le_of_factorization
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E → F) (g : E → G) (p : G → F)
    (factorization : ∀ v ∈ K.vertices, p (g v) = f v) :
    simplicialComplexity K g ≤ simplicialComplexity K f := by
  exact Finset.card_le_card
    (vertexCollisionPairs_subset_of_factorization K f g p factorization)

open Classical in
theorem simplicialComplexity_lt_of_factorization_of_separated
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E → F) (g : E → G) (p : G → F)
    (factorization : ∀ v ∈ K.vertices, p (g v) = f v)
    (separated :
      ∃ v ∈ K.vertices, ∃ w ∈ K.vertices,
        v ≠ w ∧ f v = f w ∧ g v ≠ g w) :
    simplicialComplexity K g < simplicialComplexity K f := by
  have collisionSubset :=
    vertexCollisionPairs_subset_of_factorization K f g p factorization
  obtain ⟨v, hv, w, hw, hvw, hfvw, hgvw⟩ := separated
  let s : Finset E := {v, w}
  have sourceCollision : s ∈ vertexCollisionPairs K f := by
    rw [mem_vertexCollisionPairs]
    refine ⟨?_, by simp [s, hvw], ?_⟩
    · intro x hx
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · intro injective
      exact hvw (injective (by simp [s]) (by simp [s]) hfvw)
  have targetInjective : InjOn g (s : Set E) := by
    intro x hx y hy hxy
    simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · rfl
      · exact (hgvw hxy).elim
    · rcases hy with rfl | rfl
      · exact (hgvw hxy.symm).elim
      · rfl
  have targetNotCollision : s ∉ vertexCollisionPairs K g := by
    intro hs
    exact ((mem_vertexCollisionPairs K g s).mp hs).2.2 targetInjective
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨collisionSubset, fun heq => targetNotCollision (heq ▸ sourceCollision)⟩

open Classical in
theorem eq_vertexMap_of_eq_simplicialComplexity_of_factorization
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E → F) (g : E → G) (p : G → F)
    (factorization : ∀ v ∈ K.vertices, p (g v) = f v)
    (complexity_eq : simplicialComplexity K g = simplicialComplexity K f)
    {v w : E} (hv : v ∈ K.vertices) (hw : w ∈ K.vertices)
    (hfvw : f v = f w) : g v = g w := by
  by_contra hgvw
  have hlt := simplicialComplexity_lt_of_factorization_of_separated K f g p factorization
    ⟨v, hv, w, hw, fun hvw => hgvw (congrArg g hvw), hfvw, hgvw⟩
  rw [complexity_eq] at hlt
  exact (lt_irrefl _ hlt)

open Classical in
theorem injOn_vertexMap_iff_of_eq_simplicialComplexity_of_factorization
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : E → F) (g : E → G) (p : G → F)
    (factorization : ∀ v ∈ K.vertices, p (g v) = f v)
    (complexity_eq : simplicialComplexity K g = simplicialComplexity K f) :
    InjOn f K.vertices ↔ InjOn g K.vertices := by
  constructor
  · intro hf v hv w hw hgvw
    apply hf hv hw
    calc
      f v = p (g v) := (factorization v hv).symm
      _ = p (g w) := congrArg p hgvw
      _ = f w := factorization w hw
  · intro hg v hv w hw hfvw
    exact hg hv hw
      (eq_vertexMap_of_eq_simplicialComplexity_of_factorization K f g p factorization
        complexity_eq hv hw hfvw)

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
