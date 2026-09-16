import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SurfaceNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Mathlib.Topology.Covering.Basic

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSystem

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
  have collisionSubset :
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
noncomputable def boundaryComponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) : Set E :=
  connectedComponentIn S.boundaryComplex.space (S.boundaryLoop 0 : E)

open Classical in
noncomputable def IsOrientableManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) : Prop := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact IsOrientable 3 S.manifoldComplex

open Classical in
structure NonsingularCell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) where
  sourceComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))
  finite_source : sourceComplex.faces.Finite
  source_isPLBall : IsPLBall 2 sourceComplex.space
  vertexMap : EuclideanSpace ℝ (Fin 2) → E
  source_faces_map :
    ∀ s ∈ sourceComplex.faces, s.image vertexMap ∈ S.manifoldComplex.faces
  nonsingular : InjOn (simplicialMap sourceComplex vertexMap) sourceComplex.space
  boundaryLoop : freeLoop S.boundaryNeighborhoodSpace
  boundary_range :
    Set.range (fun θ => (boundaryLoop θ : E)) =
      simplicialMap sourceComplex vertexMap '' frontier sourceComplex.space
  connector : Path S.basepoint (boundaryLoop 0)
  loopClass_avoids_normal :
    ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass S.basepoint boundaryLoop connector) S.normalSubgroup

open Classical in
structure DoubleCoverReduction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (S : NormalSystem E)
    (T : NormalSystem (EuclideanSpace ℝ (Fin N))) where
  projection : T.manifoldComplex.space → S.manifoldComplex.space
  isCoveringMap : IsCoveringMap projection
  fiber_card : ∀ x, Nat.card (projection ⁻¹' {x}) = 2
  complexity_lt : T.complexity < S.complexity

open Classical in
theorem exists_nonsingular_cell_of_stallings_induction
    (lemmaOne :
      ∀ {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N))),
        IsPLSphere 2 S.boundaryComponent → Nonempty (NonsingularCell S))
    (lemmaTwo :
      ∀ {N N' : ℕ} {S : NormalSystem (EuclideanSpace ℝ (Fin N))}
        {T : NormalSystem (EuclideanSpace ℝ (Fin N'))},
        DoubleCoverReduction S T → Nonempty (NonsingularCell T) →
          Nonempty (NonsingularCell S))
    (nonorientableDoubleCover :
      ∀ {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N))),
        ¬S.IsOrientableManifold →
          ∃ (N' : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N'))),
            Nonempty (DoubleCoverReduction S T))
    (orientableNonsphericalBoundaryDoubleCover :
      ∀ {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N))),
        S.IsOrientableManifold → ¬IsPLSphere 2 S.boundaryComponent →
          ∃ (N' : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N'))),
            Nonempty (DoubleCoverReduction S T))
    {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N))) :
    Nonempty (NonsingularCell S) := by
  have inductionStatement :
      ∀ k : ℕ, ∀ (N : ℕ) (S : NormalSystem (EuclideanSpace ℝ (Fin N))),
        S.complexity = k → Nonempty (NonsingularCell S) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k inductionHypothesis =>
        intro N S hcomplexity
        by_cases sphereBoundary : IsPLSphere 2 S.boundaryComponent
        · exact lemmaOne S sphereBoundary
        · by_cases orientable : S.IsOrientableManifold
          · obtain ⟨N', T, ⟨reduction⟩⟩ :=
              orientableNonsphericalBoundaryDoubleCover S orientable sphereBoundary
            apply lemmaTwo reduction
            apply inductionHypothesis T.complexity
            · simpa only [hcomplexity] using reduction.complexity_lt
            · rfl
          · obtain ⟨N', T, ⟨reduction⟩⟩ := nonorientableDoubleCover S orientable
            apply lemmaTwo reduction
            apply inductionHypothesis T.complexity
            · simpa only [hcomplexity] using reduction.complexity_lt
            · rfl
  exact inductionStatement S.complexity N S rfl

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
