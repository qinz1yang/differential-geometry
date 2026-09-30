import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Covering.Defs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSystem

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
