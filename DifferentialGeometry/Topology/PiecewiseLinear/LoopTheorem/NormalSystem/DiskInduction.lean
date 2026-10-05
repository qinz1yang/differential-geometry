import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Covering.Existence
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalSystem.Basepoint
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryComponent.Sphere
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalSystem.Realization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_embeddedDisk_of_stallings_induction
    (lemmaTwo :
      ∀ {M M' : ℕ} {S : NormalSystem (EuclideanSpace ℝ (Fin M))}
        {T : NormalSystem (EuclideanSpace ℝ (Fin M'))},
        NormalSystem.DoubleCoverReduction S T →
        T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
          frontier T.sourceComplex.space →
        T.basepoint = T.boundaryLoop 0 →
        Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S))
    {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N)))
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space) :
    Nonempty (NormalSystem.EmbeddedDisk S) := by
  have inductionStatement :
      ∀ k : ℕ, ∀ (M : ℕ) (R : NormalSystem (EuclideanSpace ℝ (Fin M))),
        R.complexity = k →
        R.sourceComplex.space ∩ R.singularMap ⁻¹' R.boundaryComplex.space =
          frontier R.sourceComplex.space →
        R.basepoint = R.boundaryLoop 0 → Nonempty (NormalSystem.EmbeddedDisk R) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k inductionHypothesis =>
        intro M R hcomplexity hproperR hbaseR
        by_cases sphereBoundary : IsPLSphere 2 R.boundaryComponent
        · exact R.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent sphereBoundary
        · obtain ⟨M', T, ⟨reduction⟩, hbaseT, hproperT⟩ :=
            R.exists_doubleCoverReduction_of_boundaryComponent_not_isPLSphere
              hproperR hbaseR sphereBoundary
          refine lemmaTwo reduction hproperT hbaseT ?_
          exact inductionHypothesis T.complexity
            (by simpa only [hcomplexity] using reduction.complexity_lt) M' T rfl hproperT hbaseT
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (inductionStatement S.atBoundaryLoop.complexity N S.atBoundaryLoop rfl hproper rfl)

theorem exists_embeddedDisk_of_stallings_induction_general
    (lemmaTwo :
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))},
        NormalSystem.DoubleCoverReduction S T →
        T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
          frontier T.sourceComplex.space →
        T.basepoint = T.boundaryLoop 0 →
        Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space) :
    Nonempty (NormalSystem.EmbeddedDisk S) := by
  have normalised : ∀ R : NormalSystem E,
      R.sourceComplex.space ∩ R.singularMap ⁻¹' R.boundaryComplex.space =
        frontier R.sourceComplex.space →
      R.basepoint = R.boundaryLoop 0 → Nonempty (NormalSystem.EmbeddedDisk R) := by
    intro R hproperR hbaseR
    by_cases sphereBoundary : IsPLSphere 2 R.boundaryComponent
    · exact R.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent sphereBoundary
    · obtain ⟨M, T, ⟨reduction⟩, hbaseT, hproperT⟩ :=
        R.exists_doubleCoverReduction_of_boundaryComponent_not_isPLSphere
          hproperR hbaseR sphereBoundary
      exact lemmaTwo reduction hproperT hbaseT
        (exists_embeddedDisk_of_stallings_induction
          (fun reduction' hproper' hbase' hdisk' => lemmaTwo reduction' hproper' hbase' hdisk')
          T hproperT)
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (normalised S.atBoundaryLoop hproper rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
