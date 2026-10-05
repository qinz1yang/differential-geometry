import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalSystem.Orientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_embeddedDisk_of_stallings_induction_orientable_buffered
    (coverStep :
        ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
          (S : NormalSystem E),
          S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
            frontier S.sourceComplex.space →
          S.basepoint = S.boundaryLoop 0 →
          S.IsOrientableManifold →
          ¬IsPLSphere 2 S.boundaryComponent →
          ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
            (R : NormalSystem.DoubleCoverReduction S T),
            T.basepoint = T.boundaryLoop 0 ∧
            T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
              frontier T.sourceComplex.space ∧
            T.IsOrientableManifold ∧
            ∀ x ∈ T.boundaryNeighborhood.space,
              S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x))
    (lemmaTwo :
      ∀ {M M' : ℕ} {S : NormalSystem (EuclideanSpace ℝ (Fin M))}
        {T : NormalSystem (EuclideanSpace ℝ (Fin M'))}
        (R : NormalSystem.DoubleCoverReduction S T),
        S.IsOrientableManifold →
        T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
          frontier T.sourceComplex.space →
        T.basepoint = T.boundaryLoop 0 →
        (∀ x ∈ T.boundaryNeighborhood.space,
          S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) →
        Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S))
    {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N)))
    (hor : S.IsOrientableManifold)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space) :
    Nonempty (NormalSystem.EmbeddedDisk S) := by
  have inductionStatement :
      ∀ k : ℕ, ∀ (M : ℕ) (R : NormalSystem (EuclideanSpace ℝ (Fin M))),
        R.complexity = k → R.IsOrientableManifold →
        R.sourceComplex.space ∩ R.singularMap ⁻¹' R.boundaryComplex.space =
          frontier R.sourceComplex.space →
        R.basepoint = R.boundaryLoop 0 → Nonempty (NormalSystem.EmbeddedDisk R) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k inductionHypothesis =>
        intro M R hcomplexity horR hproperR hbaseR
        by_cases sphereBoundary : IsPLSphere 2 R.boundaryComponent
        · exact R.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent sphereBoundary
        · obtain ⟨M', T, reduction, hbaseT, hproperT, horT, hbufferT⟩ :=
            coverStep R hproperR hbaseR horR sphereBoundary
          refine lemmaTwo reduction horR hproperT hbaseT hbufferT ?_
          exact inductionHypothesis T.complexity
            (by simpa only [hcomplexity] using reduction.complexity_lt) M' T rfl horT hproperT
              hbaseT
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (inductionStatement S.atBoundaryLoop.complexity N S.atBoundaryLoop rfl hor hproper rfl)

theorem exists_embeddedDisk_of_stallings_induction_general_orientable_buffered
    (coverStep :
        ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
          (S : NormalSystem E),
          S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
            frontier S.sourceComplex.space →
          S.basepoint = S.boundaryLoop 0 →
          S.IsOrientableManifold →
          ¬IsPLSphere 2 S.boundaryComponent →
          ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
            (R : NormalSystem.DoubleCoverReduction S T),
            T.basepoint = T.boundaryLoop 0 ∧
            T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
              frontier T.sourceComplex.space ∧
            T.IsOrientableManifold ∧
            ∀ x ∈ T.boundaryNeighborhood.space,
              S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x))
    (lemmaTwo :
        ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
          {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))}
          (R : NormalSystem.DoubleCoverReduction S T),
          S.IsOrientableManifold →
          T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
            frontier T.sourceComplex.space →
          T.basepoint = T.boundaryLoop 0 →
          (∀ x ∈ T.boundaryNeighborhood.space,
            S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) →
          Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) (hor : S.IsOrientableManifold)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space) :
    Nonempty (NormalSystem.EmbeddedDisk S) := by
  have normalised : ∀ R : NormalSystem E, R.IsOrientableManifold →
      R.sourceComplex.space ∩ R.singularMap ⁻¹' R.boundaryComplex.space =
        frontier R.sourceComplex.space →
      R.basepoint = R.boundaryLoop 0 → Nonempty (NormalSystem.EmbeddedDisk R) := by
    intro R horR hproperR hbaseR
    by_cases sphereBoundary : IsPLSphere 2 R.boundaryComponent
    · exact R.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent sphereBoundary
    · obtain ⟨M, T, reduction, hbaseT, hproperT, horT, hbufferT⟩ :=
        coverStep R hproperR hbaseR horR sphereBoundary
      exact lemmaTwo reduction horR hproperT hbaseT hbufferT
        (exists_embeddedDisk_of_stallings_induction_orientable_buffered coverStep
          (fun reduction' hor' hproper' hbase' hbuffer' hdisk' =>
            lemmaTwo reduction' hor' hproper' hbase' hbuffer' hdisk')
          T horT hproperT)
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (normalised S.atBoundaryLoop hor hproper rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
