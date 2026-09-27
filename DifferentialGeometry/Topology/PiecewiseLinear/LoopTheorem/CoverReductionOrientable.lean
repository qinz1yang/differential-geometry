/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem NormalSystem.isOrientableManifold_of_isSubdivision
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hsubdiv : IsSubdivision S.ambientComplex K) (hor : IsOrientable 3 K) :
    S.IsOrientableManifold := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hamb : IsCombinatorialManifoldWithBoundary 3 S.ambientComplex :=
    hK.of_isSubdivision hsubdiv
  exact IsOrientable.of_space_subset (derivedNeighborhood S.ambientComplex S.imageComplex)
    S.manifoldComplex S.manifold_space.subset (hamb.derivedNeighborhood S.imageComplex)
    S.isManifold (IsOrientable.derivedNeighborhood hamb (hor.subdivision hK hsubdiv))

def OrientableCoverReductionStatement : Prop :=
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
        S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)

theorem exists_embeddedDisk_of_stallings_induction_orientable_buffered
    (coverStep : OrientableCoverReductionStatement)
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
    (coverStep : OrientableCoverReductionStatement)
    (lemmaTwo : LemmaTwoBufferedOrientableStatement)
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

open Classical in
theorem moise252_of_normalSystemDiskOfProperOfOrientable
    (hdisk : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (S : NormalSystem E), S.IsOrientableManifold →
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space → Nonempty (NormalSystem.EmbeddedDisk S)) :
    Moise252 := by
  intro E _ _ _ K hKfin hK hor c hsub γ hnull hess
  let _ : Finite K.faces := hKfin
  have hVB : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆
      (boundaryComplex 3 K).space :=
    space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)
  have hVcomp : ∀ z ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space,
      connectedComponentIn (boundaryComplex 3 K).space z =
        (connectedComponentComplex (boundaryComplex 3 K) c).space := fun z hz =>
    (connectedComponentComplex_space_eq_connectedComponentIn (boundaryComplex 3 K) c hz).symm
  obtain ⟨P, f, a, δ, hP, hf, hfmap, hfbd, hδ, hhom⟩ :=
    exists_isPiecewiseAffineOn_fill_of_nullhomotopic K (boundaryComplex 3 K)
      (boundaryComplex_faces_subset 3 K) hVB hsub hVcomp γ hnull
  have hδess : ¬ δ.Nullhomotopic := fun hd =>
    hess (show γ.Nullhomotopic from FreeLoop.nullhomotopic_of_homotopic hhom hd)
  obtain ⟨O, hO, hOV⟩ :=
    exists_isOpen_inter_eq_connectedComponentComplex_space (boundaryComplex 3 K) c
  have hnbhd : (connectedComponentComplex (boundaryComplex 3 K) c).space ∈
      𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P) := by
    refine mem_nhdsSetWithin.mpr ⟨O, hO, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hOV.symm.subset (hfbd hz)).1
    · exact hOV.subset
  obtain ⟨S, hsource, hsubdiv, -, -, -, hproperS, hSB, β, hbase, hβ, -, hNcomap⟩ :=
    exists_normalSystem_of_isPiecewiseAffineOn K hK hP hf hfmap (hfbd.mono_right hVB) hnbhd a δ hδ
      (⊥ : Subgroup (FundamentalGroup
        (connectedComponentComplex (boundaryComplex 3 K) c).space (δ 0)))
      (fun hmeet => hδess ((conjugacyClassMeets_bot_iff_nullhomotopic δ _).mp hmeet))
  have hSK : S.manifoldComplex.space ⊆ K.space := by
    rw [S.manifold_space]
    exact (derivedNeighborhood_space_subset S.ambientComplex S.imageComplex).trans
      hsubdiv.space_eq.subset
  have hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space := hproperS.trans (congrArg frontier hsource.symm)
  have horS : S.IsOrientableManifold := S.isOrientableManifold_of_isSubdivision hK hsubdiv hor
  exact exists_polyhedralDisk_of_embeddedDisk K hK (Classical.choice (hdisk S horS hproper)) hSK
    (fun z hz => (hSB hz).1) β hβ hbase hNcomap

theorem moise252_of_lemmaTwoBufferedOrientable
    (coverStep : OrientableCoverReductionStatement)
    (lemmaTwo : LemmaTwoBufferedOrientableStatement) : Moise252 :=
  moise252_of_normalSystemDiskOfProperOfOrientable fun S hor hproper =>
    exists_embeddedDisk_of_stallings_induction_general_orientable_buffered coverStep lemmaTwo S
      hor hproper

theorem moise304_of_lemmaTwoBufferedOrientable
    (coverStep : OrientableCoverReductionStatement)
    (lemmaTwo : LemmaTwoBufferedOrientableStatement) : Moise304 :=
  moise304_of_moise252 (moise252_of_lemmaTwoBufferedOrientable coverStep lemmaTwo)

theorem moise305_tame_of_lemmaTwoBufferedOrientable
    (coverStep : OrientableCoverReductionStatement)
    (lemmaTwo : LemmaTwoBufferedOrientableStatement) : Moise305Tame :=
  moise305_tame_of_moise304 (moise304_of_lemmaTwoBufferedOrientable coverStep lemmaTwo)

theorem moise304_of_generalPosition_of_descentStepOrientable
    (coverStep : OrientableCoverReductionStatement)
    (generalPosition : GeneralPositionInDoubleBufferedStatement)
    (descentStep : DescentStepOrientableStatement) : Moise304 :=
  moise304_of_lemmaTwoBufferedOrientable coverStep
    (lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable
      generalPosition descentStep)

end DifferentialGeometry.Topology.PiecewiseLinear
