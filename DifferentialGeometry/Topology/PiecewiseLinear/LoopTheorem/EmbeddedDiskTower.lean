/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalBasepoint
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SphereCase

/-!
# The Stallings tower at the level of embedded disks

`MoiseChainPL` reduces `Moise252` to the production of a proper piecewise linear embedded disk
inside a normal system, a statement recorded there as `Moise251PLGeneral`.  This file carries out
the Stallings tower induction for that production, so that only the tower step itself, Lemma 2, is
left open.

The induction is on `NormalSystem.complexity`.  When the relevant boundary component is a
piecewise linear `2`-sphere the disk is produced outright by
`NormalSystem.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent`.  Otherwise
`NormalSystem.exists_doubleCoverReduction_of_boundaryComponent_not_isPLSphere` produces a double
cover of strictly smaller complexity, together with the properness and basepoint normalisations
of the cover, and Lemma 2 pushes an embedded disk of the cover back down.

Two hypotheses of the analogous nonsingular-cell induction
`NormalSystem.exists_nonsingular_cell_of_stallings_induction` are absent here.

* No orientability cover hypotheses appear, because the cover producer makes the
  orientable / non-orientable case split internally and covers both branches.
* No basepoint normalisation `NormalSystem.basepoint = NormalSystem.boundaryLoop 0` appears,
  because `NormalSystem.atBoundaryLoop` establishes it without changing the source complex, the
  singular map, the boundary complex or the complexity, and
  `NormalSystem.EmbeddedDisk.ofAtBoundaryLoop` transports the resulting disk back.

The properness condition

`S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space = frontier S.sourceComplex.space`

does remain a hypothesis.  It is not a consequence of the `NormalSystem` structure: the structure
records the image-side identity
`imageComplex.space ∩ boundaryComplex.space = loopComplex.space`, which gives one inclusion, while
the reverse inclusion genuinely fails for a singular map carrying an interior point of the source
onto the boundary.  It is, however, produced alongside every normal system that
`exists_normalSystem_of_isPiecewiseAffineOn` manufactures, hence available for every normal system
the `Moise252` chain actually builds.

Main contents.

* `exists_embeddedDisk_of_stallings_induction`: the tower induction over a Euclidean ambient
  space, from Lemma 2 in its Euclidean form.
* `exists_embeddedDisk_of_stallings_induction_general`: the same over an arbitrary finite
  dimensional real normed space, from Lemma 2 in its general form.  The first cover already lands
  in a Euclidean space, so only the outermost tower step uses the general form.
* `nonempty_embeddedDisk_of_lemmaTwo_of_properness`: the statement of `Moise251PLGeneral`, written
  out, from Lemma 2 together with the properness condition for all normal systems.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- The Stallings tower induction producing a proper piecewise linear embedded disk in a normal
system over a Euclidean ambient space, assuming Lemma 2.

`lemmaTwo` is the tower step: an embedded disk in a double cover of a normal system, the cover
being proper and basepoint normalised, descends to an embedded disk in the system itself.  The
properness hypothesis `hproper` is what the cover producer consumes and is not available for a
general normal system. -/
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

/-- The Stallings tower induction over an arbitrary finite dimensional real normed space.

The first double cover already lives over a Euclidean space, so `lemmaTwo` is used in its general
form only for the outermost step; everything below it is
`exists_embeddedDisk_of_stallings_induction`. -/
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

/-- The conclusion of `Moise251PLGeneral`, written out, from Lemma 2 together with the properness
condition for all normal systems.

`Moise251PLGeneral` asks for an embedded disk in *every* normal system, including ones whose
singular map carries an interior point of the source onto the boundary, so the properness
condition cannot be dropped here.  It can be discharged wherever the normal system comes from
`exists_normalSystem_of_isPiecewiseAffineOn`, which produces it. -/
theorem nonempty_embeddedDisk_of_lemmaTwo_of_properness
    (lemmaTwo :
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))},
        NormalSystem.DoubleCoverReduction S T →
        T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
          frontier T.sourceComplex.space →
        T.basepoint = T.boundaryLoop 0 →
        Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S))
    (properness :
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        (S : NormalSystem F),
        S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
          frontier S.sourceComplex.space) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (S : NormalSystem E), Nonempty (NormalSystem.EmbeddedDisk S) :=
  fun S => exists_embeddedDisk_of_stallings_induction_general
    (fun reduction hproper' hbase' hdisk' => lemmaTwo reduction hproper' hbase' hdisk')
    S (properness S)

end DifferentialGeometry.Topology.PiecewiseLinear
