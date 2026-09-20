/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskTower
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoSpine

/-!
# The buffered form of Moise's Lemma 2

`LemmaTwoStatement` gives the tower step only the double cover reduction and the two
normalisations of the covering system.  The cover producers actually establish one thing more:
the boundary neighborhood downstairs is a *neighborhood*, inside the boundary surface, of the
projection of the whole boundary neighborhood upstairs.  That extra clause is what Moise's
surgery needs at the boundary (the tube of Cases 1--4 has to stay inside the boundary
neighborhood after a small motion), and `LemmaTwoStatement` throws it away.

`LemmaTwoBufferedStatement` keeps it.  It is a *weaker* obligation than `LemmaTwoStatement`, and
this file shows that it is still enough for everything the tower needs.

* `lemmaTwoBufferedStatement_of_lemmaTwoStatement`: the unbuffered statement implies the buffered
  one, so nothing is gained for free.
* `exists_embeddedDisk_of_stallings_induction_buffered` and its general form re-run the Stallings
  tower of `EmbeddedDiskTower` from the buffered step.  Nothing in that tower is abstract over the
  reduction: both call sites of Lemma 2 construct their reduction on the spot, with
  `exists_doubleCoverReduction_of_boundaryComponent_not_isPLSphere`, whose unwrapped form
  `exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere` returns the buffer
  clause alongside.  So the buffer is in scope at every application of the step, and
  `moise252_of_lemmaTwoBuffered` and `moise304_of_lemmaTwoBuffered` follow.
* `GeneralPositionInDoubleBufferedStatement` is the general position obligation of
  `LemmaTwoSpine` with the buffer moved from its conclusion into its hypotheses, which is what the
  extra clause buys: general position no longer has to push the boundary curve off the frontier of
  the boundary neighborhood, it only has to keep it where it already is.
  `generalPositionInDoubleBufferedStatement_of_generalPositionInDoubleStatement` records that this
  is a weakening.  `lemmaTwoBufferedStatement_of_generalPosition_of_descentStep` is the buffered
  spine; the descent step obligation `DescentStepStatement` is reused unchanged.

## Transporting the buffer into the double

The two neighborhood conditions are the same condition read on the two sides of the embedding of
`|K|` into its double.  Downstairs the cover producers give
`S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)`, and
`NormalSystem.boundaryComplex` unfolds to `boundaryComplex 3 S.manifoldComplex`, which is the
complex whose image is the seam `Bd` of the double; so the two ambient sets agree.  The transport
itself is along the retraction `glueSnd`, which is continuous on the double and inverts the
embedding on the copy of `|K|` (`glueSnd_simplicialMap`), so preimages of downstairs
neighborhoods are neighborhoods upstairs.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- **Moise's Lemma 2 with the boundary buffer retained.**  Same as `LemmaTwoStatement`, except
that the covering system's boundary neighborhood is required to project into the *relative
interior*, inside the boundary surface downstairs, of the boundary neighborhood downstairs.  This
is exactly the clause the cover producers of `LoopTheorem.CoverReduction` establish and
`LemmaTwoStatement` discards. -/
def LemmaTwoBufferedStatement : Prop :=
  ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))}
    (R : NormalSystem.DoubleCoverReduction S T),
    T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
      frontier T.sourceComplex.space →
    T.basepoint = T.boundaryLoop 0 →
    (∀ x ∈ T.boundaryNeighborhood.space,
      S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) →
    Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S)

/-- The buffered statement is weaker: an unbuffered Lemma 2 proves it by ignoring the extra
clause.  Nothing else in this file uses this, it is the sanity check that the two statements are
not accidentally unrelated. -/
theorem lemmaTwoBufferedStatement_of_lemmaTwoStatement (lemmaTwo : LemmaTwoStatement) :
    LemmaTwoBufferedStatement :=
  fun R hproper hbase _ hdisk => lemmaTwo R hproper hbase hdisk

/-- The Stallings tower induction over a Euclidean ambient space, from the *buffered* Lemma 2.

This is `exists_embeddedDisk_of_stallings_induction` with the buffer clause threaded through.  The
reduction is built inside the induction, by the cover producer, so the buffer is available exactly
where the step consumes it; no abstraction over reductions is in the way. -/
theorem exists_embeddedDisk_of_stallings_induction_buffered
    (lemmaTwo :
      ∀ {M M' : ℕ} {S : NormalSystem (EuclideanSpace ℝ (Fin M))}
        {T : NormalSystem (EuclideanSpace ℝ (Fin M'))}
        (R : NormalSystem.DoubleCoverReduction S T),
        T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
          frontier T.sourceComplex.space →
        T.basepoint = T.boundaryLoop 0 →
        (∀ x ∈ T.boundaryNeighborhood.space,
          S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) →
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
        · obtain ⟨M', T, reduction, hbaseT, hproperT, hbufferT⟩ :=
            R.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere
              hproperR hbaseR sphereBoundary
          refine lemmaTwo reduction hproperT hbaseT hbufferT ?_
          exact inductionHypothesis T.complexity
            (by simpa only [hcomplexity] using reduction.complexity_lt) M' T rfl hproperT hbaseT
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (inductionStatement S.atBoundaryLoop.complexity N S.atBoundaryLoop rfl hproper rfl)

/-- The Stallings tower induction over an arbitrary finite dimensional real normed space, from the
buffered Lemma 2.  As in the unbuffered tower, only the outermost step uses the general form. -/
theorem exists_embeddedDisk_of_stallings_induction_general_buffered
    (lemmaTwo : LemmaTwoBufferedStatement)
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
    · obtain ⟨M, T, reduction, hbaseT, hproperT, hbufferT⟩ :=
        R.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere
          hproperR hbaseR sphereBoundary
      exact lemmaTwo reduction hproperT hbaseT hbufferT
        (exists_embeddedDisk_of_stallings_induction_buffered
          (fun reduction' hproper' hbase' hbuffer' hdisk' =>
            lemmaTwo reduction' hproper' hbase' hbuffer' hdisk')
          T hproperT)
  exact NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop
    (normalised S.atBoundaryLoop hproper rfl)

/-- `Moise252` follows from the buffered Lemma 2 alone, exactly as it follows from the unbuffered
one.  The buffer is supplied by the cover producer at every step of the tower. -/
theorem moise252_of_lemmaTwoBuffered (lemmaTwo : LemmaTwoBufferedStatement) : Moise252 :=
  moise252_of_normalSystemDiskOfProper fun S hproper =>
    exists_embeddedDisk_of_stallings_induction_general_buffered lemmaTwo S hproper

/-- The buffered Lemma 2 yields the spherical shell separation endpoint, so the buffered route
reaches the same place as `moise304_of_lemmaTwo`. -/
theorem moise304_of_lemmaTwoBuffered (lemmaTwo : LemmaTwoBufferedStatement) : Moise304 :=
  moise304_of_moise252 (moise252_of_lemmaTwoBuffered lemmaTwo)

open Classical in
/-- **General position in the double, with the boundary buffer given rather than produced.**  This
is `GeneralPositionInDoubleStatement` with one hypothesis added: the boundary circle of the cell
it starts from already has the boundary neighborhood as a relative neighborhood in the seam.  The
conclusion is unchanged, so the buffer has to be preserved, not created.

That is the whole point of the buffered route.  Under `LemmaTwoStatement` the entry cell only
satisfies `Set.range G.boundary ⊆ B`, and general position would have to push the curve off the
frontier of `B` with a collar the tree does not have; under `LemmaTwoBufferedStatement` the entry
cell satisfies the neighborhood form outright. -/
def GeneralPositionInDoubleBufferedStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E),
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    let B := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∀ (G : SingularTwoCell (double 3 K).space)
      (β : ContinuousMap loopCircle (frontier G.domain))
      (γ : freeLoop S.boundaryNeighborhoodSpace),
      (∀ x ∈ G.domain, ∃ U ∈ 𝓝[G.domain] x, Set.InjOn G U) →
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) →
      Set.range G.boundary ⊆ B →
      (∀ z ∈ Set.range G.boundary, B ∈ 𝓝[Bd] z) →
      G '' G.domain ∩ Bd = Set.range G.boundary →
      MapsTo G G.domain C →
      G.domain ∩ G ⁻¹' Bd = frontier G.domain →
      Function.Surjective β →
      (∀ θ, ((G (β θ) : (double 3 K).space) : E × E × ℝ) = ι (γ θ)) →
      ¬loopClassMeets γ S.basepoint S.normalSubgroup →
      ∃ (A : SingularTwoCell (double 3 K).space) (_ : NormalSingularCellData A Bd B),
        A.domain = G.domain ∧ MapsTo A A.domain C ∧
        (∀ z ∈ Set.range A.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier A.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((A (c θ) : (double 3 K).space) : E × E × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup

/-- The buffered general position obligation is weaker than the unbuffered one: it has the same
conclusion and one hypothesis more.  So proving it is strictly less work, which is what the
buffered route is for. -/
theorem generalPositionInDoubleBufferedStatement_of_generalPositionInDoubleStatement
    (generalPosition : GeneralPositionInDoubleStatement) :
    GeneralPositionInDoubleBufferedStatement :=
  fun S G β γ hinj hfiber hsubset _ hinter hside hproper hsurj hparam havoid =>
    generalPosition S G β γ hinj hfiber hsubset hinter hside hproper hsurj hparam havoid

/-- **The buffered spine of Moise's Lemma 2.**  Buffered general position in the double and the
unchanged descent step of Cases 1--4 give the whole of `LemmaTwoBufferedStatement`.

The only new content over `lemmaTwoStatement_of_generalPosition_of_descentStep` is the derivation
of the entry buffer: the projected boundary circle is `R.boundaryMap ∘ D.boundaryLoop`, whose
values are projections of points of the covering system's boundary neighborhood, so the buffer
hypothesis applies to them verbatim, and the retraction `glueSnd` carries the resulting downstairs
neighborhoods to neighborhoods in the seam of the double. -/
theorem lemmaTwoBufferedStatement_of_generalPosition_of_descentStep
    (generalPosition : GeneralPositionInDoubleBufferedStatement)
    (descentStep : DescentStepStatement) :
    LemmaTwoBufferedStatement := by
  classical
  intro F _ _ _ M S T R _ _ hbuffer hdisk
  obtain ⟨D⟩ := hdisk
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
    (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
  let B := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
    (ι '' S.boundaryNeighborhood.space)
  let π : (double 3 K).space → F := fun x => glueSnd F F (x : F × F × ℝ)
  obtain ⟨G, γ, q, β, -, hγ, -, hmapC, hproperC, hloc, hcard, havoid, hβsurj, hβ⟩ :=
    R.toDoubleCoverDiagram.exists_projected_singular_two_cell_with_boundaryLoop_lift D
  have hfrontC : frontier C = Bd := by
    have hC : C = ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
        (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space := by
      rw [glued₂_space]
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K S.isManifold
  have havoidγ : ¬loopClassMeets γ S.basepoint S.normalSubgroup := by
    have h := havoid
    rw [normalSystemLoopConjugacyClass_eq_conjugacyClass γ q] at h
    exact h
  have hBsub : Set.range G.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨θ, rfl⟩ := hβsurj x
    exact ⟨(γ θ : F), (γ θ).2, (hβ θ).symm⟩
  have hproperBd : G.domain ∩ G ⁻¹' Bd = frontier G.domain := by
    rw [← hfrontC]
    exact hproperC
  have hinterBd : G '' G.domain ∩ Bd = Set.range G.boundary := by
    rw [← image_inter_preimage, hproperBd]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  have hπcont : Continuous π := continuous_glueSnd.comp continuous_subtype_val
  have hπι : ∀ x ∈ K.space, glueSnd F F (ι x) = x := fun x hx =>
    glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hx
  have hγK : ∀ θ, (γ θ : F) ∈ K.space := fun θ =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).property)
  have hγproj : ∀ θ, (γ θ : F) = R.projection (D.boundaryLoop θ) := by
    intro θ
    rw [hγ]
    exact R.boundaryMap_eq (D.boundaryLoop θ)
  have hbufferBd : ∀ z ∈ Set.range G.boundary, B ∈ 𝓝[Bd] z := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨θ, rfl⟩ := hβsurj x
    have hval : ((G.boundary (β θ) : (double 3 K).space) : F × F × ℝ) = ι (γ θ) := hβ θ
    have hz : π (G.boundary (β θ)) = (γ θ : F) := by
      change glueSnd F F ((G.boundary (β θ) : (double 3 K).space) : F × F × ℝ) = (γ θ : F)
      rw [hval]
      exact hπι _ (hγK θ)
    have hp : S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (γ θ : F) := by
      rw [hγproj θ]
      exact hbuffer (D.boundaryLoop θ) (D.boundaryLoop θ).property
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hp
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨π ⁻¹' V, ?_, ?_⟩
    · apply hπcont.continuousAt.preimage_mem_nhds
      rw [hz]
      exact hV
    · rintro w ⟨hwV, b, hb, hbw⟩
      have hπw : π w = b := by
        change glueSnd F F ((w : (double 3 K).space) : F × F × ℝ) = b
        rw [← hbw]
        exact hπι b (PiecewiseLinear.boundaryComplex_space_subset 3 K hb)
      refine ⟨b, hVsub ⟨?_, hb⟩, hbw⟩
      rw [← hπw]
      exact hwV
  obtain ⟨A, hA, -, hAside, hAbuffer, hAloop⟩ :=
    generalPosition S G β γ (Covering.isLocallyInjective_domRestrict_iff.mp hloc) hcard
      hBsub hbufferBd hinterBd hmapC hproperBd hβsurj hβ havoidγ
  obtain ⟨A', hA', -, hnonsingular, -, hside, -, hloop⟩ :=
    NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive
      (fun A₀ _ => MapsTo A₀ A₀.domain C ∧
        (∀ z ∈ Set.range A₀.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier A₀.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((A₀ (c θ) : (double 3 K).space) : F × F × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup)
      (fun A₀ hA₀ hcomplexity hmotive =>
        descentStep S A₀ hA₀ hcomplexity hmotive.1 hmotive.2.1 hmotive.2.2)
      hA ⟨hAside, hAbuffer, hAloop⟩
  refine S.exists_embeddedDisk_of_nonsingular_two_cell_in_double A' hnonsingular ?_
    hA'.image_inter_boundary hloop
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact hside hx

end DifferentialGeometry.Topology.PiecewiseLinear
