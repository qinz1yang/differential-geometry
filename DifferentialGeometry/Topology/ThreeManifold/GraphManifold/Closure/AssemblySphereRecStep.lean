import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapProjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapBallApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBadModelsApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ComponentsApplications

/-!
# FC42 sphere recursion, packet S5: the strengthened B4 step

Lane ASM-SPH2b (frozen statements `build-logs/scratch/ASM-SPH/Targets.lean` v2, S5, verbatim).

* `sphereSide_model`: a side of a sphere seam is a ball, a punctured `RP³` or an `S² × I` (the
  restatement of lane ASM-NRM's `sphereSide_cases`).
* `exists_sphereRecursionStep`: cut and cap the seam `c` (`exists_sphereCutCapped`), take the
  component decomposition of the capped carrier (`SphereCutCapped.nonempty_components`); a component
  containing the cap of a ball side is `S³` (Raw, `nonempty_rawGraphPresentation_component_of_ball`),
  one containing the cap of a punctured-`RP³` side is `RP³` (S3b,
  `componentCarrier_projective_of_puncturedRP3`), and every other component has only `S² × I` caps
  and carries the inherited certificate (S4, `exists_cappedComponentCertificate`).
* Consumer `exists_sphereRecursionStep_sphereMeasure_lt`: the inherited certificates have smaller
  measure `μ = sphereSeamCount + badVertexCount`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **S5 (classification of sphere sides).** A side of a sphere seam is a ball, a punctured `RP³`
or an `S² × I` (no other vertex model has a two-sphere boundary component). -/
theorem sphereSide_model (c : Fin D.sphereSeamCount) (b : Bool) :
    (D.vertex (D.sphereSide c b)).IsBall ∨
    (∃ (P : PieceEmbedding W)
      (c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)) ∨
    (∃ (P : PieceEmbedding W)
      (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :=
  D.sphereSide_cases c b

/-- **S5 = strengthened B4** (review 40 §2.3 with the coordinator's finer bad-count clause;
`X` is produced jointly with the inherited data). For a sphere seam `c` of a certificate without
closed zero vertex on a connected carrier: some cut-and-capped data of `c` and a component
decomposition of the capped carrier such that every component is Raw (`S³` from a ball side), or
`RP³` (punctured-`RP³` side), or carries an inherited certificate with the restricted ports, one
sphere seam fewer, bad vertices injecting into the non-side bad vertices of `D`, no closed zero
vertex, and the rim-product clause inherited. -/
theorem exists_sphereRecursionStep [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (c : Fin D.sphereSeamCount) :
    ∃ (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
        D'.sphereSeamCount < D.sphereSeamCount ∧
        D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
        (∀ k C, D'.vertex k ≠ .closedZero C) ∧
        (D.RimProduct → D'.RimProduct) := by
  obtain ⟨X⟩ := exists_sphereCutCapped W (D.sphereSeam c) E D.external_exhausted
    fun i => D.external_sphereSeam_disjoint i c
  obtain ⟨DQ⟩ := X.nonempty_components
  refine ⟨X, DQ, fun i => ?_⟩
  by_cases hball : ∃ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i ∧
      (D.vertex (D.sphereSide c b)).IsBall
  · obtain ⟨b, hb, hk⟩ := hball
    subst hb
    exact Or.inl (D.nonempty_rawGraphPresentation_component_of_ball c X b hk DQ)
  by_cases hrp : ∃ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i ∧
      ∃ (P : PieceEmbedding W)
        (c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
        (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
        (hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
        D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)
  · obtain ⟨b, hb, P, c', f, hf, hr, hv⟩ := hrp
    subst hb
    exact Or.inr (Or.inl (D.componentCarrier_projective_of_puncturedRP3 c X b hv DQ))
  · refine Or.inr (Or.inr (D.exists_cappedComponentCertificate hnz c X DQ i fun b hb => ?_))
    rcases D.sphereSide_model c b with h | h | h
    · exact (hball ⟨b, hb, h⟩).elim
    · exact (hrp ⟨b, hb, h⟩).elim
    · exact h

/-- **Consumer (S5).** The inherited certificates of the sphere recursion step have smaller
measure `μ = sphereSeamCount + badVertexCount`, no closed zero vertex, and inherit the rim-product
clause. -/
theorem exists_sphereRecursionStep_sphereMeasure_lt [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (c : Fin D.sphereSeamCount) :
    ∃ (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
        D'.sphereMeasure < D.sphereMeasure ∧ (∀ k C, D'.vertex k ≠ .closedZero C) ∧
        (D.RimProduct → D'.RimProduct) := by
  obtain ⟨X, DQ, h⟩ := D.exists_sphereRecursionStep hnz c
  refine ⟨X, DQ, fun i => ?_⟩
  rcases h i with h | h | ⟨D', hs, hb, hz, hr⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨D', ?_, hz, hr⟩)
    have hle : (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ≤
        D.badVertexCount := by
      rw [← D.card_badVertexSet]
      exact Finset.card_filter_le _ _
    unfold sphereMeasure
    omega

end DecompositionCertificate

end GC.GraphManifold.Assembly
