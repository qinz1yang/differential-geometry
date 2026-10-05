import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapProjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.ProjectiveLens

/-!
# Consumers of packet S3b (lane ASM-SPH3b)

* `DecompositionCertificate.componentCarrier_projective_of_sphereSide`: S3b read from the
  existential form of a punctured-`ℝP³` side (the middle disjunct of the S5 side classification
  `sphereSide_model`, frozen in `build-logs/scratch/ASM-SPH/Targets.lean`).
* `DecompositionCertificate.exists_rawGraphPresentation_component_of_puncturedRP3`: B4's first
  branch for a punctured-`ℝP³` side — the component of the capped carrier containing its cap has a
  raw graph presentation with two pieces, one pairing torus and no external torus (the lens
  presentation of `ℝP³`, `exists_rawGraphPresentation_of_projectiveThreeSpaceLift_diffeomorph`,
  carried along S3b).
* `SphereCutCapped.exists_capUnion_closedDiffeomorph`: the X-level form, for any piece on one side
  of the seam embedded in a closed three-manifold `Y` as the complement of an open unit ball chart,
  with the seam sphere as model boundary and the half collar of its side.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **X-level: a punctured `Y` side and its cap are `Y`.** -/
theorem SphereCutCapped.exists_capUnion_closedDiffeomorph {W : CompactCarrier.{u}}
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E)
    (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    {Y : ConnectedClosedOrientedManifold.{u} 3}
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    {f : P.Piece → Y.Carrier} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (hhalf : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, cutSideSign j * s) ∈ range P.map) :
    ∃ U : TopologicalSpace.Opens X.Q.Carrier,
      (U : Set X.Q.Carrier) = range (X.liftPiece P j hside).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm j)) ∧
      IsCompact (U : Set X.Q.Carrier) ∧ Nonempty (U ≃ₘ⟮X.Q.model, 𝓡 3⟯ Y.Carrier) :=
  ⟨_, rfl, X.isCompact_capUnion P j hside,
    X.nonempty_capUnion_closedDiffeomorph P j hside c hc hf hrange hbd hhalf⟩

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **S3b from the side classification**: if side `b` of the seam is a punctured `ℝP³` (in the
existential form of the S5 classification), the component of the capped carrier containing its
cap is the fixed `ℝP³`. -/
theorem componentCarrier_projective_of_sphereSide (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool)
    (h : ∃ (P : PieceEmbedding W)
      (c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange))
    (DQ : X.Q.Components) :
    Nonempty ((GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).Carrier ≃ₘ⟮
      (GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).model, 𝓡 3⟯
      projectiveThreeSpaceLift.{u}.Carrier) := by
  obtain ⟨P, c', f, hf, hrange, hv⟩ := h
  exact D.componentCarrier_projective_of_puncturedRP3 c X b hv DQ

/-- **B4, first branch, punctured-`ℝP³` side**: the capped component of a punctured-`ℝP³` side
has a raw graph presentation with two pieces, one pairing torus and no external torus. -/
theorem exists_rawGraphPresentation_component_of_puncturedRP3 (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool) {P : PieceEmbedding W}
    {c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange))
    (DQ : X.Q.Components) :
    ∃ G : RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))),
      G.components.count = 2 ∧ G.pairing.count = 1 ∧ G.externalCount = 0 := by
  obtain ⟨φ⟩ := D.componentCarrier_projective_of_puncturedRP3 c X b hv DQ
  exact exists_rawGraphPresentation_of_projectiveThreeSpaceLift_diffeomorph φ

end DecompositionCertificate

end GC.GraphManifold.Assembly
