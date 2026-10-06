import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.LocalRawFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawConnectedSumConnector
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereBundle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleRaw
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyEdgeCircleSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalTheorem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.ProjectiveLens
import DifferentialGeometry.Geometry.Thurston.CyclicSphericalRecognition
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive

/-!
# FC41 as one row: the topological closure library for the static output

Lane S-FC41 (suffix `_SFR`), group G1. Blueprint `master207B.tex`, FC41
(`found:fibration-topological-closure`, B:7476–7499), read against the clause table of lane
S-CLEAN (`docs/geometrization/chapter14/evidence/decisions/fc41-b10979-SCL.md`, part (a)).

`fc41_row_SFR` is the conjunction of the clauses of FC41 in the form in which FC42
(`exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct`) consumes them. Every
conjunct is stated in full (no named `Prop`, no new hypothesis, nothing conditional) and is proved
by an existing production declaration. The graph class of KL Definition 1.2 is
`RawGraphPresentation`, so a clause "`X` has a presentation" is `Nonempty (RawGraphPresentation X)`.

## Clause table (blueprint clause ↔ conjunct number ↔ library item)

The conjuncts of `fc41_row_SFR` are numbered 1–18 in the order of the statement.

* (1a) gluing along ENTIRE torus boundary components, finite collared witnesses — conjunct 1:
  `exists_rawGraphPresentation_of_rawPieces` (`Closure/LocalRawFaces.lean:331`, from a
  `TorusPresentation`); conjunct 2: `exists_rawGraphPresentation_of_regularCutData`
  (`Closure/AssemblyCutRaw.lean:53`, from explicit regular cut data and piece diffeomorphisms).
* (1b) connected sum — conjunct 3 (closed carriers): `rawGraphPresentation_connectedSum`
  (`Closure/RawConnectedSumConnector.lean:274`). The reading "possibly with boundary" is NOT a
  separate conjunct: the tree has no connected sum of two carriers with boundary. The direction
  FC42 consumes is the RECONSTRUCTION from the capped components of a sphere cut relative to the
  boundary tori: conjunct 15 (A4, separating: the connected sum of the two components) and
  conjunct 16 (A3, non-separating: addition of `S¹ × S²`).
* (2a) solid tori — conjunct 4: `exists_rawGraphPresentation_of_solidTorus_diffeomorph`
  (`Closure/CarrierDiffeomorphTransport.lean:70`), on every compact carrier diffeomorphic to the
  standard solid torus.
* (2b) twisted interval bundles over the Klein bottle — conjunct 5:
  `exists_rawGraphPresentation_of_twistedIBundle_diffeomorph` (same file).
* (2c) `S¹ × S²` — conjunct 6: `exists_rawGraphPresentation_of_sphereTwoTimesCircle_diffeomorph`
  (`Closure/AssemblySphereBundle.lean:133`).
* (2d) `RP³` — conjunct 7: `exists_rawGraphPresentation_of_projectiveThreeSpaceLift_diffeomorph`
  (`ProjectiveLens.lean:68`).
* (2e) orientable flat and spherical space forms, under the nonnegative-branch interface ruling
  (`docs/geometrization/chapter14/decision-nonnegative-branch-20261004.md`). Conjunct 8: the
  CYCLIC spherical space forms (lens spaces, `S³`) by
  `rawGraphPresentation_of_sphericalSpaceForm_cyclic`
  (`Geometry/Thurston/CyclicSphericalRecognition.lean:78`, proved). Conjunct 9: the disjunctive
  closed `sec ≥ 0` form: a raw presentation OR a closed carrier with an auxiliary `sec ≥ 0` metric
  gives a raw presentation OR a closed carrier with a spherical, `S² × ℝ` or Euclidean geometric
  structure (`raw_or_closedGeometric_of_raw_or_aux_nonneg`,
  `Geometry/Collapse/ThresholdDisjunctive.lean:20`, by
  `closed_nonnegative_sectional_classification_unconditional`). The two admitted statements
  `rawGraphPresentation_of_sphericalSpaceForm` and `rawGraphPresentation_of_flat`
  (`Geometry/Thurston/GraphPresentation.lean:12`, `:26`) are not used.
* (2f) `T²`-bundles over `S¹`, "cut at a fiber" — conjunct 10:
  `exists_rawGraphPresentation_of_torusBundle` (`Closure/AssemblyTorusBundleRaw.lean:31`), with the
  fibre-cut data (a submersion `p` to `S¹` and an embedded torus `f` with `range f = p⁻¹ {1}`), as
  in the blueprint's wording.
* (2g) an orientable `S²`-bundle over `S¹` is `S¹ × S²` — conjunct 11:
  `exists_sphereTwoTimesCircle_of_sphereBundle` (`Closure/AssemblySphereBundle.lean:69`), with the
  same fibre-cut data.
* (3a) a punctured `RP³` replaced by a ball with explicit reconstruction — conjunct 13 (N2):
  `DecompositionCertificate.exists_internalSphereCut_puncturedRP3`
  (`Closure/AssemblyNormSphereCutProjective.lean:40`); the `RP³` component itself is Raw by
  conjunct 7.
* (3b) a sphere cylinder cut and capped, reconstruction a connected sum or `+ S¹ × S²` —
  conjunct 12 (S5 `DecompositionCertificate.exists_sphereRecursionStep`), conjunct 14 (N3
  `DecompositionCertificate.exists_internalSphereCut_sphereInterval`), conjuncts 15 and 16 (A4
  `exists_rawGraphPresentation_of_sphereCut_separating`, A3
  `exists_rawGraphPresentation_of_sphereCut_nonseparating`).
* (4) a finite cyclic assembly of balls with exactly two disk faces and product disk handles is a
  solid torus with its actual attaching maps — conjunct 17 (L1,
  `exists_solidTorus_of_ballHandleCycle_of_rimProduct`, `Closure/AssemblyL1Cycle.lean:37`, whose
  rim-product and interior clauses are part of the clause itself); conjunct 18 (D2S1,
  `exists_solidTorus_of_edgeCirclePiece`, `Closure/AssemblyEdgeCircleSolidTorus.lean:44`: a
  circle-base edge piece is a solid torus).

No `sorry` declaration is used: the three Thurston recognitions of
`Geometry/Thurston/GraphPresentation.lean` do not occur below the row.

Gaps recorded (see the delivery block): the literal "connected sum possibly with boundary" in the
forward direction (two carriers with boundary in, their sum out) has no statement in the tree and
is not needed by FC42; the non-cyclic spherical and the six flat space forms are the admitted,
non-critical recognitions.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **FC41** (`found:fibration-topological-closure`, B:7476–7499): the topological closure library
for the static output, in the nonnegative-branch interface form. The conjuncts, in order: (1a)
torus gluing from a torus presentation; (1a′) torus gluing from regular cut data; (1b) closed
connected sum; (2a) solid torus; (2b) twisted interval bundle over the Klein bottle; (2c)
`S² × S¹`; (2d) `RP³`; (2e) cyclic spherical space forms; (2e) the closed `sec ≥ 0` disjunction;
(2f) torus bundles over the circle cut at a fibre; (2g) sphere bundles over the circle are
`S² × S¹`; the sphere recursion step S5; the punctured `RP³` cut N2; the sphere cylinder cut N3;
the separating and non-separating reconstructions A4 and A3; the ball–handle cycle L1; the
circle-base edge piece D2S1. -/
theorem fc41_row_SFR :
    -- (1a) gluing along entire torus boundary components (torus presentation)
    (∀ {W : CompactCarrier.{u}} (T : TorusPresentation W),
      (∀ i, Nonempty (RawGraphPresentation (T.Component i))) →
        Nonempty (RawGraphPresentation W)) ∧
    -- (1a′) the same from regular cut data with piece diffeomorphisms
    (∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : RegularCutData W E),
      (∀ j, ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
        Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (D.piece j).Piece)) →
        Nonempty (RawGraphPresentation W)) ∧
    -- (1b) connected sum of closed carriers
    (∀ M N : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (RawGraphPresentation (NoCuts.carrier M)) →
      Nonempty (RawGraphPresentation (NoCuts.carrier N)) →
        Nonempty (RawGraphPresentation (NoCuts.carrier (connectedSum M N)))) ∧
    -- (2a) solid tori
    (∀ {W : CompactCarrier.{u}},
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, W.model⟯ W.Carrier) →
        ∃ G : RawGraphPresentation W,
          G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1) ∧
    -- (2b) twisted interval bundles over the Klein bottle
    (∀ {W : CompactCarrier.{u}},
      Nonempty (mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, W.model⟯
        W.Carrier) →
        ∃ G : RawGraphPresentation W,
          G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1) ∧
    -- (2c) S¹ × S²
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier],
      Nonempty (W.Carrier ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) →
        Nonempty (RawGraphPresentation W)) ∧
    -- (2d) RP³
    (∀ {W : CompactCarrier.{u}},
      Nonempty (W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) →
        ∃ G : RawGraphPresentation W,
          G.components.count = 2 ∧ G.pairing.count = 1 ∧ G.externalCount = 0) ∧
    -- (2e) cyclic spherical space forms (lens spaces, S³)
    (∀ (G : SphericalSpaceFormGroup) [IsCyclic G.group],
      Nonempty (RawGraphPresentation (NoCuts.carrier G.manifold.ulift.{0, u}))) ∧
    -- (2e) the closed sec ≥ 0 branch, disjunctive form (nonnegative-branch interface ruling)
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier],
      (Nonempty (RawGraphPresentation W) ∨
        (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0)) →
      Nonempty (RawGraphPresentation W) ∨
        (W.model.boundary W.Carrier = ∅ ∧
          ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) ∧
    -- (2f) T²-bundles over S¹, cut at a fibre
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier], W.model.boundary W.Carrier = ∅ →
      ∀ p : W.Carrier → Circle, ContMDiff W.model (𝓡 1) ∞ p →
      (∀ x, Surjective (mfderiv W.model (𝓡 1) p x)) →
      ∀ f : Torus → W.Carrier, IsSmoothEmbedding torusModel W.model ∞ f →
      range f = p ⁻¹' {1} → Nonempty (RawGraphPresentation W)) ∧
    -- (2g) S²-bundles over S¹ are S¹ × S²
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier], W.model.boundary W.Carrier = ∅ →
      ∀ p : W.Carrier → Circle, ContMDiff W.model (𝓡 1) ∞ p →
      (∀ x, Surjective (mfderiv W.model (𝓡 1) p x)) →
      ∀ f : ClosureSphere.{u} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ f →
      range f = p ⁻¹' {1} →
        Nonempty (W.Carrier ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle)) ∧
    -- (3b) S5: the sphere recursion step
    (∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → ∀ c : Fin D.sphereSeamCount,
      ∃ (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯
            projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount < D.sphereSeamCount ∧
          D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧
          (D.RimProduct → D'.RimProduct)) ∧
    -- (3a) N2: a punctured RP³ is cut off by a sphere and replaced by a ball
    (∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
        {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
        {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
        {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}},
      D.vertex k = .zero P (.puncturedRP3 c f hf hr) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯
            projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct)) ∧
    -- (3b) N3: a sphere cylinder is cut and capped
    (∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece},
      D.vertex k = .slim P (.sphereInterval e) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯
            projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct)) ∧
    -- (3b) A4: reconstruction from two capped components (connected sum, with boundary tori)
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 2 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W)) ∧
    -- (3b) A3: reconstruction from one capped component (addition of S¹ × S²)
    (∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 1 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W)) ∧
    -- (4) L1: a ball–handle cycle with product rims is a solid torus
    (∀ {W : CompactCarrier.{u}} (C : BallHandleCycle W), C.RimProduct →
      (∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) →
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece)) ∧
    -- (4) D2S1: a circle-base edge piece is a solid torus
    (∀ {W : CompactCarrier.{u}} (P : EdgeCirclePiece W),
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        P.piece.Piece)) :=
  ⟨fun T R => exists_rawGraphPresentation_of_rawPieces T fun i => (R i).some,
    fun D h => exists_rawGraphPresentation_of_regularCutData D h,
    fun M N G H => rawGraphPresentation_connectedSum M N G.some H.some,
    fun ⟨e⟩ => exists_rawGraphPresentation_of_solidTorus_diffeomorph e,
    fun ⟨e⟩ => exists_rawGraphPresentation_of_twistedIBundle_diffeomorph e,
    fun W _ ⟨e⟩ => exists_rawGraphPresentation_of_sphereTwoTimesCircle_diffeomorph W e,
    fun ⟨e⟩ => exists_rawGraphPresentation_of_projectiveThreeSpaceLift_diffeomorph e,
    fun G _ => GC.GraphManifold.rawGraphPresentation_of_sphericalSpaceForm_cyclic G,
    fun W _ h =>
      DifferentialGeometry.Geometry.Collapse.raw_or_closedGeometric_of_raw_or_aux_nonneg W h,
    fun W _ hW p hp hsub f hf hr =>
      exists_rawGraphPresentation_of_torusBundle W hW p hp hsub f hf hr,
    fun W _ hW p hp hsub f hf hr =>
      exists_sphereTwoTimesCircle_of_sphereBundle W hW p hp hsub f hf hr,
    DecompositionCertificate.exists_sphereRecursionStep,
    DecompositionCertificate.exists_internalSphereCut_puncturedRP3,
    DecompositionCertificate.exists_internalSphereCut_sphereInterval,
    exists_rawGraphPresentation_of_sphereCut_separating,
    fun W _ => exists_rawGraphPresentation_of_sphereCut_nonseparating W,
    exists_solidTorus_of_ballHandleCycle_of_rimProduct,
    exists_solidTorus_of_edgeCirclePiece⟩

end GC.GraphManifold.Assembly
