import DifferentialGeometry.Geometry.Thurston.SphericalStructureStandard
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandardClassification

/-!
# Closed nonnegatively curved `3`-manifolds geometrize

Chapter 7, survey packet P6: the closed `sec ≥ 0` branch of the endpoint goes straight to
`Geometrizes` through the standard certificates instead of a raw graph presentation.

* `FlatStructurePrime` is the named input (packet P7) that a closed oriented `3`-manifold
  with a Euclidean structure is prime; `geometrizes_of_euclideanStructure` then uses the
  zero-cut prime certificate whose single piece carries the given structure.
* `ClosedNonnegativeClassification` is the statement of the admitted
  `GC.Geometry.closed_nonnegative_sectional_classification`, recorded as a named input so this
  module depends on no admitted declaration. It is stated for a `CompactCarrier` with empty
  boundary; the closed carrier `NoCuts.carrier P` of `P` is the bridge
  (`exists_geometricStructure_of_nonnegative`). Splitting on the model gives
  `geometrizes_of_nonnegative_of_classification`; the `S² × ℝ` case consumes
  `SphericalProductStandardConnectedSum`.
* `ClosedNonnegativeTrichotomy` is the diffeomorphism-type form: a spherical space form,
  `S² × S¹` with either orientation, `RP³ # RP³`, or a Euclidean structure. In this form
  `geometrizes_of_nonnegative_of_trichotomy` needs only `FlatStructurePrime` and the standard
  certificates, not the `S² × ℝ` classification.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u

def FlatStructurePrime : Prop :=
  ∀ P : ConnectedClosedOrientedManifold.{u} 3,
    ∀ g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier, g.model = .euclidean → IsPrime P

theorem geometrizes_of_euclideanStructure (hF : FlatStructurePrime.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    Geometrizes P :=
  ⟨primeGeometricCertificate P (hF P g hg) g⟩

def ClosedNonnegativeClassification : Prop :=
  ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier),
    W.model.boundary W.Carrier = ∅ → SectionalBoundedBelow g 0 →
      ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
        G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean

theorem NoCuts.carrier_boundary_eq_empty (P : ConnectedClosedOrientedManifold.{u} 3) :
    (NoCuts.carrier P).model.boundary (NoCuts.carrier P).Carrier = ∅ :=
  ModelWithCorners.Boundaryless.boundary_eq_empty

theorem exists_geometricStructure_of_nonnegative (hC : ClosedNonnegativeClassification.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric (𝓡 3) P.Carrier)
    (hsec : SectionalBoundedBelow g 0) :
    ∃ G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  hC (NoCuts.carrier P) g (NoCuts.carrier_boundary_eq_empty P) hsec

theorem geometrizes_of_nonnegative_of_classification (hC : ClosedNonnegativeClassification.{u})
    (hF : FlatStructurePrime.{u}) (hS : SphericalProductStandardConnectedSum.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric (𝓡 3) P.Carrier)
    (hsec : SectionalBoundedBelow g 0) : Geometrizes P := by
  obtain ⟨G, hG | hG | hG⟩ := exists_geometricStructure_of_nonnegative hC P g hsec
  · exact geometrizes_of_sphericalStructure P G hG
  · exact geometrizes_of_sphericalProductStructure hS P G hG
  · exact geometrizes_of_euclideanStructure hF P G hG

def ClosedNonnegativeTrichotomy : Prop :=
  ∀ (P : ConnectedClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric (𝓡 3) P.Carrier),
    SectionalBoundedBelow g 0 →
      (∃ G : SphericalSpaceFormGroup, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        P.toClosedOrientedManifold G.manifold.toClosedOrientedManifold)) ∨
      (∃ f : P.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
        f.preservesOrientation P.orientation sphereTwoTimesCircleOrientation ∨
          f.preservesOrientation P.orientation sphereTwoTimesCircleOrientation.opposite) ∨
      (∃ A B : ConnectedClosedOrientedManifold.{u} 3,
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
          SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph B.toClosedOrientedManifold
          SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.toClosedOrientedManifold
          (connectedSum A B).toClosedOrientedManifold)) ∨
      ∃ G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier, G.model = .euclidean

theorem geometrizes_of_nonnegative_of_trichotomy (hT : ClosedNonnegativeTrichotomy.{u})
    (hF : FlatStructurePrime.{u}) (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier) (hsec : SectionalBoundedBelow g 0) :
    Geometrizes P := by
  rcases hT P g hsec with hP | ⟨f, hf | hf⟩ | ⟨A, B, ⟨eA⟩, ⟨eB⟩, ⟨e⟩⟩ | ⟨G, hG⟩
  · exact geometrizes_of_isStandardFactor P (Or.inl hP)
  · exact geometrizes_of_isStandardFactor P (Or.inr ⟨f, hf⟩)
  · have h := Diffeomorph.preservesOrientation_opposite hf
    rw [ManifoldOrientation.opposite_opposite] at h
    exact geometrizes_of_isPoincareStandard P
      (isStandardConnectedSum_of_standard_factor P.opposite (Or.inr ⟨f, h⟩))
  · have hAB := isStandardConnectedSum_connectedSum_of_standardFactor A B
      (Or.inl ⟨_, ⟨eA⟩⟩) (Or.inl ⟨_, ⟨eB⟩⟩)
    exact geometrizes_of_isPoincareStandard P (isStandardConnectedSum_of_diffeomorph e.1 hAB)
  · exact geometrizes_of_euclideanStructure hF P G hG

end GC.Endpoint
