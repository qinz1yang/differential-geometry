import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Flatten

/-!
Raw certificates from actual product cut systems and compatible local product refinements.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def rawGraphPresentation_of_productCutSystem {W : CompactCarrier.{u}} {k : CarrierModel}
    (S : EmbeddedCutSystem W k) (C : S.ProductCertificate) : RawGraphPresentation W :=
  (S.toElementaryPresentation C).toRaw

theorem rawGraphPresentation_of_productCutSystem_seam {W : CompactCarrier.{u}}
    {k : CarrierModel} (S : EmbeddedCutSystem W k) (C : S.ProductCertificate)
    (j : Fin S.seamCount) :
    (rawGraphPresentation_of_productCutSystem S C).seam j = S.seam j := rfl

theorem rawGraphPresentation_of_productCutSystem_matching {W : CompactCarrier.{u}}
    {k : CarrierModel} (S : EmbeddedCutSystem W k) (C : S.ProductCertificate)
    (j : Fin S.seamCount) :
    (rawGraphPresentation_of_productCutSystem S C).pairing.matching j = S.matching j := rfl

theorem rawGraphPresentation_of_productCutSystem_external_collar {W : CompactCarrier.{u}}
    {k : CarrierModel} (S : EmbeddedCutSystem W k) (C : S.ProductCertificate)
    (i : Fin S.externalCount) (p : Torus × EuclideanHalfSpace 1) :
    (rawGraphPresentation_of_productCutSystem S C).external.collar i p =
      S.fold (S.sideCollar (S.externalSide i) p) :=
  S.toTorusPresentation_external_collar i p

theorem rawGraphPresentation_of_productCutSystem_counts {W : CompactCarrier.{u}}
    {k : CarrierModel} (S : EmbeddedCutSystem W k) (C : S.ProductCertificate) :
    (rawGraphPresentation_of_productCutSystem S C).components.count = S.count ∧
    (rawGraphPresentation_of_productCutSystem S C).pairing.count = S.seamCount ∧
    (rawGraphPresentation_of_productCutSystem S C).externalCount = S.externalCount :=
  ⟨rfl, rfl, rfl⟩

def rawGraphPresentation_of_productRefinement {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : T.ProductRefinement) : RawGraphPresentation W :=
  R.toElementaryPresentation.toRaw

theorem rawGraphPresentation_of_productRefinement_external_collar {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : T.ProductRefinement) (i : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (rawGraphPresentation_of_productRefinement T R).external.collar i p =
      T.external.collar i p :=
  R.toElementaryPresentation_external_collar i hp

theorem rawGraphPresentation_of_productRefinement_seam_old {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : T.ProductRefinement) (j : Fin T.pairing.count) :
    (rawGraphPresentation_of_productRefinement T R).seam (finSumFinEquiv (.inr j)) =
      T.seam j :=
  R.toRefinement.splice_seam_old j

theorem rawGraphPresentation_of_productRefinement_matching_old {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : T.ProductRefinement) (j : Fin T.pairing.count) :
    (rawGraphPresentation_of_productRefinement T R).pairing.matching
      (finSumFinEquiv (.inr j)) = T.pairing.matching j :=
  R.toRefinement.splice_matching_old j

theorem rawGraphPresentation_of_productRefinement_counts {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : T.ProductRefinement) :
    (rawGraphPresentation_of_productRefinement T R).components.count = R.count ∧
    (rawGraphPresentation_of_productRefinement T R).pairing.count =
      R.newSeamCount + T.pairing.count ∧
    (rawGraphPresentation_of_productRefinement T R).externalCount = T.externalCount :=
  ⟨rfl, rfl, rfl⟩

end GC.GraphManifold
