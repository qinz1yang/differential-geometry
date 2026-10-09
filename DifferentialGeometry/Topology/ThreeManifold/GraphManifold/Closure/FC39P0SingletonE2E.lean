import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonLinks

/-!
The two actual X136 singleton fixtures consume the same prepared rows, adapted data and strong
certificate. The closed-zero and slim-over-circle FC42 branches have fully discharged inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

instance configurationConnected (b : Bool) : ConnectedSpace (configurationW b).Carrier :=
  (configurationQ b).connected

instance zeroFixtureConnected : ConnectedSpace zeroW.Carrier := standardThreeSphere.connected

instance slimFixtureConnected : ConnectedSpace slimW.Carrier := sphereTwoTimesCircleLift.connected

theorem configurationInhabitants (b : Bool) :
    Nonempty (FC39RowsV2 (configurationW b) (BoundaryTori.empty (configurationW b))) ∧
      Nonempty (FC39Prepared (configurationW b) (BoundaryTori.empty (configurationW b))) ∧
      Nonempty (AdaptedEdgeRimData (configurationPrepared b) (configurationSafe b)) ∧
      Nonempty (StrongCertificate (configurationW b) (BoundaryTori.empty (configurationW b))) :=
  ⟨⟨configurationRows b⟩, ⟨configurationPrepared b⟩, ⟨configurationAdapted b⟩,
    ⟨configurationStrong b⟩⟩

theorem configurationStrong_same_vertex (b : Bool)
    (k : Fin (configurationStrong b).1.vertexCount) :
    (configurationStrong b).1.vertex k =
      (configurationPrepared b).rows.rowVertex ((configurationVertexLink b).index k) :=
  (configurationVertexLink b).vertex_eq k

theorem configurationStrong_same_adapted (b : Bool) :
    (configurationStrong b).1.handle = (configurationAdapted b).edges.handle ∧
      (configurationStrong b).1.rimChart = (configurationAdapted b).rims.rimChart ∧
      (configurationStrong b).1.circ = (configurationAdapted b).circ :=
  ⟨rfl, rfl, rfl⟩

theorem configurationCatalogueEmpty (b : Bool) :
    IsEmpty (Σ v : Fin (configurationStrong b).1.vertexCount,
      ModelBoundaryFace ((configurationStrong b).1.vertex v).piece) :=
  configurationModelCatalogueEmpty b

theorem configurationCounts (b : Bool) :
    (configurationRows b).zero.count + (configurationRows b).slim.count = 1 ∧
      (configurationStrong b).1.vertexCount = 1 ∧
      (configurationStrong b).1.faceCount = 0 ∧
      (configurationStrong b).1.handleCount = 0 ∧
      (configurationStrong b).1.torusSeamCount = 0 ∧
      (configurationStrong b).1.sphereSeamCount = 0 ∧
      (configurationStrong b).1.circ.cornerCount = 0 := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem configurationRawOrAux (b : Bool) :
    Nonempty (RawGraphPresentation (configurationW b)) ∨
      (configurationW b).model.boundary (configurationW b).Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric (configurationW b).model (configurationW b).Carrier,
          Geometry.Riemannian.SectionalBoundedBelow g 0 :=
  StrongCertificate.raw_or_aux_nonneg (configurationW b) (configurationStrong b)

theorem configurationFC42 (b : Bool) :
    Nonempty (RawGraphPresentation (configurationW b)) ∨
      (configurationW b).model.boundary (configurationW b).Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric (configurationW b).model (configurationW b).Carrier,
          Geometry.Riemannian.SectionalBoundedBelow g 0 :=
  exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct
    (configurationW b) (configurationStrong b).1 (configurationStrong b).2

theorem zeroClosedZeroBranch : zeroW.model.boundary zeroW.Carrier = ∅ ∧
    ∃ g : SmoothRiemannianMetric zeroW.model zeroW.Carrier,
      Geometry.Riemannian.SectionalBoundedBelow g 0 :=
  zeroStrong.1.boundary_eq_empty_and_exists_nonneg_of_closedZero
    ⟨(0 : Fin 1), zeroClosedPiece, rfl⟩

theorem slimCircleBranch : Nonempty (RawGraphPresentation slimW) :=
  slimStrong.1.nonempty_rawGraphPresentation_of_slimCircle
    ⟨(0 : Fin 1), slimPiece, slimProjection, slimProjection_smooth,
      slimProjection_submersion, slimFibre, wholePiece_boundary sphereTwoTimesCircleLift, rfl⟩

end GC.GraphManifold.Assembly.FC39P0.X136
