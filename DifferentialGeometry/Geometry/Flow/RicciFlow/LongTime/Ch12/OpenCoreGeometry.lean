import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlas
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Transport a complete finite-volume hyperbolic model onto the actual interior
of a compact piece. The input is an actual smooth diffeomorphism, not a model tag. -/
theorem hyperbolicInteriorGeometry_of_diffeomorph_CX1
    (H : FiniteVolumeHyperbolicModel.{u}) {C : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier}
    (D : Diffeomorph C.model (𝓡 3) (C.pieceInterior U) H.Carrier ∞) :
    ∃ geometry : C.InteriorGeometry U, isHyperbolicInteriorGeometry geometry := by
  let := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
  let := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
  let E := (Manifold.interiorAtlasDiffeomorph C.model ∞
    (M := C.pieceInterior U)).symm.trans D
  exact ⟨(hyperbolicGeometricStructure H.metric H.curvature H.complete H.finite_volume).pullback E,
    rfl⟩

/-- The transported witness has exactly the shape consumed by the hyperbolic
alternative for a specified cut component. -/
theorem hyperbolicAlternative_of_diffeomorph_CX1
    (H : FiniteVolumeHyperbolicModel.{u})
    {P : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    (D : GC.Topology.TorusDecomposition P)
    (metric : ∀ i, SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ)
    (i : Fin D.components.count) (hnot : ¬ thin i)
    (E : Diffeomorph D.carrier.model (𝓡 3)
      (D.carrier.pieceInterior (D.components.piece i)) H.Carrier ∞) :
    Nonempty (HyperbolicOrThin D metric thin K w i) := by
  obtain ⟨geometry, hgeometry⟩ := hyperbolicInteriorGeometry_of_diffeomorph_CX1 H E
  exact ⟨.hyperbolic hnot geometry hgeometry⟩

end GC.LongTime.Ch12
