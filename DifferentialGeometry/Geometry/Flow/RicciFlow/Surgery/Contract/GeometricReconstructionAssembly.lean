import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ExtinctionContractReduction
import DifferentialGeometry.Topology.Manifold.CollarStraighteningProducer
import DifferentialGeometry.Topology.Manifold.IsotopyOrientation

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology.Collar
  (BoundaryCollarStraighteningWithPrescribedSupport
    relativeCollarUniqueness_of_boundaryCollarStraighteningWithPrescribedSupport) in
theorem boundaryCollarGeometry_of_boundaryCollarStraighteningWithPrescribedSupport
    (h : BoundaryCollarStraighteningWithPrescribedSupport.{u}) :
    boundaryCollarGeometry.{u} :=
  ⟨disjointBoundaryCollarFamily_holds,
    relativeCollarUniqueness_of_boundaryCollarStraighteningWithPrescribedSupport h⟩

theorem geometricReconstructionBackground_of_relativeCollarUniqueness_orientedBallStraightening
    (hcollar : relativeCollarUniqueness.{u})
    (hball : orientedBallChartStraighteningAwayFromCompact.{u}) :
    geometricReconstructionBackground.{u} :=
  geometricReconstructionBackground_iff.mpr
    ⟨hcollar,
      ballEmbeddingIsotopy_of_orientedBallChartStraighteningAwayFromCompact hball
        isotopyPreservesOrientation_holds,
      sphereDiffeomorphismIsotopyConnected_holds⟩

open DifferentialGeometry.Topology.Collar (BoundaryCollarStraighteningWithPrescribedSupport) in
theorem geometricReconstructionBackground_of_boundaryCollarStraightening_orientedBallStraightening
    (hcollar : BoundaryCollarStraighteningWithPrescribedSupport.{u})
    (hball : orientedBallChartStraighteningAwayFromCompact.{u}) :
    geometricReconstructionBackground.{u} :=
  geometricReconstructionBackground_of_relativeCollarUniqueness_orientedBallStraightening
    (boundaryCollarGeometry_of_boundaryCollarStraighteningWithPrescribedSupport hcollar).2 hball

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
