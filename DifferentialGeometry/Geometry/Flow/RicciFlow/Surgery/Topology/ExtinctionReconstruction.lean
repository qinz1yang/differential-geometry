import DifferentialGeometry.Topology.ThreeManifold.CutCapPoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction

universe u

variable {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
  {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}

theorem isPoincareStandard [ConnectedSpace M.Carrier]
    (W : PoincareControlledExtinction M g) :
    DifferentialGeometry.Topology.isPoincareStandard M.Carrier :=
  W.history.cutCapTrace.isPoincareStandard_of_initialIdentification_of_poincareControlled_extinct
    W.controlled_extinct_trace.1 W.controlled_extinct_trace.2 M W.initialCutCapIdentification

theorem nonempty_diffeomorph_sphere
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g) [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨f⟩ :=
    DifferentialGeometry.Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
      W.isPoincareStandard
  exact ⟨f.trans DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction
