import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomain
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hopenU : IsOpen K.domain.carrier) :
    W.embedding '' K.domain.carrier = connectedComponent x := by
  have hU := W.canonical_domain_subset_source K hbuffer
  have hcont := W.embedding.contMDiffOn_toFun.continuousOn.mono hU
  have hclosed := (K.domain.compact.image_of_continuousOn hcont).isClosed
  have hconnected := K.domain.connected.image W.embedding hcont
  have hopen : IsOpen (W.embedding '' K.domain.carrier) :=
    W.embedding.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      hopenU hU
  have hx : x ∈ W.embedding '' K.domain.carrier :=
    ⟨W.model.basepoint, interior_subset K.center_inside, W.base_map⟩
  exact subset_antisymm (hconnected.subset_connectedComponent hx)
    ((show IsClopen (W.embedding '' K.domain.carrier) from ⟨hclosed, hopen⟩).connectedComponent_subset hx)

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.image_canonical_domain_eq_connectedComponent
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hwhole : K.domain.carrier = connectedComponent W.model.basepoint) :
    W.embedding '' K.domain.carrier = connectedComponent x := by
  let : LocallyConnectedSpace W.model.M :=
    ChartedSpace.locallyConnectedSpace ThreeSpace W.model.M
  exact W.image_canonical_domain_eq_connectedComponent_of_isOpen K hbuffer
    (hwhole ▸ isOpen_connectedComponent)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
