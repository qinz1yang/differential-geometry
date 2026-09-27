import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def connectedComponentOpen (p : M) : Opens M := by
  letI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨connectedComponent p, isOpen_connectedComponent⟩

def connectedComponentPoint (p : M) : connectedComponentOpen (I := I) p :=
  ⟨p, mem_connectedComponent⟩

theorem connectedComponentOpen_connectedSpace (p : M) :
    ConnectedSpace (connectedComponentOpen (I := I) p) := by
  apply Subtype.connectedSpace
  unfold connectedComponentOpen
  exact isConnected_connectedComponent

theorem connectedComponentOpen_compactSpace [CompactSpace M] (p : M) :
    CompactSpace (connectedComponentOpen (I := I) p) := by
  apply isCompact_iff_compactSpace.mp
  unfold connectedComponentOpen
  exact (isClosed_connectedComponent (x := p)).isCompact

end DifferentialGeometry
