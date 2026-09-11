import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms








namespace DifferentialGeometry.Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



def loopComponentOpen (γ : freeLoop M) : TopologicalSpace.Opens M := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  exact ⟨loopComponent γ, isOpen_loopComponent γ⟩

@[simp] theorem loopComponentOpen_coe (γ : freeLoop M) :
    (loopComponentOpen E γ : Set M) = loopComponent γ := rfl

theorem isClosed_loopComponentOpen (γ : freeLoop M) :
    IsClosed (loopComponentOpen E γ : Set M) := isClosed_loopComponent γ

instance loopComponentOpen_connectedSpace (γ : freeLoop M) :
    ConnectedSpace (loopComponentOpen E γ) :=
  inferInstanceAs (ConnectedSpace (loopComponent γ))

instance loopComponentOpen_compactSpace [CompactSpace M] (γ : freeLoop M) :
    CompactSpace (loopComponentOpen E γ) :=
  inferInstanceAs (CompactSpace (loopComponent γ))

end DifferentialGeometry.Topology
