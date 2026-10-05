import DifferentialGeometry.Topology.Manifold.ClosedBall.ThreeBall
import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.Topological
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.Handle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.terminalRegularRegion_eq_univ
    (G : P.IncomingSlab a s) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Ico a s, ∀ y : P.Carrier, G.riemannNorm t y ≤ K) :
    G.terminalRegularRegion = univ := by
  refine eq_univ_of_forall fun x =>
    ⟨univ, isOpen_univ, mem_univ x, a, ⟨le_rfl, G.lt⟩, K, hK, ?_⟩
  intro y _ t ht
  exact hb t ht y

theorem SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ
    {Q D N : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D N}
    (G : P.IncomingSlab a s) (h : G.terminalRegularRegion = univ) :
    ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore → x.1 ∈ G.terminalRegularRegion :=
  fun _ _ => by rw [h]; exact mem_univ _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
