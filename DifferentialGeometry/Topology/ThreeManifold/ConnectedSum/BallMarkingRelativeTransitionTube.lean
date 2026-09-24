import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingRelativeIsotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupportRegion

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

namespace BallMarking

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

def RelativeTransitionTube (B B' : BallMarking M I) : Prop :=
  (∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
    (B.ball i).chart x ∈ (B'.ball i).chart.target) ∧
  ∃ V : I → Set E3,
    (∀ i, IsOpen (V i)) ∧
    (∀ i, V i ⊆ (B'.ball i).chart.source) ∧
    (∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
      (B'.ball i).chart.symm ((B.ball i).chart x) ∈ V i) ∧
    (∀ i, Metric.closedBall (0 : E3) 2 ⊆ V i) ∧
    (∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (B'.ball i).chart.symm ((B.ball i).chart 0) + t • (0 : E3) ∈ V i) ∧
    (∀ i j, i ≠ j →
      Disjoint ((B'.ball i).chart '' V i) ((B'.ball j).chart '' V j)) ∧
    ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E3) 2,
      (B.ball i).chart x ∉ (B'.ball j).chart '' V j

theorem isotropic_of_relativeTransitionTube (B B' : BallMarking M I)
    (h : B.RelativeTransitionTube B') : B.Isotopic B' := by
  obtain ⟨hover, V, hVopen, hVsub, hVψ, hVball, hseg, hdisj, havoid⟩ := h
  exact BallMarking.isotopic_of_relative_transition_tube B B' hover V hVopen hVsub
    hVψ hVball hseg hdisj havoid

theorem relativeTransitionTube_refl_of_subsingleton (B : BallMarking M I) [Subsingleton I] :
    B.RelativeTransitionTube B := by
  refine ⟨?_, fun i => (B.ball i).chart.source, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    exact (B.ball i).chart.map_source ((B.ball i).closedBall_subset_source hx)
  · exact fun i => (B.ball i).chart.open_source
  · exact fun _ => subset_rfl
  · intro i x hx
    exact (B.ball i).chart.map_target ((B.ball i).chart.map_source
      ((B.ball i).closedBall_subset_source hx))
  · exact fun i => (B.ball i).closedBall_subset_source
  · intro i t ht
    have h0 : (0 : E3) ∈ (B.ball i).chart.source :=
      (B.ball i).closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
    have hsymm : (B.ball i).chart.symm ((B.ball i).chart (0 : E3)) = (0 : E3) :=
      (B.ball i).chart.toPartialEquiv.left_inv' h0
    rw [hsymm]
    simpa using h0
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

end BallMarking

theorem G_ball_of_relativeTransitionTube
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u)
      [Fintype I] (B B' : BallMarking M I), B.RelativeTransitionTube B') :
    G_ball.{u} := by
  intro M _ I _ B B'
  exact B.isotropic_of_relativeTransitionTube B' (h M I B B')

theorem selfTransport_of_relativeTransitionTube
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u)
      [Fintype I] (B B' : BallMarking M I), B.RelativeTransitionTube B') :
    SelfTransport.{u} :=
  selfTransport_of_G_ball (G_ball_of_relativeTransitionTube h)

end DifferentialGeometry.Topology
