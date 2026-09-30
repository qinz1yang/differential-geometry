import DifferentialGeometry.Topology.Manifold.BallEmbedding.Isotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingRelativeIsotopy

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def OrientedBallEmbedding.ofOrientedBallChart
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) :
    OrientedBallEmbedding M.Carrier M.orientation where
  chart := c.chart
  closedBall_subset_source := c.closedBall_subset_source
  preserves_orientation := c.preserves_orientation

def OrientedBallEmbedding.toOrientedBallChart
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (e : OrientedBallEmbedding M.Carrier M.orientation) :
    DifferentialGeometry.Topology.OrientedBallChart M where
  toBallChart := ⟨e.chart, e.closedBall_subset_source⟩
  preserves_orientation := e.preserves_orientation

@[simp]
theorem OrientedBallEmbedding.toOrientedBallChart_ofOrientedBallChart
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) :
    (OrientedBallEmbedding.ofOrientedBallChart c).toOrientedBallChart = c := by
  cases c
  rfl

@[simp]
theorem OrientedBallEmbedding.ofOrientedBallChart_toOrientedBallChart
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (e : OrientedBallEmbedding M.Carrier M.orientation) :
    OrientedBallEmbedding.ofOrientedBallChart e.toOrientedBallChart = e := by
  cases e
  rfl

def OrientedBallEmbedding.orientedBallChartEquiv
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) :
    OrientedBallEmbedding M.Carrier M.orientation ≃
      DifferentialGeometry.Topology.OrientedBallChart M where
  toFun := OrientedBallEmbedding.toOrientedBallChart
  invFun := OrientedBallEmbedding.ofOrientedBallChart
  left_inv := OrientedBallEmbedding.ofOrientedBallChart_toOrientedBallChart
  right_inv := OrientedBallEmbedding.toOrientedBallChart_ofOrientedBallChart

theorem ballEmbeddingAmbientIsotopic_of_ballMarkingIsotopic
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (I : Type u) [Fintype I] (B B' : DifferentialGeometry.Topology.BallMarking M I)
    (h : B.Isotopic B') :
    BallEmbeddingAmbientIsotopic I M.Carrier M.orientation
      (fun i => OrientedBallEmbedding.ofOrientedBallChart (B.ball i))
      (fun i => OrientedBallEmbedding.ofOrientedBallChart (B'.ball i)) := by
  obtain ⟨H, hHc, hHi, hH0, hH1⟩ := h
  refine ⟨H, hH0, hHc, hHi, Set.univ, isCompact_univ, ?_, ?_, 1, by norm_num, le_rfl,
    fun i x hx => hH1 i x (Metric.closedBall_subset_closedBall (by norm_num) hx)⟩
  · intro t x hx
    exact absurd (Set.mem_univ x) hx
  · intro t x hx
    exact absurd (Set.mem_univ x) hx

theorem ballEmbeddingAmbientIsotopic_standardThreeSphere :
    BallEmbeddingAmbientIsotopic PUnit
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}.orientation
      (fun _ => OrientedBallEmbedding.ofOrientedBallChart
        (DifferentialGeometry.Topology.orientedBallChart
          DifferentialGeometry.Topology.standardThreeSphereLift.{u}))
      (fun _ => OrientedBallEmbedding.ofOrientedBallChart
        (DifferentialGeometry.Topology.OrientedBallChart.affine
          (DifferentialGeometry.Topology.orientedBallChart
            DifferentialGeometry.Topology.standardThreeSphereLift.{u})
          (0 : ThreeSpace) (1 / 2) (by norm_num) (by norm_num))) := by
  exact ballEmbeddingAmbientIsotopic_of_ballMarkingIsotopic PUnit _ _
    (DifferentialGeometry.Topology.BallMarking.singleton_isotopic_of_affine
      (DifferentialGeometry.Topology.orientedBallChart
        DifferentialGeometry.Topology.standardThreeSphereLift.{u})
      (0 : ThreeSpace) (1 / 2) (by norm_num) (by norm_num))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
