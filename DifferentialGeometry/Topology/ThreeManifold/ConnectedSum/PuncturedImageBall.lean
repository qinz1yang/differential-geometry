import DifferentialGeometry.Topology.PuncturedConnected
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Piecewise

noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Topology

section EuclideanRank

open Module

private theorem one_lt_rank_euclideanSpace {n : ℕ} (hn : 2 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have h : (2 : Cardinal) ≤ Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast hn
  exact lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) h

end EuclideanRank

namespace BallChart

section

variable {n : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isPathConnected_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : IsPathConnected ((c.chart '' Metric.ball 0 1)ᶜ : Set M) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) H := I.toHomeomorph.symm.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) H M
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  exact isPathConnected_compl_image_ball c.chart.toOpenPartialHomeomorph (one_lt_rank_euclideanSpace hn)
    (fun z hz => c.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hz))

theorem connectedSpace_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : ConnectedSpace c.Punctured :=
  isConnected_iff_connectedSpace.mp (c.isPathConnected_punctured hn).isConnected

theorem pathConnectedSpace_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : PathConnectedSpace c.Punctured :=
  isPathConnected_iff_pathConnectedSpace.mp (c.isPathConnected_punctured hn)

end

section Three

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance instConnectedSpacePuncturedThree (c : BallChart 3 I M) [T2Space M] [ConnectedSpace M] :
    ConnectedSpace c.Punctured :=
  c.connectedSpace_punctured (by norm_num)

instance instPathConnectedSpacePuncturedThree (c : BallChart 3 I M) [T2Space M] [ConnectedSpace M] :
    PathConnectedSpace c.Punctured :=
  c.pathConnectedSpace_punctured (by norm_num)

end Three

end BallChart

end DifferentialGeometry.Topology
