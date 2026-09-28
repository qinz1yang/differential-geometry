import DifferentialGeometry.Geometry.Metric.ConeDistance.Embedding

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace Metric

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  {T : Type*} [MetricSpace T] [CompactSpace T] {a b lambda : ℝ}
  {ι : Type*} {l : Filter ι} [NeBot l]

theorem exists_marked_cone_embedding_of_compact_pair_limits
    (ha : 0 < a) (hlambda : 0 < lambda) (D : Set (ℝ × Y))
    (hD : ∀ x ∈ D, x.1 ∈ Icc a b)
    (u : ι → D → T)
    (hpair : ∀ x y : D, Tendsto (fun i => dist (u i x) (u i y)) l
      (𝓝 (lambda * coneDistance (x : ℝ × Y) (y : ℝ × Y))))
    (o : D) (q : T) (hbase : Tendsto (fun i => dist (u i o) q) l (𝓝 0)) :
    ∃ F : D → T, MapClusterPt F l u ∧ Topology.IsEmbedding F ∧ F o = q ∧
      ∀ x y : D, dist (F x) (F y) =
        lambda * coneDistance (x : ℝ × Y) (y : ℝ × Y) := by
  obtain ⟨F, hF, hmetric⟩ := Topology.exists_mapClusterPt_of_continuous_pairwise_limits u
    (fun p : T × T => dist p.1 p.2) (continuous_fst.dist continuous_snd)
    (fun x y : D => lambda * coneDistance (x : ℝ × Y) (y : ℝ × Y)) hpair
  refine ⟨F, hF, isEmbedding_of_scaled_cone_distance ha hlambda D hD F hmetric, ?_, hmetric⟩
  have hobs : Continuous (fun G : D → T => dist (G o) q) :=
    (continuous_apply o).dist continuous_const
  have hc := hF.continuousAt_comp hobs.continuousAt
  apply dist_eq_zero.mp
  exact eq_of_nhds_neBot (hc.clusterPt.mono hbase)

end Metric
