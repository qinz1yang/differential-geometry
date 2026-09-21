import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

theorem Isometry.isCompact_closedBall_of_punctured_closedBall
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {p : Y} {r : ℝ} (hcompact : IsCompact (Metric.closedBall p r))
    (hcover : Metric.closedBall p r ⊆ insert p (range f))
    {x : X} {R : ℝ} (hR : R < dist (f x) p) (hbuffer : dist (f x) p + R ≤ r) :
    IsCompact (Metric.closedBall x R) := by
  have hsub : Metric.closedBall (f x) R ⊆ Metric.closedBall p r := by
    intro y hy
    have htriangle := dist_triangle y (f x) p
    change dist y (f x) ≤ R at hy
    change dist y p ≤ r
    linarith only [htriangle, hy, hbuffer]
  have hK := hcompact.of_isClosed_subset Metric.isClosed_closedBall hsub
  have hrange : Metric.closedBall (f x) R ⊆ range f := by
    intro y hy
    rcases hcover (hsub hy) with h | h
    · rw [h] at hy
      have hdist : dist (f x) p ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
      exact False.elim (hR.not_ge hdist)
    · exact h
  have hpre : f ⁻¹' Metric.closedBall (f x) R = Metric.closedBall x R := by
    ext y
    simp only [mem_preimage, Metric.mem_closedBall, hf.dist_eq]
  rw [← hpre]
  exact (hf.isEmbedding.isInducing.isCompact_preimage_iff hrange).mpr hK
