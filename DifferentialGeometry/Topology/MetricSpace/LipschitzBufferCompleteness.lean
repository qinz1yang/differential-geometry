import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric Filter Topology

namespace Topology.IsEmbedding

theorem isComplete_closedBall_of_nonexpansive
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X]
    {f : Y → X} (hf : IsEmbedding f) (hLip : LipschitzWith 1 f) {p : Y} {L : ℝ}
    (hinside : closedBall (f p) L ⊆ range f) : IsComplete (closedBall p L) := by
  intro F hF hFball
  let : NeBot F := hF.1
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.mp (hF.map hLip.uniformContinuous)
  have hxball : x ∈ closedBall (f p) L := by
    apply isClosed_closedBall.mem_of_tendsto hx
    filter_upwards [hFball (mem_principal_self (closedBall p L))] with y hy
    have hd : dist (f y) (f p) ≤ dist y p := by
      simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul y p
    exact hd.trans hy
  obtain ⟨y, rfl⟩ := hinside hxball
  have hy : Tendsto id F (𝓝 y) := hf.tendsto_nhds_iff.mpr hx
  exact ⟨y, isClosed_closedBall.mem_of_tendsto hy
    (hFball (mem_principal_self (closedBall p L))), by simpa only [Tendsto, map_id] using hy⟩

theorem isComplete_closedBall_of_range_ball
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X]
    {f : Y → X} (hf : IsEmbedding f) (hLip : LipschitzWith 1 f)
    {o : X} {S : ℝ} (hrange : range f = ball o S) {p : Y} {L : ℝ}
    (hmargin : dist (f p) o + L < S) : IsComplete (closedBall p L) := by
  apply hf.isComplete_closedBall_of_nonexpansive hLip
  intro x hx
  rw [hrange]
  exact (dist_triangle x (f p) o).trans_lt (by linarith [mem_closedBall.mp hx])

theorem isComplete_closedBall_of_256_radius_buffer
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X]
    {f : Y → X} (hf : IsEmbedding f) (hLip : LipschitzWith 1 f)
    {o : X} {R : ℝ} (hR : 0 < R) (hrange : range f = ball o (256 * R))
    {p : Y} (hp : f p ∈ ball o (4 * R)) : IsComplete (closedBall p (200 * R)) := by
  apply hf.isComplete_closedBall_of_range_ball hLip hrange
  have hd : dist (f p) o < 4 * R := hp
  linarith

end Topology.IsEmbedding
