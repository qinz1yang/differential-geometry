import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace MetricSpace

variable {X : Type*}

@[instance_reducible]
def rescale (m : MetricSpace X) (c : ℝ) (hc : 0 < c) : MetricSpace X := by
  letI : MetricSpace X := m
  apply MetricSpace.ofDistTopology (fun x y => c * dist x y)
  · intro x
    simp
  · intro x y
    rw [dist_comm]
  · intro x y z
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (dist_triangle x y z) hc.le
  · intro s
    rw [Metric.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hball⟩ := h x hx
      refine ⟨c * ε, mul_pos hc hε, fun y hy => hball ?_⟩
      rw [Metric.mem_ball, dist_comm]
      exact (mul_lt_mul_iff_right₀ hc).mp hy
    · intro h x hx
      obtain ⟨ε, hε, hball⟩ := h x hx
      refine ⟨ε / c, div_pos hε hc, fun y hy => hball y ?_⟩
      rw [Metric.mem_ball, dist_comm] at hy
      nlinarith [(lt_div_iff₀ hc).mp hy]
  · intro x y h
    exact eq_of_dist_eq_zero ((mul_eq_zero.mp h).resolve_left hc.ne')

theorem rescale_dist (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (x y : X) :
    @dist X (m.rescale c hc).toDist x y = c * @dist X m.toDist x y := rfl

theorem rescale_topology (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    (m.rescale c hc).toUniformSpace.toTopologicalSpace =
      m.toUniformSpace.toTopologicalSpace := rfl

def rescaleHomeomorph (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    @Homeomorph X X m.toUniformSpace.toTopologicalSpace
      (m.rescale c hc).toUniformSpace.toTopologicalSpace :=
  @Homeomorph.refl X m.toUniformSpace.toTopologicalSpace

theorem rescaleHomeomorph_apply (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (x : X) :
    m.rescaleHomeomorph c hc x = x := rfl

theorem lipschitzWith_rescale_id (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    @LipschitzWith X X m.toPseudoEMetricSpace (m.rescale c hc).toPseudoEMetricSpace
      ⟨c, hc.le⟩ id := by
  apply @LipschitzWith.of_dist_le_mul X X m.toPseudoMetricSpace
    (m.rescale c hc).toPseudoMetricSpace
  intro x y
  exact le_rfl

theorem lipschitzWith_id_rescale (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    @LipschitzWith X X (m.rescale c hc).toPseudoEMetricSpace m.toPseudoEMetricSpace
      ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ id := by
  apply @LipschitzWith.of_dist_le_mul X X (m.rescale c hc).toPseudoMetricSpace
    m.toPseudoMetricSpace
  intro x y
  change @dist X m.toDist x y ≤ c⁻¹ * (c * @dist X m.toDist x y)
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem rescale_compactSpace (m : MetricSpace X) (c : ℝ) (hc : 0 < c)
    [h : @CompactSpace X m.toUniformSpace.toTopologicalSpace] :
    @CompactSpace X (m.rescale c hc).toUniformSpace.toTopologicalSpace := h

theorem rescale_isBounded_iff (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (s : Set X) :
    @Bornology.IsBounded X (m.rescale c hc).toBornology s ↔
      @Bornology.IsBounded X m.toBornology s := by
  rw [@Metric.isBounded_iff X (m.rescale c hc).toPseudoMetricSpace s,
    @Metric.isBounded_iff X m.toPseudoMetricSpace s]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun x hx y hy => ?_⟩
    exact (le_div_iff₀ hc).mpr (by simpa [rescale_dist, mul_comm] using hC hx hy)
  · rintro ⟨C, hC⟩
    exact ⟨c * C, fun x hx y hy => mul_le_mul_of_nonneg_left (hC hx hy) hc.le⟩

theorem rescale_diam (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (s : Set X)
    (hs : @Bornology.IsBounded X m.toBornology s) :
    @Metric.diam X (m.rescale c hc).toPseudoMetricSpace s =
      c * @Metric.diam X m.toPseudoMetricSpace s := by
  have hs' := (rescale_isBounded_iff m c hc s).mpr hs
  apply le_antisymm
  · apply @Metric.diam_le_of_forall_dist_le X s (m.rescale c hc).toPseudoMetricSpace
      (c * @Metric.diam X m.toPseudoMetricSpace s)
      (mul_nonneg hc.le (@Metric.diam_nonneg X s m.toPseudoMetricSpace))
    intro x hx y hy
    exact mul_le_mul_of_nonneg_left (@Metric.dist_le_diam_of_mem X s x y
      m.toPseudoMetricSpace hs hx hy) hc.le
  · have h : @Metric.diam X m.toPseudoMetricSpace s ≤
        @Metric.diam X (m.rescale c hc).toPseudoMetricSpace s / c := by
      apply @Metric.diam_le_of_forall_dist_le X s m.toPseudoMetricSpace
        (@Metric.diam X (m.rescale c hc).toPseudoMetricSpace s / c)
        (div_nonneg (@Metric.diam_nonneg X s (m.rescale c hc).toPseudoMetricSpace) hc.le)
      intro x hx y hy
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm, rescale_dist] using
        (@Metric.dist_le_diam_of_mem X s x y (m.rescale c hc).toPseudoMetricSpace hs' hx hy)
    nlinarith [(le_div_iff₀ hc).mp h]

end MetricSpace
