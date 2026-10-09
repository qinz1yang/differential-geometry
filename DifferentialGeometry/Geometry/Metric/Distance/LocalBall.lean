import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isClosed_riemannianClosedBallOf (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    IsClosed (riemannianClosedBallOf g p r) :=
  isClosed_le (Riemannian.continuous_riemannianEDist g p) continuous_const

theorem riemannianBallOf_subset_interior_riemannianClosedBallOf
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    riemannianBallOf g p r ⊆ interior (riemannianClosedBallOf g p r) := by
  apply interior_maximal
  · intro q hq
    change riemannianEDistOf g p q < ENNReal.ofReal r at hq
    exact hq.le
  · exact isOpen_lt (Riemannian.continuous_riemannianEDist g p) continuous_const

theorem mem_interior_riemannianClosedBallOf (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ} (hr : 0 < r) : p ∈ interior (riemannianClosedBallOf g p r) := by
  apply riemannianBallOf_subset_interior_riemannianClosedBallOf g p r
  change riemannianEDistOf g p p < ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hr

theorem riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} {q : M}
    (hq : q ∈ frontier (riemannianClosedBallOf g p r)) :
    riemannianEDistOf g p q = ENNReal.ofReal r := by
  have hmem : q ∈ riemannianClosedBallOf g p r :=
    (isClosed_riemannianClosedBallOf g p r).closure_eq ▸ hq.1
  have hle : riemannianEDistOf g p q ≤ ENNReal.ofReal r := hmem
  apply le_antisymm hle
  apply le_of_not_gt
  intro hlt
  exact hq.2 (riemannianBallOf_subset_interior_riemannianClosedBallOf g p r hlt)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_riemannianClosedBallOf_subset_of_mem_nhds
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set M} (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ riemannianClosedBallOf g p r ⊆ U := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let : RegularSpace M := inferInstance
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hU
  refine ⟨(c : ℝ) / 2, by positivity, ?_⟩
  intro q hq
  apply hball
  change riemannianEDistOf g p q < (c : ℝ≥0∞)
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlt : ENNReal.ofReal ((c : ℝ) / 2) < (c : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hcR).mpr (by linarith)
  exact hq.trans_lt hlt

theorem exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set M} (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf g p r) ∧
      riemannianClosedBallOf g p r ⊆ U := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨K, hK, hpK⟩ := exists_compact_mem_nhds p
  obtain ⟨r, hr, hball⟩ := exists_pos_riemannianClosedBallOf_subset_of_mem_nhds g p
    (Filter.inter_mem hU hpK)
  exact ⟨r, hr, hK.of_isClosed_subset (isClosed_riemannianClosedBallOf g p r)
    (fun x hx => (hball hx).2), fun x hx => (hball hx).1⟩

end DifferentialGeometry.Geometry.Metric

end

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ofReal_sub_le_riemannianEDistOf_of_mem_closedBall_of_mem_frontier
    (g : SmoothRiemannianMetric I M) (p : M) {R r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    {y z : M} (hy : y ∈ riemannianClosedBallOf g p r)
    (hz : z ∈ frontier (riemannianClosedBallOf g p R)) :
    ENNReal.ofReal (R - r) ≤ riemannianEDistOf g z y := by
  have hfar := riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf g p hz
  change riemannianEDistOf g p y ≤ ENNReal.ofReal r at hy
  have hfinite : riemannianEDistOf g p y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
  by_contra hnot
  have hlt : riemannianEDistOf g z y < ENNReal.ofReal (R - r) := lt_of_not_ge hnot
  have htriangle := riemannianEDistOf_triangle g p y z
  rw [riemannianEDistOf_comm g y z, hfar] at htriangle
  have hsum := ENNReal.add_lt_add_of_le_of_lt hfinite hy hlt
  rw [← ENNReal.ofReal_add hr (sub_nonneg.mpr hrR), add_sub_cancel] at hsum
  exact (not_lt_of_ge htriangle) hsum

theorem ofReal_half_le_riemannianEDistOf_of_mem_ball_of_mem_frontier
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    {y z : M} (hy : y ∈ riemannianBallOf g p (R / 2))
    (hz : z ∈ frontier (riemannianClosedBallOf g p R)) :
    ENNReal.ofReal (R / 2) ≤ riemannianEDistOf g z y := by
  have hclosed : y ∈ riemannianClosedBallOf g p (R / 2) := by
    change riemannianEDistOf g p y < ENNReal.ofReal (R / 2) at hy
    exact hy.le
  simpa only [show R - R / 2 = R / 2 by ring] using
    ofReal_sub_le_riemannianEDistOf_of_mem_closedBall_of_mem_frontier g p
      (by linarith : 0 ≤ R / 2) (by linarith : R / 2 ≤ R) hclosed hz

end DifferentialGeometry.Geometry.Metric
