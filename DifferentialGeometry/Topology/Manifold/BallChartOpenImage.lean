import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ} {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace N] [ChartedSpace K N]

theorem exists_ballChart_of_open_embedding (c : BallChart n I M) (U : TopologicalSpace.Opens M)
    (f : U → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (hU : ∀ x ∈ Metric.closedBall 0 2, c.chart x ∈ U) :
    ∃ d : BallChart n J N, d.chart.source ⊆ c.chart.source ∧
      (∀ x ∈ d.chart.source, ∃ hx : c.chart x ∈ U, d.chart x = f ⟨c.chart x, hx⟩) ∧
      ∀ x (hx : x ∈ Metric.closedBall 0 2), d.chart x = f ⟨c.chart x, hU x hx⟩ := by
  classical
  let W : Set (EuclideanSpace ℝ (Fin n)) := c.chart.source ∩ c.chart ⁻¹' (U : Set M)
  have hW : IsOpen W := c.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    c.chart.open_source U.isOpen
  have hKW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 2 ⊆ W :=
    fun x hx => ⟨c.closedBall_subset_source hx, hU x hx⟩
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ W := hKW (Metric.mem_closedBall_self (by norm_num))
  let g : EuclideanSpace ℝ (Fin n) → U := fun x =>
    if hx : x ∈ W then ⟨c.chart x, hx.2⟩ else ⟨c.chart 0, hzero.2⟩
  have hg (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) : g x = ⟨c.chart x, hx.2⟩ := dif_pos hx
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ (f ∘ g) W := by
    intro x
    have hcg : (fun y => (g y).val) =ᶠ[𝓝 x.val] c.chart := by
      filter_upwards [hW.mem_nhds x.property] with y hy
      rw [hg y hy]
    have hc := IsLocalDiffeomorphAt.of_eventuallyEq hcg
      (c.chart.isLocalDiffeomorphAt _ _ _ x.property.1)
    have hg' := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun y => (g y).property) hc
    exact hg'.comp (K := J) (P := N) (hf (g x.val))
  have hi : InjOn (f ∘ g) W := by
    intro x hx y hy hxy
    have h := congrArg Subtype.val (hinj hxy)
    rw [hg x hx, hg y hy] at h
    exact c.chart.toPartialEquiv.injOn hx.1 hy.1 h
  obtain ⟨φ, hsrc, _, hφ⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    hloc hW ⟨0, hzero⟩ hi
  refine ⟨⟨φ, hsrc.symm ▸ hKW⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact (show x ∈ W from hsrc ▸ hx).1
  · intro x hx
    have hxW : x ∈ W := hsrc ▸ hx
    refine ⟨hxW.2, ?_⟩
    change φ x = _
    rw [hφ]
    change f (g x) = _
    rw [hg x hxW]
  · intro x hx
    change φ x = _
    rw [hφ]
    change f (g x) = _
    rw [hg x (hKW hx)]

end DifferentialGeometry.Topology.BallChart
