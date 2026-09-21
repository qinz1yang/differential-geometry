import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.Metric.Construction.OpenCoefficients

section

noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_smoothMetric_regularized_pullback
    (g : SmoothRiemannianMetric I M) (Ω : TopologicalSpace.Opens V) {q : V → M}
    (hq : ContMDiffOn 𝓘(ℝ, V) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : SmoothRiemannianMetric 𝓘(ℝ, V) Ω,
      (∀ (x : Ω) (v w : V), h.inner x v w =
        pullbackMetricCoefficients g q x.1 v w + δ * inner ℝ v w) ∧
      ∀ (x : Ω) (v : V), δ * ‖v‖ ^ 2 ≤ h.inner x v v := by
  let A := pullbackMetricCoefficients g q
  let J : V →L[ℝ] V →L[ℝ] ℝ := by exact innerSL ℝ
  let B (x : V) : V →L[ℝ] V →L[ℝ] ℝ := A x + δ • J
  have hA : ContDiffOn ℝ ∞ A Ω := contDiffOn_pullback_metric_coefficients g Ω.isOpen hq
  have hsym (x : V) (hx : x ∈ Ω) (v w : V) : B x v w = B x w v := by
    change A x v w + δ * inner ℝ v w = A x w v + δ * inner ℝ w v
    rw [show A x v w = A x w v from g.symm _ _ _, real_inner_comm v w]
  have hpos (x : V) (hx : x ∈ Ω) (v : V) (hv : v ≠ 0) : 0 < B x v v := by
    have hbase : 0 ≤ A x v v := metric_inner_self_nonneg g (q x) _
    have hinner : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    change 0 < A x v v + δ * inner ℝ v v
    exact add_pos_of_nonneg_of_pos hbase (mul_pos hδ hinner)
  obtain ⟨h, hh⟩ := exists_smoothMetric_of_contDiffOn_bilinearField Ω B hsym hpos
    (hA.add contDiffOn_const)
  have hh' (x : Ω) (v w : V) : h.inner x v w = A x v w + δ * inner ℝ v w :=
    hh x v w
  refine ⟨h, hh', ?_⟩
  intro x v
  rw [hh']
  rw [real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (metric_inner_self_nonneg g (q x) _)

end DifferentialGeometry.Geometry

end

end
