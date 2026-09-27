import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem compactSpace_of_metricScalarAt_lower_bound_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2)
    {c : ℝ} (hc : 0 < c) (hscalar : ∀ x, c ≤ metricScalarAt g x) :
    CompactSpace M := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  apply BonnetMyers.bonnet_myers_compactSpace_of_complete_metric g hcomplete
    (by omega) (show 0 < c / 2 by positivity)
  intro x v
  rw [hdim]
  norm_num
  rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two g hdim]
  have hinner : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (g.pos x v hv).le
  exact mul_le_mul_of_nonneg_right (by linarith [hscalar x]) hinner

theorem exists_metricScalarAt_lt_of_not_compactSpace_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2) (hnoncompact : ¬ CompactSpace M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x, metricScalarAt g x < ε := by
  by_contra! h
  exact hnoncompact
    (compactSpace_of_metricScalarAt_lower_bound_of_finrank_eq_two g hcomplete hdim hε h)

theorem exists_not_mem_and_metricScalarAt_lt_of_pos_on_compact_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2) (hnoncompact : ¬ CompactSpace M)
    {K : Set M} (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < metricScalarAt g x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∉ K, metricScalarAt g x < ε := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (metricScalar_smooth g).continuous.continuousOn
    obtain ⟨y, hy⟩ := exists_metricScalarAt_lt_of_not_compactSpace_of_finrank_eq_two
      g hcomplete hdim hnoncompact (lt_min hε (hpos x hx))
    refine ⟨y, ?_, hy.trans_le (min_le_left _ _)⟩
    intro hyK
    exact (not_lt_of_ge (hmin hyK)) (hy.trans_le (min_le_right _ _))
  · obtain ⟨x, hx⟩ := exists_metricScalarAt_lt_of_not_compactSpace_of_finrank_eq_two
      g hcomplete hdim hnoncompact hε
    exact ⟨x, fun hxK => hne ⟨x, hxK⟩, hx⟩

end DifferentialGeometry.Geometry.Riemannian
