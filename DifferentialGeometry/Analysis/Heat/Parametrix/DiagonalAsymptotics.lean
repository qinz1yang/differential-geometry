import DifferentialGeometry.Analysis.Heat.Parametrix.KernelComparison
import DifferentialGeometry.Geometry.Exponential.ExpInvBranch

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm)
open Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem cutoffHeatParametrix_one_centre
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source)
    {χ : M → ℝ} (hχ : χ p = 1) (t : ℝ) :
    cutoffHeatParametrix g B χ 1 t p =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        (1 + t * Geometry.Curvature.metricScalarAt g p / 6) := by
  have he := branchEnergy_exp B (u := (0 : TangentSpace I p))
    (by simpa only [map_zero] using hB)
  have he0 : branchEnergy g B p = 0 := by
    simpa only [expMapIntrinsic_zero, map_zero, mul_zero] using he
  rw [cutoffHeatParametrix, hχ, one_mul, heatParametrix, he0]
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    heatParametrixCoefficient_zero_centre, heatParametrixCoefficient_one_centre]
  ring

theorem cutoffHeatParametrix_one_centre_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2) (B : ExpInvBranch g hEnorm p)
    (hB : (0 : E) ∈ B.hom.source) {χ : M → ℝ} (hχ : χ p = 1) (t : ℝ) :
    cutoffHeatParametrix g B χ 1 t p =
      (4 * Real.pi * t)⁻¹ * (1 + t * Geometry.Curvature.metricScalarAt g p / 6) := by
  rw [cutoffHeatParametrix_one_centre B hB hχ t, hn]
  norm_num only [Nat.cast_ofNat, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

theorem cutoffHeatParametrix_one_centre_sub_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2) (B : ExpInvBranch g hEnorm p)
    (hB : (0 : E) ∈ B.hom.source) {χ : M → ℝ} (hχ : χ p = 1)
    {t : ℝ} (ht : t ≠ 0) :
    cutoffHeatParametrix g B χ 1 t p - 1 / (4 * Real.pi * t) =
      Geometry.Curvature.metricScalarAt g p / (24 * Real.pi) := by
  rw [cutoffHeatParametrix_one_centre_of_finrank_eq_two hn B hB hχ t]
  field_simp
  ring

private theorem tendsto_sub_cutoffHeatParametrix_of_error_le_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2) (B : ExpInvBranch g hEnorm p)
    (hB : (0 : E) ∈ B.hom.source) {χ : M → ℝ} (hχ : χ p = 1)
    {K : ℝ → ℝ} {C T : ℝ} (hT : 0 < T)
    (hbound : ∀ t ∈ Ioc 0 T, |K t - cutoffHeatParametrix g B χ 1 t p| ≤ C * t) :
    Tendsto (fun t => K t - 1 / (4 * Real.pi * t)) (𝓝[>] 0)
      (𝓝 (Geometry.Curvature.metricScalarAt g p / (24 * Real.pi))) := by
  have herr : Tendsto (fun t => K t - cutoffHeatParametrix g B χ 1 t p)
      (𝓝[>] 0) (𝓝 0) := by
    have htend : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using hid.const_mul C
    apply squeeze_zero_norm' ?_ htend
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    simpa only [Real.norm_eq_abs] using hbound t ⟨ht.1, ht.2.le⟩
  have hlim := herr.add (tendsto_const_nhds (x := Geometry.Curvature.metricScalarAt g p / (24 * Real.pi)))
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he := cutoffHeatParametrix_one_centre_sub_of_finrank_eq_two hn B hB hχ
    (show t ≠ 0 from ne_of_gt ht)
  linarith

theorem heatKernel_diagonal_sub_leading_tendsto_of_parametrix_error [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2) (B : ExpInvBranch g hEnorm p)
    (hB : (0 : E) ∈ B.hom.source) {χ : M → ℝ} (hχ : χ p = 1)
    {C T : ℝ} (hT : 0 < T)
    (hbound : ∀ t ∈ Ioc 0 T,
      |heatKernel g t p p - cutoffHeatParametrix g B χ 1 t p| ≤ C * t) :
    Tendsto (fun t => heatKernel g t p p - 1 / (4 * Real.pi * t)) (𝓝[>] 0)
      (𝓝 (Geometry.Curvature.metricScalarAt g p / (24 * Real.pi))) :=
  tendsto_sub_cutoffHeatParametrix_of_error_le_mul hn B hB hχ hT hbound

end DifferentialGeometry.Analysis.HeatEquation

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius)
open Geometry.Riemannian.Exponential Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [CompactSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem heatKernel_diagonal_sub_leading_tendsto_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g)
    (hn : Module.finrank ℝ E = 2) (p : M) :
    Tendsto (fun t => heatKernel g t p p - 1 / (4 * Real.pi * t)) (𝓝[>] 0)
      (𝓝 (Geometry.Curvature.metricScalarAt g p / (24 * Real.pi))) := by
  obtain ⟨B, hB⟩ := exists_expInvBranch_zero_mem g hEnorm p
  obtain ⟨χ, hχ, _, hp, hs, _⟩ := exists_heatParametrix_cutoff_in B hB isOpen_univ (mem_univ p)
  have hsupport : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    fun q hq => (hs hq).1.1
  have hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p := by
    intro q hq
    simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using (hs hq).1.2
  obtain ⟨C, _, hC⟩ := exists_cutoffHeatParametrix_sub_heatKernel_bound_of_finrank_eq_two
    hn B hχ hsupport hp hsmall 1
  apply heatKernel_diagonal_sub_leading_tendsto_of_parametrix_error (C := C) hn B hB hp.eq_of_nhds
    (by norm_num : (0 : ℝ) < 1)
  intro t ht
  simpa only [abs_sub_comm, mul_comm] using hC t ht p

end DifferentialGeometry.Analysis.HeatEquation
