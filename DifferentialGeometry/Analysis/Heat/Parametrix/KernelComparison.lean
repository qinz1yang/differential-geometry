import DifferentialGeometry.Analysis.Heat.Parametrix.Approximation
import DifferentialGeometry.Analysis.Heat.Kernel.Representation
import DifferentialGeometry.Analysis.Heat.Parametrix.ResidualBound
import DifferentialGeometry.Analysis.Integration.Measure.UniformPairing
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff ENNReal

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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem tendstoUniformly_heatKernel_sub
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t) (x : M) :
    TendstoUniformly (fun s y => heatKernel g (t - s) x y) (heatKernel g t x)
      (𝓝[>] (0 : ℝ)) := by
  have hU : Iio t ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds ht
  have hmap : Continuous (fun z : ℝ × M => (t - z.1, (x, z.2))) := by
    fun_prop
  have hcont : ContinuousOn (fun z : ℝ × M => heatKernel g (t - z.1) x z.2)
      (Iio t ×ˢ univ) := by
    apply (continuousOn_heatKernel g).comp hmap.continuousOn
    intro z hz
    change 0 < t - z.1 ∧ True
    exact ⟨sub_pos.mpr hz.1, trivial⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨v, hv, hvu⟩ := isCompact_univ.mem_uniformity_of_prod
    (f := fun s y => heatKernel g (t - s) x y)
    (s := Iio t) (q := (0 : ℝ)) hcont (mem_Iio.mpr ht)
    (Metric.dist_mem_uniformity (α := ℝ) hε)
  have hv' : v ∈ 𝓝 (0 : ℝ) := by
    rwa [nhdsWithin_eq_nhds.mpr hU] at hv
  filter_upwards [mem_nhdsWithin_of_mem_nhds hv'] with s hs
  intro y
  simpa only [Set.mem_ofPred_eq, sub_zero, dist_comm] using hvu s hs y (mem_univ y)

private theorem integrable_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (N : ℕ) (s : ℝ) :
    Integrable (cutoffHeatParametrix g B χ N s)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    g _ (hasCompactSupport_cutoffHeatParametrix B (HasCompactSupport.of_compactSpace χ) N s)
  exact (contMDiff_cutoffHeatParametrix B hχ hs N s).continuous

private theorem integrable_cutoffHeatParametrix_mul_heatKernel
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (N : ℕ) (s : ℝ) {r : ℝ} (hr : 0 < r) (x : M) :
    Integrable (fun y => cutoffHeatParametrix g B χ N s y * heatKernel g r x y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    g _ ((hasCompactSupport_cutoffHeatParametrix B (HasCompactSupport.of_compactSpace χ) N s).mul_right)
  exact (contMDiff_cutoffHeatParametrix B hχ hs N s).continuous.mul
    ((continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (fun _ => ⟨hr, mem_univ _⟩))

theorem tendsto_integral_heatKernel_mul_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (hχ0 : χ p = 1)
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    (N : ℕ) {t : ℝ} (ht : 0 < t) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y *
      cutoffHeatParametrix g B χ N s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (heatKernel g t x p)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let K : ℝ → M → ℝ := fun s y => cutoffHeatParametrix g B χ N s y
  let f : ℝ → M → ℝ := fun s y => heatKernel g (t - s) x y
  let f₀ : M → ℝ := heatKernel g t x
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (K s) μ :=
    Filter.Eventually.of_forall (fun s => integrable_cutoffHeatParametrix B hχ hs N s)
  have hχs : tsupport χ ⊆ B.dom := fun q hq => (hs hq).1
  have hspos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < t - s := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hst
    exact sub_pos.mpr hst
  have hif : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (fun y => K s y * f s y) μ := by
    filter_upwards [hspos] with s hsp
    exact integrable_cutoffHeatParametrix_mul_heatKernel B hχ hs N s hsp x
  have hi₀ : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (fun y => K s y * f₀ y) μ := by
    filter_upwards with s
    apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      g _ ((hasCompactSupport_cutoffHeatParametrix B (HasCompactSupport.of_compactSpace χ) N s).mul_right)
    exact (contMDiff_cutoffHeatParametrix B hχ hs N s).continuous.mul
      ((continuousOn_heatKernel g).comp_continuous
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (fun _ => ⟨ht, mem_univ _⟩))
  have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫ y, ‖K s y‖ ∂μ) ≤ 2 := by
    simpa only [K, μ] using
      (eventually_integral_norm_cutoffHeatParametrix_le_two B N χ hχ.continuous
        (HasCompactSupport.of_compactSpace χ) hχ0 hχs hsmall)
  have hf : TendstoUniformly f f₀ (𝓝[>] (0 : ℝ)) :=
    tendstoUniformly_heatKernel_sub g ht x
  have hlim : Tendsto (fun s => ∫ y, K s y * f₀ y ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (heatKernel g t x p)) := by
    simpa only [K, f₀, μ, mul_comm] using
      (tendsto_integral_cutoffHeatParametrix_mul B N χ (heatKernel g t x)
        hχ.continuous (HasCompactSupport.of_compactSpace χ) hχ0 hχs hsmall
        (by exact ((continuousOn_heatKernel g).comp_continuous
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          (fun _ => ⟨ht, mem_univ _⟩))))
  have hmain := MeasureTheory.tendsto_integral_mul_of_tendstoUniformly_of_integral_norm_bounded
    hK hif hi₀ hbound hf hlim
  simpa only [f, K, μ, mul_comm] using hmain

open Geometry.Curvature

private theorem cutoffHeatParametrix_sub_heatKernel_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    {t C : ℝ} (ht : 0 < t) (x : M)
    (hbound : ∀ s ∈ Ioc 0 t, ∀ y, |cutoffHeatParametrixResidual g B χ 1 s y| ≤ C)
    (hinit : Tendsto (fun s => ∫ y, heatKernel g (t - s) x y *
      cutoffHeatParametrix g B χ 1 s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (heatKernel g t x p))) :
    |cutoffHeatParametrix g B χ 1 t x - heatKernel g t x p| ≤ t * C := by
  have hcont := continuousOn_cutoffHeatParametrixResidual_one B hχ hs
  let D : RealTimeInterval := RealTimeInterval.openInterval 0 (t + 1) t ⟨ht, by linarith⟩
  have hD : D.carrier ⊆ Ioi 0 := fun _ hs => hs.1
  have hu := cutoffHeatParametrix_isHeatForcedOnStationary B hχ hs hsmall 1 D hD
  have hint : IntervalIntegrable (fun s => ∫ y, heatKernel g (t - s) x y *
      cutoffHeatParametrixResidual g B χ 1 s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      volume 0 t := by
    apply intervalIntegrable_integral_heatKernel_mul_of_bounded
      (F := cutoffHeatParametrixResidual g B χ 1) g ht.le x
      (hcont.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
    · intro s hs y
      simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1, hs.2.le⟩ y
  have hreg : Ioo 0 t ⊆ D.regular := fun _ hs => ⟨hs.1, by linarith [hs.2]⟩
  have htD : t ∈ D.carrier := ⟨ht, by linarith⟩
  have hf : ∀ s ∈ Ioo 0 t, ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g,
      ‖cutoffHeatParametrixResidual g B χ 1 s y‖ ≤ C := by
    intro s hs
    exact ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1, hs.2.le⟩ y
  have h := norm_sub_heatKernel_le_of_initial_pairing_tendsto g hu ht hreg htD x p hint hf
    (by simpa only [sub_zero] using hinit)
  simpa only [sub_zero, Real.norm_eq_abs] using h


theorem exists_cutoffHeatParametrix_sub_heatKernel_bound_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2) (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (hp : χ =ᶠ[nhds p] 1)
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ x : M,
      |cutoffHeatParametrix g B χ 1 t x - heatKernel g t x p| ≤ t * C := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffHeatParametrix_residual_bound_of_finrank_eq_two
    hn B hχ (HasCompactSupport.of_compactSpace χ) hs hp T
  refine ⟨C, hC, ?_⟩
  intro t ht x
  apply cutoffHeatParametrix_sub_heatKernel_bound B hχ hs hsmall ht.1 x
  · intro s hs y
    exact hbound s ⟨hs.1, hs.2.trans ht.2⟩ y
  · exact tendsto_integral_heatKernel_mul_cutoffHeatParametrix B hχ hs
      hp.eq_of_nhds hsmall 1 ht.1 x

end DifferentialGeometry.Analysis.HeatEquation
