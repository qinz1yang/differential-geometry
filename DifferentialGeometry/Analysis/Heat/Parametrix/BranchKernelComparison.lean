import DifferentialGeometry.Analysis.Heat.Parametrix.BranchEvolution
import DifferentialGeometry.Analysis.Heat.Parametrix.BranchApproximation
import DifferentialGeometry.Analysis.Heat.Kernel.Representation
import DifferentialGeometry.Analysis.Heat.Parametrix.BranchResidualBound
import DifferentialGeometry.Analysis.Integration.Measure.UniformPairing

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

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

theorem tendsto_integral_heatKernel_mul_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U)
    (hχp : χ p = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y *
      B.cutoffHeatParametrix χ N s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (heatKernel g t x p)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let K : ℝ → M → ℝ := B.cutoffHeatParametrix χ N
  let f : ℝ → M → ℝ := fun s y => heatKernel g (t - s) x y
  let f₀ : M → ℝ := heatKernel g t x
  have hKs (s : ℝ) : Continuous (K s) := (B.contMDiff_cutoffHeatParametrix hχ hs N s).continuous
  have hcK (s : ℝ) : HasCompactSupport (K s) :=
    B.hasCompactSupport_cutoffHeatParametrix (HasCompactSupport.of_compactSpace χ) N s
  have hif (s : ℝ) {r : ℝ} (hr : 0 < r) : Integrable (fun y => K s y * heatKernel g r x y) μ := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      g _ ((hcK s).mul_right)
    exact (hKs s).mul ((continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => ⟨hr, mem_univ _⟩))
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (K s) μ :=
    Filter.Eventually.of_forall (fun s =>
      DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        g (hKs s) (hcK s))
  have hifs : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (fun y => K s y * f s y) μ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hst
    exact hif s (sub_pos.mpr hst)
  have hi₀ : ∀ᶠ s in 𝓝[>] (0 : ℝ), Integrable (fun y => K s y * f₀ y) μ :=
    Filter.Eventually.of_forall (fun s => hif s ht)
  have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫ y, ‖K s y‖ ∂μ) ≤ 3 :=
    B.eventually_integral_norm_cutoffHeatParametrix_le_three N χ hχ.continuous
      (HasCompactSupport.of_compactSpace χ) hχp hs
  have hf : TendstoUniformly f f₀ (𝓝[>] (0 : ℝ)) := tendstoUniformly_heatKernel_sub g ht x
  have hlim : Tendsto (fun s => ∫ y, K s y * f₀ y ∂μ)
      (𝓝[>] 0) (𝓝 (heatKernel g t x p)) :=
    B.tendsto_integral_cutoffHeatParametrix_mul N χ (heatKernel g t x) hχ.continuous
      (HasCompactSupport.of_compactSpace χ) hχp hs
      ((continuousOn_heatKernel g).comp_continuous
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => ⟨ht, mem_univ _⟩))
  have hmain := MeasureTheory.tendsto_integral_mul_of_tendstoUniformly_of_integral_norm_bounded
    hK hifs hi₀ hbound hf hlim
  simpa only [f, K, μ, mul_comm] using hmain

omit [T2Space (TangentBundle I M)] in
private theorem cutoffHeatParametrix_sub_heatKernel_le_of_initial_pairing
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U)
    (N : ℕ) {t C : ℝ} (ht : 0 < t) (x : M)
    (hbound : ∀ s ∈ Ioc 0 t, ∀ y, |B.cutoffHeatParametrixResidual χ N s y| ≤ C)
    (hinit : Tendsto (fun s => ∫ y, heatKernel g (t - s) x y *
      B.cutoffHeatParametrix χ N s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (heatKernel g t x p))) :
    |B.cutoffHeatParametrix χ N t x - heatKernel g t x p| ≤ t * C := by
  have hcont := (B.contMDiffOn_cutoffHeatParametrixResidual_joint hχ hs N).continuousOn
  let D : RealTimeInterval := RealTimeInterval.openInterval 0 (t + 1) t ⟨ht, by linarith⟩
  have hD : D.carrier ⊆ Ioi 0 := fun _ hs => hs.1
  have hu := B.cutoffHeatParametrix_isHeatForcedOnStationary hχ hs N D hD
  have hint : IntervalIntegrable (fun s => ∫ y, heatKernel g (t - s) x y *
      B.cutoffHeatParametrixResidual χ N s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      volume 0 t := by
    apply intervalIntegrable_integral_heatKernel_mul_of_bounded
      (F := B.cutoffHeatParametrixResidual χ N) (C := C) g ht.le x
      (hcont.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
    intro s hs y
    simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1, hs.2.le⟩ y
  have hreg : Ioo 0 t ⊆ D.regular := fun _ hs => ⟨hs.1, by linarith [hs.2]⟩
  have htD : t ∈ D.carrier := ⟨ht, by linarith⟩
  have hf : ∀ s ∈ Ioo 0 t, ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g,
      ‖B.cutoffHeatParametrixResidual χ N s y‖ ≤ C := by
    intro s hs
    exact ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1, hs.2.le⟩ y
  have h := norm_sub_heatKernel_le_of_initial_pairing_tendsto g hu ht hreg htD x p hint hf
    (by simpa only [sub_zero] using hinit)
  simpa only [sub_zero, Real.norm_eq_abs] using h

private theorem cutoffHeatParametrix_two_centre
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (h0 : (0 : E) ∈ B.hom.source)
    (hn : Module.finrank ℝ E = 2) {χ : M → ℝ} (hχ : χ p = 1) {t : ℝ} (ht : 0 < t) :
    B.cutoffHeatParametrix χ 2 t p =
      1 / (4 * Real.pi * t) + metricScalarAt g p / (24 * Real.pi) +
        t / (4 * Real.pi) * heatParametrixCoefficientInCoordinates g B.hom B.inv
          (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) 2 p := by
  have ha₀ := (B.heatParametrixCoefficientInCoordinates_eventuallyEq h0 0).eq_of_nhds
  have ha₁ := (B.heatParametrixCoefficientInCoordinates_eventuallyEq h0 1).eq_of_nhds
  rw [heatParametrixCoefficient_zero_centre] at ha₀
  rw [heatParametrixCoefficient_one_centre] at ha₁
  simp only [cutoffHeatParametrix, heatParametrix, hχ, branchEnergy_center B h0,
    neg_zero, zero_div, Real.exp_zero, mul_one, one_mul, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pow_zero, pow_one, ha₀, ha₁, hn]
  norm_num only [Nat.cast_ofNat, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  have ht0 := ht.ne'
  field_simp
  ring

theorem cutoffHeatParametrix_sub_heatKernel_le_of_residual_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U)
    (hχp : χ p = 1) (N : ℕ) {t C : ℝ} (ht : 0 < t) (x : M)
    (hbound : ∀ s ∈ Ioc 0 t, ∀ y, |B.cutoffHeatParametrixResidual χ N s y| ≤ C) :
    |B.cutoffHeatParametrix χ N t x - heatKernel g t x p| ≤ t * C := by
  exact cutoffHeatParametrix_sub_heatKernel_le_of_initial_pairing B hχ hs N ht x hbound
    (B.tendsto_integral_heatKernel_mul_cutoffHeatParametrix hχ hs hχp N ht x)

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch

namespace DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

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

private theorem exists_heatKernel_diagonal_sub_leading_local_bound_of_isMetricNorm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hn : Module.finrank ℝ E = 2) (T : ℝ) (c : M) :
    ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ioc 0 T, ∀ p ∈ U,
        |heatKernel g t p p - 1 / (4 * Real.pi * t) -
          metricScalarAt g p / (24 * Real.pi)| ≤ t * C := by
  let B := stdBranch g hEnorm c
  obtain ⟨U, hU, hcU, _, hzero, χ, hχ, _, hχone, _, hsource, C, hC, hres⟩ :=
    B.exists_cutoffHeatParametrix_residual_le_mul_of_finrank_eq_two hn T
  obtain ⟨V, hV, hcV, _, hVreg⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInCoordinates_fixed_prod
  let a : M → ℝ := fun p => heatParametrixCoefficientInCoordinates g
    (B.fixed p).hom (B.fixed p).inv
    (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) 2 p
  have ha : ContinuousAt a c :=
    ((hVreg 2).continuousOn.continuousAt (hV.mem_nhds hcV)).comp
      (f := fun p : M => (p, p)) (continuousAt_id.prodMk continuousAt_id)
  have hb : ∀ᶠ p in 𝓝 c, |a p| < |a c| + 1 :=
    ha.abs (Iio_mem_nhds (by linarith : |a c| < |a c| + 1))
  obtain ⟨W, hWsub, hW, hcW⟩ := mem_nhds_iff.mp hb
  let A := |a c| + 1
  refine ⟨U ∩ W, hU.inter hW, ⟨hcU, hcW⟩, C * |T| + A / (4 * Real.pi),
    add_nonneg (mul_nonneg hC (abs_nonneg T)) (by dsimp [A]; positivity), ?_⟩
  intro t ht p hp
  have hpU : p ∈ closure U := subset_closure hp.1
  have hχp : χ p = 1 := (hχone p hpU).eq_of_nhds
  have herr := (B.fixed p).cutoffHeatParametrix_sub_heatKernel_le_of_residual_bound
    hχ (hsource p hpU) hχp 2 ht.1 p (C := C * |T|) (by
      intro s hs y
      rw [← (B.fixed p).cutoffHeatParametrix_residual
        (hχ.of_le ENat.LEInfty.out) (hsource p hpU) 2 hs.1 y]
      exact (hres p hpU s ⟨hs.1, hs.2.trans ht.2⟩ y).trans
        (mul_le_mul_of_nonneg_left ((hs.2.trans ht.2).trans (le_abs_self T)) hC))
  have hcentre := (B.fixed p).cutoffHeatParametrix_two_centre (hzero p hpU) hn hχp ht.1
  have haBound : |a p| ≤ A := (hWsub hp.2).le
  have htail : |t / (4 * Real.pi) * a p| ≤ t * (A / (4 * Real.pi)) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg ht.1.le (by positivity) : 0 ≤ t / (4 * Real.pi))]
    calc
      t / (4 * Real.pi) * |a p| ≤ t / (4 * Real.pi) * A :=
        mul_le_mul_of_nonneg_left haBound (div_nonneg ht.1.le (by positivity))
      _ = t * (A / (4 * Real.pi)) := by ring
  calc
    |heatKernel g t p p - 1 / (4 * Real.pi * t) - metricScalarAt g p / (24 * Real.pi)| =
        |(heatKernel g t p p - (B.fixed p).cutoffHeatParametrix χ 2 t p) +
          t / (4 * Real.pi) * a p| := by rw [hcentre]; congr 1; dsimp [a]; ring
    _ ≤ |heatKernel g t p p - (B.fixed p).cutoffHeatParametrix χ 2 t p| +
        |t / (4 * Real.pi) * a p| := abs_add_le _ _
    _ ≤ t * (C * |T|) + t * (A / (4 * Real.pi)) :=
      add_le_add (by rwa [abs_sub_comm]) htail
    _ = t * (C * |T| + A / (4 * Real.pi)) := by ring

end DifferentialGeometry.Analysis.HeatEquation

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_heatKernel_diagonal_sub_leading_local_bound
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank ℝ E = 2) (T : ℝ) (c : M) :
    ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ioc 0 T, ∀ p ∈ U,
        |heatKernel g t p p - 1 / (4 * Real.pi * t) -
          Geometry.Curvature.metricScalarAt g p / (24 * Real.pi)| ≤ t * C := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := inferInstance
  have hEnorm : IsMetricNorm g := isMetricNorm_of_riemannianBundle g
  exact exists_heatKernel_diagonal_sub_leading_local_bound_of_isMetricNorm g hEnorm hn T c

end DifferentialGeometry.Analysis.HeatEquation
