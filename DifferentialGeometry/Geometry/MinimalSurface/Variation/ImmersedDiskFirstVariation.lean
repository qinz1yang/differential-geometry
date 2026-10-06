import DifferentialGeometry.Geometry.MinimalSurface.Variation.CompactDiskMetricIntegral
import DifferentialGeometry.Geometry.Measure.Area.GramFirstDerivative
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import DifferentialGeometry.Geometry.Measure.Area.Pullback
import DifferentialGeometry.Geometry.Metric.ParameterPullbackFamily

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

/-- The actual metric derivative of an immersed disk's Gram area density,
expressed in its supplied coordinate frame. -/
def diskMapGramMetricVariationDensity (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (t : ℝ) (U : ℂ → M) (z : ℂ) : ℝ :=
  let A := fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)
  let B := fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)
  let C := fun r => (G r).inner (U z)
    (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)
  (C t * deriv A t + A t * deriv C t - 2 * B t * deriv B t) /
    (2 * riemannianAreaDensity (G t) U z)

omit [T2Space M] in
/-- The Gram quotient is the actual time derivative of the supplied immersion's
area density at each point. -/
theorem hasDerivAt_diskMapAreaDensity_metric_of_immersion
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {z : ℂ}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    HasDerivAt (fun r => riemannianAreaDensity (G r) U z)
      (diskMapGramMetricVariationDensity G t U z) t := by
  have hpair (v w : TangentSpace 𝓘(ℝ, E) (U z)) :=
    (((hG.coeff (U z) v w).contDiffAt ht).differentiableAt (by simp)).hasDerivAt
  have hframe : LinearIndependent ℝ
      ![diskMapPartial (E := E) U z 1, diskMapPartial (E := E) U z Complex.I] := by
    convert Complex.basisOneI.linearIndependent.map'
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z).toLinearMap (LinearMap.ker_eq_bot.mpr hi) using 1
    ext i
    fin_cases i <;> simp [Complex.coe_basisOneI] <;> rfl
  exact hasDerivAt_tangentTwoJacobian
    (x := fun _ => U z) (v := fun _ => diskMapPartial U z 1)
    (w := fun _ => diskMapPartial U z Complex.I)
    (hpair _ _) (hpair _ _) (hpair _ _) hframe

omit [T2Space M] in
private theorem contDiffOn_diskMapMetricPairing_deriv
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (v w : ℂ) :
    ContDiffOn ℝ ∞ (fun z => deriv (fun r =>
      (G r).inner (U z) (diskMapPartial U z v) (diskMapPartial U z w)) t) s := by
  intro z hz
  have hp : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ =>
      (G q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)) (t, z) :=
    ((contDiffOn_metricFamilyDiskPairing hG D.regular_isOpen Subset.rfl hs hU v w)
      (t, z) ⟨mem_of_mem_nhds ht, hz⟩).contDiffAt
        ((D.regular_isOpen.prod hs).mem_nhds ⟨mem_of_mem_nhds ht, hz⟩)
  exact ((contDiffAt_deriv_fst hp).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

private theorem hasDerivAt_integral_diskMapAreaDensity_metric_of_immersion
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    IntegrableOn (diskMapGramMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapGramMetricVariationDensity G t₀ U z) t₀ := by
  let B := Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B := isCompact_closedBall _ _
  have himage : IsCompact (U '' B) := hB.image_of_continuousOn (hU.continuousOn.mono hDs)
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hco (v w : ℂ) : ContinuousOn (fun z =>
      (G t₀).inner (U z) (diskMapPartial U z v) (diskMapPartial U z w)) B :=
    (contDiffOn_metricFamilyDiskPairing hG D.regular_isOpen Subset.rfl hs hU v w).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨mem_of_mem_nhds ht₀, hDs hz⟩)
  have hcd (v w : ℂ) : ContinuousOn (fun z => deriv (fun r =>
      (G r).inner (U z) (diskMapPartial U z v) (diskMapPartial U z w)) t₀) B :=
    (contDiffOn_diskMapMetricPairing_deriv hG ht₀ hs hU v w).continuousOn.mono hDs
  have hder : ContinuousOn (diskMapGramMetricVariationDensity G t₀ U) B := by
    apply ((((hco Complex.I Complex.I).mul (hcd 1 1)).add
      ((hco 1 1).mul (hcd Complex.I Complex.I))).sub
      ((continuousOn_const.mul (hco 1 Complex.I)).mul (hcd 1 Complex.I))).div
      (continuousOn_const.mul ((hJ t₀).mono hDs))
    intro z hz
    exact mul_ne_zero (by norm_num) (riemannianAreaDensity_pos_of_injective_mfderiv
      (G t₀) (hi z hz)).ne'
  obtain ⟨r, C, hr, hC, _, hbounds, hLip⟩ :=
    exists_metricFamily_quadratic_time_bounds_on_compact hG ht₀ himage
  let bound : ℂ → ℝ := fun z => 4 * C * riemannianAreaDensity (G t₀) U z
  have hbound : IntegrableOn bound B := hJ0.const_mul (4 * C)
  have hloc : ∀ z ∈ B,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t => riemannianAreaDensity (G t) U z) (Metric.ball t₀ r) := by
    intro z hz
    have hzimage : U z ∈ U '' B := mem_image_of_mem U hz
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht q hq
    have hδ : 0 ≤ 2 * C * |t - q| := by positivity
    have hrel : ∀ v : TangentSpace 𝓘(ℝ, E) (U z),
        |(G t).inner (U z) v v - (G q).inner (U z) v v| ≤
          (2 * C * |t - q|) * (G q).inner (U z) v v := by
      intro v
      calc
        |(G t).inner (U z) v v - (G q).inner (U z) v v| ≤
            C * |t - q| * (G t₀).inner (U z) v v := hLip t ht q hq (U z) hzimage v
        _ = (2 * C * |t - q|) * ((1 / 2 : ℝ) * (G t₀).inner (U z) v v) := by ring
        _ ≤ (2 * C * |t - q|) * (G q).inner (U z) v v :=
          mul_le_mul_of_nonneg_left (hbounds q hq (U z) hzimage v).1 hδ
    have herr := riemannianAreaDensity_metric_relative_error_at (G q) (G t)
      (u := U) (z := z) hδ hrel
    have harea := riemannianAreaDensity_metric_upper_at (G t₀) (G q)
      (u := U) (z := z) (by norm_num : (0 : ℝ) < 2)
      (fun v => (hbounds q hq (U z) hzimage v).2)
    have hmajor : |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G q) U z| ≤
        bound z * |t - q| := by
      calc
        _ ≤ (2 * C * |t - q|) * riemannianAreaDensity (G q) U z := herr
        _ ≤ (2 * C * |t - q|) * (2 * riemannianAreaDensity (G t₀) U z) :=
          mul_le_mul_of_nonneg_left harea hδ
        _ = bound z * |t - q| := by dsimp only [bound]; ring
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hC)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G q) U z| ≤
      |bound z| * |t - q|
    simpa only [abs_of_nonneg hn] using hmajor
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict B)
    (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapGramMetricVariationDensity G t₀ U) (bound := bound)
    (Metric.ball_mem_nhds t₀ hr)
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    ((ae_restrict_mem hB.measurableSet).mono (fun z hz => hloc z hz)) hbound
    ((ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivAt_diskMapAreaDensity_metric_of_immersion hG ht₀ (hi z hz)))

/-- First metric variation of the actual area of a smoothly extended disk.
Compactness of the disk image suffices; the ambient manifold need not be compact.
The supplied parametrization may be any immersion on the closed disk. -/
theorem SmoothDiskExtension.hasDerivAt_riemannianDiskArea_metric_of_immersion
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    IntegrableOn (diskMapGramMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapGramMetricVariationDensity G t₀ U z) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  obtain ⟨hInt, hderiv⟩ :=
    hasDerivAt_integral_diskMapAreaDensity_metric_of_immersion hG ht₀ hs hU hDs hi
  refine ⟨hInt, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact hderiv


/-- Actual disk-area variation under a smooth metric and ambient isotopy.
Compactness of the disk image supplies the integral domination. -/
theorem SmoothDiskExtension.hasDerivAt_riemannianDiskArea_isotopy_of_immersion
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hiU : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
    IntegrableOn (diskMapGramMetricVariationDensity H t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapGramMetricVariationDensity H t₀ U z) t₀ := by
  let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hT.mem_nhds hT₀) ht₀)
  have hi : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ hi
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  have hH : MetricFamilySmoothOn D' H :=
    metricFamilySmoothOn_parameterPullback hG hT hΦ D' rfl hsub
  have h := hu.hasDerivAt_riemannianDiskArea_metric_of_immersion hH
    (isOpen_Ioo.mem_nhds hi) hiU
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (H t) u) =
      (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) := by
    funext t
    exact hu.area_pullback (G t) (Φ t)
  rw [he] at h
  exact h.2


end DifferentialGeometry.Geometry
