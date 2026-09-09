import DifferentialGeometry.Analysis.Heat.Kernel.Regularity
import DifferentialGeometry.Analysis.Integration.Measure.FiniteParametricIntegral
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

import DifferentialGeometry.Analysis.Heat.Kernel.Approximation

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open Filter MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem continuousOn_integral_heatKernel_mul_time_dependent
    (g : SmoothRiemannianMetric I M) {u : ℝ → M → ℝ} {U : Set ℝ} (t : ℝ)
    (hu : ContinuousOn u.uncurry (U ×ˢ univ)) (x : M) :
    ContinuousOn (fun s : ℝ => ∫ y, heatKernel g (t - s) x y * u s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (U ∩ Iio t) := by
  let _ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts g
  apply continuousOn_integral_of_compact_support (k := (univ : Set M)) isCompact_univ
  · apply ContinuousOn.mul
    · exact (continuousOn_heatKernel g).comp
        (show ContinuousOn (fun q : ℝ × M => (t - q.1, (x, q.2)))
          ((U ∩ Iio t) ×ˢ univ) from by fun_prop)
        (fun q hq => ⟨show 0 < t - q.1 from sub_pos.mpr hq.1.2, mem_univ _⟩)
    · exact hu.mono (fun q hq => ⟨hq.1.1, hq.2⟩)
  · exact fun _ y _ hy => (hy (mem_univ y)).elim

theorem tendsto_integral_heatKernel_mul_time_dependent_left
    (g : SmoothRiemannianMetric I M) {u : ℝ → M → ℝ} {a t : ℝ}
    (hat : a < t) (hu : ContinuousOn u.uncurry (Icc a t ×ˢ univ)) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y * u s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] a)
      (𝓝 (∫ y, heatKernel g (t - a) x y * u a y
        ∂riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hc := continuousOn_integral_heatKernel_mul_time_dependent g t hu x
  have hlim := (hc a ⟨⟨le_rfl, hat.le⟩, hat⟩).tendsto
  apply hlim.mono_left
  rw [← nhdsWithin_Ioo_eq_nhdsGT hat]
  exact nhdsWithin_mono _ (fun s hs => ⟨⟨hs.1.le, hs.2.le⟩, hs.2⟩)

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private theorem continuous_deriv_slice_of_jointSmoothOn
    {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => f q.1 q.2) (U ×ˢ univ))
    {t : ℝ} (ht : t ∈ U) :
    Continuous (fun y => deriv (fun r => f r y) t) := by
  have hdf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => deriv (fun r => f r q.2) q.1) (U ×ˢ univ) := by
    intro q hq
    exact (timeDeriv_smoothAt ((hf q hq).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds hq)) (by simp)).contMDiffWithinAt
  exact hdf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    (fun y => ⟨ht, mem_univ y⟩)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem hasDerivAt_integral_jointSmoothOn
    (g : SmoothRiemannianMetric I M) {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => f q.1 q.2) (U ×ˢ univ))
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun s => ∫ y, f s y ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (∫ y, deriv (fun s => f s y) t ∂riemannianVolumeMeasure (I := I) (M := M) g) t := by
  let L := ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
  have hdf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => deriv (fun s => f s q.2) q.1) (U ×ˢ univ) := by
    intro q hq
    exact (timeDeriv_smoothAt ((hf q hq).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds hq)) (by simp)).contMDiffWithinAt
  have hslice (s : ℝ) (hs : s ∈ U) (y : M) : DifferentiableAt ℝ (fun r => f r y) s := by
    have hat := (hf (s, y) ⟨hs, mem_univ y⟩).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hcomp := hat.comp s (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hd := hasFDerivAt_integral_compactOn μ hU f
    (fun s y => L (deriv (fun r => f r y) s)) hf.continuousOn
    (L.continuous.comp_continuousOn hdf.continuousOn)
    (fun s hs y => (hslice s hs y).hasDerivAt.hasFDerivAt) t ht
  have hi : Integrable (fun y => L (deriv (fun r => f r y) t)) μ := by
    have hcont := (L.continuous.comp_continuousOn hdf.continuousOn).comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨ht, mem_univ y⟩)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomm := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) hi
  apply hd.hasDerivAt.congr_deriv
  calc
    _ = ∫ y, L (deriv (fun r => f r y) t) 1 ∂μ := hcomm.symm
    _ = _ := by simp [L, ContinuousLinearMap.smulRightL, μ]

private theorem heatKernel_hasDerivAt_right (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) (x y : M) :
    HasDerivAt (fun s => heatKernel g s x y)
      (laplacian (LeviCivita g) g (fun z => heatKernel g t x z) y) t := by
  simpa only [heatKernel_symm g _ x] using heatKernel_hasDerivAt g ht y x


private theorem contMDiffOn_heatKernel_mul_forced
    (g : SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {f u : ℝ → M → ℝ} (hu : Parabolic.IsHeatForcedOnStationary D g f u)
    (t : ℝ) (x : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => heatKernel g (t-q.1) x q.2 * u q.1 q.2)
      ((D.regular ∩ Iio t) ×ˢ univ) := by
  let U := D.regular ∩ Iio t
  have hksmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => heatKernel g (t-q.1) x q.2) (U ×ˢ univ) := by
    have harg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (t-q.1, q.2)) :=
      (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
    have h := (contMDiffOn_heatKernel_left g x).comp (s := U ×ˢ univ)
      harg.contMDiffOn
      (by
        intro q hq
        constructor
        · change 0 < t - q.1
          exact sub_pos.mpr hq.1.2
        · exact mem_univ q.2)
    convert h using 1
    ext q
    simp [heatKernel_symm]
  have husmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2) (U ×ˢ univ) :=
    hu.jointSmooth.mono (prod_mono inter_subset_left Subset.rfl)
  exact hksmooth.mul husmooth

private theorem deriv_heatKernel_mul_forced
    (g : SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {f u : ℝ → M → ℝ} (hu : Parabolic.IsHeatForcedOnStationary D g f u)
    {s t : ℝ} (hs : s ∈ D.regular) (hst : s < t) (x y : M) :
    deriv (fun r => heatKernel g (t - r) x y * u r y) s =
      (heatKernel g (t - s) x y * ΔG g ⟨u s, hu.sliceSmooth s (D.regular_subset hs)⟩ y -
        u s y * ΔG g ⟨fun z => heatKernel g (t - s) x z,
          heatKernel_right_contMDiff g (sub_pos.mpr hst) x⟩ y) +
            heatKernel g (t - s) x y * f s y := by
  have hpos := sub_pos.mpr hst
  have hku := heatKernel_right_contMDiff g hpos x
  have hus := hu.sliceSmooth s (D.regular_subset hs)
  have hk := (heatKernel_hasDerivAt_right g hpos x y).comp s
    ((hasDerivAt_id s).const_sub t)
  have hh := hk.mul (hu.equation s hs y)
  have hpoint : HasDerivAt (fun r => heatKernel g (t - r) x y * u r y)
      (laplacian (LeviCivita g) g (fun z => heatKernel g (t - s) x z) y * -1 * u s y +
        heatKernel g (t - s) x y *
          (laplacianAt (stationaryMetricFamily g) s (u s) y + f s y)) s := by
    exact hh
  have hlu : laplacianAt (stationaryMetricFamily g) s (u s) y = ΔG g ⟨_, hus⟩ y :=
    laplacianAt_eq_delta (stationaryMetricFamily g) s hus
      (LeviCivita_eq_leviCivitaConnectionOfMetric g).symm y
  exact hpoint.deriv.trans (by rw [laplacian_levi_eq g hku, hlu]; ring)

theorem hasDerivAt_integral_heatKernel_mul_forced
    (g : SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {f u : ℝ → M → ℝ} (hu : Parabolic.IsHeatForcedOnStationary D g f u)
    {s t : ℝ} (hs : s ∈ D.regular) (hst : s < t) (x : M) :
    HasDerivAt
      (fun r => ∫ y, heatKernel g (t - r) x y * u r y
        ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (∫ y, heatKernel g (t - s) x y * f s y
        ∂riemannianVolumeMeasure (I := I) (M := M) g) s := by
  let U := D.regular ∩ Iio t
  have hU : IsOpen U := D.regular_isOpen.inter isOpen_Iio
  have hsU : s ∈ U := ⟨hs, hst⟩
  have hjoint := contMDiffOn_heatKernel_mul_forced g hu t x
  have hd := hasDerivAt_integral_jointSmoothOn g hU
    (fun r y => heatKernel g (t - r) x y * u r y) hjoint hsU
  have hpos := sub_pos.mpr hst
  have hku := heatKernel_right_contMDiff g hpos x
  have hus := hu.sliceSmooth s (D.regular_subset hs)
  have hder (y : M) := deriv_heatKernel_mul_forced g hu hs hst x y
  have hdercont := continuous_deriv_slice_of_jointSmoothOn hU
    (fun r y => heatKernel g (t - r) x y * u r y) hjoint hsU
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hcancel : Integrable (fun y =>
      heatKernel g (t - s) x y * ΔG g ⟨u s, hus⟩ y -
        u s y * ΔG g ⟨fun z => heatKernel g (t - s) x z, hku⟩ y) μ :=
    ((hku.continuous.mul (Δ_g_contMDiff g ⟨u s, hus⟩).continuous).sub
      (hus.continuous.mul (Δ_g_contMDiff g ⟨_, hku⟩).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hforce : Integrable (fun y => heatKernel g (t - s) x y * f s y) μ := by
    have hdint := hdercont.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    have hint := hdint.sub hcancel
    apply hint.congr
    filter_upwards [] with y
    change deriv (fun r => heatKernel g (t - r) x y * u r y) s -
      (heatKernel g (t - s) x y * ΔG g ⟨u s, hus⟩ y -
        u s y * ΔG g ⟨fun z => heatKernel g (t - s) x z, hku⟩ y) =
      heatKernel g (t - s) x y * f s y
    rw [hder y]
    ring
  apply hd.congr_deriv
  simp_rw [hder]
  rw [integral_add hcancel hforce,
    green_second_integral_smul_laplacian_sub_eq_zero g hku hus, zero_add]

theorem intervalIntegrable_integral_heatKernel_mul_of_bounded
    (g : SmoothRiemannianMetric I M) {F : ℝ → M → ℝ} {a t C : ℝ}
    (hat : a ≤ t) (x : M) (hF : ContinuousOn F.uncurry (Ioo a t ×ˢ univ))
    (hbound : ∀ s ∈ Ioo a t, ∀ y, ‖F s y‖ ≤ C) :
    IntervalIntegrable (fun s => ∫ y, heatKernel g (t - s) x y * F s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) volume a t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat]
  apply IntegrableOn.of_bound (C := C) measure_Ioo_lt_top
    (((continuousOn_integral_heatKernel_mul_time_dependent g t hF x).mono
      (fun s hs => ⟨hs, hs.2⟩)).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact norm_integral_heatKernel_mul_le g (sub_pos.mpr hs.2) x
    (ae_of_all _ (hbound s hs))

theorem intervalIntegrable_integral_heatKernel_mul
    (g : SmoothRiemannianMetric I M) {F : ℝ → M → ℝ} {a t : ℝ}
    (hat : a ≤ t) (x : M) (hF : ContinuousOn F.uncurry (Icc a t ×ˢ univ)) :
    IntervalIntegrable (fun s => ∫ y, heatKernel g (t - s) x y * F s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) volume a t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hF
  apply intervalIntegrable_integral_heatKernel_mul_of_bounded (C := C) g hat x
    (hF.mono (fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩))
  intro s hs y
  exact hC (s, y) ⟨⟨hs.1.le, hs.2.le⟩, mem_univ _⟩


theorem heatDuhamel_eq_sub_integral_heatKernel_mul
    (g : SmoothRiemannianMetric I M) {f u : ℝ → M → ℝ}
    {a t : ℝ} (hat : a < t)
    (hu : Parabolic.IsHeatForcedOnStationary (RealTimeInterval.closed a t hat.le) g f u)
    (x : M)
    (hint : IntervalIntegrable (fun s => ∫ y, heatKernel g (t - s) x y * f s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) volume a t) :
    heatDuhamel g f a t x = u t x -
      ∫ y, heatKernel g (t - a) x y * u a y
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have hright := tendsto_integral_heatKernel_mul_time_dependent_Icc g hat hu.jointCont x
  have hleft := tendsto_integral_heatKernel_mul_time_dependent_left g hat hu.jointCont x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hat
    (fun s hs => hasDerivAt_integral_heatKernel_mul_forced g hu hs hs.2 x)
    hint hleft hright
  simpa only [intervalIntegral.integral_of_le hat.le, integral_Ioc_eq_integral_Ioo,
    heatDuhamel] using hFTC

theorem heatDuhamel_eq_sub_integral_heatKernel_mul_of_bounded
    (g : SmoothRiemannianMetric I M) {f u : ℝ → M → ℝ}
    {a t C : ℝ} (hat : a < t)
    (hu : Parabolic.IsHeatForcedOnStationary (RealTimeInterval.closed a t hat.le) g f u)
    (hf : ContinuousOn f.uncurry (Ioo a t ×ˢ univ))
    (hbound : ∀ s ∈ Ioo a t, ∀ y, ‖f s y‖ ≤ C) (x : M) :
    heatDuhamel g f a t x = u t x -
      ∫ y, heatKernel g (t - a) x y * u a y
        ∂riemannianVolumeMeasure (I := I) (M := M) g :=
  heatDuhamel_eq_sub_integral_heatKernel_mul g hat hu x
    (intervalIntegrable_integral_heatKernel_mul_of_bounded g hat.le x hf hbound)

theorem heatDuhamel_eq_sub_integral_heatKernel_mul_of_continuous
    (g : SmoothRiemannianMetric I M) {f u : ℝ → M → ℝ}
    {a t : ℝ} (hat : a < t)
    (hu : Parabolic.IsHeatForcedOnStationary (RealTimeInterval.closed a t hat.le) g f u)
    (hf : ContinuousOn f.uncurry (Icc a t ×ˢ univ)) (x : M) :
    heatDuhamel g f a t x = u t x -
      ∫ y, heatKernel g (t - a) x y * u a y
        ∂riemannianVolumeMeasure (I := I) (M := M) g :=
  heatDuhamel_eq_sub_integral_heatKernel_mul g hat hu x
    (intervalIntegrable_integral_heatKernel_mul g hat.le x hf)

end

end DifferentialGeometry.Analysis.HeatEquation
