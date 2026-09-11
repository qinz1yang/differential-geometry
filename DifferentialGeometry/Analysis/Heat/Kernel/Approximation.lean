import DifferentialGeometry.Analysis.Heat.Kernel.PointwiseForcing
import DifferentialGeometry.Analysis.Heat.Kernel.DuhamelBound
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory Filter Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem tendsto_integral_heatKernel_mul_smoothScalar
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g) (x : M) :
    Tendsto (fun r : ℝ => ∫ y, heatKernel g r x y * u₀.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (u₀.toFun x)) := by
  have hcont : ContinuousOn
      (fun r : ℝ => scalarHeatFlow g (smoothToLp g u₀) r x) (Icc 0 1) :=
    (scalarHeatFlow_smoothInitial_contMDiffOn_closed g u₀
      (T := 1) zero_lt_one).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ x⟩)
  have hlim := (hcont 0 ⟨le_rfl, zero_le_one⟩).tendsto.mono_left
    (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsGT (zero_lt_one : (0 : ℝ) < 1),
    scalarHeatFlow_smoothInitial_zero_apply] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (integral_heatKernel_mul_smoothScalar_eq_scalarHeatFlow g u₀ hr x).symm

private theorem integrable_heatKernel_mul_continuous
    (g : SmoothRiemannianMetric I M) {r : ℝ} (hr : 0 < r) (x : M)
    {f : M → ℝ} (hf : Continuous f) :
    Integrable (fun y => heatKernel g r x y * f y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    g _ (HasCompactSupport.of_compactSpace _)
  exact ((continuousOn_heatKernel g).comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun _ => ⟨hr, mem_univ _⟩)).mul hf

theorem tendsto_integral_heatKernel_mul_of_continuous
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : Continuous f) (x : M) :
    Tendsto (fun r : ℝ => ∫ y, heatKernel g r x y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, _⟩ := hf.exists_contMDiff_approx I (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : M => ε / 3)) (fun _ => by positivity)
  let u : SmoothScalar g := ⟨v, v.contMDiff⟩
  have hlim := (Metric.tendsto_nhds.mp
    (tendsto_integral_heatKernel_mul_smoothScalar g u x)) (ε / 3) (by positivity)
  filter_upwards [hlim, self_mem_nhdsWithin] with r hr hrpos
  have hif := integrable_heatKernel_mul_continuous g hrpos x hf
  have hiu := integrable_heatKernel_mul_continuous g hrpos x u.smooth.continuous
  have heq : (∫ y, heatKernel g r x y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) -
      (∫ y, heatKernel g r x y * u.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y, heatKernel g r x y * (f y - u.toFun y)
      ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    simp_rw [mul_sub]
    exact (integral_sub hif hiu).symm
  have hb : dist (∫ y, heatKernel g r x y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (∫ y, heatKernel g r x y * u.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε / 3 := by
    rw [dist_eq_norm, heq]
    apply norm_integral_heatKernel_mul_le g hrpos x
    exact Filter.Eventually.of_forall (fun y => by
      simpa only [← dist_eq_norm, dist_comm] using (hv y).le)
  have hx : dist (u.toFun x) (f x) < ε / 3 := hv x
  have htri := dist_triangle
    (∫ y, heatKernel g r x y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
    (∫ y, heatKernel g r x y * u.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (f x)
  have htri' := dist_triangle
    (∫ y, heatKernel g r x y * u.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (u.toFun x) (f x)
  linarith

private theorem tendsto_integral_heatKernel_mul_sub
    (g : SmoothRiemannianMetric I M) {u : ℝ → M → ℝ} {U : Set ℝ} {t : ℝ}
    (hu : ContinuousOn u.uncurry (U ×ˢ univ)) (ht : t ∈ U) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y * (u s y - u t y)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[U ∩ Iio t] t) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, hvu⟩ := isCompact_univ.mem_uniformity_of_prod hu ht
    (Metric.dist_mem_uniformity (α := ℝ) (half_pos hε))
  have hle : 𝓝[U ∩ Iio t] t ≤ 𝓝[U] t := nhdsWithin_mono _ inter_subset_left
  filter_upwards [hle hv, self_mem_nhdsWithin] with s hs hst
  have hb := norm_integral_heatKernel_mul_le g (sub_pos.mpr hst.2) x
    (show ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g,
      ‖u s y - u t y‖ ≤ ε / 2 from by
      filter_upwards with y
      exact le_of_lt (by
        simpa only [Set.mem_ofPred_eq, dist_eq_norm] using hvu s hs y (mem_univ y)))
  simpa only [dist_zero_right] using lt_of_le_of_lt hb (half_lt_self hε)

theorem tendsto_integral_heatKernel_mul_time_dependent
    (g : SmoothRiemannianMetric I M) {u : ℝ → M → ℝ} {U : Set ℝ} {t : ℝ}
    (hu : ContinuousOn u.uncurry (U ×ˢ univ)) (ht : t ∈ U) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y * u s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[U ∩ Iio t] t) (𝓝 (u t x)) := by
  have hut : Continuous (u t) := hu.comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨ht, mem_univ y⟩)
  have hsub : Tendsto (fun s : ℝ => t - s) (𝓝[U ∩ Iio t] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using
        (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun s : ℝ => t - s) (𝓝[U ∩ Iio t] t) (𝓝 (t - t)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact show 0 < t - s from sub_pos.mpr hs.2
  have hfixed := (tendsto_integral_heatKernel_mul_of_continuous g hut x).comp hsub
  have hsum := (tendsto_integral_heatKernel_mul_sub g hu ht x).add hfixed
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hus : Continuous (u s) := hu.comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨hs.1, mem_univ y⟩)
  have hi₁ := integrable_heatKernel_mul_continuous g (sub_pos.mpr hs.2) x (hus.sub hut)
  have hi₂ := integrable_heatKernel_mul_continuous g (sub_pos.mpr hs.2) x hut
  change (∫ y, heatKernel g (t - s) x y * (u s y - u t y)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) +
      (∫ y, heatKernel g (t - s) x y * u t y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = _
  calc
    _ = ∫ y, (heatKernel g (t - s) x y * (u s y - u t y) +
        heatKernel g (t - s) x y * u t y)
      ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      (integral_add hi₁ hi₂).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      ring

theorem tendsto_integral_heatKernel_mul_time_dependent_Icc
    (g : SmoothRiemannianMetric I M) {u : ℝ → M → ℝ} {a t : ℝ}
    (hat : a < t) (hu : ContinuousOn u.uncurry (Icc a t ×ˢ univ)) (x : M) :
    Tendsto (fun s : ℝ => ∫ y, heatKernel g (t - s) x y * u s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[<] t) (𝓝 (u t x)) := by
  apply (tendsto_integral_heatKernel_mul_time_dependent g hu ⟨hat.le, le_rfl⟩ x).mono_left
  rw [← nhdsWithin_Ico_eq_nhdsLT hat]
  exact nhdsWithin_mono _ (fun s hs => ⟨⟨hs.1, hs.2.le⟩, hs.2⟩)

end DifferentialGeometry.Analysis.HeatEquation
