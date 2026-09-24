import DifferentialGeometry.Analysis.Integration.Measure.Chart.Convergence
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Integral.Measure

open CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tendsto_riemannianVolumeDensity_of_metricDerivNorm
    {ι : Type*} {l : Filter ι} (gs : ι → SmoothRiemannianMetric I M)
    (g R : SmoothRiemannianMetric I M) (x : M)
    (hconv : Tendsto (fun i => metricDerivNorm (I := I) 0 (gs i) g R x) l (𝓝 0)) :
    Tendsto (fun i => riemannianVolumeDensity g (gs i) x) l (𝓝 1) := by
  let z := extChartAt I x x
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hz : z ∈ (extChartAt I x).target := (extChartAt I x).map_source hx
  have hzx : (extChartAt I x).symm z = x := (extChartAt I x).left_inv hx
  have hc := tendstoUniformlyOn_chartDensity_of_metricDerivNorm gs g R x
    (isCompact_singleton (x := z)) (singleton_subset_iff.mpr hz)
    (by
      rw [tendstoUniformlyOn_singleton_iff_tendsto, hzx]
      exact hconv)
  have hd : Tendsto (fun i => chartDensity (gs i) x x) l (𝓝 (chartDensity g x x)) := by
    simpa only [hzx] using hc.tendsto_at (mem_singleton z)
  have hp : chartDensity g x x ≠ 0 := (chartDensity_pos g x (mem_chart_source H x)).ne'
  have hratio := hd.div_const (chartDensity g x x)
  simp only [div_self hp] at hratio
  simpa only [riemannianVolumeDensity_apply_of_mem_chart_source g _ x
    (mem_chart_source H x)] using hratio

private theorem eventually_riemannianVolumeDensity_le
    {ι : Type*} {l : Filter ι} (gs : ι → SmoothRiemannianMetric I M)
    (g : SmoothRiemannianMetric I M) (s : Set M)
    (hconv : TendstoUniformlyOn (fun i x => metricDerivNorm (I := I) 0 (gs i) g g x)
      (fun _ => 0) l s) :
    ∀ᶠ i in l, ∀ x ∈ s,
      riemannianVolumeDensity g (gs i) x ≤ Real.sqrt ((2 : ℝ) ^ Module.finrank ℝ E) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hδ : 0 < 1 / (n + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv _ hδ] with i hi
  intro x hx
  apply riemannianVolumeDensity_le_of_inner_le g (gs i) (by norm_num) x
  intro v
  have hg0 : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hnorm : 0 ≤ metricDerivNorm (I := I) 0 (gs i) g g x := Real.sqrt_nonneg _
  have hsmall : metricDerivNorm (I := I) 0 (gs i) g g x < 1 / (n + 1) := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hnorm] using hi x hx
  have hcoef : n * metricDerivNorm (I := I) 0 (gs i) g g x ≤ 1 := by
    calc
      _ ≤ n * (1 / (n + 1)) := mul_le_mul_of_nonneg_left hsmall.le hn
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity : 0 < n + 1)]; linarith
  have hb := metricQuadFormDiff_le_metricDerivNorm (gs i) g g x v
  change |(gs i).inner x v v - g.inner x v v| ≤
    n * metricDerivNorm (I := I) 0 (gs i) g g x * g.inner x v v at hb
  have hd := (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_right hcoef hg0))
  nlinarith

theorem tendsto_setLIntegral_of_dominated_convergence_of_metricDerivNorm
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (gs : ι → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    {s : Set M} (hs : MeasurableSet s)
    (hmetric : TendstoUniformlyOn (fun i x => metricDerivNorm (I := I) 0 (gs i) g g x)
      (fun _ => 0) l s)
    {fs : ι → M → ℝ≥0∞} {f : M → ℝ≥0∞} (bound : M → ℝ≥0∞)
    (hmeas : ∀ᶠ i in l, AEMeasurable (fs i)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict s))
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g).restrict s,
      fs i x ≤ bound x)
    (hfin : ∫⁻ x in s, bound x ∂riemannianVolumeMeasure (I := I) (M := M) g ≠ ⊤)
    (hlim : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g).restrict s,
      Tendsto (fun i => fs i x) l (𝓝 (f x))) :
    Tendsto (fun i => ∫⁻ x in s, fs i x ∂riemannianVolumeMeasure (I := I) (M := M) (gs i))
      l (𝓝 (∫⁻ x in s, f x ∂riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ρ : ι → M → ℝ≥0∞ := fun i x => ENNReal.ofReal (riemannianVolumeDensity g (gs i) x)
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ Module.finrank ℝ E))
  have hρmeas (i : ι) : Measurable (ρ i) :=
    ENNReal.measurable_ofReal.comp (riemannianVolumeDensity_contMDiff g (gs i)).continuous.measurable
  have hmeas' : ∀ᶠ i in l, AEMeasurable (fun x => ρ i x * fs i x) (μ.restrict s) := by
    filter_upwards [hmeas] with i hi
    exact (hρmeas i).aemeasurable.mul hi
  have hbound' : ∀ᶠ i in l, ∀ᵐ x ∂μ.restrict s, ρ i x * fs i x ≤ C * bound x := by
    filter_upwards [hbound, eventually_riemannianVolumeDensity_le gs g s hmetric] with i hi hρ
    filter_upwards [hi, ae_restrict_mem hs] with x hx hxs
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hρ x hxs)) hx
  have hfin' : ∫⁻ x, C * bound x ∂μ.restrict s ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hlim' : ∀ᵐ x ∂μ.restrict s, Tendsto (fun i => ρ i x * fs i x) l (𝓝 (f x)) := by
    filter_upwards [hlim, ae_restrict_mem hs] with x hx hxs
    have hρ : Tendsto (fun i => ρ i x) l (𝓝 1) := by
      simpa only [ENNReal.ofReal_one, Function.comp_def, ρ] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_riemannianVolumeDensity_of_metricDerivNorm gs g g x (hmetric.tendsto_at hxs))
    simpa only [one_mul] using ENNReal.Tendsto.mul hρ (Or.inl one_ne_zero) hx
      (Or.inr ENNReal.one_ne_top)
  have hD := tendsto_lintegral_filter_of_dominated_convergence'
    (fun x => C * bound x) hmeas' hbound' hfin' hlim'
  apply hD.congr'
  apply Eventually.of_forall
  intro i
  dsimp only
  rw [riemannianVolumeMeasure_eq_withDensity g (gs i)]
  exact (setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable μ (hρmeas i)
    (fs i) hs (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).symm

end DifferentialGeometry.Integral.Measure
