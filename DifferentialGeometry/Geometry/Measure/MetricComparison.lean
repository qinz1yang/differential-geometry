import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory Bundle
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_apply_le_of_inner_le
    (g h : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 < C)
    {S : Set M} (hS : MeasurableSet S)
    (hcomp : ∀ x ∈ S, ∀ v : TangentSpace I x, h.inner x v v ≤ C * g.inner x v v) :
    riemannianVolumeMeasure I M h S ≤
      ENNReal.ofReal (Real.sqrt (C ^ Module.finrank ℝ E)) * riemannianVolumeMeasure I M g S := by
  let F : M → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS
  let R : ℝ := Real.sqrt (C ^ Module.finrank ℝ E)
  have hlocal (α : M) :
      ∫⁻ x, ENNReal.ofReal (chartAtlasPOU I M α x) * F x ∂chartLocalMeasure h α ≤
        ENNReal.ofReal R *
          ∫⁻ x, ENNReal.ofReal (chartAtlasPOU I M α x) * F x ∂chartLocalMeasure g α := by
    have hm : Measurable (fun x => ENNReal.ofReal (chartAtlasPOU I M α x) * F x) :=
      (measurable_ofReal_pou_weight (chartAtlasPOU I M) α).mul hF
    rw [chartLocalMeasure_lintegral h α hm, chartLocalMeasure_lintegral g α hm,
      ← lintegral_const_mul' (ENNReal.ofReal R) _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro y
    let x := (extChartAt I α).symm y
    by_cases hx : x ∈ S
    · by_cases hρ : chartAtlasPOU I M α x = 0
      · change _ * (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) ≤
          _ * (_ * (ENNReal.ofReal (chartAtlasPOU I M α x) * F x))
        simp only [hρ, ENNReal.ofReal_zero, zero_mul, mul_zero, le_refl]
      · have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
          rw [trivializationAt_baseSet_eq_chartAt_source]
          exact chartAtlasPOU_isSubordinate I M α (subset_tsupport _ hρ)
        have hd := ENNReal.ofReal_le_ofReal (chartDensity_le g h hC α hbase (hcomp x hx))
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hd
        change ENNReal.ofReal (chartDensity h α x) *
          (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) ≤
          ENNReal.ofReal R * (ENNReal.ofReal (chartDensity g α x) *
            (ENNReal.ofReal (chartAtlasPOU I M α x) * F x))
        calc
          _ ≤ (ENNReal.ofReal R * ENNReal.ofReal (chartDensity g α x)) *
              (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) := mul_le_mul' hd le_rfl
          _ = _ := mul_assoc _ _ _
    · have hz : F x = 0 := indicator_of_notMem hx _
      change _ * (_ * F x) ≤ _ * (_ * (_ * F x))
      simp [hz]
  rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS]
  change (∫⁻ x, F x ∂riemannianVolumeMeasure I M h) ≤
    ENNReal.ofReal R * ∫⁻ x, F x ∂riemannianVolumeMeasure I M g
  rw [riemannianVolumeMeasure_def, riemannianVolumeMeasure_def,
    riemannianMeasure_lintegral_eq h _ hF, riemannianMeasure_lintegral_eq g _ hF]
  exact (ENNReal.tsum_le_tsum hlocal).trans_eq ENNReal.tsum_mul_left

end DifferentialGeometry.Geometry.Measure
