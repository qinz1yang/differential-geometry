import DifferentialGeometry.Analysis.Integration.Measure.Invariance

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space M] [SigmaCompactSpace M] in
lemma chartDensity_div_eq
    (q h : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    chartDensity h x₀ x / chartDensity q x₀ x =
      chartDensity h x₁ x / chartDensity q x₁ x := by
  have hh := chartDensity_pullback_eq_abs_det_jacobian (I := I) h x₀ x₁
    (show x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet from hx₀)
    (show x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet from hx₁)
  have hq := chartDensity_pullback_eq_abs_det_jacobian (I := I) q x₀ x₁
    (show x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet from hx₀)
    (show x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet from hx₁)
  have hJ : |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| ≠ 0 := by
    intro hzero
    have hhpos : 0 < chartDensity h x₁ x := chartDensity_pos (I := I) h x₁ hx₁
    rw [hh, hzero, zero_mul] at hhpos
    exact lt_irrefl 0 hhpos
  rw [hh, hq]
  field_simp

def riemannianVolumeDensity
    (q h : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  ∑ᶠ α : M, (chartAtlasPOU I M α : M → ℝ) x •
    (chartDensity h α x / chartDensity q α x)

lemma riemannianVolumeDensity_apply_of_mem_chart_source
    (q h : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    riemannianVolumeDensity q h x =
      chartDensity h α x / chartDensity q α x := by
  unfold riemannianVolumeDensity
  calc
    ∑ᶠ β : M, (chartAtlasPOU I M β : M → ℝ) x •
        (chartDensity h β x / chartDensity q β x) =
      ∑ᶠ β : M, (chartAtlasPOU I M β : M → ℝ) x •
        (chartDensity h α x / chartDensity q α x) := by
          refine finsum_congr fun β => ?_
          by_cases hβ : (chartAtlasPOU I M β : M → ℝ) x = 0
          · simp [hβ]
          · have hxβ : x ∈ (chartAt H β).source :=
              (chartAtlasPOU_isSubordinate I M) β (subset_tsupport _ hβ)
            rw [chartDensity_div_eq (I := I) q h α β hx hxβ]
    _ = (∑ᶠ β : M, (chartAtlasPOU I M β : M → ℝ) x) •
        (chartDensity h α x / chartDensity q α x) := by
          rw [finsum_smul]
    _ = chartDensity h α x / chartDensity q α x := by
          rw [(chartAtlasPOU I M).sum_eq_one (mem_univ x), one_smul]

theorem riemannianVolumeDensity_contMDiff
    (q h : SmoothRiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ) ∞ (riemannianVolumeDensity q h) := by
  apply (chartAtlasPOU_isSubordinate I M).contMDiff_finsum_smul
  · exact fun α => (chartAt H α).open_source
  · intro α
    exact (chartDensity_contMDiffOn (I := I) h α).div₀
      (chartDensity_contMDiffOn (I := I) q α)
      (fun x hx => ne_of_gt (chartDensity_pos (I := I) q α hx))

def riemannianVolumeDensitySmoothMap
    (q h : SmoothRiemannianMetric I M) : C^∞⟮I, M; ℝ⟯ :=
  ⟨riemannianVolumeDensity q h, riemannianVolumeDensity_contMDiff q h⟩

theorem riemannianVolumeDensity_pos
    (q h : SmoothRiemannianMetric I M) (x : M) :
    0 < riemannianVolumeDensity q h x := by
  rw [riemannianVolumeDensity_apply_of_mem_chart_source
    (I := I) q h x (mem_chart_source H x)]
  exact div_pos (chartDensity_pos (I := I) h x (mem_chart_source H x))
    (chartDensity_pos (I := I) q x (mem_chart_source H x))

@[simp]
theorem riemannianVolumeDensity_self
    (q : SmoothRiemannianMetric I M) (x : M) :
    riemannianVolumeDensity q q x = 1 := by
  rw [riemannianVolumeDensity_apply_of_mem_chart_source
    (I := I) q q x (mem_chart_source H x)]
  exact div_self (ne_of_gt (chartDensity_pos (I := I) q x (mem_chart_source H x)))

theorem riemannianVolumeDensity_mul
    (q h k : SmoothRiemannianMetric I M) (x : M) :
    riemannianVolumeDensity q h x * riemannianVolumeDensity h k x =
      riemannianVolumeDensity q k x := by
  rw [riemannianVolumeDensity_apply_of_mem_chart_source
      (I := I) q h x (mem_chart_source H x),
    riemannianVolumeDensity_apply_of_mem_chart_source
      (I := I) h k x (mem_chart_source H x),
    riemannianVolumeDensity_apply_of_mem_chart_source
      (I := I) q k x (mem_chart_source H x)]
  have hq : chartDensity q x x ≠ 0 :=
    ne_of_gt (chartDensity_pos (I := I) q x (mem_chart_source H x))
  have hh : chartDensity h x x ≠ 0 :=
    ne_of_gt (chartDensity_pos (I := I) h x (mem_chart_source H x))
  field_simp

@[simp]
theorem riemannianVolumeDensity_mul_swap
    (q h : SmoothRiemannianMetric I M) (x : M) :
    riemannianVolumeDensity q h x * riemannianVolumeDensity h q x = 1 := by
  rw [riemannianVolumeDensity_mul, riemannianVolumeDensity_self]

private lemma chartLocalMeasure_lintegral_eq_withDensity
    (q h : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) h α) =
      ∫⁻ x, ENNReal.ofReal (riemannianVolumeDensity q h x) * F x
        ∂(chartLocalMeasure (I := I) q α) := by
  rw [chartLocalMeasure_lintegral (I := I) h α hF]
  have hprod : Measurable
      (fun x => ENNReal.ofReal (riemannianVolumeDensity q h x) * F x) :=
    (ENNReal.measurable_ofReal.comp
      (riemannianVolumeDensity_contMDiff (I := I) q h).continuous.measurable).mul hF
  conv_rhs =>
    rw [chartLocalMeasure_lintegral (I := I) q α hprod]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := modelHaar (E := E))
    (s := (extChartAt I α).target)
    (measurableSet_extChartAt_target (I := I) α)] with y hy
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hy
  have hqpos : 0 < chartDensity q α ((extChartAt I α).symm y) :=
    chartDensity_pos (I := I) q α hx
  have hqtop : ENNReal.ofReal (chartDensity q α ((extChartAt I α).symm y)) ≠
      (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hqzero : ENNReal.ofReal (chartDensity q α ((extChartAt I α).symm y)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hqpos
  rw [riemannianVolumeDensity_apply_of_mem_chart_source (I := I) q h α hx]
  rw [ENNReal.ofReal_div_of_pos hqpos]
  rw [← mul_assoc]
  rw [mul_comm (ENNReal.ofReal (chartDensity q α ((extChartAt I α).symm y)))
    (ENNReal.ofReal (chartDensity h α ((extChartAt I α).symm y)) /
      ENNReal.ofReal (chartDensity q α ((extChartAt I α).symm y)))]
  rw [ENNReal.div_mul_cancel hqzero hqtop]

theorem chartLocalMeasure_eq_withDensity
    (q h : SmoothRiemannianMetric I M) (α : M) :
    chartLocalMeasure (I := I) h α =
      (chartLocalMeasure (I := I) q α).withDensity
        (fun x => ENNReal.ofReal (riemannianVolumeDensity q h x)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  conv_rhs =>
    rw [lintegral_withDensity_eq_lintegral_mul
      (μ := chartLocalMeasure (I := I) q α)
      (f := fun x => ENNReal.ofReal (riemannianVolumeDensity q h x))
      (ENNReal.measurable_ofReal.comp
        (riemannianVolumeDensity_contMDiff (I := I) q h).continuous.measurable)
      (g := F) hF]
  exact chartLocalMeasure_lintegral_eq_withDensity (I := I) q h α hF

theorem riemannianVolumeMeasure_eq_withDensity
    (q h : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) h =
      (riemannianVolumeMeasure (I := I) (M := M) q).withDensity
        (fun x => ENNReal.ofReal (riemannianVolumeDensity q h x)) := by
  have hd : Measurable (fun x => ENNReal.ofReal (riemannianVolumeDensity q h x)) :=
    ENNReal.measurable_ofReal.comp
      (riemannianVolumeDensity_contMDiff (I := I) q h).continuous.measurable
  rw [riemannianVolumeMeasure_def, riemannianVolumeMeasure_def,
    riemannianMeasure_def, riemannianMeasure_def, withDensity_sum]
  congr 1
  funext α
  have hρ : Measurable (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) :=
    measurable_ofReal_pou_weight (chartAtlasPOU I M) α
  rw [chartLocalMeasure_eq_withDensity (I := I) q h α]
  rw [← withDensity_mul _ hd hρ, ← withDensity_mul _ hρ hd]
  congr 1
  funext x
  change ENNReal.ofReal (riemannianVolumeDensity q h x) *
      ENNReal.ofReal ((chartAtlasPOU I M) α x) =
    ENNReal.ofReal ((chartAtlasPOU I M) α x) *
      ENNReal.ofReal (riemannianVolumeDensity q h x)
  exact mul_comm _ _

theorem integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q h : SmoothRiemannianMetric I M) (f : M → F) :
    (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) h)) =
      ∫ x, riemannianVolumeDensity q h x • f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  rw [riemannianVolumeMeasure_eq_withDensity (I := I) q h]
  have hρ : AEMeasurable
      (fun x : M => ENNReal.ofReal (riemannianVolumeDensity q h x))
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    (ENNReal.measurable_ofReal.comp
      (riemannianVolumeDensity_contMDiff (I := I) q h).continuous.measurable).aemeasurable
  have hρtop : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) q),
      ENNReal.ofReal (riemannianVolumeDensity q h x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => by simp
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal
    (le_of_lt (riemannianVolumeDensity_pos (I := I) q h x))]

end Measure
end Integral
end DifferentialGeometry
