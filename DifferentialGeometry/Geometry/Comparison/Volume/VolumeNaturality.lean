import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma chartLIntegral_indicator_le
    (g h : SmoothRiemannianMetric I M) (x₀ : M)
    {A : Set M} (hA : MeasurableSet A) {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ A, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    ∫⁻ x,
        ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → ℝ) x) *
          A.indicator (1 : M → ℝ≥0∞) x
        ∂(chartLocalMeasure (I := I) h x₀) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → ℝ) x) *
            A.indicator (1 : M → ℝ≥0∞) x
          ∂(chartLocalMeasure (I := I) g x₀) := by
  let ρ : M → ℝ := fun x ↦ (chartAtlasPOU I M x₀ : M → ℝ) x
  let F : M → ℝ≥0∞ := A.indicator 1
  have hF : Measurable F := measurable_const.indicator hA
  have hρ : Measurable (fun x : M ↦ ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp
      ((chartAtlasPOU I M x₀).contMDiff.continuous.measurable)
  have hprod : Measurable (fun x : M ↦ ENNReal.ofReal (ρ x) * F x) :=
    hρ.mul hF
  rw [chartLocalMeasure_lintegral (I := I) h x₀ hprod,
    chartLocalMeasure_lintegral (I := I) g x₀ hprod]
  let target : Set E := (extChartAt I x₀).target
  let symm : E → M := fun y ↦ (extChartAt I x₀).symm y
  calc
    ∫⁻ y in target,
        ENNReal.ofReal (chartDensity (I := I) h x₀ (symm y)) *
          (ENNReal.ofReal (ρ (symm y)) * F (symm y))
        ∂(modelHaar (E := E)) ≤
      ∫⁻ y in target,
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (chartDensity (I := I) g x₀ (symm y)) *
            (ENNReal.ofReal (ρ (symm y)) * F (symm y)))
        ∂(modelHaar (E := E)) := by
      refine lintegral_mono fun y ↦ ?_
      by_cases hyA : symm y ∈ A
      · by_cases hρy : ρ (symm y) = 0
        · simp [hρy]
        · have hsource : symm y ∈
              (trivializationAt E (TangentSpace I) x₀).baseSet := by
            rw [trivializationAt_baseSet_eq_chartAt_source]
            exact (chartAtlasPOU_isSubordinate I M) x₀
              (subset_tsupport ρ hρy)
          have hdensity := chartDensity_le (I := I) g h hQ x₀ hsource
            (hcomp (symm y) hyA)
          have hdensity' :
              ENNReal.ofReal (chartDensity (I := I) h x₀ (symm y)) ≤
                ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
                  ENNReal.ofReal (chartDensity (I := I) g x₀ (symm y)) := by
            have := ENNReal.ofReal_le_ofReal hdensity
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at this
            exact this
          have hmul := mul_le_mul_left hdensity'
            (ENNReal.ofReal (ρ (symm y)) * F (symm y))
          simpa only [mul_assoc] using hmul
      · simp [F, Set.indicator_of_notMem hyA]
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ y in target,
          ENNReal.ofReal (chartDensity (I := I) g x₀ (symm y)) *
            (ENNReal.ofReal (ρ (symm y)) * F (symm y))
          ∂(modelHaar (E := E)) := by
      rw [lintegral_const_mul'
        (μ := (modelHaar (E := E)).restrict target)
        (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E))) _
        ENNReal.ofReal_ne_top]

theorem riemannianVolumeMeasure_apply_le_of_inner_le_on
    (g h : SmoothRiemannianMetric I M) {A : Set M} (hA : MeasurableSet A)
    {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ A, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := M) h A ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g A := by
  let F : M → ℝ≥0∞ := A.indicator 1
  have hF : Measurable F := measurable_const.indicator hA
  have hlin :
      (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h)) ≤
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
          ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    change (∫⁻ x, F x ∂riemannianMeasure (I := I) h (chartAtlasPOU I M)) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ x, F x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M)
    rw [riemannianMeasure_lintegral_eq (I := I) h (chartAtlasPOU I M) hF,
      riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF]
    calc
      (∑' x₀ : M, ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) h x₀)) ≤
        ∑' x₀ : M,
          ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
            ∫⁻ x,
              ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → ℝ) x) * F x
                ∂(chartLocalMeasure (I := I) g x₀) := by
          refine ENNReal.tsum_le_tsum fun x₀ ↦ ?_
          exact chartLIntegral_indicator_le (I := I) g h x₀ hA hQ hcomp
      _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
          ∑' x₀ : M, ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) g x₀) := ENNReal.tsum_mul_left
  simpa only [F, lintegral_indicator_one hA] using hlin

theorem riemannianVolumeMeasure_apply_eq_of_inner_eqOn
    (g h : SmoothRiemannianMetric I M) {A : Set M} (hA : MeasurableSet A)
    (heq : ∀ x ∈ A, ∀ v : TangentSpace I x,
      g.inner x v v = h.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      riemannianVolumeMeasure (I := I) (M := M) h A := by
  apply le_antisymm
  · simpa using
      (riemannianVolumeMeasure_apply_le_of_inner_le_on
        (I := I) h g hA (Q := 1) zero_lt_one
        (fun x hx v ↦ by simpa using (heq x hx v).le))
  · simpa using
      (riemannianVolumeMeasure_apply_le_of_inner_le_on
        (I := I) g h hA (Q := 1) zero_lt_one
        (fun x hx v ↦ by simpa using (heq x hx v).ge))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
