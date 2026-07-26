import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition

/-!
# Uniform comparison of compact metric-family volume measures

This file proves the measure comparison needed by nonautonomous weak parabolic
problems on a closed manifold.  The input is deliberately only joint `C^0`
control of the chart Gram matrices on a compact time set.  No time derivative
of the metric and no matrix Loewner-to-determinant estimate is needed.

The proof uses the finite canonical partition of unity.  On each compact set
`J x tsupport rho_alpha`, both ratios of the moving and reference chart
densities are continuous and hence bounded.  The chart-target lower-integral
formula then compares the weighted chart-local measures, and the finite POU
sum gives a single constant for the global volume measures.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Joint continuity of chart density follows from joint continuity of every
chart Gram-matrix entry.  This is the `C^0` core of
`continuousOn_chartDensity_family`, separated from its stronger time-derivative
interface. -/
lemma density_cont_of_gram
    (g : ℝ → SmoothRiemannianMetric I M) (alpha : M)
    {S : Set (ℝ × M)}
    (hG : ∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) alpha p.2 i j) S) :
    ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g p.1) alpha p.2) S := by
  classical
  let n := Fin (Module.finrank ℝ E)
  have hdet : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) alpha p.2).det) S := by
    have hexp :
        (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) alpha p.2).det) =
          (fun p : ℝ × M =>
            ∑ sigma : Equiv.Perm n, ((Equiv.Perm.sign sigma : ℤ) : ℝ) *
              ∏ i, chartGramMatrix (I := I) (g p.1) alpha p.2 (sigma i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finset_sum _ (fun sigma _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    exact hG (sigma i) i
  exact Real.continuous_sqrt.comp_continuousOn hdet

/-- On one POU chart, both moving/reference density ratios are uniformly
bounded on a compact time set and the POU `tsupport`. -/
lemma density_ratio_bdd
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) (alpha : M)
    {J : Set ℝ} (hJ : IsCompact J)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) alpha p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ J, ∀ x ∈ tsupport
        (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
      chartDensity (I := I) (g t) alpha x ≤ C * chartDensity (I := I) q alpha x ∧
      chartDensity (I := I) q alpha x ≤ C * chartDensity (I := I) (g t) alpha x := by
  classical
  let rho : M → ℝ := fun x => (chartAtlasPOU I M alpha : M → ℝ) x
  let K : Set (ℝ × M) := J ×ˢ tsupport rho
  have hrho_compact : IsCompact (tsupport rho) := isClosed_tsupport rho |>.isCompact
  have hK_compact : IsCompact K := hJ.prod hrho_compact
  have hrho_base : tsupport rho ⊆
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) alpha hx
  have hK_base : K ⊆
      J ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    intro p hp
    exact ⟨hp.1, hrho_base hp.2⟩
  have hg_cont : ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g p.1) alpha p.2) K :=
    density_cont_of_gram (I := I) (M := M) g alpha
      (fun i j => (hgram i j).mono hK_base)
  have hq_cont : ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) q alpha p.2) K := by
    refine (chartDensity_continuousOn (I := I) q alpha).comp
      continuous_snd.continuousOn ?_
    intro p hp
    exact hrho_base hp.2
  have hg_pos : ∀ p ∈ K,
      0 < chartDensity (I := I) (g p.1) alpha p.2 := by
    intro p hp
    exact chartDensity_pos (I := I) (g p.1) alpha (hrho_base hp.2)
  have hq_pos : ∀ p ∈ K,
      0 < chartDensity (I := I) q alpha p.2 := by
    intro p hp
    exact chartDensity_pos (I := I) q alpha (hrho_base hp.2)
  let rgh : ℝ × M → ℝ := fun p =>
    chartDensity (I := I) (g p.1) alpha p.2 /
      chartDensity (I := I) q alpha p.2
  let rhg : ℝ × M → ℝ := fun p =>
    chartDensity (I := I) q alpha p.2 /
      chartDensity (I := I) (g p.1) alpha p.2
  have rgh_cont : ContinuousOn rgh K := by
    exact hg_cont.div hq_cont (fun p hp => ne_of_gt (hq_pos p hp))
  have rhg_cont : ContinuousOn rhg K := by
    exact hq_cont.div hg_cont (fun p hp => ne_of_gt (hg_pos p hp))
  by_cases hK_ne : K.Nonempty
  · obtain ⟨pgh, _hpgh, hpgh_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne rgh_cont
    obtain ⟨phg, _hphg, hphg_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne rhg_cont
    let C : ℝ := max 1 (max (rgh pgh) (rhg phg))
    refine ⟨C, le_max_left _ _, ?_⟩
    intro t ht x hx
    have htx : (t, x) ∈ K := ⟨ht, hx⟩
    have hrgh : rgh (t, x) ≤ C :=
      (hpgh_max htx).trans
        ((le_max_left (rgh pgh) (rhg phg)).trans (le_max_right 1 _))
    have hrhg : rhg (t, x) ≤ C :=
      (hphg_max htx).trans
        ((le_max_right (rgh pgh) (rhg phg)).trans (le_max_right 1 _))
    constructor
    · exact (div_le_iff₀ (hq_pos (t, x) htx)).mp hrgh
    · exact (div_le_iff₀ (hg_pos (t, x) htx)).mp hrhg
  · refine ⟨1, le_rfl, ?_⟩
    intro t ht x hx
    exact (hK_ne ⟨(t, x), ht, hx⟩).elim

/-- A single real constant controls both chart-density directions on every
nonzero chart of the finite canonical POU. -/
theorem volume_density_bdd
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J)
    (hgram : ∀ alpha (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) alpha p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ alpha ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ t ∈ J, ∀ x ∈ tsupport
          (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
          chartDensity (I := I) (g t) alpha x ≤
              C * chartDensity (I := I) q alpha x ∧
            chartDensity (I := I) q alpha x ≤
              C * chartDensity (I := I) (g t) alpha x := by
  classical
  have h_each : ∀ alpha : M, ∃ C : ℝ, 1 ≤ C ∧
      ∀ t ∈ J, ∀ x ∈ tsupport
        (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
        chartDensity (I := I) (g t) alpha x ≤
            C * chartDensity (I := I) q alpha x ∧
          chartDensity (I := I) q alpha x ≤
            C * chartDensity (I := I) (g t) alpha x := fun alpha =>
    density_ratio_bdd (I := I) (M := M) q g alpha hJ (hgram alpha)
  choose Cchart hCchart hCchart_bdd using h_each
  let Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  let C : ℝ := 1 + ∑ alpha ∈ Sfin, Cchart alpha
  have hC : 1 ≤ C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ alpha ∈ Sfin, Cchart alpha :=
      Finset.sum_nonneg fun alpha _ => (zero_le_one.trans (hCchart alpha))
    linarith
  refine ⟨C, hC, ?_⟩
  intro alpha halpha t ht x hx
  have hCalpha : Cchart alpha ≤ C := by
    have hsingle : Cchart alpha ≤ ∑ beta ∈ Sfin, Cchart beta :=
      Finset.single_le_sum
        (fun beta _ => zero_le_one.trans (hCchart beta)) halpha
    dsimp [C]
    linarith
  rcases hCchart_bdd alpha t ht x hx with ⟨hforward, hreverse⟩
  constructor
  · exact hforward.trans (mul_le_mul_of_nonneg_right hCalpha (Real.sqrt_nonneg _))
  · exact hreverse.trans (mul_le_mul_of_nonneg_right hCalpha (Real.sqrt_nonneg _))

/-- Comparison of one POU-weighted chart-local lower integral from a pointwise
chart-density bound on the POU `tsupport`. -/
lemma chart_lintegral_le
    (q h : SmoothRiemannianMetric I M) (alpha : M) (C : ℝ) (hC : 0 ≤ C)
    (hdensity : ∀ x ∈ tsupport
      (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
      chartDensity (I := I) h alpha x ≤ C * chartDensity (I := I) q alpha x)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
        ∂(chartLocalMeasure (I := I) h alpha) ≤
      ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) q alpha) := by
  let rho : M → ℝ := fun x => (chartAtlasPOU I M alpha : M → ℝ) x
  have hrho_meas : Measurable (fun x : M => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp ((chartAtlasPOU I M alpha).contMDiff.continuous.measurable
      )
  have hprod_meas : Measurable (fun x : M => ENNReal.ofReal (rho x) * F x) :=
    hrho_meas.mul hF
  rw [chartLocalMeasure_lintegral (I := I) h alpha hprod_meas,
    chartLocalMeasure_lintegral (I := I) q alpha hprod_meas]
  let target : Set E := (extChartAt I alpha).target
  let symm : E → M := fun y => (extChartAt I alpha).symm y
  calc
    ∫⁻ y in target,
        ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) *
          (ENNReal.ofReal (rho (symm y)) * F (symm y))
        ∂(modelHaar (E := E)) ≤
      ∫⁻ y in target, ENNReal.ofReal C *
        (ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) *
          (ENNReal.ofReal (rho (symm y)) * F (symm y)))
        ∂(modelHaar (E := E)) := by
          refine lintegral_mono fun y => ?_
          by_cases hrho : rho (symm y) = 0
          · simp [hrho]
          · have hsymm_tsupp : symm y ∈ tsupport rho :=
              subset_tsupport rho hrho
            have hd := hdensity (symm y) hsymm_tsupp
            have hd_en : ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) := by
              have := ENNReal.ofReal_le_ofReal hd
              rw [ENNReal.ofReal_mul hC] at this
              exact this
            have hmul := mul_le_mul_right'
              hd_en (ENNReal.ofReal (rho (symm y)) * F (symm y))
            simpa only [mul_assoc] using hmul
    _ = ENNReal.ofReal C *
        ∫⁻ y in target,
          ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) *
            (ENNReal.ofReal (rho (symm y)) * F (symm y))
          ∂(modelHaar (E := E)) := by
        rw [MeasureTheory.lintegral_const_mul'
          (μ := (modelHaar (E := E)).restrict target)
          (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]

private lemma volume_tsum_eq_sum
    (g : SmoothRiemannianMetric I M) (F : M → ℝ≥0∞) :
    ∑' alpha : M, ∫⁻ x,
        ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) g alpha) =
      ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
        ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) g alpha) := by
  classical
  rw [tsum_eq_sum]
  intro alpha halpha
  have hrho_zero : ∀ x : M, (chartAtlasPOU I M alpha : M → ℝ) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) halpha x
  simp only [hrho_zero, ENNReal.ofReal_zero, zero_mul, lintegral_zero]

private lemma volume_lintegral_sum
    (g : SmoothRiemannianMetric I M) {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
        ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) g alpha) := by
  rw [riemannianVolumeMeasure_def,
    riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF,
    volume_tsum_eq_sum (I := I) (M := M) g F]

/-- Uniform two-sided lower-integral comparison for a compact `C^0` metric
family.  The same real constant works for every time in `J`. -/
theorem volume_lintegral_le
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J)
    (hgram : ∀ alpha (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) alpha p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ J, ∀ (F : M → ℝ≥0∞), Measurable F →
      (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) ≤
          ENNReal.ofReal C *
            ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q) ∧
        (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) ≤
          ENNReal.ofReal C *
            ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t)) := by
  classical
  obtain ⟨C, hC, hdensity⟩ :=
    volume_density_bdd (I := I) (M := M) q g hJ hgram
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, hC, ?_⟩
  intro t ht F hF
  have hsum_g := volume_lintegral_sum (I := I) (M := M) (g t) hF
  have hsum_q := volume_lintegral_sum (I := I) (M := M) q hF
  constructor
  · calc
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t)) =
          ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) (g t) alpha) := hsum_g
      _ ≤ ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M),
          ENNReal.ofReal C * ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) q alpha) := by
            refine Finset.sum_le_sum (fun alpha halpha => ?_)
            exact chart_lintegral_le (I := I) (M := M) q (g t) alpha C hC0
              (fun x hx => (hdensity alpha halpha t ht x hx).1) hF
      _ = ENNReal.ofReal C *
          ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) q alpha) := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal C *
          ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
            rw [hsum_q]
  · calc
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q) =
          ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) q alpha) := hsum_q
      _ ≤ ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M),
          ENNReal.ofReal C * ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) (g t) alpha) := by
            refine Finset.sum_le_sum (fun alpha halpha => ?_)
            exact chart_lintegral_le (I := I) (M := M) (g t) q alpha C hC0
              (fun x hx => (hdensity alpha halpha t ht x hx).2) hF
      _ = ENNReal.ofReal C *
          ∑ alpha ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
              ∂(chartLocalMeasure (I := I) (g t) alpha) := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal C *
          ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t)) := by
            rw [hsum_g]

/-- On a compact time set, joint `C^0` chart-Gram regularity makes all moving
Riemannian volume measures uniformly equivalent to the reference measure. -/
theorem volume_uniform_equiv
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J)
    (hgram : ∀ alpha (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) alpha p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ t ∈ J,
      riemannianVolumeMeasure (I := I) (M := M) (g t) ≤
          C • riemannianVolumeMeasure (I := I) (M := M) q ∧
        riemannianVolumeMeasure (I := I) (M := M) q ≤
          C • riemannianVolumeMeasure (I := I) (M := M) (g t) := by
  classical
  obtain ⟨C, hC, hlin⟩ := volume_lintegral_le (I := I) (M := M) q g hJ hgram
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨ENNReal.ofReal C, ?_, ENNReal.ofReal_ne_top, ?_⟩
  · rw [ENNReal.ofReal_ne_zero_iff]
    exact hCpos
  intro t ht
  constructor
  · rw [Measure.le_iff]
    intro s hs
    have h := (hlin t ht (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)).1
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]
  · rw [Measure.le_iff]
    intro s hs
    have h := (hlin t ht (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)).2
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]

end Measure
end Integral
end DifferentialGeometry

end
