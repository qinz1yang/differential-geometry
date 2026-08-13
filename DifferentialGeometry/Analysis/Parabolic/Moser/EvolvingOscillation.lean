import DifferentialGeometry.Analysis.Parabolic.Energy.EvolvingCaccioppoli
import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedIntegral (I := I) (M := M) g cutoff (fun _ _ => 1) t

def evolvingLocalizedAverage
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedIntegral (I := I) (M := M) g cutoff u t /
    evolvingCutoffMass (I := I) (M := M) g cutoff t

def evolvingLocalizedL2Deviation
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (center t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 * (u t x - center) ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedL2Oscillation
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedL2Deviation (I := I) (M := M) g cutoff u
    (evolvingLocalizedAverage (I := I) (M := M) g cutoff u t) t

def HasEvolvingLocalizedPoincare
    (g : ℝ → SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : M → ℝ) (C : ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ u : SmoothScalar (g t),
    evolvingLocalizedL2Oscillation (I := I) (M := M) g averagingCutoff
        (fun _ x => u.toFun x) t ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g energyCutoff (fun _ x => u.toFun x) t

def HasEvolvingLocalizedPoincareAtAverage
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ) (C : ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ u : SmoothScalar (g t),
    evolvingLocalizedL2Deviation
        (I := I) (M := M) g deviationCutoff (fun _ x => u.toFun x)
        (evolvingLocalizedAverage
          (I := I) (M := M) g averagingCutoff (fun _ x => u.toFun x) t) t ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff (fun _ x => u.toFun x) t

omit [CompactSpace M] in
theorem hasEvolvingLocalizedPoincare_iff
    (g : ℝ → SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : M → ℝ) (C : ℝ) (J : Set ℝ)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (henergyCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ energyCutoff) :
    HasEvolvingLocalizedPoincare
        (I := I) (M := M) g averagingCutoff energyCutoff C J ↔
      ∀ t ∈ J,
        HasLocalizedPoincare (I := I) (M := M) (g t)
          ⟨averagingCutoff, haveragingCutoff⟩
          ⟨energyCutoff, henergyCutoff⟩ C := by
  constructor
  · intro h t ht u
    simpa only [HasLocalizedPoincare, localizedL2Oscillation,
      localizedL2Deviation, localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincare,
      evolvingLocalizedL2Oscillation, evolvingLocalizedL2Deviation,
      evolvingLocalizedAverage, evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u
  · intro h t ht u
    simpa only [HasLocalizedPoincare, localizedL2Oscillation,
      localizedL2Deviation, localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincare,
      evolvingLocalizedL2Oscillation, evolvingLocalizedL2Deviation,
      evolvingLocalizedAverage, evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u

omit [CompactSpace M] in
theorem hasEvolvingLocalizedPoincareAtAverage_iff
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ) (C : ℝ) (J : Set ℝ)
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff) :
    HasEvolvingLocalizedPoincareAtAverage
        (I := I) (M := M) g deviationCutoff averagingCutoff C J ↔
      ∀ t ∈ J,
        HasLocalizedPoincareAtAverage (I := I) (M := M) (g t)
          ⟨deviationCutoff, hdeviationCutoff⟩
          ⟨averagingCutoff, haveragingCutoff⟩ C := by
  constructor
  · intro h t ht u
    simpa only [HasLocalizedPoincareAtAverage, localizedL2Deviation,
      localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincareAtAverage,
      evolvingLocalizedL2Deviation, evolvingLocalizedAverage,
      evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u
  · intro h t ht u
    simpa only [HasLocalizedPoincareAtAverage, localizedL2Deviation,
      localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincareAtAverage,
      evolvingLocalizedL2Deviation, evolvingLocalizedAverage,
      evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u

omit [CompactSpace M] in
theorem evolvingCutoffMass_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ) :
    0 ≤ evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  simp only [evolvingCutoffMass, evolvingLocalizedIntegral, mul_one]
  exact integral_nonneg fun x => sq_nonneg (cutoff x)

theorem evolvingCutoffMass_pos
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ)
    (hcutoff : Continuous cutoff) (hne : ∃ x, cutoff x ≠ 0) :
    0 < evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  letI : μ.IsOpenPosMeasure := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g t)
  obtain ⟨x, hx⟩ := hne
  have hsq : cutoff x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  simp only [evolvingCutoffMass, evolvingLocalizedIntegral, mul_one]
  exact integral_pos_of_integrable_nonneg_nonzero
    (hcutoff.pow 2)
    ((hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun y => sq_nonneg (cutoff y)) hsq

theorem evolvingCutoffMass_continuous
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : Continuous cutoff) :
    Continuous (evolvingCutoffMass (I := I) (M := M) g cutoff) := by
  have h := evolvingLocalizedIntegral_continuous
    (I := I) (M := M) g cutoff (fun _ _ => 1) hg hcutoff continuous_const
  simpa only [evolvingCutoffMass] using h

theorem evolvingLocalizedAverage_continuous
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2))
    (hne : ∃ x, cutoff x ≠ 0) :
    Continuous (evolvingLocalizedAverage (I := I) (M := M) g cutoff u) := by
  have hnum := evolvingLocalizedIntegral_continuous
    (I := I) (M := M) g cutoff u hg hcutoff hu
  have hden := evolvingCutoffMass_continuous
    (I := I) (M := M) g cutoff hg hcutoff
  exact hnum.div hden fun t =>
    (evolvingCutoffMass_pos
      (I := I) (M := M) g cutoff t hcutoff hne).ne'

omit [CompactSpace M] in
theorem evolvingLocalizedL2Oscillation_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedL2Oscillation
      (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem hasDerivAt_evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff) :
    HasDerivAt
      (evolvingCutoffMass (I := I) (M := M) g cutoff)
      (∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) t := by
  have h := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff (fun _ _ => 1) t hg hcutoff contMDiff_const
  simpa only [evolvingCutoffMass, evolvingLocalizedIntegral, deriv_const,
    zero_add, mul_one] using h

theorem hasDerivAt_evolvingLocalizedAverage
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hmass : evolvingCutoffMass (I := I) (M := M) g cutoff t ≠ 0) :
    HasDerivAt
      (evolvingLocalizedAverage (I := I) (M := M) g cutoff u)
      (((∫ x, cutoff x ^ 2 *
            (deriv (fun s => u s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t)) *
          evolvingCutoffMass (I := I) (M := M) g cutoff t -
        evolvingLocalizedIntegral (I := I) (M := M) g cutoff u t *
          (∫ x, cutoff x ^ 2 *
              ((1 / 2) * traceTimeDerivMetric (I := I) g t x)
            ∂(riemannianMeasureFamily (I := I) (M := M) g t))) /
        evolvingCutoffMass (I := I) (M := M) g cutoff t ^ 2) t := by
  have hnum := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff u t hg hcutoff hu
  have hden := hasDerivAt_evolvingCutoffMass
    (I := I) (M := M) g cutoff t hg hcutoff
  simpa only [evolvingLocalizedAverage] using hnum.div hden hmass

theorem deriv_evolvingLocalizedAverage_eq_integral_centered
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hmass : evolvingCutoffMass (I := I) (M := M) g cutoff t ≠ 0) :
    deriv (evolvingLocalizedAverage (I := I) (M := M) g cutoff u) t =
      (∫ x, cutoff x ^ 2 *
          (deriv (fun s => u s x) t +
            (1 / 2) * traceTimeDerivMetric (I := I) g t x *
              (u t x - evolvingLocalizedAverage
                (I := I) (M := M) g cutoff u t))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) /
        evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  let mass := evolvingCutoffMass (I := I) (M := M) g cutoff t
  let average := evolvingLocalizedAverage (I := I) (M := M) g cutoff u t
  let trace : M → ℝ := fun x =>
    (1 / 2) * traceTimeDerivMetric (I := I) g t x
  let timeDeriv : M → ℝ := fun x => deriv (fun s => u s x) t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => u p.1 p.2, hu⟩
  have hu_t : Continuous (u t) :=
    (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have htimeDeriv : Continuous timeDeriv := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace : Continuous trace :=
    continuous_const.mul
      (traceTimeDerivMetric_continuous (I := I) (M := M) hg)
  have hweight : Continuous (fun x : M => cutoff x ^ 2) :=
    hcutoff.continuous.pow 2
  have htime_int : Integrable
      (fun x : M => cutoff x ^ 2 * timeDeriv x) μ :=
    (hweight.mul htimeDeriv).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have htrace_u_int : Integrable
      (fun x : M => cutoff x ^ 2 * trace x * u t x) μ :=
    ((hweight.mul htrace).mul hu_t).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have htrace_int : Integrable
      (fun x : M => cutoff x ^ 2 * trace x) μ :=
    (hweight.mul htrace).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcentered :
      (∫ x, cutoff x ^ 2 *
          (timeDeriv x + trace x * (u t x - average)) ∂μ) =
        (∫ x, cutoff x ^ 2 *
          (timeDeriv x + trace x * u t x) ∂μ) -
          average * ∫ x, cutoff x ^ 2 * trace x ∂μ := by
    have hsum_int : Integrable
        (fun x : M => cutoff x ^ 2 *
          (timeDeriv x + trace x * u t x)) μ := by
      simpa only [mul_add, mul_assoc] using htime_int.add htrace_u_int
    calc
      _ = ∫ x,
          cutoff x ^ 2 * (timeDeriv x + trace x * u t x) -
            average * (cutoff x ^ 2 * trace x) ∂μ := by
              refine integral_congr_ae (ae_of_all μ fun x => ?_)
              ring
      _ = (∫ x, cutoff x ^ 2 *
            (timeDeriv x + trace x * u t x) ∂μ) -
          ∫ x, average * (cutoff x ^ 2 * trace x) ∂μ :=
            integral_sub hsum_int (htrace_int.const_mul average)
      _ = _ := by rw [integral_const_mul]
  have hnumerator_eq :
      (∫ x, cutoff x ^ 2 *
          (deriv (fun s => u s x) t +
            (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) =
        ∫ x, cutoff x ^ 2 *
          (timeDeriv x + trace x * u t x) ∂μ := by
    refine integral_congr_ae (ae_of_all μ fun x => ?_)
    dsimp only [timeDeriv, trace]
  have hmassDeriv_eq :
      (∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) =
        ∫ x, cutoff x ^ 2 * trace x ∂μ := by
    refine integral_congr_ae (ae_of_all μ fun x => ?_)
    rfl
  rw [(hasDerivAt_evolvingLocalizedAverage
    (I := I) (M := M) g cutoff u t hg hcutoff hu hmass).deriv]
  rw [hnumerator_eq, hmassDeriv_eq]
  change _ = (∫ x, cutoff x ^ 2 *
      (timeDeriv x + trace x * (u t x - average)) ∂μ) / mass
  rw [hcentered]
  dsimp only [average, evolvingLocalizedAverage, mass]
  field_simp [hmass]

private theorem covariance_young_lower {d h K H : ℝ}
    (hK : 0 < K) (hh : |h| ≤ H) :
    -(1 / (4 * K)) * d ^ 2 - K * H ^ 2 ≤ h * d := by
  have hh_bounds := abs_le.mp hh
  have hh_sq : h ^ 2 ≤ H ^ 2 := by
    nlinarith
  have hsquare : 0 ≤ (d + 2 * K * h) ^ 2 := sq_nonneg _
  have hraw : -d ^ 2 - 4 * K ^ 2 * H ^ 2 ≤ 4 * K * (h * d) := by
    nlinarith
  have hden : 0 < 4 * K := mul_pos (by norm_num) hK
  calc
    -(1 / (4 * K)) * d ^ 2 - K * H ^ 2 =
        (-d ^ 2 - 4 * K ^ 2 * H ^ 2) / (4 * K) := by
          field_simp [hK.ne']
    _ ≤ (4 * K * (h * d)) / (4 * K) :=
      (div_le_div_iff_of_pos_right hden).mpr hraw
    _ = h * d := by field_simp [hK.ne']

private theorem quarter_dirichlet_le_covariance_cost
    {oscillation dirichlet K : ℝ} (hK : 0 < K)
    (hbound : oscillation ≤ K * dirichlet) :
    -(1 / 4) * dirichlet ≤ -(1 / (4 * K)) * oscillation := by
  have hden : 0 < 4 * K := mul_pos (by norm_num) hK
  have hfrac : oscillation / (4 * K) ≤ dirichlet / 4 := by
    apply (div_le_iff₀ hden).2
    calc
      oscillation ≤ K * dirichlet := hbound
      _ = dirichlet / 4 * (4 * K) := by ring
  have hneg := neg_le_neg hfrac
  convert hneg using 1 <;> field_simp [hK.ne']

omit [CompactSpace M] in
theorem evolving_volume_covariance_lower_bound
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t K H : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hcutoff_compact : HasCompactSupport cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hK : 0 < K)
    (htrace : ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H) :
    -(1 / (4 * K)) *
          evolvingLocalizedL2Oscillation (I := I) (M := M) g cutoff u t -
        K * H ^ 2 * evolvingCutoffMass (I := I) (M := M) g cutoff t ≤
      ∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x) *
          (u t x - evolvingLocalizedAverage
            (I := I) (M := M) g cutoff u t)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  let center := evolvingLocalizedAverage (I := I) (M := M) g cutoff u t
  let h : M → ℝ := fun x =>
    (1 / 2) * traceTimeDerivMetric (I := I) g t x
  let dev : M → ℝ := fun x => u t x - center
  letI : IsFiniteMeasureOnCompacts μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasureOnCompacts
      (I := I) (M := M) (g t)
  have hu_t : Continuous (u t) :=
    (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have hh : Continuous h := by
    exact continuous_const.mul
      (traceTimeDerivMetric_continuous (I := I) (M := M) hg)
  have hdev : Continuous dev := hu_t.sub continuous_const
  have hweight_support : HasCompactSupport (fun x : M => cutoff x ^ 2) := by
    simpa only [pow_two] using
      (hcutoff_compact.mul_left : HasCompactSupport (cutoff * cutoff))
  have hweight : Integrable (fun x : M => cutoff x ^ 2) μ :=
    (hcutoff.continuous.pow 2).integrable_of_hasCompactSupport
      hweight_support
  have hdeviation : Integrable
      (fun x : M => cutoff x ^ 2 * dev x ^ 2) μ :=
    ((hcutoff.continuous.pow 2).mul (hdev.pow 2))
      |>.integrable_of_hasCompactSupport hweight_support.mul_right
  have hinside : Continuous
      (fun x : M => -(1 / (4 * K)) * dev x ^ 2 - K * H ^ 2) :=
    (continuous_const.mul (hdev.pow 2)).sub continuous_const
  have hleft : Integrable
      (fun x : M => cutoff x ^ 2 *
        (-(1 / (4 * K)) * dev x ^ 2 - K * H ^ 2)) μ :=
    ((hcutoff.continuous.pow 2).mul hinside)
      |>.integrable_of_hasCompactSupport hweight_support.mul_right
  have hright : Integrable
      (fun x : M => cutoff x ^ 2 * h x * dev x) μ :=
    (((hcutoff.continuous.pow 2).mul hh).mul hdev)
      |>.integrable_of_hasCompactSupport hweight_support.mul_right.mul_right
  have hpointwise : ∀ x : M,
      cutoff x ^ 2 * (-(1 / (4 * K)) * dev x ^ 2 - K * H ^ 2) ≤
        cutoff x ^ 2 * h x * dev x := by
    intro x
    have hyoung := covariance_young_lower (d := dev x) (h := h x) hK (htrace x)
    have hmul := mul_le_mul_of_nonneg_left hyoung (sq_nonneg (cutoff x))
    convert hmul using 1
    all_goals ring
  have hintegral := integral_mono hleft hright hpointwise
  have hleft_eq :
      (∫ x, cutoff x ^ 2 *
          (-(1 / (4 * K)) * dev x ^ 2 - K * H ^ 2) ∂μ) =
        -(1 / (4 * K)) * (∫ x, cutoff x ^ 2 * dev x ^ 2 ∂μ) -
          K * H ^ 2 * ∫ x, cutoff x ^ 2 ∂μ := by
    calc
      _ = ∫ x,
          (-(1 / (4 * K))) * (cutoff x ^ 2 * dev x ^ 2) +
            (-(K * H ^ 2)) * cutoff x ^ 2 ∂μ := by
              refine integral_congr_ae (ae_of_all μ fun x => ?_)
              ring
      _ = _ := by
        rw [integral_add (hdeviation.const_mul (-(1 / (4 * K))))
          (hweight.const_mul (-(K * H ^ 2))),
          integral_const_mul, integral_const_mul]
        ring
  rw [hleft_eq] at hintegral
  simpa only [evolvingLocalizedL2Oscillation, evolvingLocalizedL2Deviation,
    evolvingCutoffMass, evolvingLocalizedIntegral, center, dev, h, μ, mul_one]
    using hintegral

omit [CompactSpace M] in
theorem evolving_volume_covariance_lower_bound_of_poincare
    (g : ℝ → SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t C H : ℝ) (J : Set ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (haveragingCutoff_compact : HasCompactSupport averagingCutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hP : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff energyCutoff C J)
    (ht : t ∈ J)
    (htrace : ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H) :
    -(1 / 4) * evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g energyCutoff u t -
        max 1 C * H ^ 2 *
          evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤
      ∫ x, averagingCutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x) *
          (u t x - evolvingLocalizedAverage
            (I := I) (M := M) g averagingCutoff u t)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let K := max 1 C
  let oscillation := evolvingLocalizedL2Oscillation
    (I := I) (M := M) g averagingCutoff u t
  let dirichlet := evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g energyCutoff u t
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hdirichlet : 0 ≤ dirichlet :=
    evolvingLocalizedDirichletEnergy_nonneg
      (I := I) (M := M) g energyCutoff u t
  have hoscillation : oscillation ≤ C * dirichlet := by
    simpa only [oscillation, dirichlet, smoothScalarSlice_toFun] using
      hP t ht (smoothScalarSlice (I := I) (g t) u hu t)
  have hoscillationK : oscillation ≤ K * dirichlet :=
    hoscillation.trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) hdirichlet)
  have hquarter := quarter_dirichlet_le_covariance_cost hK hoscillationK
  have hbase := evolving_volume_covariance_lower_bound
    (I := I) (M := M) g averagingCutoff u t K H hg
      haveragingCutoff haveragingCutoff_compact hu hK htrace
  change -(1 / 4) * dirichlet -
      K * H ^ 2 * evolvingCutoffMass
        (I := I) (M := M) g averagingCutoff t ≤ _
  exact (sub_le_sub_right hquarter _).trans (by
    simpa only [oscillation, K] using hbase)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
