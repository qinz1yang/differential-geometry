import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingOscillation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingLogCenterDrift
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (C H t : ℝ) : ℝ :=
  2 * evolvingCutoffGradientError
      (I := I) (M := M) g cutoff (fun _ _ => 1) t /
      evolvingCutoffMass (I := I) (M := M) g cutoff t +
    max 1 C * H ^ 2

def evolvingShiftedLogCenter
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (C H base t : ℝ) : ℝ :=
  evolvingLocalizedAverage
      (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t +
    ∫ s in base..t,
      evolvingLogCenterDrift (I := I) (M := M) g cutoff C H s

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLogCenterDrift_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (C H t : ℝ) :
    0 ≤ evolvingLogCenterDrift (I := I) (M := M) g cutoff C H t := by
  exact add_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num)
        (evolvingCutoffGradientError_nonneg
          (I := I) (M := M) g cutoff (fun _ _ => 1) t))
      (evolvingCutoffMass_nonneg (I := I) (M := M) g cutoff t))
    (mul_nonneg (zero_le_one.trans (le_max_left 1 C)) (sq_nonneg H))

omit [I.Boundaryless] in
theorem evolvingLogCenterDrift_continuous
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (C H : ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0) :
    Continuous (evolvingLogCenterDrift
      (I := I) (M := M) g cutoff C H) := by
  have herror := evolvingCutoffGradientError_continuous
    (I := I) (M := M) g cutoff (fun _ _ => 1) hg hgram hcutoff contMDiff_const
  have hmass := evolvingCutoffMass_continuous
    (I := I) (M := M) g cutoff hg hcutoff.continuous
  have hnum : Continuous (fun t =>
      2 * evolvingCutoffGradientError
        (I := I) (M := M) g cutoff (fun _ _ => 1) t) :=
    continuous_const.mul herror
  have hratio : Continuous (fun t =>
      2 * evolvingCutoffGradientError
          (I := I) (M := M) g cutoff (fun _ _ => 1) t /
        evolvingCutoffMass (I := I) (M := M) g cutoff t) :=
    hnum.div hmass fun t =>
      (evolvingCutoffMass_pos
        (I := I) (M := M) g cutoff t hcutoff.continuous hne).ne'
  simpa only [evolvingLogCenterDrift] using hratio.add continuous_const

omit [I.Boundaryless] in
theorem exists_nonnegative_evolving_log_center_drift_upper_bound
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (C H : ℝ) {a b t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0) :
    ∃ rate : ℝ, 0 ≤ rate ∧ ∀ t ∈ Icc a b,
      evolvingLogCenterDrift (I := I) (M := M) g cutoff C H t ≤ rate := by
  let drift := evolvingLogCenterDrift (I := I) (M := M) g cutoff C H
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g cutoff C H hg hgram hcutoff hne
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) hdrift.continuousOn
  refine ⟨drift t, ?_, ?_⟩
  · exact evolvingLogCenterDrift_nonneg
      (I := I) (M := M) g cutoff C H t
  · intro s hs
    exact hmax hs

omit [I.Boundaryless] in
theorem hasDerivAt_evolvingShiftedLogCenter
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (C H base t : ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0) :
    HasDerivAt
      (evolvingShiftedLogCenter
        (I := I) (M := M) g cutoff u C H base)
      (deriv (evolvingLocalizedAverage
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))) t +
        evolvingLogCenterDrift (I := I) (M := M) g cutoff C H t) t := by
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let hlog := contMDiff_log_of_pos hu hpos
  have hmass := (evolvingCutoffMass_pos
    (I := I) (M := M) g cutoff t hcutoff.continuous hne).ne'
  have haverage := hasDerivAt_evolvingLocalizedAverage
    (I := I) (M := M) g cutoff logu t (hg.at_any t) hcutoff hlog hmass
  have haverage' : HasDerivAt
      (evolvingLocalizedAverage (I := I) (M := M) g cutoff logu)
      (deriv (evolvingLocalizedAverage (I := I) (M := M) g cutoff logu) t) t :=
    haverage.differentiableAt.hasDerivAt
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g cutoff C H hg hgram hcutoff hne
  have hprimitive : HasDerivAt
      (fun q => ∫ s in base..q,
        evolvingLogCenterDrift (I := I) (M := M) g cutoff C H s)
      (evolvingLogCenterDrift (I := I) (M := M) g cutoff C H t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hdrift.intervalIntegrable base t)
      hdrift.aestronglyMeasurable.stronglyMeasurableAtFilter hdrift.continuousAt
  simpa only [evolvingShiftedLogCenter, logu] using haverage'.add hprimitive

omit [I.Boundaryless] in
theorem contDiff_evolvingShiftedLogCenter
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (C H base : ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0) :
    ContDiff ℝ 1 (evolvingShiftedLogCenter
      (I := I) (M := M) g cutoff u C H base) := by
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let average := evolvingLocalizedAverage
    (I := I) (M := M) g cutoff logu
  let mass := evolvingCutoffMass (I := I) (M := M) g cutoff
  let trace : ℝ → M → ℝ := fun t x =>
    (1 / 2) * traceTimeDerivMetric (I := I) g t x
  let averageDerivativeIntegrand : ℝ → M → ℝ := fun t x =>
    deriv (fun s => logu s x) t + trace t x * (logu t x - average t)
  let averageDerivative : ℝ → ℝ := fun t =>
    evolvingLocalizedIntegral
      (I := I) (M := M) g cutoff averageDerivativeIntegrand t / mass t
  let centerDerivative : ℝ → ℝ := fun t =>
    averageDerivative t +
      evolvingLogCenterDrift (I := I) (M := M) g cutoff C H t
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g cutoff u C H base
  let hlog := contMDiff_log_of_pos hu hpos
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => logu p.1 p.2, hlog⟩
  have htime : Continuous (fun p : ℝ × M =>
      deriv (fun s => logu s p.2) p.1) := by
    simpa only [F, logu] using
      (DifferentialGeometry.contMDiff_partial_deriv_fst I F).continuous
  have htrace : Continuous (fun p : ℝ × M => trace p.1 p.2) := by
    exact continuous_const.mul
      (traceTimeDerivMetric_joint_continuous (I := I) (M := M) hg)
  have haverage : Continuous average := by
    exact evolvingLocalizedAverage_continuous
      (I := I) (M := M) g cutoff logu hg hcutoff.continuous hlog.continuous hne
  have hintegrand : Continuous (fun p : ℝ × M =>
      averageDerivativeIntegrand p.1 p.2) := by
    exact htime.add (htrace.mul
      (hlog.continuous.sub (haverage.comp continuous_fst)))
  have hnumerator : Continuous (fun t =>
      evolvingLocalizedIntegral
        (I := I) (M := M) g cutoff averageDerivativeIntegrand t) :=
    evolvingLocalizedIntegral_continuous
      (I := I) (M := M) g cutoff averageDerivativeIntegrand
        hg hcutoff.continuous hintegrand
  have hmass : Continuous mass :=
    evolvingCutoffMass_continuous
      (I := I) (M := M) g cutoff hg hcutoff.continuous
  have haverageDerivative : Continuous averageDerivative :=
    hnumerator.div hmass fun t =>
      (evolvingCutoffMass_pos
        (I := I) (M := M) g cutoff t hcutoff.continuous hne).ne'
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g cutoff C H hg hgram hcutoff hne
  have hcenterDerivative : Continuous centerDerivative :=
    haverageDerivative.add hdrift
  have hshifted : ∀ t, HasDerivAt shifted (centerDerivative t) t := by
    intro t
    have hmass_t := (evolvingCutoffMass_pos
      (I := I) (M := M) g cutoff t hcutoff.continuous hne).ne'
    have haverage_eq := deriv_evolvingLocalizedAverage_eq_integral_centered
      (I := I) (M := M) g cutoff logu t (hg.at_any t) hcutoff hlog hmass_t
    have hraw := hasDerivAt_evolvingShiftedLogCenter
      (I := I) (M := M) g cutoff u hu hpos C H base t hg hgram hcutoff hne
    convert hraw using 1
    rw [haverage_eq]
    rfl
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (hshifted t).differentiableAt
  · rw [show deriv shifted = centerDerivative from funext fun t => (hshifted t).deriv]
    exact hcenterDerivative

theorem evolving_log_spatial_energy_differential_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t ≤
      (∫ x, cutoff x ^ 2 * deriv (fun s => Real.log (u s x)) t
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) +
        2 * evolvingCutoffGradientError
          (I := I) (M := M) g cutoff (fun _ _ => 1) t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let hlog := contMDiff_log_of_pos hu hpos
  have hfixed := log_energy_differential_of_supersolution
    (I := I) (M := M) (g t) cutoff_t u hu hpos t hpde
  have hderiv := hasDerivAt_localizedIntegral
    (I := I) (M := M) cutoff_t (fun s x => Real.log (u s x)) hlog t
  rw [hderiv.deriv] at hfixed
  simpa only [evolvingLocalizedDirichletEnergy, localizedDirichletEnergy,
    evolvingCutoffGradientError, cutoffDirichletEnergy,
    riemannianMeasureFamily_def, smoothScalarSlice_toFun, cutoff_t,
    one_pow, one_mul] using hfixed

theorem evolving_log_average_deriv_lower_bound_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t C H : ℝ) (J : Set ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0)
    (hP : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g cutoff cutoff C J)
    (ht : t ∈ J)
    (htrace : ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ((1 / 4 : ℝ) * evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t -
        2 * evolvingCutoffGradientError
          (I := I) (M := M) g cutoff (fun _ _ => 1) t) /
        evolvingCutoffMass (I := I) (M := M) g cutoff t -
      max 1 C * H ^ 2 ≤
        deriv (evolvingLocalizedAverage
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))) t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let mass := evolvingCutoffMass (I := I) (M := M) g cutoff t
  let average := evolvingLocalizedAverage
    (I := I) (M := M) g cutoff logu t
  let dirichlet := evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g cutoff logu t
  let cutoffError := evolvingCutoffGradientError
    (I := I) (M := M) g cutoff (fun _ _ => 1) t
  let K := max 1 C
  let trace : M → ℝ := fun x =>
    (1 / 2) * traceTimeDerivMetric (I := I) g t x
  let timeIntegrand : M → ℝ := fun x =>
    cutoff x ^ 2 * deriv (fun s => logu s x) t
  let covarianceIntegrand : M → ℝ := fun x =>
    cutoff x ^ 2 * trace x * (logu t x - average)
  let hlog := contMDiff_log_of_pos hu hpos
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hmass : 0 < mass := by
    exact evolvingCutoffMass_pos
      (I := I) (M := M) g cutoff t hcutoff.continuous hne
  have hspatial :
      (1 / 2 : ℝ) * dirichlet ≤ ∫ x, timeIntegrand x ∂μ + 2 * cutoffError := by
    simpa only [dirichlet, timeIntegrand, cutoffError, logu, μ] using
      evolving_log_spatial_energy_differential_of_supersolution
        (I := I) (M := M) g cutoff u hu hpos t hcutoff hpde
  have hcovariance :
      -(1 / 4 : ℝ) * dirichlet - K * H ^ 2 * mass ≤
        ∫ x, covarianceIntegrand x ∂μ := by
    simpa only [dirichlet, K, mass, covarianceIntegrand, trace, logu, average, μ]
      using evolving_volume_covariance_lower_bound_of_poincare
        (I := I) (M := M) g cutoff cutoff logu t C H J hg hcutoff
          (HasCompactSupport.of_compactSpace _) hlog hP ht htrace
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => logu p.1 p.2, hlog⟩
  have htime : Continuous (fun x : M => deriv (fun s => logu s x) t) := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace_cont : Continuous trace :=
    continuous_const.mul
      (traceTimeDerivMetric_continuous (I := I) (M := M) hg)
  have hlog_t : Continuous (logu t) :=
    (hlog.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have htime_int : Integrable timeIntegrand μ := by
    exact ((hcutoff.continuous.pow 2).mul htime).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcovariance_int : Integrable covarianceIntegrand μ := by
    exact (((hcutoff.continuous.pow 2).mul htrace_cont).mul
      (hlog_t.sub continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hsum :
      (1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass ≤
        ∫ x, cutoff x ^ 2 *
          (deriv (fun s => logu s x) t +
            trace x * (logu t x - average)) ∂μ := by
    calc
      (1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass =
          ((1 / 2 : ℝ) * dirichlet - 2 * cutoffError) +
            (-(1 / 4 : ℝ) * dirichlet - K * H ^ 2 * mass) := by ring
      _ ≤ (∫ x, timeIntegrand x ∂μ) +
          ∫ x, covarianceIntegrand x ∂μ := by
            exact add_le_add (by linarith) hcovariance
      _ = ∫ x, cutoff x ^ 2 *
          (deriv (fun s => logu s x) t +
            trace x * (logu t x - average)) ∂μ := by
            rw [← integral_add htime_int hcovariance_int]
            exact integral_congr_ae (ae_of_all μ fun x => by
              dsimp only [timeIntegrand, covarianceIntegrand]
              ring)
  have haverage := deriv_evolvingLocalizedAverage_eq_integral_centered
    (I := I) (M := M) g cutoff logu t hg hcutoff hlog hmass.ne'
  have hnormalized :
      ((1 / 4 : ℝ) * dirichlet - 2 * cutoffError) / mass - K * H ^ 2 =
        ((1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass) /
          mass := by
    field_simp [hmass.ne']
  rw [hnormalized]
  rw [haverage]
  apply (div_le_div_iff_of_pos_right hmass).2
  simpa only [logu, mass, average, trace, μ] using hsum

theorem quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t C H base : ℝ) (J : Set ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0)
    (hP : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g cutoff cutoff C J)
    (ht : t ∈ J)
    (htrace : ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ((1 / 4 : ℝ) * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t) /
      evolvingCutoffMass (I := I) (M := M) g cutoff t ≤
        deriv (evolvingShiftedLogCenter
          (I := I) (M := M) g cutoff u C H base) t := by
  have hlower := evolving_log_average_deriv_lower_bound_of_supersolution
    (I := I) (M := M) g cutoff u hu hpos t C H J (hg.at_any t)
      hcutoff hne hP ht htrace hpde
  have hshifted := hasDerivAt_evolvingShiftedLogCenter
    (I := I) (M := M) g cutoff u hu hpos C H base t hg hgram hcutoff hne
  rw [hshifted.deriv]
  change _ ≤ deriv (evolvingLocalizedAverage
      (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))) t +
    (2 * evolvingCutoffGradientError
        (I := I) (M := M) g cutoff (fun _ _ => 1) t /
        evolvingCutoffMass (I := I) (M := M) g cutoff t +
      max 1 C * H ^ 2)
  ring_nf at hlower ⊢
  linarith

theorem evolvingShiftedLogCenter_monotoneOn_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (C H base : ℝ) {a b t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0)
    (hP : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g cutoff cutoff C (Icc a b))
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    MonotoneOn
      (evolvingShiftedLogCenter
        (I := I) (M := M) g cutoff u C H base) (Icc a b) := by
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g cutoff u C H base
  have hshifted : ∀ t, HasDerivAt shifted (deriv shifted t) t := by
    intro t
    exact (hasDerivAt_evolvingShiftedLogCenter
      (I := I) (M := M) g cutoff u hu hpos C H base t hg hgram hcutoff hne)
        |>.differentiableAt.hasDerivAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro t _
    exact (hshifted t).continuousAt.continuousWithinAt
  · intro t _
    exact (hshifted t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    have henergy :=
      quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
        (I := I) (M := M) g cutoff u hu hpos t C H base (Icc a b)
          hg hgram hcutoff hne hP ht' (htrace t ht') (hpde t ht')
    have hnonneg : 0 ≤
        ((1 / 4 : ℝ) * evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t) /
          evolvingCutoffMass (I := I) (M := M) g cutoff t :=
      div_nonneg
        (mul_nonneg (by norm_num)
          (evolvingLocalizedDirichletEnergy_nonneg
            (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t))
        (evolvingCutoffMass_nonneg (I := I) (M := M) g cutoff t)
    exact hnonneg.trans (by simpa only [shifted] using henergy)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
