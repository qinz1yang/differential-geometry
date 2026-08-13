import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLogEnergy
import DifferentialGeometry.Analysis.Parabolic.Moser.LogTail

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

private theorem mul_dirichlet_le_mul_mass_bound_normalized
    {C D m W : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 0 < m) (hmW : m ≤ W) :
    C * D ≤ (C * W) * (D / m) := by
  have hD_eq : D = m * (D / m) := by
    field_simp [hm.ne']
  have hnormalized : 0 ≤ D / m := div_nonneg hD hm.le
  have hscaled := mul_le_mul_of_nonneg_right hmW hnormalized
  calc
    C * D = C * (m * (D / m)) := congrArg (fun x : ℝ => C * x) hD_eq
    _ ≤ C * (W * (D / m)) := mul_le_mul_of_nonneg_left hscaled hC
    _ = (C * W) * (D / m) := by ring

private theorem recentered_tail_le
    {D Z K r value : ℝ}
    (hZ : 0 ≤ Z) (hK : 0 ≤ K) (hr : 0 < r)
    (hsmall : value ≤ Z)
    (hlarge : D < r → value ≤ K / (r - D)) :
    value ≤ max (2 * D * Z) (2 * K) / r := by
  by_cases hcase : r ≤ 2 * D
  · calc
      value ≤ Z := hsmall
      _ ≤ (2 * D * Z) / r := by
        apply (le_div_iff₀ hr).2
        nlinarith
      _ ≤ max (2 * D * Z) (2 * K) / r := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) hr.le
  · have h2D : 2 * D < r := lt_of_not_ge hcase
    have hDr : D < r := by linarith
    have hdenom : 0 < r - D := sub_pos.mpr hDr
    calc
      value ≤ K / (r - D) := hlarge hDr
      _ ≤ (2 * K) / r := by
        apply (div_le_div_iff₀ hdenom hr).2
        nlinarith
      _ ≤ max (2 * D * Z) (2 * K) / r := by
        exact div_le_div_of_nonneg_right (le_max_right _ _) hr.le

def evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ) : ℝ :=
  ∫ x in {x : M | level < u t x}, cutoff x ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ) : ℝ :=
  ∫ x in {x : M | u t x < level}, cutoff x ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSuperlevelMass_log_exponentialTimeRescale
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hpos : ∀ t x, 0 < u t x) (t level : ℝ) :
    evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff
          (fun s x => Real.log (exponentialTimeRescale rate center u s x))
          t level =
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))
          t (center - rate * t + level) := by
  unfold evolvingLocalizedSuperlevelMass
  have hset :
      {x : M | level < Real.log (exponentialTimeRescale rate center u t x)} =
        {x : M | center - rate * t + level < Real.log (u t x)} := by
    ext x
    change level < Real.log (exponentialTimeRescale rate center u t x) ↔
      center - rate * t + level < Real.log (u t x)
    simp only [exponentialTimeRescale]
    rw [Real.log_mul (Real.exp_ne_zero _) (hpos t x).ne', Real.log_exp]
    constructor <;> intro h <;> linarith
  rw [hset]

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSublevelMass_log_exponentialTimeRescale
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hpos : ∀ t x, 0 < u t x) (t level : ℝ) :
    evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff
          (fun s x => Real.log (exponentialTimeRescale rate center u s x))
          t level =
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))
          t (center - rate * t + level) := by
  unfold evolvingLocalizedSublevelMass
  have hset :
      {x : M | Real.log (exponentialTimeRescale rate center u t x) < level} =
        {x : M | Real.log (u t x) < center - rate * t + level} := by
    ext x
    change Real.log (exponentialTimeRescale rate center u t x) < level ↔
      Real.log (u t x) < center - rate * t + level
    simp only [exponentialTimeRescale]
    rw [Real.log_mul (Real.exp_ne_zero _) (hpos t x).ne', Real.log_exp]
    constructor <;> intro h <;> linarith
  rw [hset]

omit [I.Boundaryless] in
theorem evolvingLocalizedSuperlevelMass_le_evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : Continuous cutoff) :
    evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hweight_int : Integrable (fun x : M => cutoff x ^ 2) μ :=
    (hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simpa only [evolvingLocalizedSuperlevelMass, evolvingCutoffMass,
    evolvingLocalizedIntegral, mul_one, μ] using
    setIntegral_le_integral hweight_int
      (ae_of_all μ fun x => sq_nonneg (cutoff x))
        (s := {x : M | level < u t x})

omit [I.Boundaryless] in
theorem evolvingLocalizedSublevelMass_le_evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : Continuous cutoff) :
    evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hweight_int : Integrable (fun x : M => cutoff x ^ 2) μ :=
    (hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simpa only [evolvingLocalizedSublevelMass, evolvingCutoffMass,
    evolvingLocalizedIntegral, mul_one, μ] using
    setIntegral_le_integral hweight_int
      (ae_of_all μ fun x => sq_nonneg (cutoff x))
        (s := {x : M | u t x < level})

omit [I.Boundaryless] in
theorem evolvingLocalizedSuperlevelMass_antitone
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) {lower upper : ℝ}
    (hcutoff : Continuous cutoff) (hlevel : lower ≤ upper) :
    evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t upper ≤
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t lower := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hweight_int : Integrable (fun x : M => cutoff x ^ 2) μ :=
    (hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hweight_int.restrict
  · exact ae_of_all _ fun x => sq_nonneg (cutoff x)
  · exact ae_of_all _ fun x hx => hlevel.trans_lt hx

omit [I.Boundaryless] in
theorem evolvingLocalizedSublevelMass_mono
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) {lower upper : ℝ}
    (hcutoff : Continuous cutoff) (hlevel : lower ≤ upper) :
    evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t lower ≤
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t upper := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hweight_int : Integrable (fun x : M => cutoff x ^ 2) μ :=
    (hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hweight_int.restrict
  · exact ae_of_all _ fun x => sq_nonneg (cutoff x)
  · exact ae_of_all _ fun x hx => hx.trans_le hlevel

omit [I.Boundaryless] in
theorem intervalIntegrable_evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t (level t)) volume a b := by
  exact intervalIntegrable_evolvingLocalizedSuperlevelIntegral
    (I := I) (M := M) g cutoff u level hg hcutoff.continuous
      hu.continuous hlevel a b

omit [I.Boundaryless] in
theorem intervalIntegrable_evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t (level t)) volume a b := by
  exact intervalIntegrable_evolvingLocalizedSublevelIntegral
    (I := I) (M := M) g cutoff u level hg hcutoff.continuous
      hu.continuous hlevel a b

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSuperlevelMass_eq_localizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (u t)) :
    evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t level =
      localizedSuperlevelMass (I := I) (M := M)
        (g := g t) ⟨cutoff, hcutoff⟩ ⟨u t, hu⟩ level := by
  rfl

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSublevelMass_eq_localizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (u t)) :
    evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t level =
      localizedSublevelMass (I := I) (M := M)
        (g := g t) ⟨cutoff, hcutoff⟩ ⟨u t, hu⟩ level := by
  rfl

omit [I.Boundaryless] in
theorem evolving_superlevel_chebyshev_of_center
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (t center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r) (hlevel : center + r ≤ level) :
    r ^ 2 * evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingLocalizedL2Deviation
        (I := I) (M := M) g cutoff u center t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have h := localized_superlevel_chebyshev_of_center
    (I := I) (M := M) cutoff_t u_t center hr hlevel
  simpa only [evolvingLocalizedSuperlevelMass, localizedSuperlevelMass,
    evolvingLocalizedL2Deviation, localizedL2Deviation,
    riemannianMeasureFamily_def, cutoff_t, u_t] using h

omit [I.Boundaryless] in
theorem evolving_sublevel_chebyshev_of_center
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (t center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r) (hlevel : level ≤ center - r) :
    r ^ 2 * evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingLocalizedL2Deviation
        (I := I) (M := M) g cutoff u center t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have h := localized_sublevel_chebyshev_of_center
    (I := I) (M := M) cutoff_t u_t center hr hlevel
  simpa only [evolvingLocalizedSublevelMass, localizedSublevelMass,
    evolvingLocalizedL2Deviation, localizedL2Deviation,
    riemannianMeasureFamily_def, cutoff_t, u_t] using h

omit [I.Boundaryless] in
theorem evolving_superlevel_tail_of_poincareAtAverage
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (C : ℝ) (J : Set ℝ)
    (hP : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff C J)
    (t : ℝ) (ht : t ∈ J) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff u t + r ≤ level) :
    r ^ 2 * evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff u t level ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff u t := by
  let u_t := smoothScalarSlice (I := I) (g t) u hu t
  have hchebyshev := evolving_superlevel_chebyshev_of_center
    (I := I) (M := M) g deviationCutoff u hu hdeviationCutoff t
      (evolvingLocalizedAverage
        (I := I) (M := M) g averagingCutoff u t) hr hlevel
  exact hchebyshev.trans (by
    simpa only [u_t, smoothScalarSlice_toFun] using hP t ht u_t)

omit [I.Boundaryless] in
theorem evolving_sublevel_tail_of_poincareAtAverage
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (C : ℝ) (J : Set ℝ)
    (hP : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff C J)
    (t : ℝ) (ht : t ∈ J) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff u t - r) :
    r ^ 2 * evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff u t level ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff u t := by
  let u_t := smoothScalarSlice (I := I) (g t) u hu t
  have hchebyshev := evolving_sublevel_chebyshev_of_center
    (I := I) (M := M) g deviationCutoff u hu hdeviationCutoff t
      (evolvingLocalizedAverage
        (I := I) (M := M) g averagingCutoff u t) hr hlevel
  exact hchebyshev.trans (by
    simpa only [u_t, smoothScalarSlice_toFun] using hP t ht u_t)

theorem early_evolving_log_superlevel_tail_with_center_gap_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base : ℝ) {a τ s t₀ r : ℝ}
    (haτ : a ≤ τ) (hs : s ∈ Icc a τ) (hr : 0 ≤ r)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
        evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base s + r) ^ 2 *
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) + r) ≤
      Ctail * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff
          (fun q x => Real.log (u q x)) s := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let driftIntegral : ℝ → ℝ := fun t => ∫ q in base..t,
    evolvingLogCenterDrift
      (I := I) (M := M) g averagingCutoff Ccenter H q
  let gap := shifted τ - shifted s + r
  let level := shifted τ - driftIntegral s + r
  let hlog := contMDiff_log_of_pos hu hpos
  have hmono := evolvingShiftedLogCenter_monotoneOn_of_supersolution
    (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base hg hgram
      haveragingCutoff hne hPcenter htrace hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff logu s + gap ≤ level := by
    dsimp only [gap, level, shifted, driftIntegral, logu]
    simp only [evolvingShiftedLogCenter]
    ring_nf
    exact le_rfl
  simpa only [gap, level, shifted, driftIntegral, logu] using
    evolving_superlevel_tail_of_poincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff logu hlog
        hdeviationCutoff Ctail (Icc a τ) hPtail s hs hgap hlevel

theorem late_evolving_log_sublevel_tail_with_center_gap_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base : ℝ) {τ b s t₀ r : ℝ}
    (hτb : τ ≤ b) (hs : s ∈ Icc τ b) (hr : 0 ≤ r)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base s -
        evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base τ + r) ^ 2 *
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) - r) ≤
      Ctail * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff
          (fun q x => Real.log (u q x)) s := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let driftIntegral : ℝ → ℝ := fun t => ∫ q in base..t,
    evolvingLogCenterDrift
      (I := I) (M := M) g averagingCutoff Ccenter H q
  let gap := shifted s - shifted τ + r
  let level := shifted τ - driftIntegral s - r
  let hlog := contMDiff_log_of_pos hu hpos
  have hmono := evolvingShiftedLogCenter_monotoneOn_of_supersolution
    (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base hg hgram
      haveragingCutoff hne hPcenter htrace hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : level ≤ evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff logu s - gap := by
    dsimp only [gap, level, shifted, driftIntegral, logu]
    simp only [evolvingShiftedLogCenter]
    ring_nf
    exact le_rfl
  simpa only [gap, level, shifted, driftIntegral, logu] using
    evolving_sublevel_tail_of_poincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff logu hlog
        hdeviationCutoff Ctail (Icc τ b) hPtail s hs hgap hlevel

theorem integrated_early_evolving_log_superlevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base W : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in a..τ,
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) + r)) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let center := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let level : ℝ → ℝ := fun s =>
    center τ - (∫ q in base..s,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H q) + r
  let tailMass : ℝ → ℝ := fun s => evolvingLocalizedSuperlevelMass
    (I := I) (M := M) g deviationCutoff logu s (level s)
  let dirichlet : ℝ → ℝ := fun s => evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g averagingCutoff logu s
  let mass : ℝ → ℝ := evolvingCutoffMass
    (I := I) (M := M) g averagingCutoff
  let normalizedEnergy : ℝ → ℝ := fun s => dirichlet s / mass s
  have hcenter_smooth : ContDiff ℝ 1 center :=
    contDiff_evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne
  have hcenter_mono : MonotoneOn center (Icc a τ) := by
    exact evolvingShiftedLogCenter_monotoneOn_of_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne hPcenter htrace hpde
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.add continuous_const
  have htail_int : IntervalIntegrable tailMass volume a τ := by
    simpa only [tailMass, level, logu] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu
          (contMDiff_log_of_pos hu hpos) level hlevel_cont hg
            hdeviationCutoff a τ
  have htail : ∀ s ∈ Icc a τ,
      (center τ - center s + r) ^ 2 * tailMass s ≤
        (Ctail * W) * normalizedEnergy s := by
    intro s hs
    have hpointwise :=
      early_evolving_log_superlevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H base haτ hs hr.le hg hgram hdeviationCutoff
          haveragingCutoff hne hPcenter hPtail htrace hpde
    have hdirichlet : 0 ≤ dirichlet s :=
      evolvingLocalizedDirichletEnergy_nonneg
        (I := I) (M := M) g averagingCutoff logu s
    have hmass : 0 < mass s := evolvingCutoffMass_pos
      (I := I) (M := M) g averagingCutoff s
        haveragingCutoff.continuous hne
    have hnormalize := mul_dirichlet_le_mul_mass_bound_normalized
      hCtail hdirichlet hmass (hmass_le s hs)
    have hpointwise' :
        (center τ - center s + r) ^ 2 * tailMass s ≤ Ctail * dirichlet s := by
      simpa only [center, tailMass, level, dirichlet, logu] using hpointwise
    have hnormalize' :
        Ctail * dirichlet s ≤ (Ctail * W) * normalizedEnergy s := by
      simpa only [normalizedEnergy, dirichlet, mass] using hnormalize
    exact hpointwise'.trans hnormalize'
  have henergy : ∀ s ∈ Icc a τ,
      (1 / 2 : ℝ) * normalizedEnergy s ≤ 2 * deriv center s := by
    intro s hs
    have hquarter :=
      quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
        (I := I) (M := M) g averagingCutoff u hu hpos s Ccenter H base
          (Icc a τ) hg hgram haveragingCutoff hne hPcenter hs
            (htrace s hs) (hpde s hs)
    change (1 / 2 : ℝ) * (dirichlet s / mass s) ≤ 2 * deriv center s
    change (1 / 4 : ℝ) * dirichlet s / mass s ≤ deriv center s at hquarter
    calc
      (1 / 2 : ℝ) * (dirichlet s / mass s) =
          2 * ((1 / 4 : ℝ) * dirichlet s / mass s) := by ring
      _ ≤ 2 * deriv center s := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff a).trans
        (hmass_le a ⟨le_rfl, haτ⟩)
  have hresult := integral_tail_le_of_center_gap_sq
    center tailMass normalizedEnergy hcenter_smooth haτ hr
      (mul_nonneg hCtail hW) (by norm_num) hcenter_mono
      htail_int htail henergy
  simpa only [tailMass, level, center, logu] using (show
    (∫ s in a..τ, tailMass s) ≤ 4 * Ctail * W / r by
      calc
        (∫ s in a..τ, tailMass s) ≤ 2 * (Ctail * W) * 2 / r := hresult
        _ = 4 * Ctail * W / r := by ring)

theorem integrated_late_evolving_log_sublevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base W : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in τ..b,
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) - r)) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let center := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let level : ℝ → ℝ := fun s =>
    center τ - (∫ q in base..s,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H q) - r
  let tailMass : ℝ → ℝ := fun s => evolvingLocalizedSublevelMass
    (I := I) (M := M) g deviationCutoff logu s (level s)
  let dirichlet : ℝ → ℝ := fun s => evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g averagingCutoff logu s
  let mass : ℝ → ℝ := evolvingCutoffMass
    (I := I) (M := M) g averagingCutoff
  let normalizedEnergy : ℝ → ℝ := fun s => dirichlet s / mass s
  have hcenter_smooth : ContDiff ℝ 1 center :=
    contDiff_evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne
  have hcenter_mono : MonotoneOn center (Icc τ b) := by
    exact evolvingShiftedLogCenter_monotoneOn_of_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne hPcenter htrace hpde
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.sub continuous_const
  have htail_int : IntervalIntegrable tailMass volume τ b := by
    simpa only [tailMass, level, logu] using
      intervalIntegrable_evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu
          (contMDiff_log_of_pos hu hpos) level hlevel_cont hg
            hdeviationCutoff τ b
  have htail : ∀ s ∈ Icc τ b,
      (center s - center τ + r) ^ 2 * tailMass s ≤
        (Ctail * W) * normalizedEnergy s := by
    intro s hs
    have hpointwise :=
      late_evolving_log_sublevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H base hτb hs hr.le hg hgram hdeviationCutoff
          haveragingCutoff hne hPcenter hPtail htrace hpde
    have hdirichlet : 0 ≤ dirichlet s :=
      evolvingLocalizedDirichletEnergy_nonneg
        (I := I) (M := M) g averagingCutoff logu s
    have hmass : 0 < mass s := evolvingCutoffMass_pos
      (I := I) (M := M) g averagingCutoff s
        haveragingCutoff.continuous hne
    have hnormalize := mul_dirichlet_le_mul_mass_bound_normalized
      hCtail hdirichlet hmass (hmass_le s hs)
    have hpointwise' :
        (center s - center τ + r) ^ 2 * tailMass s ≤ Ctail * dirichlet s := by
      simpa only [center, tailMass, level, dirichlet, logu] using hpointwise
    have hnormalize' :
        Ctail * dirichlet s ≤ (Ctail * W) * normalizedEnergy s := by
      simpa only [normalizedEnergy, dirichlet, mass] using hnormalize
    exact hpointwise'.trans hnormalize'
  have henergy : ∀ s ∈ Icc τ b,
      (1 / 2 : ℝ) * normalizedEnergy s ≤ 2 * deriv center s := by
    intro s hs
    have hquarter :=
      quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
        (I := I) (M := M) g averagingCutoff u hu hpos s Ccenter H base
          (Icc τ b) hg hgram haveragingCutoff hne hPcenter hs
            (htrace s hs) (hpde s hs)
    change (1 / 2 : ℝ) * (dirichlet s / mass s) ≤ 2 * deriv center s
    change (1 / 4 : ℝ) * dirichlet s / mass s ≤ deriv center s at hquarter
    calc
      (1 / 2 : ℝ) * (dirichlet s / mass s) =
          2 * ((1 / 4 : ℝ) * dirichlet s / mass s) := by ring
      _ ≤ 2 * deriv center s := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff τ).trans
        (hmass_le τ ⟨le_rfl, hτb⟩)
  have hresult := integral_tail_le_of_center_gap_sq_from_left
    center tailMass normalizedEnergy hcenter_smooth hτb hr
      (mul_nonneg hCtail hW) (by norm_num) hcenter_mono
      htail_int htail henergy
  simpa only [tailMass, level, center, logu] using (show
    (∫ s in τ..b, tailMass s) ≤ 4 * Ctail * W / r by
      calc
        (∫ s in τ..b, tailMass s) ≤ 2 * (Ctail * W) * 2 / r := hresult
        _ = 4 * Ctail * W / r := by ring)

theorem integrated_early_centered_evolving_log_superlevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W Wdeviation : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdeviationMass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g deviationCutoff t ≤ Wdeviation)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in a..τ,
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingLocalizedAverage
            (I := I) (M := M) g averagingCutoff
              (fun q x => Real.log (u q x)) τ + r)) ≤
      max
          (2 * (∫ q in a..τ,
            evolvingLogCenterDrift
              (I := I) (M := M) g averagingCutoff Ccenter H q) *
            ((τ - a) * Wdeviation))
          (8 * Ctail * W) / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let drift := evolvingLogCenterDrift
    (I := I) (M := M) g averagingCutoff Ccenter H
  let D := ∫ q in a..τ, drift q
  let Z := (τ - a) * Wdeviation
  let K := 4 * Ctail * W
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ
  let tailMass : ℝ → ℝ := fun s =>
    evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g deviationCutoff logu s (center + r)
  have hlog := contMDiff_log_of_pos hu hpos
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hdrift_nonneg : ∀ q, 0 ≤ drift q := fun q =>
    evolvingLogCenterDrift_nonneg
      (I := I) (M := M) g averagingCutoff Ccenter H q
  have hdrift_int : IntervalIntegrable drift volume a τ :=
    hdrift.intervalIntegrable a τ
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff a).trans
        (hmass_le a ⟨le_rfl, haτ⟩)
  have hWdeviation : 0 ≤ Wdeviation :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g deviationCutoff a).trans
        (hdeviationMass_le a ⟨le_rfl, haτ⟩)
  have hZ : 0 ≤ Z := mul_nonneg (sub_nonneg.mpr haτ) hWdeviation
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hCtail) hW
  have htail_int : IntervalIntegrable tailMass volume a τ := by
    simpa only [tailMass, center] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu hlog
          (fun _ => center + r) continuous_const hg hdeviationCutoff a τ
  have hsmall : (∫ s in a..τ, tailMass s) ≤ Z := by
    have hconst_int : IntervalIntegrable
        (fun _ : ℝ => Wdeviation) volume a τ := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on haτ htail_int hconst_int
      (fun s hs =>
        (evolvingLocalizedSuperlevelMass_le_evolvingCutoffMass
          (I := I) (M := M) g deviationCutoff logu s (center + r)
            hdeviationCutoff.continuous).trans (hdeviationMass_le s hs))
    simpa only [Z, intervalIntegral.integral_const, smul_eq_mul] using hmono
  have haccum : ∀ s ∈ Icc a τ, -(∫ q in τ..s, drift q) ≤ D := by
    intro s hs
    rw [intervalIntegral.integral_symm s τ, neg_neg]
    exact intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      (ae_of_all _ fun q => hdrift_nonneg q) hdrift_int
  have hcenter : evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u Ccenter H τ τ = center := by
    simp only [evolvingShiftedLogCenter, intervalIntegral.integral_same,
      add_zero, center, logu]
  have hlarge : D < r → (∫ s in a..τ, tailMass s) ≤ K / (r - D) := by
    intro hDr
    let q := r - D
    let shiftedLevel : ℝ → ℝ := fun s =>
      evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H τ τ -
        (∫ z in τ..s, drift z) + q
    let shiftedMass : ℝ → ℝ := fun s =>
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu s (shiftedLevel s)
    have hq : 0 < q := sub_pos.mpr hDr
    have hlevel_cont : Continuous shiftedLevel := by
      exact continuous_const.sub
        (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
          |>.add continuous_const
    have hshifted_int : IntervalIntegrable shiftedMass volume a τ := by
      simpa only [shiftedMass] using
        intervalIntegrable_evolvingLocalizedSuperlevelMass
          (I := I) (M := M) g deviationCutoff logu hlog shiftedLevel
            hlevel_cont hg hdeviationCutoff a τ
    have hlevel : ∀ s ∈ Icc a τ, shiftedLevel s ≤ center + r := by
      intro s hs
      have hsaccum := haccum s hs
      dsimp only [shiftedLevel, q]
      rw [hcenter]
      linarith
    have hmono : (∫ s in a..τ, tailMass s) ≤ ∫ s in a..τ, shiftedMass s := by
      exact intervalIntegral.integral_mono_on haτ htail_int hshifted_int
        (fun s hs => evolvingLocalizedSuperlevelMass_antitone
          (I := I) (M := M) g deviationCutoff logu s
            hdeviationCutoff.continuous (hlevel s hs))
    have hbound :=
      integrated_early_evolving_log_superlevel_tail_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H τ W haτ hq hCtail hg hgram hdeviationCutoff
            haveragingCutoff hne hPcenter hPtail htrace hmass_le hpde
    calc
      (∫ s in a..τ, tailMass s) ≤ ∫ s in a..τ, shiftedMass s := hmono
      _ ≤ K / (r - D) := by
        simpa only [shiftedMass, shiftedLevel, drift, logu, q, K] using hbound
  have hresult := recentered_tail_le hZ hK hr hsmall hlarge
  have hK_eq : 2 * K = 8 * Ctail * W := by
    dsimp only [K]
    ring
  rw [hK_eq] at hresult
  simpa only [tailMass, center, logu, D, Z, drift] using hresult

theorem integrated_late_centered_evolving_log_sublevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W Wdeviation : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdeviationMass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g deviationCutoff t ≤ Wdeviation)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in τ..b,
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingLocalizedAverage
            (I := I) (M := M) g averagingCutoff
              (fun q x => Real.log (u q x)) τ - r)) ≤
      max
          (2 * (∫ q in τ..b,
            evolvingLogCenterDrift
              (I := I) (M := M) g averagingCutoff Ccenter H q) *
            ((b - τ) * Wdeviation))
          (8 * Ctail * W) / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let drift := evolvingLogCenterDrift
    (I := I) (M := M) g averagingCutoff Ccenter H
  let D := ∫ q in τ..b, drift q
  let Z := (b - τ) * Wdeviation
  let K := 4 * Ctail * W
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ
  let tailMass : ℝ → ℝ := fun s =>
    evolvingLocalizedSublevelMass
      (I := I) (M := M) g deviationCutoff logu s (center - r)
  have hlog := contMDiff_log_of_pos hu hpos
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hdrift_nonneg : ∀ q, 0 ≤ drift q := fun q =>
    evolvingLogCenterDrift_nonneg
      (I := I) (M := M) g averagingCutoff Ccenter H q
  have hdrift_int : IntervalIntegrable drift volume τ b :=
    hdrift.intervalIntegrable τ b
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff τ).trans
        (hmass_le τ ⟨le_rfl, hτb⟩)
  have hWdeviation : 0 ≤ Wdeviation :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g deviationCutoff τ).trans
        (hdeviationMass_le τ ⟨le_rfl, hτb⟩)
  have hZ : 0 ≤ Z := mul_nonneg (sub_nonneg.mpr hτb) hWdeviation
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hCtail) hW
  have htail_int : IntervalIntegrable tailMass volume τ b := by
    simpa only [tailMass, center] using
      intervalIntegrable_evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu hlog
          (fun _ => center - r) continuous_const hg hdeviationCutoff τ b
  have hsmall : (∫ s in τ..b, tailMass s) ≤ Z := by
    have hconst_int : IntervalIntegrable
        (fun _ : ℝ => Wdeviation) volume τ b := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hτb htail_int hconst_int
      (fun s hs =>
        (evolvingLocalizedSublevelMass_le_evolvingCutoffMass
          (I := I) (M := M) g deviationCutoff logu s (center - r)
            hdeviationCutoff.continuous).trans (hdeviationMass_le s hs))
    simpa only [Z, intervalIntegral.integral_const, smul_eq_mul] using hmono
  have haccum : ∀ s ∈ Icc τ b, (∫ q in τ..s, drift q) ≤ D := by
    intro s hs
    exact intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
      (ae_of_all _ fun q => hdrift_nonneg q) hdrift_int
  have hcenter : evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u Ccenter H τ τ = center := by
    simp only [evolvingShiftedLogCenter, intervalIntegral.integral_same,
      add_zero, center, logu]
  have hlarge : D < r → (∫ s in τ..b, tailMass s) ≤ K / (r - D) := by
    intro hDr
    let q := r - D
    let shiftedLevel : ℝ → ℝ := fun s =>
      evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H τ τ -
        (∫ z in τ..s, drift z) - q
    let shiftedMass : ℝ → ℝ := fun s =>
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu s (shiftedLevel s)
    have hq : 0 < q := sub_pos.mpr hDr
    have hlevel_cont : Continuous shiftedLevel := by
      exact continuous_const.sub
        (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
          |>.sub continuous_const
    have hshifted_int : IntervalIntegrable shiftedMass volume τ b := by
      simpa only [shiftedMass] using
        intervalIntegrable_evolvingLocalizedSublevelMass
          (I := I) (M := M) g deviationCutoff logu hlog shiftedLevel
            hlevel_cont hg hdeviationCutoff τ b
    have hlevel : ∀ s ∈ Icc τ b, center - r ≤ shiftedLevel s := by
      intro s hs
      have hsaccum := haccum s hs
      dsimp only [shiftedLevel, q]
      rw [hcenter]
      linarith
    have hmono : (∫ s in τ..b, tailMass s) ≤ ∫ s in τ..b, shiftedMass s := by
      exact intervalIntegral.integral_mono_on hτb htail_int hshifted_int
        (fun s hs => evolvingLocalizedSublevelMass_mono
          (I := I) (M := M) g deviationCutoff logu s
            hdeviationCutoff.continuous (hlevel s hs))
    have hbound :=
      integrated_late_evolving_log_sublevel_tail_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H τ W hτb hq hCtail hg hgram hdeviationCutoff
            haveragingCutoff hne hPcenter hPtail htrace hmass_le hpde
    calc
      (∫ s in τ..b, tailMass s) ≤ ∫ s in τ..b, shiftedMass s := hmono
      _ ≤ K / (r - D) := by
        simpa only [shiftedMass, shiftedLevel, drift, logu, q, K] using hbound
  have hresult := recentered_tail_le hZ hK hr hsmall hlarge
  have hK_eq : 2 * K = 8 * Ctail * W := by
    dsimp only [K]
    ring
  rw [hK_eq] at hresult
  simpa only [tailMass, center, logu, D, Z, drift] using hresult

theorem integrated_early_evolving_log_superlevel_tail_of_exponentialTimeRescale_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc a τ,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x ↦ Real.log (u s x)) τ + rate * τ
    (∫ s in a..τ,
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x ↦ Real.log (exponentialTimeRescale rate center u q x)) s r) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x ↦ Real.log (u q x)
  let drift := evolvingLogCenterDrift
    (I := I) (M := M) g averagingCutoff Ccenter H
  let average := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ
  let center := average + rate * τ
  let shiftedLevel : ℝ → ℝ := fun s ↦
    average - (∫ q in τ..s, drift q) + r
  let rescaledLog : ℝ → M → ℝ := fun q x ↦
    Real.log (exponentialTimeRescale rate center u q x)
  let rescaledMass : ℝ → ℝ := fun s ↦
    evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g deviationCutoff rescaledLog s r
  let shiftedMass : ℝ → ℝ := fun s ↦
    evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g deviationCutoff logu s (shiftedLevel s)
  have hlog := contMDiff_log_of_pos hu hpos
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  have hrescaledLog := contMDiff_log_of_pos hrescaled hrescaled_pos
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hshiftedLevel : Continuous shiftedLevel := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.add continuous_const
  have hrescaled_int : IntervalIntegrable rescaledMass volume a τ := by
    simpa only [rescaledMass, rescaledLog] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff rescaledLog hrescaledLog
          (fun _ ↦ r) continuous_const hg hdeviationCutoff a τ
  have hshifted_int : IntervalIntegrable shiftedMass volume a τ := by
    simpa only [shiftedMass] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu hlog shiftedLevel
          hshiftedLevel hg hdeviationCutoff a τ
  have hlevel : ∀ s ∈ Icc a τ,
      shiftedLevel s ≤ center - rate * s + r := by
    intro s hs
    have hdrift_int : IntervalIntegrable drift volume s τ := hdrift.intervalIntegrable s τ
    have hrate_int : IntervalIntegrable (fun _ : ℝ ↦ rate) volume s τ :=
      intervalIntegrable_const
    have hintegral := intervalIntegral.integral_mono_on hs.2 hdrift_int hrate_int
      (fun q hq ↦ hdrift_le q ⟨hs.1.trans hq.1, hq.2⟩)
    have hintegral' : (∫ q in s..τ, drift q) ≤ rate * (τ - s) := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hintegral
    dsimp only [shiftedLevel, center]
    rw [intervalIntegral.integral_symm s τ]
    linarith
  have hpoint : ∀ s ∈ Icc a τ, rescaledMass s ≤ shiftedMass s := by
    intro s hs
    rw [show rescaledMass s = evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu s (center - rate * s + r) by
      simpa only [rescaledMass, rescaledLog, logu] using
        evolvingLocalizedSuperlevelMass_log_exponentialTimeRescale
          (I := I) (M := M) g deviationCutoff rate center u hpos s r]
    exact evolvingLocalizedSuperlevelMass_antitone
      (I := I) (M := M) g deviationCutoff logu s
        hdeviationCutoff.continuous (hlevel s hs)
  have hmono : (∫ s in a..τ, rescaledMass s) ≤ ∫ s in a..τ, shiftedMass s :=
    intervalIntegral.integral_mono_on haτ hrescaled_int hshifted_int hpoint
  have htail := integrated_early_evolving_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
      Ccenter Ctail H τ W haτ hr hCtail hg hgram hdeviationCutoff
        haveragingCutoff hne hPcenter hPtail htrace hmass_le hpde
  exact hmono.trans (by
    simpa only [shiftedMass, shiftedLevel, average, drift, logu,
      evolvingShiftedLogCenter, intervalIntegral.integral_same, add_zero] using htail)

theorem integrated_late_evolving_log_sublevel_tail_of_exponentialTimeRescale_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc τ b,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x ↦ Real.log (u s x)) τ + rate * τ
    (∫ s in τ..b,
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x ↦ Real.log (exponentialTimeRescale rate center u q x)) s (-r)) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x ↦ Real.log (u q x)
  let drift := evolvingLogCenterDrift
    (I := I) (M := M) g averagingCutoff Ccenter H
  let average := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ
  let center := average + rate * τ
  let shiftedLevel : ℝ → ℝ := fun s ↦
    average - (∫ q in τ..s, drift q) - r
  let rescaledLog : ℝ → M → ℝ := fun q x ↦
    Real.log (exponentialTimeRescale rate center u q x)
  let rescaledMass : ℝ → ℝ := fun s ↦
    evolvingLocalizedSublevelMass
      (I := I) (M := M) g deviationCutoff rescaledLog s (-r)
  let shiftedMass : ℝ → ℝ := fun s ↦
    evolvingLocalizedSublevelMass
      (I := I) (M := M) g deviationCutoff logu s (shiftedLevel s)
  have hlog := contMDiff_log_of_pos hu hpos
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  have hrescaledLog := contMDiff_log_of_pos hrescaled hrescaled_pos
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hshiftedLevel : Continuous shiftedLevel := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.sub continuous_const
  have hrescaled_int : IntervalIntegrable rescaledMass volume τ b := by
    simpa only [rescaledMass, rescaledLog] using
      intervalIntegrable_evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff rescaledLog hrescaledLog
          (fun _ ↦ -r) continuous_const hg hdeviationCutoff τ b
  have hshifted_int : IntervalIntegrable shiftedMass volume τ b := by
    simpa only [shiftedMass] using
      intervalIntegrable_evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu hlog shiftedLevel
          hshiftedLevel hg hdeviationCutoff τ b
  have hlevel : ∀ s ∈ Icc τ b,
      center - rate * s - r ≤ shiftedLevel s := by
    intro s hs
    have hdrift_int : IntervalIntegrable drift volume τ s := hdrift.intervalIntegrable τ s
    have hrate_int : IntervalIntegrable (fun _ : ℝ ↦ rate) volume τ s :=
      intervalIntegrable_const
    have hintegral := intervalIntegral.integral_mono_on hs.1 hdrift_int hrate_int
      (fun q hq ↦ hdrift_le q ⟨hq.1, hq.2.trans hs.2⟩)
    have hintegral' : (∫ q in τ..s, drift q) ≤ rate * (s - τ) := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hintegral
    dsimp only [shiftedLevel, center]
    linarith
  have hpoint : ∀ s ∈ Icc τ b, rescaledMass s ≤ shiftedMass s := by
    intro s hs
    rw [show rescaledMass s = evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu s (center - rate * s - r) by
      simpa only [rescaledMass, rescaledLog, logu] using
        evolvingLocalizedSublevelMass_log_exponentialTimeRescale
          (I := I) (M := M) g deviationCutoff rate center u hpos s (-r)]
    exact evolvingLocalizedSublevelMass_mono
      (I := I) (M := M) g deviationCutoff logu s
        hdeviationCutoff.continuous (hlevel s hs)
  have hmono : (∫ s in τ..b, rescaledMass s) ≤ ∫ s in τ..b, shiftedMass s :=
    intervalIntegral.integral_mono_on hτb hrescaled_int hshifted_int hpoint
  have htail := integrated_late_evolving_log_sublevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
      Ccenter Ctail H τ W hτb hr hCtail hg hgram hdeviationCutoff
        haveragingCutoff hne hPcenter hPtail htrace hmass_le hpde
  exact hmono.trans (by
    simpa only [shiftedMass, shiftedLevel, average, drift, logu,
      evolvingShiftedLogCenter, intervalIntegral.integral_same, add_zero] using htail)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
