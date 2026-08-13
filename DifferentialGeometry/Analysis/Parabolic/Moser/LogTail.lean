import DifferentialGeometry.Analysis.Parabolic.ExponentialRescaling
import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def localizedSuperlevelMass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (level : ℝ) : ℝ :=
  ∫ x in {x : M | level < u.toFun x}, cutoff.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedSublevelMass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (level : ℝ) : ℝ :=
  ∫ x in {x : M | u.toFun x < level}, cutoff.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [I.Boundaryless] in
theorem intervalIntegrable_localizedSuperlevelMass
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => localizedSuperlevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) (level t)) volume a b := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let S : Set (ℝ × M) := {z | level z.1 < u z.1 z.2}
  let F : ℝ × M → ℝ := fun z => S.indicator
    (fun q => cutoff.toFun q.2 ^ 2) z
  let inner : ℝ → ℝ := fun t => ∫ x, F (t, x) ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hS : MeasurableSet S := by
    exact (isOpen_lt (hlevel.comp continuous_fst)
      hu.continuous).measurableSet
  have hweight_cont : Continuous (fun z : ℝ × M => cutoff.toFun z.2 ^ 2) :=
    (cutoff.smooth.continuous.comp continuous_snd).pow 2
  have hF : StronglyMeasurable F := by
    exact hweight_cont.stronglyMeasurable.indicator hS
  have hinner_meas : StronglyMeasurable inner := by
    exact hF.integral_prod_right
  have hweight_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hinner_eq : ∀ t,
      inner t = localizedSuperlevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) (level t) := by
    intro t
    let St : Set M := {x | level t < u t x}
    have hSt : MeasurableSet St :=
      (isOpen_lt continuous_const
        (hu.continuous.comp (continuous_const.prodMk continuous_id))).measurableSet
    change (∫ x, F (t, x) ∂μ) = ∫ x in St, cutoff.toFun x ^ 2 ∂μ
    rw [← integral_indicator hSt]
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hinner_nonneg : ∀ t, 0 ≤ inner t := by
    intro t
    rw [hinner_eq]
    exact integral_nonneg fun x => sq_nonneg _
  have hinner_le : ∀ t, inner t ≤ cutoffMass (I := I) (M := M) cutoff := by
    intro t
    rw [hinner_eq]
    exact setIntegral_le_integral hweight_int
      (ae_of_all μ fun x => sq_nonneg _)
  have hinner_int : IntegrableOn inner (uIcc a b) volume := by
    apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne
      hinner_meas.aestronglyMeasurable
    exact ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hinner_nonneg t)]
      exact hinner_le t
  have hmass_int : IntegrableOn
      (fun t => localizedSuperlevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) (level t))
      (uIcc a b) volume := by
    exact hinner_int.congr_fun (fun t ht => hinner_eq t) measurableSet_uIcc
  exact hmass_int.intervalIntegrable

omit [I.Boundaryless] in
theorem intervalIntegrable_localizedSublevelMass
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => localizedSublevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) (level t)) volume a b := by
  have h := intervalIntegrable_localizedSuperlevelMass
    (I := I) (M := M) g cutoff (fun t x => -u t x) hu.neg
      (fun t => -level t) hlevel.neg a b
  simpa only [localizedSuperlevelMass, localizedSublevelMass,
    smoothScalarSlice_toFun, neg_lt_neg_iff] using h

omit [I.Boundaryless] in
theorem localized_superlevel_chebyshev_of_center
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : center + r ≤ level) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Deviation (I := I) (M := M) cutoff u center := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let S : Set M := {x : M | level < u.toFun x}
  let oscilland : M → ℝ := fun x =>
    cutoff.toFun x ^ 2 * (u.toFun x - center) ^ 2
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const u.smooth.continuous).measurableSet
  have hweight_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft_int : IntegrableOn (fun x : M => r ^ 2 * cutoff.toFun x ^ 2) S μ :=
    (hweight_int.const_mul (r ^ 2)).integrableOn
  have hoscilland_int : Integrable oscilland μ := by
    exact ((cutoff.smooth.continuous.pow 2).mul
      ((u.smooth.continuous.sub continuous_const).pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : IntegrableOn oscilland S μ := hoscilland_int.integrableOn
  have hpointwise : ∀ x ∈ S,
      r ^ 2 * cutoff.toFun x ^ 2 ≤ oscilland x := by
    intro x hx
    have hdiff : r ≤ u.toFun x - center := by
      change level < u.toFun x at hx
      linarith
    have hsquare : r ^ 2 ≤ (u.toFun x - center) ^ 2 :=
      (sq_le_sq₀ hr (hr.trans hdiff)).2 hdiff
    simpa only [oscilland, mul_comm] using
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg (cutoff.toFun x))
  calc
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level =
        ∫ x in S, r ^ 2 * cutoff.toFun x ^ 2 ∂μ := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ x in S, oscilland x ∂μ :=
      setIntegral_mono_on hleft_int hright_int hS hpointwise
    _ ≤ ∫ x, oscilland x ∂μ :=
      setIntegral_le_integral hoscilland_int
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = localizedL2Deviation (I := I) (M := M) cutoff u center := by
      rfl

omit [I.Boundaryless] in
theorem localized_superlevel_chebyshev
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : localizedAverage (I := I) (M := M) cutoff u + r ≤ level) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Oscillation (I := I) (M := M) cutoff u := by
  exact localized_superlevel_chebyshev_of_center
    (I := I) (M := M) cutoff u
      (localizedAverage (I := I) (M := M) cutoff u) hr hlevel

omit [I.Boundaryless] in
theorem localized_sublevel_chebyshev_of_center
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ center - r) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Deviation (I := I) (M := M) cutoff u center := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let S : Set M := {x : M | u.toFun x < level}
  let oscilland : M → ℝ := fun x =>
    cutoff.toFun x ^ 2 * (u.toFun x - center) ^ 2
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hS : MeasurableSet S :=
    (isOpen_lt u.smooth.continuous continuous_const).measurableSet
  have hweight_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft_int : IntegrableOn (fun x : M => r ^ 2 * cutoff.toFun x ^ 2) S μ :=
    (hweight_int.const_mul (r ^ 2)).integrableOn
  have hoscilland_int : Integrable oscilland μ := by
    exact ((cutoff.smooth.continuous.pow 2).mul
      ((u.smooth.continuous.sub continuous_const).pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : IntegrableOn oscilland S μ := hoscilland_int.integrableOn
  have hpointwise : ∀ x ∈ S,
      r ^ 2 * cutoff.toFun x ^ 2 ≤ oscilland x := by
    intro x hx
    have hdiff : r ≤ center - u.toFun x := by
      change u.toFun x < level at hx
      linarith
    have hsquare : r ^ 2 ≤ (center - u.toFun x) ^ 2 :=
      (sq_le_sq₀ hr (hr.trans hdiff)).2 hdiff
    have hsquare' : r ^ 2 ≤ (u.toFun x - center) ^ 2 := by
      nlinarith
    simpa only [oscilland, mul_comm] using
      mul_le_mul_of_nonneg_right hsquare' (sq_nonneg (cutoff.toFun x))
  calc
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level =
        ∫ x in S, r ^ 2 * cutoff.toFun x ^ 2 ∂μ := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ x in S, oscilland x ∂μ :=
      setIntegral_mono_on hleft_int hright_int hS hpointwise
    _ ≤ ∫ x, oscilland x ∂μ :=
      setIntegral_le_integral hoscilland_int
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = localizedL2Deviation (I := I) (M := M) cutoff u center := by
      rfl

omit [I.Boundaryless] in
theorem localized_sublevel_chebyshev
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ localizedAverage (I := I) (M := M) cutoff u - r) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Oscillation (I := I) (M := M) cutoff u := by
  exact localized_sublevel_chebyshev_of_center
    (I := I) (M := M) cutoff u
      (localizedAverage (I := I) (M := M) cutoff u) hr hlevel

def shiftedLogMass
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) : ℝ :=
  localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
        (contMDiff_log_of_pos hu hpos) t) +
    t * (2 * cutoffDirichletEnergy (I := I) (M := M) cutoff)

def shiftedLogCenter
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) : ℝ :=
  shiftedLogMass (I := I) (M := M) g cutoff u hu hpos t /
    cutoffMass (I := I) (M := M) cutoff

def logCenterDrift
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g) : ℝ :=
  2 * cutoffDirichletEnergy (I := I) (M := M) cutoff /
    cutoffMass (I := I) (M := M) cutoff

omit [I.Boundaryless] [CompactSpace M] in
theorem logCenterDrift_nonneg
    (g : SmoothRiemannianMetric I M) (cutoff : SmoothScalar g) :
    0 ≤ logCenterDrift (I := I) (M := M) g cutoff := by
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (cutoffDirichletEnergy_nonneg (I := I) (M := M) cutoff))
    (cutoff_mass_nonneg (I := I) (M := M) cutoff)

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedSuperlevelMass_log_exponentialTimeRescale
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (rate center : ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t level : ℝ) :
    localizedSuperlevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g
          (fun s x => Real.log (exponentialTimeRescale rate center u s x))
          (contMDiff_log_of_pos
            (contMDiff_exponentialTimeRescale rate center u hu)
            (exponentialTimeRescale_pos rate center u hpos)) t) level =
      localizedSuperlevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
          (contMDiff_log_of_pos hu hpos) t)
        (center - rate * t + level) := by
  unfold localizedSuperlevelMass
  simp only [smoothScalarSlice_toFun]
  have hset :
      {x : M | level < Real.log (exponentialTimeRescale rate center u t x)} =
        {x : M | center - rate * t + level < Real.log (u t x)} := by
    ext x
    change level < Real.log (exponentialTimeRescale rate center u t x) ↔
      center - rate * t + level < Real.log (u t x)
    simp only [exponentialTimeRescale]
    rw [Real.log_mul (Real.exp_ne_zero _) (hpos t x).ne', Real.log_exp]
    constructor <;> intro h <;> change _ < _ at h ⊢ <;> linarith
  rw [hset]

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedSublevelMass_log_exponentialTimeRescale
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (rate center : ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t level : ℝ) :
    localizedSublevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g
          (fun s x => Real.log (exponentialTimeRescale rate center u s x))
          (contMDiff_log_of_pos
            (contMDiff_exponentialTimeRescale rate center u hu)
            (exponentialTimeRescale_pos rate center u hpos)) t) level =
      localizedSublevelMass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
          (contMDiff_log_of_pos hu hpos) t)
        (center - rate * t + level) := by
  unfold localizedSublevelMass
  simp only [smoothScalarSlice_toFun]
  have hset :
      {x : M | Real.log (exponentialTimeRescale rate center u t x) < level} =
        {x : M | Real.log (u t x) < center - rate * t + level} := by
    ext x
    change Real.log (exponentialTimeRescale rate center u t x) < level ↔
      Real.log (u t x) < center - rate * t + level
    simp only [exponentialTimeRescale]
    rw [Real.log_mul (Real.exp_ne_zero _) (hpos t x).ne', Real.log_exp]
    constructor <;> intro h <;> change _ < _ at h ⊢ <;> linarith
  rw [hset]

omit [CompactSpace M] in
theorem centered_exponential_time_rescale_supersolution
    (g : SmoothRiemannianMetric I M)
    (averagingCutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (τ : ℝ) {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    Δ_g (I := I) g
        (smoothScalarSlice (I := I) g
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u)
          (contMDiff_exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u hu)
          t).toContMDiffMap x ≤
      deriv (fun s =>
        exponentialTimeRescale
          (logCenterDrift (I := I) (M := M) g averagingCutoff)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u s x) t := by
  exact exponential_time_rescale_supersolution (I := I) (M := M) g
    (logCenterDrift (I := I) (M := M) g averagingCutoff)
    (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ)
    (logCenterDrift_nonneg (I := I) (M := M) g averagingCutoff)
    u hu hpos hpde

omit [I.Boundaryless] [CompactSpace M] in
theorem shifted_log_center_eq
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) :
    shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos t =
      localizedAverage (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) +
        t * logCenterDrift (I := I) (M := M) g cutoff := by
  unfold shiftedLogCenter shiftedLogMass localizedAverage logCenterDrift
  ring

omit [I.Boundaryless] in
theorem contDiff_shiftedLogCenter
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) :
    ContDiff ℝ ∞
      (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun t =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hshifted_smooth : ContDiff ℝ ∞ (fun t => mass t + t * source) :=
    hmass_smooth.add (contDiff_id.mul contDiff_const)
  simpa only [shiftedLogCenter, shiftedLogMass, mass, source] using
    hshifted_smooth.div_const (cutoffMass (I := I) (M := M) cutoff)

theorem integral_deriv_div_center_gap_sq
    (center : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 1 center)
    {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hmono : MonotoneOn center (Icc a b)) :
    (∫ t in a..b,
        deriv center t / (center b - center t + r) ^ 2) =
      1 / r - 1 / (center b - center a + r) := by
  let gap : ℝ → ℝ := fun t => center b - center t + r
  let reciprocal : ℝ → ℝ := fun t => 1 / gap t
  have hgap_pos : ∀ t ∈ Icc a b, 0 < gap t := by
    intro t ht
    have hle := hmono ht ⟨hab, le_rfl⟩ ht.2
    dsimp only [gap]
    linarith
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt reciprocal (deriv center t / gap t ^ 2) t := by
    intro t ht
    have hcenter_deriv : HasDerivAt center (deriv center t) t :=
      (hsmooth.differentiable (by norm_num) t).hasDerivAt
    have hgap_deriv : HasDerivAt gap (-deriv center t) t := by
      simpa only [gap, Pi.sub_apply, Pi.add_apply, zero_sub] using
        ((hasDerivAt_const t (center b)).sub hcenter_deriv).add_const r
    have hinv := hgap_deriv.inv (hgap_pos t ht).ne'
    simpa only [reciprocal, one_div, neg_neg] using hinv
  have hderiv_cont : ContinuousOn
      (fun t => deriv center t / gap t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hsmooth.continuous_deriv (by norm_num)).continuousOn.div
      (((continuous_const.sub hsmooth.continuous).add continuous_const).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hgap_pos t ht).ne')
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa [uIcc_of_le hab] using ht))
    hderiv_cont.intervalIntegrable
  simpa only [reciprocal, gap, sub_self, zero_add] using hintegral

theorem integral_deriv_div_center_gap_sq_from_left
    (center : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 1 center)
    {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hmono : MonotoneOn center (Icc a b)) :
    (∫ t in a..b,
        deriv center t / (center t - center a + r) ^ 2) =
      1 / r - 1 / (center b - center a + r) := by
  let gap : ℝ → ℝ := fun t => center t - center a + r
  let negativeReciprocal : ℝ → ℝ := fun t => -(1 / gap t)
  have hgap_pos : ∀ t ∈ Icc a b, 0 < gap t := by
    intro t ht
    have hle := hmono ⟨le_rfl, hab⟩ ht ht.1
    dsimp only [gap]
    linarith
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt negativeReciprocal (deriv center t / gap t ^ 2) t := by
    intro t ht
    have hcenter_deriv : HasDerivAt center (deriv center t) t :=
      (hsmooth.differentiable (by norm_num) t).hasDerivAt
    have hgap_deriv : HasDerivAt gap (deriv center t) t := by
      simpa only [gap, Pi.sub_apply, Pi.add_apply, sub_zero] using
        (hcenter_deriv.sub_const (center a)).add_const r
    have hinv := (hgap_deriv.inv (hgap_pos t ht).ne').neg
    have hcoefficient :
        -(-deriv center t / gap t ^ 2) = deriv center t / gap t ^ 2 := by
      ring
    rw [hcoefficient] at hinv
    simpa only [negativeReciprocal, one_div] using hinv
  have hderiv_cont : ContinuousOn
      (fun t => deriv center t / gap t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hsmooth.continuous_deriv (by norm_num)).continuousOn.div
      (((hsmooth.continuous.sub continuous_const).add continuous_const).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hgap_pos t ht).ne')
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa [uIcc_of_le hab] using ht))
    hderiv_cont.intervalIntegrable
  have hendpoint :
      -(1 / (center b - center a + r)) - -(1 / r) =
        1 / r - 1 / (center b - center a + r) := by
    ring
  simpa only [negativeReciprocal, gap, sub_self, zero_add, hendpoint] using hintegral

theorem integral_tail_le_of_center_gap_sq
    (center tailMass energy : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 1 center)
    {a b r C weight : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hC : 0 ≤ C) (hweight : 0 ≤ weight)
    (hmono : MonotoneOn center (Icc a b))
    (hmass_int : IntervalIntegrable tailMass volume a b)
    (htail : ∀ t ∈ Icc a b,
      (center b - center t + r) ^ 2 * tailMass t ≤ C * energy t)
    (henergy : ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * energy t ≤ weight * deriv center t) :
    (∫ t in a..b, tailMass t) ≤ 2 * C * weight / r := by
  let gap : ℝ → ℝ := fun t => center b - center t + r
  let majorant : ℝ → ℝ := fun t =>
    2 * C * weight * (deriv center t / gap t ^ 2)
  have hgap_pos : ∀ t ∈ Icc a b, 0 < gap t := by
    intro t ht
    have hle := hmono ht ⟨hab, le_rfl⟩ ht.2
    dsimp only [gap]
    linarith
  have hpointwise : ∀ t ∈ Icc a b, tailMass t ≤ majorant t := by
    intro t ht
    have hscaled : C * energy t ≤ 2 * C * weight * deriv center t := by
      calc
        C * energy t = (2 * C) * ((1 / 2 : ℝ) * energy t) := by ring
        _ ≤ (2 * C) * (weight * deriv center t) :=
          mul_le_mul_of_nonneg_left (henergy t ht)
            (mul_nonneg (by norm_num) hC)
        _ = 2 * C * weight * deriv center t := by ring
    have hproduct :
        gap t ^ 2 * tailMass t ≤ 2 * C * weight * deriv center t := by
      simpa only [gap] using (htail t ht).trans hscaled
    have hdiv :
        tailMass t ≤ (2 * C * weight * deriv center t) / gap t ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (hgap_pos t ht))).2
      calc
        tailMass t * gap t ^ 2 = gap t ^ 2 * tailMass t := by ring
        _ ≤ 2 * C * weight * deriv center t := hproduct
    calc
      tailMass t ≤ (2 * C * weight * deriv center t) / gap t ^ 2 := hdiv
      _ = majorant t := by
        dsimp only [majorant]
        ring
  have hmajorant_cont : ContinuousOn majorant (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hquotient : ContinuousOn
        (fun t => deriv center t / gap t ^ 2) (Icc a b) :=
      (hsmooth.continuous_deriv (by norm_num)).continuousOn.div
        (((continuous_const.sub hsmooth.continuous).add continuous_const).pow 2).continuousOn
        (fun t ht => pow_ne_zero 2 (hgap_pos t ht).ne')
    exact continuousOn_const.mul hquotient
  have hmain := intervalIntegral.integral_mono_on hab hmass_int
    hmajorant_cont.intervalIntegrable hpointwise
  have hintegral := integral_deriv_div_center_gap_sq center hsmooth hab hr hmono
  have hfactor : 0 ≤ 2 * C * weight :=
    mul_nonneg (mul_nonneg (by norm_num) hC) hweight
  calc
    (∫ t in a..b, tailMass t) ≤ ∫ t in a..b, majorant t := hmain
    _ = (2 * C * weight) *
        ∫ t in a..b, deriv center t / (center b - center t + r) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = (2 * C * weight) *
        (1 / r - 1 / (center b - center a + r)) := by
      rw [hintegral]
    _ ≤ (2 * C * weight) * (1 / r) := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      exact sub_le_self _
        (one_div_nonneg.mpr (hgap_pos a ⟨le_rfl, hab⟩).le)
    _ = 2 * C * weight / r := by ring

theorem integral_tail_le_of_center_gap_sq_from_left
    (center tailMass energy : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 1 center)
    {a b r C weight : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hC : 0 ≤ C) (hweight : 0 ≤ weight)
    (hmono : MonotoneOn center (Icc a b))
    (hmass_int : IntervalIntegrable tailMass volume a b)
    (htail : ∀ t ∈ Icc a b,
      (center t - center a + r) ^ 2 * tailMass t ≤ C * energy t)
    (henergy : ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * energy t ≤ weight * deriv center t) :
    (∫ t in a..b, tailMass t) ≤ 2 * C * weight / r := by
  let gap : ℝ → ℝ := fun t => center t - center a + r
  let majorant : ℝ → ℝ := fun t =>
    2 * C * weight * (deriv center t / gap t ^ 2)
  have hgap_pos : ∀ t ∈ Icc a b, 0 < gap t := by
    intro t ht
    have hle := hmono ⟨le_rfl, hab⟩ ht ht.1
    dsimp only [gap]
    linarith
  have hpointwise : ∀ t ∈ Icc a b, tailMass t ≤ majorant t := by
    intro t ht
    have hscaled : C * energy t ≤ 2 * C * weight * deriv center t := by
      calc
        C * energy t = (2 * C) * ((1 / 2 : ℝ) * energy t) := by ring
        _ ≤ (2 * C) * (weight * deriv center t) :=
          mul_le_mul_of_nonneg_left (henergy t ht)
            (mul_nonneg (by norm_num) hC)
        _ = 2 * C * weight * deriv center t := by ring
    have hproduct :
        gap t ^ 2 * tailMass t ≤ 2 * C * weight * deriv center t := by
      simpa only [gap] using (htail t ht).trans hscaled
    have hdiv :
        tailMass t ≤ (2 * C * weight * deriv center t) / gap t ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (hgap_pos t ht))).2
      calc
        tailMass t * gap t ^ 2 = gap t ^ 2 * tailMass t := by ring
        _ ≤ 2 * C * weight * deriv center t := hproduct
    calc
      tailMass t ≤ (2 * C * weight * deriv center t) / gap t ^ 2 := hdiv
      _ = majorant t := by
        dsimp only [majorant]
        ring
  have hmajorant_cont : ContinuousOn majorant (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hquotient : ContinuousOn
        (fun t => deriv center t / gap t ^ 2) (Icc a b) :=
      (hsmooth.continuous_deriv (by norm_num)).continuousOn.div
        (((hsmooth.continuous.sub continuous_const).add continuous_const).pow 2).continuousOn
        (fun t ht => pow_ne_zero 2 (hgap_pos t ht).ne')
    exact continuousOn_const.mul hquotient
  have hmain := intervalIntegral.integral_mono_on hab hmass_int
    hmajorant_cont.intervalIntegrable hpointwise
  have hintegral := integral_deriv_div_center_gap_sq_from_left
    center hsmooth hab hr hmono
  have hfactor : 0 ≤ 2 * C * weight :=
    mul_nonneg (mul_nonneg (by norm_num) hC) hweight
  calc
    (∫ t in a..b, tailMass t) ≤ ∫ t in a..b, majorant t := hmain
    _ = (2 * C * weight) *
        ∫ t in a..b, deriv center t / (center t - center a + r) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = (2 * C * weight) *
        (1 / r - 1 / (center b - center a + r)) := by
      rw [hintegral]
    _ ≤ (2 * C * weight) * (1 / r) := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      exact sub_le_self _
        (one_div_nonneg.mpr (hgap_pos b ⟨hab, le_rfl⟩).le)
    _ = 2 * C * weight / r := by ring

theorem shifted_log_mass_monotone_on
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ}
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    MonotoneOn (shiftedLogMass (I := I) (M := M) g cutoff u hu hpos)
      (Icc a b) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun t =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  let shifted : ℝ → ℝ := fun t => mass t + t * source
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hshifted_smooth : ContDiff ℝ ∞ shifted :=
    hmass_smooth.add (contDiff_id.mul contDiff_const)
  have hmono : MonotoneOn shifted (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      hshifted_smooth.continuous.continuousOn
      (hshifted_smooth.differentiable (by simp)).differentiableOn
    intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    have hdiff := log_energy_differential_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos t (hpde t ht')
    have henergy := localizedDirichletEnergy_nonneg
      (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
    have hmass_deriv : HasDerivAt mass (deriv mass t) t :=
      (hmass_smooth.differentiable (by simp) t).hasDerivAt
    have hshifted_deriv : HasDerivAt shifted (deriv mass t + source) t := by
      simpa only [one_mul, id_eq] using
        hmass_deriv.add ((hasDerivAt_id t).mul_const source)
    rw [hshifted_deriv.deriv]
    change (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
      deriv mass t + source at hdiff
    linarith
  simpa only [shiftedLogMass, hlog, mass, source, shifted] using hmono

theorem shifted_log_center_monotone_on
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ}
    (hmass : 0 < cutoffMass (I := I) (M := M) cutoff)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    MonotoneOn (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos)
      (Icc a b) := by
  have hmono := shifted_log_mass_monotone_on
    (I := I) (M := M) g cutoff u hu hpos hpde
  intro s hs t ht hst
  exact (div_le_div_iff_of_pos_right hmass).2 (hmono hs ht hst)

theorem half_localized_dirichlet_energy_le_shifted_log_center_deriv
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hmass : 0 < cutoffMass (I := I) (M := M) cutoff)
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) ≤
      cutoffMass (I := I) (M := M) cutoff *
        deriv (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos) t := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun s =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hmass_deriv : HasDerivAt mass (deriv mass t) t :=
    (hmass_smooth.differentiable (by simp) t).hasDerivAt
  have hshifted_deriv :
      HasDerivAt (fun s => mass s + s * source) (deriv mass t + source) t := by
    simpa only [one_mul, id_eq] using
      hmass_deriv.add ((hasDerivAt_id t).mul_const source)
  have hcenter_deriv :
      HasDerivAt (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos)
        ((deriv mass t + source) /
          cutoffMass (I := I) (M := M) cutoff) t := by
    simpa only [shiftedLogCenter, shiftedLogMass, mass, source] using
      hshifted_deriv.div_const (cutoffMass (I := I) (M := M) cutoff)
  have hdiff := log_energy_differential_of_supersolution
    (I := I) (M := M) g cutoff u hu hpos t hpde
  change (1 / 2 : ℝ) *
      localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
    deriv mass t + source at hdiff
  rw [hcenter_deriv.deriv]
  calc
    (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
      deriv mass t + source := hdiff
    _ = cutoffMass (I := I) (M := M) cutoff *
        ((deriv mass t + source) /
          cutoffMass (I := I) (M := M) cutoff) := by
      field_simp [hmass.ne']

theorem early_log_superlevel_tail_with_center_gap_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ s r : ℝ}
    (haτ : a ≤ τ)
    (hs : s ∈ Icc a τ)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s + r) ^ 2 *
        localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff + r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center := localizedAverage (I := I) (M := M) averagingCutoff w
  let gap := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s + r
  let level := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff + r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : center + gap ≤ level := by
    dsimp only [center, gap, level, w, hlog]
    rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
      u hu hpos s]
    ring_nf
    exact le_rfl
  exact (localized_superlevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hgap hlevel).trans (hP w)

theorem late_log_sublevel_tail_with_center_gap_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b s r : ℝ}
    (hτb : τ ≤ b)
    (hs : s ∈ Icc τ b)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s -
          shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ + r) ^ 2 *
        localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff - r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center := localizedAverage (I := I) (M := M) averagingCutoff w
  let gap := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s -
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ + r
  let level := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff - r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : level ≤ center - gap := by
    dsimp only [center, gap, level, w, hlog]
    rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
      u hu hpos s]
    ring_nf
    exact le_rfl
  exact (localized_sublevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hgap hlevel).trans (hP w)

theorem integrated_early_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in a..τ,
        localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff + r)) ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let hlog := contMDiff_log_of_pos hu hpos
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos
  let level : ℝ → ℝ := fun s => center τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff + r
  let tailMass : ℝ → ℝ := fun s =>
    localizedSuperlevelMass (I := I) (M := M) deviationCutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
      (level s)
  let energy : ℝ → ℝ := fun s =>
    localizedDirichletEnergy (I := I) (M := M) averagingCutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
  have hcenter_smooth : ContDiff ℝ 1 center :=
    (contDiff_shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos).of_le (by simp)
  have hcenter_mono : MonotoneOn center (Icc a τ) :=
    shifted_log_center_monotone_on
      (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (continuous_id.mul continuous_const) |>.add continuous_const
  have htail_int : IntervalIntegrable tailMass volume a τ := by
    simpa only [tailMass, level, center, hlog] using
      intervalIntegrable_localizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) hlog level hlevel_cont a τ
  have htail : ∀ s ∈ Icc a τ,
      (center τ - center s + r) ^ 2 * tailMass s ≤ C * energy s := by
    intro s hs
    simpa only [center, tailMass, energy, level, hlog] using
      early_log_superlevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff C hP
          u hu hpos haτ hs hr.le hmass hpde
  have henergy : ∀ s ∈ Icc a τ,
      (1 / 2 : ℝ) * energy s ≤
        cutoffMass (I := I) (M := M) averagingCutoff * deriv center s := by
    intro s hs
    simpa only [energy, center, hlog] using
      half_localized_dirichlet_energy_le_shifted_log_center_deriv
        (I := I) (M := M) g averagingCutoff u hu hpos hmass s (hpde s hs)
  simpa only [tailMass, level, center, hlog] using
    integral_tail_le_of_center_gap_sq center tailMass energy hcenter_smooth
      haτ hr hC hmass.le hcenter_mono htail_int htail henergy

theorem integrated_late_log_sublevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in τ..b,
        localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff - r)) ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let hlog := contMDiff_log_of_pos hu hpos
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos
  let level : ℝ → ℝ := fun s => center τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff - r
  let tailMass : ℝ → ℝ := fun s =>
    localizedSublevelMass (I := I) (M := M) deviationCutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
      (level s)
  let energy : ℝ → ℝ := fun s =>
    localizedDirichletEnergy (I := I) (M := M) averagingCutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
  have hcenter_smooth : ContDiff ℝ 1 center :=
    (contDiff_shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos).of_le (by simp)
  have hcenter_mono : MonotoneOn center (Icc τ b) :=
    shifted_log_center_monotone_on
      (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (continuous_id.mul continuous_const) |>.sub continuous_const
  have htail_int : IntervalIntegrable tailMass volume τ b := by
    simpa only [tailMass, level, center, hlog] using
      intervalIntegrable_localizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) hlog level hlevel_cont τ b
  have htail : ∀ s ∈ Icc τ b,
      (center s - center τ + r) ^ 2 * tailMass s ≤ C * energy s := by
    intro s hs
    simpa only [center, tailMass, energy, level, hlog] using
      late_log_sublevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff C hP
          u hu hpos hτb hs hr.le hmass hpde
  have henergy : ∀ s ∈ Icc τ b,
      (1 / 2 : ℝ) * energy s ≤
        cutoffMass (I := I) (M := M) averagingCutoff * deriv center s := by
    intro s hs
    simpa only [energy, center, hlog] using
      half_localized_dirichlet_energy_le_shifted_log_center_deriv
        (I := I) (M := M) g averagingCutoff u hu hpos hmass s (hpde s hs)
  simpa only [tailMass, level, center, hlog] using
    integral_tail_le_of_center_gap_sq_from_left center tailMass energy hcenter_smooth
      hτb hr hC hmass.le hcenter_mono htail_int htail henergy

theorem integrated_early_centered_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in a..τ,
        localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g
            (fun q x => Real.log
              (exponentialTimeRescale
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u q x))
            (contMDiff_log_of_pos
              (contMDiff_exponentialTimeRescale
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u hu)
              (exponentialTimeRescale_pos
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u hpos)) s) r) ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  have hpointwise : ∀ s,
      localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g
            (fun q x => Real.log (exponentialTimeRescale rate center u q x))
            (contMDiff_log_of_pos
              (contMDiff_exponentialTimeRescale rate center u hu)
              (exponentialTimeRescale_pos rate center u hpos)) s) r =
        localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (center - s * rate + r) := by
    intro s
    simpa only [mul_comm] using
      localizedSuperlevelMass_log_exponentialTimeRescale
        (I := I) (M := M) g deviationCutoff rate center u hu hpos s r
  simp_rw [show logCenterDrift (I := I) (M := M) g averagingCutoff = rate from rfl,
    show shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ = center from rfl,
    hpointwise]
  exact integrated_early_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos haτ hr hmass hpde

theorem integrated_late_centered_log_sublevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (∫ s in τ..b,
        localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g
            (fun q x => Real.log
              (exponentialTimeRescale
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u q x))
            (contMDiff_log_of_pos
              (contMDiff_exponentialTimeRescale
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u hu)
              (exponentialTimeRescale_pos
                (logCenterDrift (I := I) (M := M) g averagingCutoff)
                (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                  u hu hpos τ) u hpos)) s) (-r)) ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  have hpointwise : ∀ s,
      localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g
            (fun q x => Real.log (exponentialTimeRescale rate center u q x))
            (contMDiff_log_of_pos
              (contMDiff_exponentialTimeRescale rate center u hu)
              (exponentialTimeRescale_pos rate center u hpos)) s) (-r) =
        localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (center - s * rate - r) := by
    intro s
    simpa only [mul_comm, add_neg] using
      localizedSublevelMass_log_exponentialTimeRescale
        (I := I) (M := M) g deviationCutoff rate center u hu hpos s (-r)
  simp_rw [show logCenterDrift (I := I) (M := M) g averagingCutoff = rate from rfl,
    show shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ = center from rfl,
    hpointwise]
  exact integrated_late_log_sublevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos hτb hr hmass hpde

theorem early_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ s r : ℝ}
    (haτ : a ≤ τ)
    (hs : s ∈ Icc a τ)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) deviationCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          s * logCenterDrift (I := I) (M := M) g averagingCutoff + r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center :=
    localizedAverage (I := I) (M := M) averagingCutoff w
  let level :=
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
      s * logCenterDrift (I := I) (M := M) g averagingCutoff + r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
    u hu hpos s] at hcenter_mono
  have hlevel : center + r ≤ level := by
    dsimp only [center, level, w, hlog]
    linarith
  exact (localized_superlevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hr hlevel).trans (hP w)

theorem late_log_sublevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b s r : ℝ}
    (hτb : τ ≤ b)
    (hs : s ∈ Icc τ b)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) deviationCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          s * logCenterDrift (I := I) (M := M) g averagingCutoff - r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center :=
    localizedAverage (I := I) (M := M) averagingCutoff w
  let level :=
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
      s * logCenterDrift (I := I) (M := M) g averagingCutoff - r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
    u hu hpos s] at hcenter_mono
  have hlevel : level ≤ center - r := by
    dsimp only [center, level, w, hlog]
    linarith
  exact (localized_sublevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hr hlevel).trans (hP w)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
