import DifferentialGeometry.Analysis.Parabolic.Moser.LogEnergy

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
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

def cutoffMass {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedAverage {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  localizedIntegral (I := I) (M := M) cutoff u /
    cutoffMass (I := I) (M := M) cutoff

def localizedL2Deviation {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 * (u.toFun x - center) ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedL2Oscillation {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  localizedL2Deviation (I := I) (M := M) cutoff u
    (localizedAverage (I := I) (M := M) cutoff u)

def HasLocalizedPoincare (g : SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : SmoothScalar g) (C : ℝ) : Prop :=
  ∀ u : SmoothScalar g,
    localizedL2Oscillation (I := I) (M := M) averagingCutoff u ≤
      C * localizedDirichletEnergy (I := I) (M := M) energyCutoff u

def HasLocalizedPoincareAtAverage (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g) (C : ℝ) : Prop :=
  ∀ u : SmoothScalar g,
    localizedL2Deviation (I := I) (M := M) deviationCutoff u
        (localizedAverage (I := I) (M := M) averagingCutoff u) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff u

omit [I.Boundaryless] [CompactSpace M] in
theorem cutoff_mass_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) :
    0 ≤ cutoffMass (I := I) (M := M) cutoff := by
  exact integral_nonneg fun x => sq_nonneg (cutoff.toFun x)

omit [I.Boundaryless] [CompactSpace M] in
theorem localized_l2_oscillation_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ localizedL2Oscillation (I := I) (M := M) cutoff u := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem weighted_variance_identity (Q L m : ℝ) (hm : m ≠ 0) :
    (Q - 2 * (L / m) * L) + (L / m) ^ 2 * m = Q - L ^ 2 / m := by
  field_simp [hm]
  ring

private theorem weighted_deviation_identity (Q L m center : ℝ) (hm : m ≠ 0) :
    (Q - 2 * center * L) + center ^ 2 * m =
      (Q - L ^ 2 / m) + m * (center - L / m) ^ 2 := by
  field_simp [hm]
  ring

private theorem integral_weighted_variance
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (weight value : X → ℝ)
    (hweight : Integrable weight μ)
    (hlinear : Integrable (fun x => weight x * value x) μ)
    (hquadratic : Integrable (fun x => weight x * value x ^ 2) μ)
    (hmass : ∫ x, weight x ∂μ ≠ 0) :
    (∫ x, weight x *
        (value x - (∫ y, weight y * value y ∂μ) / (∫ y, weight y ∂μ)) ^ 2 ∂μ) =
      (∫ x, weight x * value x ^ 2 ∂μ) -
        (∫ x, weight x * value x ∂μ) ^ 2 / (∫ x, weight x ∂μ) := by
  let A := (∫ x, weight x * value x ∂μ) / (∫ x, weight x ∂μ)
  have hpointwise : (fun x => weight x * (value x - A) ^ 2) =
      (fun x => weight x * value x ^ 2 -
        2 * A * (weight x * value x) + A ^ 2 * weight x) := by
    funext x
    ring
  rw [show (∫ x, weight x * value x ∂μ) / (∫ x, weight x ∂μ) = A from rfl,
    hpointwise]
  calc
    _ = (∫ x, weight x * value x ^ 2 - 2 * A * (weight x * value x) ∂μ) +
        ∫ x, A ^ 2 * weight x ∂μ :=
      integral_add (hquadratic.sub (hlinear.const_mul (2 * A)))
        (hweight.const_mul (A ^ 2))
    _ = ((∫ x, weight x * value x ^ 2 ∂μ) -
          ∫ x, 2 * A * (weight x * value x) ∂μ) +
        ∫ x, A ^ 2 * weight x ∂μ := by
      rw [integral_sub hquadratic (hlinear.const_mul (2 * A))]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]
      rw [show A = (∫ x, weight x * value x ∂μ) /
        (∫ x, weight x ∂μ) from rfl]
      exact weighted_variance_identity _ _ _ hmass

private theorem integral_weighted_deviation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (weight value : X → ℝ) (center : ℝ)
    (hweight : Integrable weight μ)
    (hlinear : Integrable (fun x => weight x * value x) μ)
    (hquadratic : Integrable (fun x => weight x * value x ^ 2) μ)
    (hmass : ∫ x, weight x ∂μ ≠ 0) :
    (∫ x, weight x * (value x - center) ^ 2 ∂μ) =
      ((∫ x, weight x * value x ^ 2 ∂μ) -
        (∫ x, weight x * value x ∂μ) ^ 2 / (∫ x, weight x ∂μ)) +
      (∫ x, weight x ∂μ) *
        (center - (∫ x, weight x * value x ∂μ) / (∫ x, weight x ∂μ)) ^ 2 := by
  have hpointwise : (fun x => weight x * (value x - center) ^ 2) =
      (fun x => weight x * value x ^ 2 -
        2 * center * (weight x * value x) + center ^ 2 * weight x) := by
    funext x
    ring
  rw [hpointwise]
  calc
    _ = (∫ x, weight x * value x ^ 2 -
          2 * center * (weight x * value x) ∂μ) +
        ∫ x, center ^ 2 * weight x ∂μ :=
      integral_add (hquadratic.sub (hlinear.const_mul (2 * center)))
        (hweight.const_mul (center ^ 2))
    _ = ((∫ x, weight x * value x ^ 2 ∂μ) -
          ∫ x, 2 * center * (weight x * value x) ∂μ) +
        ∫ x, center ^ 2 * weight x ∂μ := by
      rw [integral_sub hquadratic (hlinear.const_mul (2 * center))]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]
      exact weighted_deviation_identity _ _ _ center hmass

omit [I.Boundaryless] in
theorem localized_l2_oscillation_eq
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g)
    (hmass : cutoffMass (I := I) (M := M) cutoff ≠ 0) :
    localizedL2Oscillation (I := I) (M := M) cutoff u =
      localizedL2Mass (I := I) (M := M) cutoff u -
        localizedIntegral (I := I) (M := M) cutoff u ^ 2 /
          cutoffMass (I := I) (M := M) cutoff := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmass_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlinear_int : Integrable
      (fun x : M => cutoff.toFun x ^ 2 * u.toFun x) μ :=
    ((cutoff.smooth.continuous.pow 2).mul u.smooth.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hquadratic_int : Integrable
      (fun x : M => cutoff.toFun x ^ 2 * u.toFun x ^ 2) μ :=
    ((cutoff.smooth.continuous.pow 2).mul (u.smooth.continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simpa only [localizedL2Oscillation, localizedL2Deviation, localizedAverage,
    localizedL2Mass, localizedIntegral, cutoffMass, μ] using
    integral_weighted_variance μ (fun x : M => cutoff.toFun x ^ 2) u.toFun
      hmass_int hlinear_int hquadratic_int hmass

omit [I.Boundaryless] in
theorem localized_l2_deviation_eq_oscillation_add
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ)
    (hmass : cutoffMass (I := I) (M := M) cutoff ≠ 0) :
    localizedL2Deviation (I := I) (M := M) cutoff u center =
      localizedL2Oscillation (I := I) (M := M) cutoff u +
        cutoffMass (I := I) (M := M) cutoff *
          (center - localizedAverage (I := I) (M := M) cutoff u) ^ 2 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmass_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlinear_int : Integrable
      (fun x : M => cutoff.toFun x ^ 2 * u.toFun x) μ :=
    ((cutoff.smooth.continuous.pow 2).mul u.smooth.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hquadratic_int : Integrable
      (fun x : M => cutoff.toFun x ^ 2 * u.toFun x ^ 2) μ :=
    ((cutoff.smooth.continuous.pow 2).mul (u.smooth.continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [localized_l2_oscillation_eq (I := I) (M := M) cutoff u hmass]
  simpa only [localizedL2Deviation, localizedAverage, localizedL2Mass,
    localizedIntegral, cutoffMass, μ] using
    integral_weighted_deviation μ (fun x : M => cutoff.toFun x ^ 2) u.toFun
      center hmass_int hlinear_int hquadratic_int hmass

omit [I.Boundaryless] in
theorem localized_l2_oscillation_le_deviation
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ)
    (hmass : cutoffMass (I := I) (M := M) cutoff ≠ 0) :
    localizedL2Oscillation (I := I) (M := M) cutoff u ≤
      localizedL2Deviation (I := I) (M := M) cutoff u center := by
  rw [localized_l2_deviation_eq_oscillation_add
    (I := I) (M := M) cutoff u center hmass]
  exact le_add_of_nonneg_right
    (mul_nonneg (cutoff_mass_nonneg (I := I) (M := M) cutoff) (sq_nonneg _))

omit [I.Boundaryless] in
theorem has_localized_poincare_of_deviation
    {g : SmoothRiemannianMetric I M}
    (averagingCutoff energyCutoff : SmoothScalar g) (C : ℝ)
    (hmass : cutoffMass (I := I) (M := M) averagingCutoff ≠ 0)
    (hdeviation : ∀ u : SmoothScalar g, ∃ center : ℝ,
      localizedL2Deviation (I := I) (M := M) averagingCutoff u center ≤
        C * localizedDirichletEnergy (I := I) (M := M) energyCutoff u) :
    HasLocalizedPoincare (I := I) (M := M) g averagingCutoff energyCutoff C := by
  intro u
  obtain ⟨center, hcenter⟩ := hdeviation u
  exact (localized_l2_oscillation_le_deviation
    (I := I) (M := M) averagingCutoff u center hmass).trans hcenter

omit [I.Boundaryless] in
theorem HasLocalizedPoincareAtAverage.has_localized_poincare
    {g : SmoothRiemannianMetric I M}
    {deviationCutoff averagingCutoff : SmoothScalar g} {C : ℝ}
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (hmass : cutoffMass (I := I) (M := M) deviationCutoff ≠ 0) :
    HasLocalizedPoincare (I := I) (M := M) g
      deviationCutoff averagingCutoff C := by
  intro u
  exact (localized_l2_oscillation_le_deviation
    (I := I) (M := M) deviationCutoff u
      (localizedAverage (I := I) (M := M) averagingCutoff u) hmass).trans (hP u)

omit [I.Boundaryless] in
theorem cont_diff_localized_l2_oscillation
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hmass : cutoffMass (I := I) (M := M) cutoff ≠ 0) :
    ContDiff ℝ ∞
      (fun t => localizedL2Oscillation (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  have hformula : ∀ t : ℝ,
      localizedL2Oscillation (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) =
        localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) -
          localizedIntegral (I := I) (M := M) cutoff
              (smoothScalarSlice (I := I) g u hu t) ^ 2 /
            cutoffMass (I := I) (M := M) cutoff := fun t =>
    localized_l2_oscillation_eq (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t) hmass
  rw [funext hformula]
  exact (contDiff_localizedL2Mass (I := I) (M := M) cutoff u hu).sub
    ((contDiff_localizedIntegral (I := I) (M := M) cutoff u hu).pow 2
      |>.div_const _)

theorem integrated_localized_l2_oscillation_of_log_supersolution
    (g : SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : SmoothScalar g)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hmass : cutoffMass (I := I) (M := M) averagingCutoff ≠ 0)
    (hP : HasLocalizedPoincare (I := I) (M := M) g
      averagingCutoff energyCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ} (hab : a ≤ b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ∫ t in a..b,
        localizedL2Oscillation (I := I) (M := M) averagingCutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) ≤
      2 * C *
        (localizedIntegral (I := I) (M := M) energyCutoff
            (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
              (contMDiff_log_of_pos hu hpos) b) -
          localizedIntegral (I := I) (M := M) energyCutoff
            (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
              (contMDiff_log_of_pos hu hpos) a) +
          2 * (b - a) * cutoffDirichletEnergy (I := I) (M := M) energyCutoff) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let oscillation : ℝ → ℝ := fun t =>
    localizedL2Oscillation (I := I) (M := M) averagingCutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let energy : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) energyCutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  have hoscillation_cont : ContinuousOn oscillation (Icc a b) :=
    (cont_diff_localized_l2_oscillation (I := I) (M := M) averagingCutoff
      (fun s x => Real.log (u s x)) hlog hmass).continuous.continuousOn
  have henergy_cont : ContinuousOn energy (Icc a b) :=
    (contDiff_localizedDirichletEnergy (I := I) (M := M) energyCutoff
      (fun s x => Real.log (u s x)) hlog).continuous.continuousOn
  have hpointwise : ∀ t ∈ Icc a b, oscillation t ≤ C * energy t := by
    intro t _
    exact hP _
  have hoscillation_cont_u : ContinuousOn oscillation (uIcc a b) := by
    simpa [uIcc_of_le hab] using hoscillation_cont
  have henergy_cont_u : ContinuousOn (fun t => C * energy t) (uIcc a b) := by
    simpa [uIcc_of_le hab] using henergy_cont.const_mul C
  have hoscillation_int : IntervalIntegrable oscillation volume a b :=
    hoscillation_cont_u.intervalIntegrable
  have henergy_int : IntervalIntegrable (fun t => C * energy t) volume a b :=
    henergy_cont_u.intervalIntegrable
  have hintegral := intervalIntegral.integral_mono_on hab
    hoscillation_int henergy_int hpointwise
  have hlog_energy := log_energy_of_supersolution
    (I := I) (M := M) g energyCutoff u hu hpos hab hpde
  have htwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  have hscaled := mul_le_mul_of_nonneg_left hlog_energy htwoC
  dsimp only [oscillation, energy] at hintegral
  rw [intervalIntegral.integral_const_mul] at hintegral
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.Moser

end
