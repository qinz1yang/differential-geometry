import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingPower
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness
import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

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

def evolvingMoserLocalizedMass
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) (p₀ a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  ∫ t in moserTimeLevel a τ k..t₁,
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 *
      u t x ^ parabolicMoserExponent n p₀ k
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingMoserNormalizedMass
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) (p₀ a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  evolvingMoserLocalizedMass (I := I) (M := M) n g rho u p₀ a τ t₁ k ^
    (1 / parabolicMoserExponent n p₀ k)

def evolvingMoserSpatialGradientCost (G : ℝ) (k : ℕ) : ℝ :=
  G * 4 ^ (2 * k)

def evolvingMoserStepCoefficient
    (G B a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  (t₁ - moserTimeLevel a τ (k + 1) + 1) *
      (moserTimeDerivativeCost a τ k +
        4 * evolvingMoserSpatialGradientCost G k + (1 / 2) * B) +
    evolvingMoserSpatialGradientCost G k

def evolvingMoserStepConstant (G B a τ t₁ : ℝ) : ℝ :=
  (t₁ - a + 1) *
      (2 * timeCutoffDerivConstant / (τ - a) + 4 * G + (1 / 2) * B) + G

def evolvingMoserLocalBoundFactor
    (n : ℕ) (C G B p₀ a τ t₁ : ℝ) : ℝ :=
  Real.exp
    (∑' j, moserIterationCost (parabolicMoserDecay n)
      ((parabolicMoserDecay n * Real.log (max 1 C) +
          Real.log (max 1 (evolvingMoserStepConstant G B a τ t₁))) / p₀)
      (Real.log 16 / p₀) j)

def evolvingMoserLocalBound
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) (C G B p₀ a τ t₁ : ℝ) : ℝ :=
  evolvingMoserLocalBoundFactor n C G B p₀ a τ t₁ *
    evolvingMoserNormalizedMass
      (I := I) (M := M) n g rho u p₀ a τ t₁ 0

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingMoserLocalizedMass_nonneg
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) {p₀ a τ t₁ : ℝ}
    (haτ : a < τ) (hτt₁ : τ ≤ t₁) (hu : ∀ t x, 0 ≤ u t x) (k : ℕ) :
    0 ≤ evolvingMoserLocalizedMass
      (I := I) (M := M) n g rho u p₀ a τ t₁ k := by
  apply intervalIntegral.integral_nonneg
  · exact (moserTimeLevel_lt haτ k).le.trans hτt₁
  · intro t _
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hu t x) _)

omit [I.Boundaryless] in
theorem moserLocalizedMass_le_toReal_mul_evolvingMoserLocalizedMass
    (n : ℕ)
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ s₀ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (k : ℕ)
    (hvolume : ∀ t ∈ Icc (moserTimeLevel a τ k) t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    moserLocalizedMass (I := I) (M := M) n rho u p₀ a τ t₁ k ≤
      C.toReal * evolvingMoserLocalizedMass
        (I := I) (M := M) n g rho u p₀ a τ t₁ k := by
  let lower := moserTimeLevel a τ k
  let p := parabolicMoserExponent n p₀ k
  let fixed : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
      ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let moving : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  letI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  have hlower : lower ≤ t₁ :=
    (moserTimeLevel_lt haτ k).le.trans hτt₁
  have hintegrand : Continuous (fun z : ℝ × M =>
      (spatialMoserCutoff rho (2 * k)).toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((spatialMoserCutoff rho (2 * k)).smooth.continuous.comp
      continuous_snd).pow 2 |>.mul
        (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))
  have hfixed_cont : ContinuousOn fixed (Icc lower t₁) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc lower t₁)
      (riemannianVolumeMeasure (I := I) (M := M) q)
      (fun t x => (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hintegrand.continuousOn
    simpa only [fixed] using h
  have hmoving_cont : ContinuousOn moving (Icc lower t₁) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hintegrand.continuousOn
  have hfixed_int : IntervalIntegrable fixed volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hfixed_cont
  have hmoving_int : IntervalIntegrable moving volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hmoving_cont
  have hpoint : ∀ t ∈ Icc lower t₁, fixed t ≤ C.toReal * moving t := by
    intro t ht
    let μ := riemannianMeasureFamily (I := I) (M := M) g t
    letI : IsFiniteMeasure μ := by
      dsimp only [μ, riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    let f : M → ℝ := fun x =>
      (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
    have hf_cont : Continuous f :=
      ((spatialMoserCutoff rho (2 * k)).smooth.continuous.pow 2).mul
        ((hu.continuous.comp (continuous_const.prodMk continuous_id)).rpow_const
          (fun x => Or.inl (hpos t x).ne'))
    have hf_int : Integrable f (C • μ) :=
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure (hvolume t ht)
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (hpos t x).le _)) hf_int
    rw [integral_smul_measure] at hmono
    simpa only [fixed, moving, μ, f, smul_eq_mul] using hmono
  have hmono : (∫ t in lower..t₁, fixed t) ≤
      ∫ t in lower..t₁, C.toReal * moving t :=
    intervalIntegral.integral_mono_on hlower hfixed_int
      (hmoving_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [moserLocalizedMass, evolvingMoserLocalizedMass,
    fixed, moving, lower, p] using hmono

omit [I.Boundaryless] in
theorem evolvingMoserLocalizedMass_le_toReal_mul_moserLocalizedMass
    (n : ℕ)
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ s₀ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (k : ℕ)
    (hvolume : ∀ t ∈ Icc (moserTimeLevel a τ k) t₁,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        C • riemannianVolumeMeasure (I := I) (M := M) q) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) n g rho u p₀ a τ t₁ k ≤
      C.toReal * moserLocalizedMass
        (I := I) (M := M) n rho u p₀ a τ t₁ k := by
  let lower := moserTimeLevel a τ k
  let p := parabolicMoserExponent n p₀ k
  let fixed : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
      ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let moving : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  letI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  have hlower : lower ≤ t₁ :=
    (moserTimeLevel_lt haτ k).le.trans hτt₁
  have hintegrand : Continuous (fun z : ℝ × M =>
      (spatialMoserCutoff rho (2 * k)).toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((spatialMoserCutoff rho (2 * k)).smooth.continuous.comp
      continuous_snd).pow 2 |>.mul
        (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))
  have hfixed_cont : ContinuousOn fixed (Icc lower t₁) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc lower t₁)
      (riemannianVolumeMeasure (I := I) (M := M) q)
      (fun t x => (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hintegrand.continuousOn
    simpa only [fixed] using h
  have hmoving_cont : ContinuousOn moving (Icc lower t₁) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hintegrand.continuousOn
  have hfixed_int : IntervalIntegrable fixed volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hfixed_cont
  have hmoving_int : IntervalIntegrable moving volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hmoving_cont
  have hpoint : ∀ t ∈ Icc lower t₁, moving t ≤ C.toReal * fixed t := by
    intro t ht
    let μ := riemannianVolumeMeasure (I := I) (M := M) q
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    let f : M → ℝ := fun x =>
      (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 * u t x ^ p
    have hf_cont : Continuous f :=
      ((spatialMoserCutoff rho (2 * k)).smooth.continuous.pow 2).mul
        ((hu.continuous.comp (continuous_const.prodMk continuous_id)).rpow_const
          (fun x => Or.inl (hpos t x).ne'))
    have hf_int : Integrable f (C • μ) :=
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure (hvolume t ht)
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (hpos t x).le _)) hf_int
    rw [integral_smul_measure] at hmono
    simpa only [fixed, moving, μ, f, smul_eq_mul] using hmono
  have hmono : (∫ t in lower..t₁, moving t) ≤
      ∫ t in lower..t₁, C.toReal * fixed t :=
    intervalIntegral.integral_mono_on hlower hmoving_int
      (hfixed_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [moserLocalizedMass, evolvingMoserLocalizedMass,
    fixed, moving, lower, p] using hmono

omit [I.Boundaryless] in
theorem evolvingMoserLocalizedMass_succ_le
    (n : ℕ) [NeZero n]
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ s₀ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hg : MetricFamilyRegularAt (I := I) g s₀) (k : ℕ) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) n g rho u p₀ a τ t₁ (k + 1) ≤
      ∫ t in moserTimeLevel a τ (k + 1)..t₁,
        ∫ x,
          |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
              u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^
            (2 + 4 / (n : ℝ))
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let lower := moserTimeLevel a τ (k + 1)
  let p := parabolicMoserExponent n p₀ (k + 1)
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  let right : ℝ → ℝ := fun t =>
    ∫ x, |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
      u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcritical : 0 ≤ critical := by
    dsimp only [critical]
    positivity
  have hleft_joint : Continuous (fun z : ℝ × M =>
      (spatialMoserCutoff rho (2 * (k + 1))).toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.comp
      continuous_snd).pow 2 |>.mul
        (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))
  have hright_base : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)|) :=
    (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.comp continuous_snd).mul
      (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))).abs
  have hright_joint : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
    hright_base.rpow_const (fun _ => Or.inr hcritical)
  have hlower : lower ≤ t₁ := by
    dsimp only [lower]
    exact (moserTimeLevel_lt haτ (k + 1)).le.trans hτt₁
  have hleft_cont : ContinuousOn left (Icc lower t₁) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hleft_joint.continuousOn
  have hright_cont : ContinuousOn right (Icc lower t₁) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hright_joint.continuousOn
  have hleft_int : IntervalIntegrable left volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hleft_cont
  have hright_int : IntervalIntegrable right volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hright_cont
  have hpoint : ∀ t ∈ Icc lower t₁, left t ≤ right t := by
    intro t _
    letI : IsFiniteMeasure
        (riemannianMeasureFamily (I := I) (M := M) g t) := by
      dsimp only [riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
    have hu_slice : Continuous (u t) :=
      hu.continuous.comp (continuous_const.prodMk continuous_id)
    have hleft_slice : Continuous (fun x : M =>
        (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p) :=
      ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.pow 2).mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))
    have hright_slice : Continuous (fun x : M =>
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
      (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))).abs).rpow_const
          (fun _ => Or.inr hcritical)
    apply integral_mono
      (hleft_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    have heta := spatialMoserCutoff_add_two_sq_le_rpow
      rho (2 * k) x critical
    have hu_pow : 0 ≤ u t x ^ p := Real.rpow_nonneg (hpos t x).le p
    have hidentity := abs_mul_rpow_half_critical n
      (spatialMoserCutoff_mem_Icc rho (2 * k + 1) x).1 (hpos t x) k
      (p₀ := p₀)
    change
      (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p ≤
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    calc
      _ ≤ (spatialMoserCutoff rho (2 * k + 1)).toFun x ^ critical *
          u t x ^ p := mul_le_mul_of_nonneg_right heta hu_pow
      _ = _ := by simpa only [p, critical] using hidentity.symm
  have htime := intervalIntegral.integral_mono_on hlower hleft_int hright_int hpoint
  simpa only [evolvingMoserLocalizedMass, left, right, lower, p, critical] using htime

theorem evolvingMoserLocalizedMass_succ_le_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (k : ℕ)
    (hgradient : ∀ t ∈ Icc a t₁, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ (k + 1) ≤
      C * (evolvingMoserStepCoefficient G B a τ t₁ k *
        evolvingMoserLocalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ k) ^
        parabolicMoserGain (Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p := parabolicMoserExponent n p₀ k
  let exponent := p / 2
  let L := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho u p₀ a τ t₁ k
  let D := moserTimeDerivativeCost a τ k
  let K := evolvingMoserSpatialGradientCost G k
  have hp₀_nonneg : 0 ≤ p₀ := (by norm_num : (0 : ℝ) ≤ 2).trans hp₀
  have hp : 2 ≤ p := by
    dsimp only [p, parabolicMoserExponent]
    calc
      2 ≤ p₀ := hp₀
      _ = p₀ * 1 := (mul_one p₀).symm
      _ ≤ p₀ * parabolicMoserGain n ^ k :=
        mul_le_mul_of_nonneg_left
          (one_le_pow₀ (one_lt_parabolicMoserGain n).le) hp₀_nonneg
  have hexponent : 1 ≤ exponent := by
    dsimp only [exponent]
    linarith
  have hL : 0 ≤ L := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho u haτ hτt₁
      (fun t x => (hpos t x).le) k
  have hD : 0 ≤ D := moserTimeDerivativeCost_nonneg haτ k
  have hK : 0 ≤ K := by
    exact mul_nonneg hG (pow_nonneg (by norm_num) _)
  have hbridge := evolvingMoserLocalizedMass_succ_le
    (I := I) (M := M) n g rho u hu hpos
      (p₀ := p₀) haτ hτt₁ hg k
  have hstep := evolving_rpow_moser_step_homogeneous_le
    (I := I) (M := M) g hdim
      (spatialMoserCutoff rho (2 * k + 1)).toFun
      (spatialMoserCutoff rho (2 * k)).toFun
      (spatialMoserCutoff rho (2 * k + 1)).smooth
      (spatialMoserCutoff rho (2 * k)).smooth u hu hpos hexponent hg hgram hC
      (fun t ht => hSobolev t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩)
      (moserTimeLevel_lt_succ haτ k)
      ((moserTimeLevel_lt haτ (k + 1)).le.trans hτt₁)
      hB hD hK hL
      (fun t ht x => hpde t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (fun x => by
        simpa only [Nat.add_assoc] using
          spatialMoserCutoff_succ_sq_le rho (2 * k) x)
      (fun t ht x => hgradient t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (fun t _ => by
        simpa only [D, moserTimeDerivativeCost] using
          timeCutoffDeriv_moserTimeLevel_le_mul_pow haτ k t)
      (fun t ht x => htrace t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (by
        have heq :
            (∫ t in moserTimeLevel a τ k..t₁,
              evolvingLocalizedL2Mass (I := I) (M := M) g
                (spatialMoserCutoff rho (2 * k)).toFun
                (fun s x => u s x ^ exponent) t) = L := by
          dsimp only [L]
          rw [evolvingMoserLocalizedMass]
          apply intervalIntegral.integral_congr
          intro t _
          simp only [evolvingLocalizedL2Mass]
          apply integral_congr_ae
          filter_upwards with x
          change _ * (u t x ^ exponent) ^ 2 = _ * u t x ^ p
          dsimp only [exponent]
          congr 1
          rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
            ← Real.rpow_mul (hpos t x).le]
          congr 1
          ring
        exact heq.le)
  calc
    evolvingMoserLocalizedMass
          (I := I) (M := M) n g rho u p₀ a τ t₁ (k + 1) ≤
        ∫ t in moserTimeLevel a τ (k + 1)..t₁,
          ∫ x,
            |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
                u t x ^ exponent| ^ (2 + 4 / (n : ℝ))
            ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
      simpa only [n, exponent, p] using hbridge
    _ ≤ C * (((t₁ - moserTimeLevel a τ (k + 1) + 1) *
          ((D + 4 * K + (1 / 2) * B) * L) + K * L) ^
          (1 + 2 / (n : ℝ))) := by
      simpa only [exponent, n] using hstep
    _ = C * (evolvingMoserStepCoefficient G B a τ t₁ k * L) ^
          parabolicMoserGain n := by
      congr 2
      · rw [evolvingMoserStepCoefficient]
        change
          (t₁ - moserTimeLevel a τ (k + 1) + 1) *
                ((D + 4 * K + (1 / 2) * B) * L) + K * L =
            ((t₁ - moserTimeLevel a τ (k + 1) + 1) *
                (D + 4 * K + (1 / 2) * B) + K) * L
        ring

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem evolvingMoserStepCoefficient_nonneg
    {G B a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hG : 0 ≤ G) (hB : 0 ≤ B) (k : ℕ) :
    0 ≤ evolvingMoserStepCoefficient G B a τ t₁ k := by
  have hduration : 0 ≤ t₁ - moserTimeLevel a τ (k + 1) + 1 := by
    linarith [moserTimeLevel_lt haτ (k + 1)]
  exact add_nonneg
    (mul_nonneg hduration
      (add_nonneg
        (add_nonneg (moserTimeDerivativeCost_nonneg haτ k)
          (mul_nonneg (by norm_num)
            (mul_nonneg hG (pow_nonneg (by norm_num) _))))
        (mul_nonneg (by norm_num) hB)))
    (mul_nonneg hG (pow_nonneg (by norm_num) _))

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem evolvingMoserStepConstant_nonneg
    {G B a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hG : 0 ≤ G) (hB : 0 ≤ B) :
    0 ≤ evolvingMoserStepConstant G B a τ t₁ := by
  have hduration : 0 ≤ t₁ - a + 1 := by linarith
  exact add_nonneg
    (mul_nonneg hduration
      (add_nonneg
        (add_nonneg
          (div_nonneg
            (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
            (sub_pos.mpr haτ).le)
          (mul_nonneg (by norm_num) hG))
        (mul_nonneg (by norm_num) hB))) hG

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem evolvingMoserStepCoefficient_le
    {G B a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hG : 0 ≤ G) (hB : 0 ≤ B) (k : ℕ) :
    evolvingMoserStepCoefficient G B a τ t₁ k ≤
      evolvingMoserStepConstant G B a τ t₁ * 16 ^ k := by
  let D := 2 * timeCutoffDerivConstant / (τ - a)
  have hD : 0 ≤ D := by
    exact div_nonneg
      (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
      (sub_pos.mpr haτ).le
  have hpow_two : (2 : ℝ) ^ k ≤ 16 ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hpow_one : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
  have hgradient : evolvingMoserSpatialGradientCost G k = G * 16 ^ k := by
    rw [evolvingMoserSpatialGradientCost]
    change G * 4 ^ (2 * k) = G * 16 ^ k
    rw [pow_mul]
    norm_num
  have htime : moserTimeDerivativeCost a τ k = D * 2 ^ k := rfl
  have hduration_nonneg : 0 ≤ t₁ - moserTimeLevel a τ (k + 1) + 1 := by
    linarith [moserTimeLevel_lt haτ (k + 1)]
  have hduration_le :
      t₁ - moserTimeLevel a τ (k + 1) + 1 ≤ t₁ - a + 1 := by
    linarith [moserTimeLevel_le haτ (k + 1)]
  have hduration_max_nonneg : 0 ≤ t₁ - a + 1 := by linarith
  have hcost_le :
      D * 2 ^ k + 4 * (G * 16 ^ k) + (1 / 2) * B ≤
        (D + 4 * G + (1 / 2) * B) * 16 ^ k := by
    have hDterm : D * 2 ^ k ≤ D * 16 ^ k :=
      mul_le_mul_of_nonneg_left hpow_two hD
    have hBterm : (1 / 2) * B ≤ ((1 / 2) * B) * 16 ^ k := by
      calc
        (1 / 2) * B = ((1 / 2) * B) * 1 := (mul_one _).symm
        _ ≤ ((1 / 2) * B) * 16 ^ k :=
          mul_le_mul_of_nonneg_left hpow_one
            (mul_nonneg (by norm_num) hB)
    calc
      D * 2 ^ k + 4 * (G * 16 ^ k) + (1 / 2) * B ≤
          D * 16 ^ k + 4 * (G * 16 ^ k) + ((1 / 2) * B) * 16 ^ k := by
        exact add_le_add (add_le_add hDterm le_rfl) hBterm
      _ = (D + 4 * G + (1 / 2) * B) * 16 ^ k := by ring
  rw [evolvingMoserStepCoefficient, evolvingMoserStepConstant, htime, hgradient]
  change
    (t₁ - moserTimeLevel a τ (k + 1) + 1) *
          (D * 2 ^ k + 4 * (G * 16 ^ k) + (1 / 2) * B) + G * 16 ^ k ≤
      ((t₁ - a + 1) * (D + 4 * G + (1 / 2) * B) + G) * 16 ^ k
  calc
    _ ≤ (t₁ - a + 1) *
          ((D + 4 * G + (1 / 2) * B) * 16 ^ k) + G * 16 ^ k := by
      gcongr
    _ = ((t₁ - a + 1) * (D + 4 * G + (1 / 2) * B) + G) * 16 ^ k := by
      ring

theorem evolvingMoserLocalizedMass_succ_le_majorant
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (k : ℕ) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ (k + 1) ≤
      max 1 C *
        ((max 1 (evolvingMoserStepConstant G B a τ t₁) * 16 ^ k) *
          evolvingMoserLocalizedMass
            (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ k) ^
          parabolicMoserGain (Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let A := evolvingMoserStepConstant G B a τ t₁
  let coefficient := evolvingMoserStepCoefficient G B a τ t₁ k
  let L := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho u p₀ a τ t₁ k
  let gain := parabolicMoserGain n
  have hA : 0 ≤ A := evolvingMoserStepConstant_nonneg haτ hτt₁ hG hB
  have hcoefficient : 0 ≤ coefficient :=
    evolvingMoserStepCoefficient_nonneg haτ hτt₁ hG hB k
  have hL : 0 ≤ L := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho u haτ hτt₁
      (fun t x => (hpos t x).le) k
  have hgain : 0 ≤ gain := (parabolicMoserGain_pos n).le
  have hcoefficient_le : coefficient ≤ A * 16 ^ k :=
    evolvingMoserStepCoefficient_le haτ hτt₁ hG hB k
  have hA_le : A * 16 ^ k * L ≤ max 1 A * 16 ^ k * L := by
    gcongr
    exact le_max_right 1 A
  have hfirst := evolvingMoserLocalizedMass_succ_le_of_subsolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτt₁ hB hC hG
      hg hgram hSobolev hpde htrace k (fun t ht x => hgradient k t ht x)
  calc
    _ ≤ C * (coefficient * L) ^ gain := by
      simpa only [n, coefficient, L, gain] using hfirst
    _ ≤ C * (A * 16 ^ k * L) ^ gain := by gcongr
    _ ≤ max 1 C * (A * 16 ^ k * L) ^ gain := by
      gcongr
      exact le_max_right 1 C
    _ ≤ max 1 C * ((max 1 A * 16 ^ k) * L) ^ gain := by
      have hleft_nonneg : 0 ≤ A * 16 ^ k * L := by positivity
      have hrpow := Real.rpow_le_rpow hleft_nonneg hA_le hgain
      exact mul_le_mul_of_nonneg_left hrpow
        ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 C))
    _ = _ := by simp only [n, A, L, gain]

theorem evolvingMoserNormalizedMass_succ_le_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (k : ℕ) :
    evolvingMoserNormalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ (k + 1) ≤
      Real.exp
          (moserIterationCost (parabolicMoserDecay (Module.finrank ℝ E))
            ((parabolicMoserDecay (Module.finrank ℝ E) *
                Real.log (max 1 C) +
                Real.log (max 1 (evolvingMoserStepConstant G B a τ t₁))) / p₀)
            (Real.log 16 / p₀) k) *
        evolvingMoserNormalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let S := max 1 C
  let A := max 1 (evolvingMoserStepConstant G B a τ t₁)
  let L := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho u p₀ a τ t₁ k
  let L' := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho u p₀ a τ t₁ (k + 1)
  have hp₀pos : 0 < p₀ := lt_of_lt_of_le (by norm_num) hp₀
  have hS : 1 ≤ S := le_max_left 1 _
  have hA : 1 ≤ A := le_max_left 1 _
  have hL : 0 ≤ L := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho u haτ hτt₁
      (fun t x => (hpos t x).le) k
  have hL' : 0 ≤ L' := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho u haτ hτt₁
      (fun t x => (hpos t x).le) (k + 1)
  have hstep := evolvingMoserLocalizedMass_succ_le_majorant
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτt₁ hB hC hG
      hg hgram hSobolev hpde htrace hgradient k
  have hnormalized := normalized_moser_step (n := n) hp₀pos hS hA hL hL' k
    (by simpa only [S, A, L, L', n] using hstep)
  simpa only [evolvingMoserNormalizedMass, n, S, A, L, L'] using hnormalized

theorem evolvingMoserNormalizedMass_le_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (k : ℕ) :
    evolvingMoserNormalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ k ≤
      Real.exp
          (∑' j, moserIterationCost (parabolicMoserDecay (Module.finrank ℝ E))
            ((parabolicMoserDecay (Module.finrank ℝ E) *
                Real.log (max 1 C) +
                Real.log (max 1 (evolvingMoserStepConstant G B a τ t₁))) / p₀)
            (Real.log 16 / p₀) j) *
        evolvingMoserNormalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let theta := parabolicMoserDecay n
  let S := max 1 C
  let A := max 1 (evolvingMoserStepConstant G B a τ t₁)
  let initialCost := (theta * Real.log S + Real.log A) / p₀
  let linearCost := Real.log 16 / p₀
  let X : ℕ → ℝ := fun j =>
    evolvingMoserNormalizedMass
      (I := I) (M := M) n g rho u p₀ a τ t₁ j
  have hp₀pos : 0 < p₀ := lt_of_lt_of_le (by norm_num) hp₀
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have htheta_one : theta < 1 := parabolicMoserDecay_lt_one n
  have hS : 1 ≤ S := le_max_left 1 _
  have hA : 1 ≤ A := le_max_left 1 _
  have hinitialCost : 0 ≤ initialCost := by
    exact div_nonneg
      (add_nonneg (mul_nonneg htheta (Real.log_nonneg hS))
        (Real.log_nonneg hA)) hp₀pos.le
  have hlinearCost : 0 ≤ linearCost := by
    exact div_nonneg (Real.log_nonneg (by norm_num)) hp₀pos.le
  have hXzero : 0 ≤ X 0 := Real.rpow_nonneg
    (evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) n g rho u haτ hτt₁
        (fun t x => (hpos t x).le) 0) _
  have hstep : ∀ j, X (j + 1) ≤
      Real.exp (moserIterationCost theta initialCost linearCost j) * X j := by
    intro j
    simpa only [X, theta, initialCost, linearCost, S, A, n] using
      evolvingMoserNormalizedMass_succ_le_of_subsolution
        (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτt₁
          hB hC hG hg hgram hSobolev hpde htrace hgradient j
  have hbound := moser_iteration_bound hXzero htheta htheta_one
    hinitialCost hlinearCost hstep k
  simpa only [X, theta, initialCost, linearCost, S, A, n] using hbound

theorem evolving_local_boundedness_of_subsolution_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      u t x ≤ max 1 V.toReal *
        evolvingMoserLocalBound
          (I := I) (M := M) (Module.finrank ℝ E) g rho u
            C G B p₀ a τ t₁ := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  let ν := (volume : Measure ℝ).prod μ
  let W : Set M := {x | 1 < rho.toFun x}
  let U : Set (ℝ × M) := Ioo τ t₁ ×ˢ W
  let localBound := evolvingMoserLocalBound
    (I := I) (M := M) n g rho u C G B p₀ a τ t₁
  let volumeFactor := max 1 V.toReal
  let bound := volumeFactor * localBound
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  letI : μ.IsOpenPosMeasure := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) q
  letI : ν.IsOpenPosMeasure := by
    dsimp only [ν]
    infer_instance
  letI : IsFiniteMeasure (ν.restrict U) := by
    dsimp only [ν, U]
    rw [← Measure.prod_restrict]
    infer_instance
  have hp₀pos : 0 < p₀ := lt_of_lt_of_le (by norm_num) hp₀
  have hU : IsOpen U :=
    isOpen_Ioo.prod (isOpen_lt continuous_const rho.smooth.continuous)
  have hvolumeFactor : 1 ≤ volumeFactor := le_max_left 1 _
  have hlocalBound : 0 ≤ localBound := by
    dsimp only [localBound, evolvingMoserLocalBound]
    exact mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg
        (evolvingMoserLocalizedMass_nonneg
          (I := I) (M := M) n g rho u haτ hτt₁
            (fun t x => (hpos t x).le) 0) _)
  have hbound_nonneg : 0 ≤ bound :=
    mul_nonneg (zero_le_one.trans hvolumeFactor) hlocalBound
  have hintegrable : ∀ k,
      Integrable
        (fun z : ℝ × M => u z.1 z.2 ^ parabolicMoserExponent n p₀ k)
        (ν.restrict U) := by
    intro k
    let f : ℝ × M → ℝ := fun z =>
      u z.1 z.2 ^ parabolicMoserExponent n p₀ k
    have hf : Continuous f :=
      hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne')
    have hcompact : IsCompact (Icc τ t₁ ×ˢ (Set.univ : Set M)) :=
      isCompact_Icc.prod isCompact_univ
    have hcompact_integrable : IntegrableOn f
        (Icc τ t₁ ×ˢ (Set.univ : Set M)) ν :=
      hf.continuousOn.integrableOn_compact hcompact
    exact hcompact_integrable.mono_set fun z hz =>
      ⟨⟨hz.1.1.le, hz.1.2.le⟩, Set.mem_univ _⟩
  have hintegral : ∀ k,
      (∫ z, u z.1 z.2 ^ parabolicMoserExponent n p₀ k ∂ν.restrict U) ≤
        bound ^ parabolicMoserExponent n p₀ k := by
    intro k
    let p := parabolicMoserExponent n p₀ k
    let L := evolvingMoserLocalizedMass
      (I := I) (M := M) n g rho u p₀ a τ t₁ k
    have hp : 0 < p := parabolicMoserExponent_pos n hp₀pos k
    have hp_one : 1 ≤ p := one_le_two.trans (by
      have hp_two : 2 ≤ p := by
        dsimp only [p, parabolicMoserExponent]
        calc
          2 ≤ p₀ := hp₀
          _ = p₀ * 1 := (mul_one p₀).symm
          _ ≤ p₀ * parabolicMoserGain n ^ k :=
            mul_le_mul_of_nonneg_left
              (one_le_pow₀ (one_lt_parabolicMoserGain n).le)
              (zero_le_two.trans hp₀)
      exact hp_two)
    have hL : 0 ≤ L := evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) n g rho u haτ hτt₁
        (fun t x => (hpos t x).le) k
    have hintegral_fixed := integral_rpow_le_moserLocalizedMass
      (I := I) (M := M) n rho u hu hpos
        (p₀ := p₀) haτ hτt₁ k
    have hmass_compare := moserLocalizedMass_le_toReal_mul_evolvingMoserLocalizedMass
      (I := I) (M := M) n g rho u hu hpos
        (p₀ := p₀) haτ hτt₁ hg V hV k
      (fun t ht => hvolume t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩)
    have hnormalized := evolvingMoserNormalizedMass_le_of_subsolution
      (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτt₁
        hB hC hG hg hgram hSobolev hpde htrace hgradient k
    have hroot : L ^ (1 / p) ≤ localBound := by
      simpa only [L, p, n, localBound, evolvingMoserLocalBound,
        evolvingMoserLocalBoundFactor] using hnormalized
    have hLbound : L ≤ localBound ^ p := by
      calc
        L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ = L ^ ((1 / p) * p) := by
          congr 2
          field_simp [hp.ne']
        _ = (L ^ (1 / p)) ^ p := by rw [Real.rpow_mul hL]
        _ ≤ localBound ^ p :=
          Real.rpow_le_rpow (Real.rpow_nonneg hL _) hroot hp.le
    have hVpow : V.toReal ≤ volumeFactor ^ p := by
      exact (le_max_right 1 V.toReal).trans
        (Real.self_le_rpow_of_one_le hvolumeFactor hp_one)
    have hscaled : V.toReal * L ≤ bound ^ p := by
      calc
        V.toReal * L ≤ volumeFactor ^ p * localBound ^ p :=
          mul_le_mul hVpow hLbound hL
            (Real.rpow_nonneg (zero_le_one.trans hvolumeFactor) p)
        _ = (volumeFactor * localBound) ^ p := by
          rw [Real.mul_rpow (zero_le_one.trans hvolumeFactor) hlocalBound]
        _ = bound ^ p := rfl
    exact hintegral_fixed.trans (hmass_compare.trans hscaled)
  have hpoint :=
    DifferentialGeometry.Analysis.Integration.le_on_open_of_integral_rpow_le
      (μ := ν) (U := U) hU hbound_nonneg
      (parabolicMoserExponent_pos n hp₀pos)
      (parabolicMoserExponent_tendsto_atTop n hp₀pos)
      hu.continuous.continuousOn (fun z => (hpos z.1 z.2).le)
      hintegrable hintegral
  intro t ht x hx
  simpa only [bound, volumeFactor, localBound, n] using
    hpoint (t, x) ⟨ht, hx⟩

theorem evolving_local_boundedness_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      u t x ≤ A * evolvingMoserLocalBound
        (I := I) (M := M) (Module.finrank ℝ E) g rho u
          C G B p₀ a τ t₁ := by
  obtain ⟨V, _hVzero, hVtop, hvolume⟩ := volume_uniform_equiv
    (I := I) (M := M) q g isCompact_Icc (fun x₀ i j =>
      (hgram x₀ i j).continuousOn.mono
        (Set.prod_mono (Set.subset_univ (Icc a t₁)) Set.Subset.rfl))
  let A := max 1 V.toReal
  refine ⟨A, le_max_left 1 _, ?_⟩
  exact evolving_local_boundedness_of_subsolution_of_volume_le
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτt₁
      hB hC hG hg hgram hSobolev hpde htrace hgradient V hVtop
      (fun t ht => (hvolume t ht).2)

theorem evolving_reciprocal_local_boundedness_of_supersolution_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      (u t x)⁻¹ ≤ max 1 V.toReal *
        evolvingMoserLocalBound
          (I := I) (M := M) (Module.finrank ℝ E) g rho
            (fun s y => (u s y)⁻¹) C G B p₀ a τ t₁ := by
  let v : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => v p.1 p.2) := by
    simpa only [v, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hvpos : ∀ t x, 0 < v t x := fun t x => inv_pos.mpr (hpos t x)
  have hvpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => v s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x := by
    intro t ht x
    have h := rpow_subsolution_of_supersolution
      (I := I) (M := M) (g t) u (fun _ _ => 0) hu hpos
        (q := -1) (by norm_num) (t := t) (x := x)
        (by simpa using hpde t ht x)
    simpa only [v, Real.rpow_neg_one, rpowSource, mul_zero, add_zero] using h
  exact evolving_local_boundedness_of_subsolution_of_volume_le
    (I := I) (M := M) g hdim rho v hv hvpos hp₀ haτ hτt₁
      hB hC hG hg hgram hSobolev
      hvpde htrace hgradient V hV hvolume

theorem evolving_reciprocal_local_boundedness_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
        (u t x)⁻¹ ≤ A *
          evolvingMoserLocalBound
            (I := I) (M := M) (Module.finrank ℝ E) g rho
              (fun s y => (u s y)⁻¹) C G B p₀ a τ t₁ := by
  let v : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => v p.1 p.2) := by
    simpa only [v, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hvpos : ∀ t x, 0 < v t x := fun t x => inv_pos.mpr (hpos t x)
  have hvpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => v s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x := by
    intro t ht x
    have h := rpow_subsolution_of_supersolution
      (I := I) (M := M) (g t) u (fun _ _ => 0) hu hpos
        (q := -1) (by norm_num) (t := t) (x := x)
        (by simpa using hpde t ht x)
    simpa only [v, Real.rpow_neg_one, rpowSource, mul_zero, add_zero] using h
  exact evolving_local_boundedness_of_subsolution
    (I := I) (M := M) g hdim rho v hv hvpos hp₀ haτ hτt₁
      hB hC hG hg hgram hSobolev hvpde htrace hgradient

theorem evolving_reciprocal_local_boundedness_of_supersolution_rpow_of_volume_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ B C G s₀ : ℝ}
    (hp : 0 < p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2)
    (V : ℝ≥0∞) (hV : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a t₁,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        V • riemannianMeasureFamily (I := I) (M := M) g t) :
    let v : ℝ → M → ℝ := fun t x => u t x ^ (-p / 2)
    let F := max 1 V.toReal *
      evolvingMoserLocalBoundFactor
        (Module.finrank ℝ E) C G B 2 a τ t₁
    let D := evolvingMoserLocalizedMass
      (I := I) (M := M) (Module.finrank ℝ E) g rho v 2 a τ t₁ 0
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      (u t x)⁻¹ ≤ F ^ (2 / p) * D ^ (1 / p) := by
  let v : ℝ → M → ℝ := fun t x => u t x ^ (-p / 2)
  let F := max 1 V.toReal *
    evolvingMoserLocalBoundFactor
      (Module.finrank ℝ E) C G B 2 a τ t₁
  let D := evolvingMoserLocalizedMass
    (I := I) (M := M) (Module.finrank ℝ E) g rho v 2 a τ t₁ 0
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => v z.1 z.2) :=
    contMDiff_rpow_of_pos hu hpos (-p / 2)
  have hvpos : ∀ t x, 0 < v t x := fun t x =>
    Real.rpow_pos_of_pos (hpos t x) _
  have hvpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => v s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x := by
    intro t ht x
    have h := rpow_subsolution_of_supersolution
      (I := I) (M := M) (g t) u (fun _ _ => 0) hu hpos
        (q := -p / 2) (by linarith) (t := t) (x := x)
        (by simpa using hpde t ht x)
    simpa only [v, rpowSource, mul_zero, add_zero] using h
  have hF : 0 ≤ F := by
    exact mul_nonneg (zero_le_one.trans (le_max_left 1 V.toReal))
      (Real.exp_pos _).le
  have hD : 0 ≤ D := by
    exact evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) (Module.finrank ℝ E) g rho v
        haτ hτt₁ (fun t x => (hvpos t x).le) 0
  change ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
    (u t x)⁻¹ ≤ F ^ (2 / p) * D ^ (1 / p)
  intro t ht x hx
  have hlocal := evolving_local_boundedness_of_subsolution_of_volume_le
    (I := I) (M := M) g hdim rho v hv hvpos
      (p₀ := 2) (by norm_num) haτ hτt₁ hB hC hG hg hgram
      hSobolev hvpde htrace hgradient V hV hvolume t ht x hx
  have hlocal' : v t x ≤ F * D ^ ((1 : ℝ) / 2) := by
    simpa only [evolvingMoserLocalBound, evolvingMoserNormalizedMass,
      parabolicMoserExponent_zero, F, D, mul_assoc] using hlocal
  have hpower : v t x ^ (2 / p) ≤
      (F * D ^ ((1 : ℝ) / 2)) ^ (2 / p) :=
    Real.rpow_le_rpow (hvpos t x).le hlocal'
      (div_nonneg (by norm_num) hp.le)
  have hvpower : v t x ^ (2 / p) = (u t x)⁻¹ := by
    dsimp only [v]
    rw [← Real.rpow_mul (hpos t x).le]
    have hexponent : -p / 2 * (2 / p) = (-1 : ℝ) := by
      field_simp [hp.ne']
    rw [hexponent, Real.rpow_neg_one]
  have hright : (F * D ^ ((1 : ℝ) / 2)) ^ (2 / p) =
      F ^ (2 / p) * D ^ (1 / p) := by
    rw [Real.mul_rpow hF (Real.rpow_nonneg hD _), ← Real.rpow_mul hD]
    congr 1
    field_simp [hp.ne']
  rw [hvpower, hright] at hpower
  exact hpower

theorem evolving_reciprocal_local_boundedness_of_supersolution_rpow
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ B C G s₀ : ℝ}
    (hp : 0 < p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k t, t ∈ Icc a t₁ → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
        (u t x)⁻¹ ≤
          (A * evolvingMoserLocalBoundFactor
              (Module.finrank ℝ E) C G B 2 a τ t₁) ^ (2 / p) *
            (evolvingMoserLocalizedMass
              (I := I) (M := M) (Module.finrank ℝ E) g rho
                (fun s y => u s y ^ (-p / 2)) 2 a τ t₁ 0) ^ (1 / p) := by
  obtain ⟨V, _hVzero, hVtop, hvolume⟩ := volume_uniform_equiv
    (I := I) (M := M) q g isCompact_Icc (fun x₀ i j =>
      (hgram x₀ i j).continuousOn.mono
        (Set.prod_mono (Set.subset_univ (Icc a t₁)) Set.Subset.rfl))
  let A := max 1 V.toReal
  refine ⟨A, le_max_left 1 _, ?_⟩
  simpa only [A] using
    (evolving_reciprocal_local_boundedness_of_supersolution_rpow_of_volume_le
      (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁
        hB hC hG hg hgram hSobolev hpde htrace hgradient V hVtop
        (fun t ht => (hvolume t ht).2))

end DifferentialGeometry.Analysis.Parabolic.Moser

end
