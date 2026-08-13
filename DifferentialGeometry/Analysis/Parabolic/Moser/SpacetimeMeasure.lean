import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation
import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def cutoffWeightedMeasure {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) : Measure M :=
  (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
    (fun x => ENNReal.ofReal (cutoff.toFun x ^ 2))

instance cutoffWeightedMeasure_isFiniteMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) :
    IsFiniteMeasure (cutoffWeightedMeasure (I := I) (M := M) cutoff) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  exact isFiniteMeasure_withDensity_ofReal
    ((cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

omit [CompactSpace M] in
theorem cutoffWeightedMeasure_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    cutoffWeightedMeasure (I := I) (M := M) cutoff ≤
      cutoffWeightedMeasure (I := I) (M := M) outer := by
  unfold cutoffWeightedMeasure
  apply withDensity_mono
  filter_upwards with x
  exact ENNReal.ofReal_le_ofReal (hcutoff x)

def localizedSpacetimeMeasure {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (a b : ℝ) : Measure (ℝ × M) :=
  (volume.restrict (Ioc a b)).prod
    (cutoffWeightedMeasure (I := I) (M := M) cutoff)

theorem ae_localizedSpacetimeMeasure_fst_mem_Ioc
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (a b : ℝ) :
    ∀ᵐ z ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b,
      z.1 ∈ Ioc a b := by
  unfold localizedSpacetimeMeasure
  rw [Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioc.preimage measurable_fst)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ae_of_all _ fun _ => ht

def localizedSpacetimeRpowMoment {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (u : ℝ → M → ℝ)
    (p a b : ℝ) : ℝ :=
  ∫ z, u z.1 z.2 ^ p
    ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b

def localizedSpacetimeRpowNorm {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (u : ℝ → M → ℝ)
    (p a b : ℝ) : ℝ :=
  localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b ^ (1 / p)

omit [CompactSpace M] in
theorem localizedSpacetimeRpowMoment_inv
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (p a b : ℝ) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff
        (fun t x => (u t x)⁻¹) p a b =
      localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u (-p) a b := by
  unfold localizedSpacetimeRpowMoment
  apply integral_congr_ae
  filter_upwards with z
  exact (Real.rpow_neg_eq_inv_rpow (u z.1 z.2) p).symm

omit [CompactSpace M] in
theorem localizedSpacetimeRpowNorm_inv
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (p a b : ℝ) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff
        (fun t x => (u t x)⁻¹) p a b =
      localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u (-p) a b ^
        (1 / p) := by
  unfold localizedSpacetimeRpowNorm
  rw [localizedSpacetimeRpowMoment_inv]

theorem localizedSpacetimeMeasure_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeMeasure (I := I) (M := M) cutoff a b ≤
      localizedSpacetimeMeasure (I := I) (M := M) outer c d := by
  unfold localizedSpacetimeMeasure
  exact DifferentialGeometry.Integral.Measure.prod_mono
    (Measure.restrict_mono_set volume (Set.Ioc_subset_Ioc hca hbd))
    (cutoffWeightedMeasure_mono (I := I) (M := M) hcutoff)

instance localizedSpacetimeMeasure_isFiniteMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (a b : ℝ) :
    IsFiniteMeasure
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  unfold localizedSpacetimeMeasure
  infer_instance

theorem integrable_localizedSpacetimeMeasure_of_continuous
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (a b : ℝ) {f : ℝ × M → ℝ} (hf : Continuous f) :
    Integrable f
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  let K : Set (ℝ × M) := Icc a b ×ˢ (Set.univ : Set M)
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set M))
  have hfK : IntegrableOn f K
      ((volume : Measure ℝ).prod
        (cutoffWeightedMeasure (I := I) (M := M) cutoff)) :=
    hf.continuousOn.integrableOn_compact hK
  rw [localizedSpacetimeMeasure, Measure.restrict_prod_eq_prod_univ]
  apply hfK.mono_set
  intro z hz
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, Set.mem_univ z.2⟩

theorem integrable_localizedSpacetimeRpow_of_continuous_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) (p a b : ℝ) :
    Integrable (fun z : ℝ × M => u z.1 z.2 ^ p)
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  apply integrable_localizedSpacetimeMeasure_of_continuous
  exact hu.rpow_const fun z => Or.inl (hpos z.1 z.2).ne'

omit [CompactSpace M] in
theorem localizedSpacetimeRpowMoment_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (hu : ∀ t x, 0 ≤ u t x)
    (p a b : ℝ) :
    0 ≤ localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b := by
  exact integral_nonneg fun z => Real.rpow_nonneg (hu z.1 z.2) p

theorem localizedSpacetimeRpowMoment_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) (p a b : ℝ)
    (hmeasure : localizedSpacetimeMeasure (I := I) (M := M) cutoff a b ≠ 0) :
    0 < localizedSpacetimeRpowMoment (I := I) (M := M)
      cutoff u p a b := by
  let mu := localizedSpacetimeMeasure (I := I) (M := M) cutoff a b
  let f : ℝ × M → ℝ := fun z => u z.1 z.2 ^ p
  have hf : Integrable f mu :=
    integrable_localizedSpacetimeRpow_of_continuous_pos
      (I := I) (M := M) cutoff u hu hpos p a b
  have hnonneg : 0 ≤ f := fun z => Real.rpow_nonneg (hpos z.1 z.2).le p
  change 0 < ∫ z, f z ∂mu
  apply (integral_pos_iff_support_of_nonneg hnonneg hf).2
  have hsupp : Function.support f = Set.univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (hpos z.1 z.2) p).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.mpr hmeasure

theorem localizedSpacetimeRpowMoment_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowMoment (I := I) (M := M) outer u p c d := by
  exact integral_mono_measure
    (localizedSpacetimeMeasure_mono (I := I) (M := M) hca hbd hcutoff)
    (ae_of_all _ fun z => Real.rpow_nonneg (hpos z.1 z.2).le p)
    (integrable_localizedSpacetimeRpow_of_continuous_pos
      (I := I) (M := M) outer u hu hpos p c d)

theorem localizedSpacetimeRpowNorm_mono_measure
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d : ℝ} (hp : 0 < p) (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) outer u p c d := by
  unfold localizedSpacetimeRpowNorm
  exact Real.rpow_le_rpow
    (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      cutoff u (fun t x => (hpos t x).le) p a b)
    (localizedSpacetimeRpowMoment_mono (I := I) (M := M)
      u hu hpos hca hbd hcutoff)
    (div_pos one_pos hp).le

theorem localizedSpacetimeRpowNorm_le_const_mul_of_ae
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u v : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hv : Continuous (fun z : ℝ × M => v z.1 z.2))
    (hupos : ∀ t x, 0 < u t x) (hvpos : ∀ t x, 0 < v t x)
    {p a b C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (hbound : ∀ᵐ z ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b,
      u z.1 z.2 ≤ C * v z.1 z.2) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      C * localizedSpacetimeRpowNorm (I := I) (M := M) cutoff v p a b := by
  let U := localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b
  let V := localizedSpacetimeRpowMoment (I := I) (M := M) cutoff v p a b
  have hmoment : U ≤ C ^ p * V := by
    dsimp only [U, V, localizedSpacetimeRpowMoment]
    rw [← integral_const_mul]
    apply integral_mono_ae
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hupos p a b)
      ((integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff v hv hvpos p a b).const_mul _)
    filter_upwards [hbound] with z hz
    calc
      u z.1 z.2 ^ p ≤ (C * v z.1 z.2) ^ p :=
        Real.rpow_le_rpow (hupos z.1 z.2).le hz hp.le
      _ = C ^ p * v z.1 z.2 ^ p :=
        Real.mul_rpow hC.le (hvpos z.1 z.2).le
  have hU : 0 ≤ U := localizedSpacetimeRpowMoment_nonneg
    (I := I) (M := M) cutoff u (fun t x => (hupos t x).le) p a b
  have hV : 0 ≤ V := localizedSpacetimeRpowMoment_nonneg
    (I := I) (M := M) cutoff v (fun t x => (hvpos t x).le) p a b
  have hroot := Real.rpow_le_rpow hU hmoment (div_pos one_pos hp).le
  change U ^ (1 / p) ≤ C * V ^ (1 / p)
  calc
    U ^ (1 / p) ≤ (C ^ p * V) ^ (1 / p) := hroot
    _ = C * V ^ (1 / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) hV,
        ← Real.rpow_mul hC.le]
      have hcancel : p * (1 / p) = 1 := by field_simp [hp.ne']
      rw [hcancel, Real.rpow_one]

omit [CompactSpace M] in
theorem localizedSpacetimeRpowNorm_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (hu : ∀ t x, 0 ≤ u t x)
    (p a b : ℝ) :
    0 ≤ localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b :=
  Real.rpow_nonneg
    (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      cutoff u hu p a b) _

omit [CompactSpace M] in
theorem localizedSpacetimeRpowNorm_pos
    {g : SmoothRiemannianMetric I M} {cutoff : SmoothScalar g}
    {u : ℝ → M → ℝ} {p a b : ℝ}
    (hmoment : 0 <
      localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b) :
    0 < localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b :=
  Real.rpow_pos_of_pos hmoment _

theorem localizedSpacetimeRpowNorm_mono
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a b : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        Set.univ ≤ 1) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u q a b := by
  exact DifferentialGeometry.Integral.integral_rpow_root_mono_of_measure_le_one
    hp hpq (ae_of_all _ fun z => (hpos z.1 z.2).le)
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos q a b) hmass

theorem localizedSpacetimeRpowNorm_le_interpolation
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q r theta a b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hq_eq : q = theta * p + (1 - theta) * r) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u q a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ^
          (theta * p / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u r a b ^
          ((1 - theta) * r / q) := by
  unfold localizedSpacetimeRpowNorm localizedSpacetimeRpowMoment
  exact DifferentialGeometry.Integral.integral_rpow_root_le_interpolation
    hp hq hr htheta htheta_one hq_eq
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos p a b)
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos r a b)
      (ae_of_all _ fun z => (hpos z.1 z.2).le)

omit [CompactSpace M] in
theorem integral_cutoffWeightedMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (f : M → ℝ) :
    (∫ x, f x ∂cutoffWeightedMeasure (I := I) (M := M) cutoff) =
      ∫ x, cutoff.toFun x ^ 2 * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hdensity : Measurable (fun x : M => ENNReal.ofReal (cutoff.toFun x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (cutoff.smooth.continuous.pow 2).measurable
  rw [cutoffWeightedMeasure,
    integral_withDensity_eq_integral_toReal_smul hdensity (by simp)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

omit [CompactSpace M] in
theorem cutoffWeightedMeasure_real_apply
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {s : Set M} (hs : MeasurableSet s) :
    (cutoffWeightedMeasure (I := I) (M := M) cutoff).real s =
      ∫ x in s, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← integral_indicator_one hs,
    integral_cutoffWeightedMeasure (I := I) (M := M)]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

theorem integral_localizedSpacetimeMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b : ℝ} (hab : a ≤ b) (f : ℝ × M → ℝ)
    (hf : Integrable f
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b)) :
    (∫ z, f z ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * f (t, x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [localizedSpacetimeMeasure, integral_prod f hf]
  simp_rw [integral_cutoffWeightedMeasure (I := I) (M := M)]
  exact (intervalIntegral.integral_of_le hab).symm

theorem localizedSpacetimeMeasure_real_univ
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b : ℝ} (hab : a ≤ b) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real Set.univ =
      (b - a) * cutoffMass (I := I) (M := M) cutoff := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let ν : Measure M := cutoffWeightedMeasure (I := I) (M := M) cutoff
  have hprod : (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) = μ.prod ν := rfl
  have hμ : μ Set.univ = ENNReal.ofReal (b - a) := by
    dsimp [μ]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  have hν : ν Set.univ = ENNReal.ofReal (cutoffMass (I := I) (M := M) cutoff) := by
    dsimp [ν]
    unfold cutoffWeightedMeasure
    haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    have hlin : (∫⁻ x, ENNReal.ofReal (cutoff.toFun x ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ENNReal.ofReal (∫ x, cutoff.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        ((cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (Filter.Eventually.of_forall (fun x => sq_nonneg (cutoff.toFun x)))).symm
    rw [withDensity_apply]
    · simpa [cutoffMass] using hlin
    · exact MeasurableSet.univ
  have hprod_univ : (μ.prod ν) Set.univ =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (cutoffMass (I := I) (M := M) cutoff) := by
    rw [Measure.prod_apply]
    · have hfiber : (fun x : ℝ => ν (Prod.mk x ⁻¹' Set.univ)) = fun _ : ℝ => ν Set.univ := by
        funext x
        simp
      rw [hfiber]
      rw [lintegral_const]
      rw [hμ, hν]
      ring
    · exact MeasurableSet.univ
  change ENNReal.toReal ((localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) Set.univ) =
    (b - a) * cutoffMass (I := I) (M := M) cutoff
  rw [hprod]
  rw [hprod_univ]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [ENNReal.toReal_ofReal (cutoff_mass_nonneg (I := I) (M := M) cutoff)]

theorem localizedSpacetimeMeasure_ne_zero_of
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b : ℝ} (hab : a < b)
    (hcutoff : cutoffMass (I := I) (M := M) cutoff ≠ 0) :
    localizedSpacetimeMeasure (I := I) (M := M) cutoff a b ≠ 0 := by
  by_contra hzero
  have hreal : (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real Set.univ ≠ 0 := by
    rw [localizedSpacetimeMeasure_real_univ (I := I) (M := M) cutoff (le_of_lt hab)]
    exact mul_ne_zero (sub_pos.mpr hab).ne' hcutoff
  exact hreal (by simp [hzero])

theorem localizedSpacetimeMeasure_le_one_of
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b : ℝ} (hab : a ≤ b)
    (hbound : (b - a) * cutoffMass (I := I) (M := M) cutoff ≤ 1) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real Set.univ ≤ 1 := by
  rw [localizedSpacetimeMeasure_real_univ (I := I) (M := M) cutoff hab]
  exact hbound

theorem localizedSpacetimeRpowMoment_eq_intervalIntegral
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) {p a b : ℝ} (hab : a ≤ b)
    (hu : Integrable (fun z : ℝ × M => u z.1 z.2 ^ p)
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b)) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_localizedSpacetimeMeasure (I := I) (M := M)
    cutoff hab (fun z : ℝ × M => u z.1 z.2 ^ p) hu

theorem localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) {p a b : ℝ} (hab : a ≤ b) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact localizedSpacetimeRpowMoment_eq_intervalIntegral
    (I := I) (M := M) cutoff u hab
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos p a b)

theorem localizedSpacetimeRpowNorm_le_of_bound_on_cutoff
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a b C : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hab : a ≤ b)
    (hC : 0 < C)
    (hbound : ∀ t ∈ Icc a b, ∀ x, cutoff.toFun x ≠ 0 → u t x ≤ C) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u q a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ^ (p / q) *
        C ^ (1 - p / q) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let P : ℝ → ℝ := fun t =>
    ∫ x, cutoff.toFun x ^ 2 * u t x ^ p ∂μ
  let Q : ℝ → ℝ := fun t =>
    ∫ x, cutoff.toFun x ^ 2 * u t x ^ q ∂μ
  let Mp := localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b
  let Mq := localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u q a b
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hq : 0 < q := hp.trans_le hpq
  have hjointP : Continuous (fun z : ℝ × M =>
      cutoff.toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((cutoff.smooth.continuous.comp continuous_snd).pow 2).mul
      (hu.rpow_const fun z => Or.inl (hpos z.1 z.2).ne')
  have hjointQ : Continuous (fun z : ℝ × M =>
      cutoff.toFun z.2 ^ 2 * u z.1 z.2 ^ q) :=
    ((cutoff.smooth.continuous.comp continuous_snd).pow 2).mul
      (hu.rpow_const fun z => Or.inl (hpos z.1 z.2).ne')
  have hP_cont : ContinuousOn P (Icc a b) := by
    simpa only [P, μ] using
      (DifferentialGeometry.Integral.Measure.integral_contOn_cpt
        (K := Icc a b) μ
        (fun t x => cutoff.toFun x ^ 2 * u t x ^ p)
        isCompact_Icc hjointP.continuousOn)
  have hQ_cont : ContinuousOn Q (Icc a b) := by
    simpa only [Q, μ] using
      (DifferentialGeometry.Integral.Measure.integral_contOn_cpt
        (K := Icc a b) μ
        (fun t x => cutoff.toFun x ^ 2 * u t x ^ q)
        isCompact_Icc hjointQ.continuousOn)
  have hP_int : IntervalIntegrable P volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hP_cont
  have hQ_int : IntervalIntegrable Q volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hQ_cont
  have hpoint : ∀ t ∈ Icc a b, Q t ≤ C ^ (q - p) * P t := by
    intro t ht
    have hP_slice : Continuous (fun x : M => cutoff.toFun x ^ 2 * u t x ^ p) :=
      (cutoff.smooth.continuous.pow 2).mul
        ((hu.comp (continuous_const.prodMk continuous_id)).rpow_const
          fun x => Or.inl (hpos t x).ne')
    have hQ_slice : Continuous (fun x : M => cutoff.toFun x ^ 2 * u t x ^ q) :=
      (cutoff.smooth.continuous.pow 2).mul
        ((hu.comp (continuous_const.prodMk continuous_id)).rpow_const
          fun x => Or.inl (hpos t x).ne')
    change (∫ x, cutoff.toFun x ^ 2 * u t x ^ q ∂μ) ≤
      C ^ (q - p) * ∫ x, cutoff.toFun x ^ 2 * u t x ^ p ∂μ
    rw [← integral_const_mul]
    apply integral_mono
      (hQ_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_const.mul hP_slice).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    intro x
    by_cases hcutoff : cutoff.toFun x = 0
    · simp [hcutoff]
    have hupow : u t x ^ (q - p) ≤ C ^ (q - p) :=
      Real.rpow_le_rpow (hpos t x).le (hbound t ht x hcutoff)
        (sub_nonneg.mpr hpq)
    have hweight : 0 ≤ cutoff.toFun x ^ 2 * u t x ^ p :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hpos t x).le _)
    calc
      cutoff.toFun x ^ 2 * u t x ^ q =
          (cutoff.toFun x ^ 2 * u t x ^ p) * u t x ^ (q - p) := by
        rw [show q = p + (q - p) by ring, Real.rpow_add (hpos t x)]
        ring_nf
      _ ≤ (cutoff.toFun x ^ 2 * u t x ^ p) * C ^ (q - p) :=
        mul_le_mul_of_nonneg_left hupow hweight
      _ = C ^ (q - p) * (cutoff.toFun x ^ 2 * u t x ^ p) := by ring
  have hmoment : Mq ≤ C ^ (q - p) * Mp := by
    dsimp only [Mq, Mp]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) cutoff u hu hpos hab]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) cutoff u hu hpos hab]
    change (∫ t in a..b, Q t) ≤ C ^ (q - p) * ∫ t in a..b, P t
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab hQ_int
      (hP_int.const_mul _) hpoint
  have hMp : 0 ≤ Mp := localizedSpacetimeRpowMoment_nonneg
    (I := I) (M := M) cutoff u (fun t x => (hpos t x).le) p a b
  have hMq : 0 ≤ Mq := localizedSpacetimeRpowMoment_nonneg
    (I := I) (M := M) cutoff u (fun t x => (hpos t x).le) q a b
  have hroot := Real.rpow_le_rpow hMq hmoment (div_nonneg zero_le_one hq.le)
  change Mq ^ (1 / q) ≤ (Mp ^ (1 / p)) ^ (p / q) * C ^ (1 - p / q)
  calc
    Mq ^ (1 / q) ≤ (C ^ (q - p) * Mp) ^ (1 / q) := hroot
    _ = C ^ (1 - p / q) * Mp ^ (1 / q) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) hMp]
      rw [← Real.rpow_mul hC.le]
      congr 1
      field_simp [hq.ne']
    _ = (Mp ^ (1 / p)) ^ (p / q) * C ^ (1 - p / q) := by
      rw [← Real.rpow_mul hMp]
      have hexponent : 1 / p * (p / q) = 1 / q := by
        field_simp [hp.ne', hq.ne']
      rw [hexponent]
      ring

theorem localizedSpacetimeMeasure_real_superlevel
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b level : ℝ} (hab : a ≤ b) (v : ℝ × M → ℝ)
    (hv : Continuous v) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < v z} =
      ∫ t in a..b, ∫ x in {x : M | level < v (t, x)}, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let S : Set (ℝ × M) := {z | level < v z}
  have hS : MeasurableSet S := (isOpen_lt continuous_const hv).measurableSet
  have hInt : Integrable (S.indicator (1 : (ℝ × M) → ℝ))
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) :=
    (integrable_const (1 : ℝ)).indicator hS
  calc
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < v z} =
        ∫ z, S.indicator (1 : (ℝ × M) → ℝ) z
          ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b := by
      simpa only [S] using (integral_indicator_one hS).symm
    _ = ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 *
          S.indicator (1 : (ℝ × M) → ℝ) (t, x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_localizedSpacetimeMeasure (I := I) (M := M) cutoff hab _ hInt
    _ = ∫ t in a..b, ∫ x in {x : M | level < v (t, x)}, cutoff.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      apply intervalIntegral.integral_congr
      intro t _
      let St : Set M := {x : M | level < v (t, x)}
      have hSt : MeasurableSet St :=
        (isOpen_lt continuous_const
          (hv.comp (continuous_const.prodMk continuous_id))).measurableSet
      change (∫ x, cutoff.toFun x ^ 2 *
          S.indicator (1 : (ℝ × M) → ℝ) (t, x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x in St, cutoff.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      rw [← integral_indicator hSt]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ St
      · have hxS : (t, x) ∈ S := by simpa only [S, St, mem_setOf_eq] using hx
        simp only [Set.indicator_of_mem hxS, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      · have hxS : (t, x) ∉ S := by simpa only [S, St, mem_setOf_eq] using hx
        simp only [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hx, mul_zero]

theorem localizedSpacetimeMeasure_real_sublevel
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b level : ℝ} (hab : a ≤ b) (v : ℝ × M → ℝ)
    (hv : Continuous v) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | v z < level} =
      ∫ t in a..b, ∫ x in {x : M | v (t, x) < level}, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := localizedSpacetimeMeasure_real_superlevel
    (I := I) (M := M) cutoff hab (fun z => -v z) hv.neg
      (level := -level)
  simpa only [neg_lt_neg_iff] using h

end DifferentialGeometry.Analysis.Parabolic.Moser

end
