import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic

/-!
# The parabolic energy identity and the unconditional cross-scale trace estimate

For a `CrossScaleField` (top scale `L²([0,T]; H^{a+2})`, carrier
`H¹([0,T]; Hᵃ)`, a.e. cross-scale link), the companion file produces the
intermediate-scale representative `repr t ∈ H^{a+1}` from the continuous
per-mode coordinates `cᵢ(t) = (lo.toFun t).coeff i`, with uniform `H^{a+1}`
summability.  This file discharges the parabolic **energy identity** for that
representative and turns it into the **unconditional** sharp Lions–Magenes
energy estimate.

## The genuine sub-lemma

**Mode-sum / time-integral interchange** (`tsum_intervalIntegral_energyIntegrand_eq`).
The squared `H^{a+1}` norm is the eigenmode tsum of the per-mode weighted
squares, and the energy identity is the tsum over modes of the per-mode scalar
fundamental theorem of calculus (`coeffFun_sq_eq`, established on the companion
file).  The sum over the (countable) eigenmodes commutes with the time integral
by `MeasureTheory.integral_tsum_of_summable_integral_norm`; the dominating
series is summable because the per-mode integrand tsum is bounded a.e. in time
by `2‖hiL2 s‖_{H^{a+2}}·‖lo.deriv s‖_{Hᵃ}`, which is time-integrable.

## Main results

* `CrossScaleField.energyIdentity` — the parabolic energy identity
  `‖repr t‖² = ‖repr 0‖² + ∫₀ᵗ (∑ᵢ 2·(1+λᵢ)^{a+1} cᵢ(s)·(lo.deriv s).coeff i) ds`.
* `CrossScaleField.normSq_repr_le_init_add_integral` — the **unconditional** sharp
  Lions–Magenes energy estimate
  `‖repr t‖² ≤ ‖repr 0‖² + ∫₀ᵗ 2·‖hiL2 s‖_{H^{a+2}}·‖lo.deriv s‖_{Hᵃ} ds`, valid
  for every `t ∈ [0,T]`; taking the supremum over `t` (the right side is monotone
  in `t`) gives the sup-in-time bound by the full `∫₀ᵀ` integral, with the
  continuous representative `repr` (built on the companion file) as **output**.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

/-- **Per-mode energy identity.**  For each eigenmode `i` and `t ∈ [0,T]`,

  `wᵢ^{a+1} · cᵢ(t)² = wᵢ^{a+1} · cᵢ(0)² +
      ∫₀ᵗ 2 wᵢ^{a+1} · cᵢ(s) · (lo.deriv s).coeff i ds`. -/
theorem perMode_energyIdentity
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2 +
        ∫ τ in (0 : ℝ)..t,
          2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
            ((u.coeffFun i τ) * (u.lo.deriv τ).coeff i)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  set w := tensorSobolevWeight (I := I) (M := M) i (a + 1) with hw_def
  rw [u.coeffFun_sq_eq i h0 ht, mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  ring

/-- The countability of the eigen-index type, supplied unconditionally by the
intrinsic resolvent-compactness witness. -/
private lemma countable_eigenIdx :
    Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
    (I := I) (M := M) (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)

/-- The per-mode energy integrand, as a function of `(mode, time)`:

  `Fᵢ(s) = 2 wᵢ^{a+1} · cᵢ(s) · (lo.deriv s).coeff i`. -/
def energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) (τ : ℝ) : ℝ :=
  2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
    ((u.coeffFun i τ) * (u.lo.deriv τ).coeff i))

/-- The mode-tsum of the per-mode energy integrand. -/
lemma tsum_energyIntegrand_eq (τ : ℝ) :
    ∑' i, u.energyIntegrand i τ =
      2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ((u.coeffFun i τ) * (u.lo.deriv τ).coeff i) := by
  unfold energyIntegrand
  rw [← tsum_mul_left]

/-- The finite-set partial sum of the absolute per-mode energy integrand is
bounded, almost everywhere in `τ`, by `2‖hiL2 τ‖_{H^{a+2}}·‖lo.deriv τ‖_{Hᵃ}`. -/
lemma ae_finset_abs_energyIntegrand_le :
    ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, |u.energyIntegrand i τ| ≤ 2 * (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with τ hτ S
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) * |u.coeffFun i τ|
      with hf_def
  set d : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) * |(u.lo.deriv τ).coeff i|
      with hd_def
  have hsummand : ∀ i, |u.energyIntegrand i τ| = 2 * (f i * d i) := by
    intro i
    unfold energyIntegrand
    rw [hf_def, hd_def, abs_mul, abs_mul,
      show |(2 : ℝ)| = 2 from by norm_num,
      abs_of_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)),
      tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a, abs_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), ← Finset.mul_sum]
  have hCS : (∑ i ∈ S, f i * d i) ^ 2 ≤ (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f d
  have hfsq : ∑ i ∈ S, (f i) ^ 2 ≤ ‖u.hiL2 τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (f i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hiL2 τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hf_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)),
        sq_abs, hτ i]
    rw [heq, tensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.hiL2 τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)
  have hdsq : ∑ i ∈ S, (d i) ^ 2 ≤ ‖u.lo.deriv τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (d i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i a), sq_abs]
    rw [heq, tensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.lo.deriv τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _)
  have hsumfd_nonneg : 0 ≤ ∑ i ∈ S, f i * d i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)))
  have hsq_le : (∑ i ∈ S, f i * d i) ^ 2 ≤ (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) ^ 2 := by
    refine le_trans hCS ?_
    rw [mul_pow]
    exact mul_le_mul hfsq hdsq (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
  have hfd_le : ∑ i ∈ S, f i * d i ≤ ‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖ := by
    have := abs_le_of_sq_le_sq hsq_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rwa [abs_of_nonneg hsumfd_nonneg] at this
  linarith [hfd_le]

/-- Each per-mode energy integrand `τ ↦ Fᵢ τ` is integrable on `Ioc 0 t` for
`t ∈ [0,T]`: it is the (constant-scaled) product of the continuous, bounded
factor `cᵢ` with the interval-integrable derivative coordinate `dᵢ`. -/
lemma integrableOn_energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntegrableOn (u.energyIntegrand i) (Set.Ioc (0 : ℝ) t) volume := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcoeff_cont : ContinuousOn (u.coeffFun i) (Set.Icc (0 : ℝ) t) :=
    (u.continuousOn_coeffFun i).mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
  have hderiv_int : IntegrableOn (fun τ => (u.lo.deriv τ).coeff i)
      (Set.Ioc (0 : ℝ) t) volume := by
    have h := u.intervalIntegrable_deriv_coeffFun i h0 ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1] at h
    exact h
  have hsubIcc : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t :=
    fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hprod : IntegrableOn
      (fun τ => (u.coeffFun i τ) * (u.lo.deriv τ).coeff i) (Set.Ioc (0 : ℝ) t) volume :=
    MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcoeff_cont hderiv_int
      isCompact_Icc measurableSet_Ioc hsubIcc
  have heq : (u.energyIntegrand i) = fun τ =>
      (2 * tensorSobolevWeight (I := I) (M := M) i (a + 1)) *
        ((u.coeffFun i τ) * (u.lo.deriv τ).coeff i) := by
    funext τ; unfold energyIntegrand; ring
  rw [heq]
  exact hprod.const_mul _

/-- The dominating bound `s ↦ 2‖hiL2 s‖·‖lo.deriv s‖` is integrable on `[0,T]`. -/
lemma integrableOn_energyBound :
    IntegrableOn (fun s => 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) (Set.Icc (0 : ℝ) T) volume :=
  u.integrableOn_normMul.const_mul 2

/-- **Mode-sum / time-integral interchange.**  For `t ∈ [0,T]`,

  `∑'ᵢ ∫₀ᵗ Fᵢ s ds = ∫₀ᵗ ∑'ᵢ Fᵢ s ds`.

The eigen-index type is countable (intrinsic resolvent compactness), each `Fᵢ`
is time-integrable on `Ioc 0 t`, and the dominating series `∑'ᵢ ∫ |Fᵢ|` is
summable because the finite-set partial sums `∑_{i∈S}|Fᵢ s|` are bounded a.e. by
the time-integrable `2‖hiL2 s‖·‖lo.deriv s‖`. -/
theorem tsum_intervalIntegral_energyIntegrand_eq
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∑' i, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) =
      ∫ s in (0 : ℝ)..t, ∑' i, u.energyIntegrand i s := by
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    CrossScaleField.countable_eigenIdx (I := I) (M := M) (g := g) (r := r) (s := s)
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hF_int : ∀ i, Integrable (u.energyIntegrand i) μ := fun i =>
    u.integrableOn_energyIntegrand i ht
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_int : Integrable (fun s => 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  have hF_sum : Summable (fun i => ∫ s, ‖u.energyIntegrand i s‖ ∂μ) := by
    refine summable_of_sum_le (c := ∫ s, (2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ∂μ)
      (fun i => integral_nonneg (fun s => norm_nonneg _)) ?_
    intro S
    have hfin_int : ∀ i ∈ S, Integrable (fun s => ‖u.energyIntegrand i s‖) μ :=
      fun i _ => (hF_int i).norm
    rw [← MeasureTheory.integral_finset_sum S hfin_int]
    refine integral_mono_ae (MeasureTheory.integrable_finset_sum S hfin_int) hbound_int ?_
    filter_upwards [haebnd] with s hs
    calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
        = ∑ i ∈ S, |u.energyIntegrand i s| := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
      _ ≤ 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := hs S
  have hinterchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  rw [intervalIntegral.integral_of_le ht.1]
  rw [show (∫ s in Set.Ioc (0 : ℝ) t, ∑' i, u.energyIntegrand i s ∂volume) =
        ∫ s, ∑' i, u.energyIntegrand i s ∂μ from rfl]
  rw [← hinterchange]
  refine tsum_congr (fun i => ?_)
  rw [intervalIntegral.integral_of_le ht.1]

/-- The family of per-mode `L¹`-norm integrals `i ↦ ∫_{Ioc 0 t} ‖Fᵢ‖` is summable
for `t ∈ [0,T]`. -/
lemma summable_integral_norm_energyIntegrand {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun i => ∫ s, ‖u.energyIntegrand i s‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_int : Integrable (fun s => 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  refine summable_of_sum_le (c := ∫ s, (2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ∂μ)
    (fun i => integral_nonneg (fun s => norm_nonneg _)) ?_
  intro S
  have hfin_int : ∀ i ∈ S, Integrable (fun s => ‖u.energyIntegrand i s‖) μ :=
    fun i _ => (u.integrableOn_energyIntegrand i ht).norm
  rw [← MeasureTheory.integral_finset_sum S hfin_int]
  refine integral_mono_ae (MeasureTheory.integrable_finset_sum S hfin_int) hbound_int ?_
  filter_upwards [haebnd] with s hs
  calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
      = ∑ i ∈ S, |u.energyIntegrand i s| := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
    _ ≤ 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := hs S

/-- The family of per-mode time integrals `i ↦ ∫₀ᵗ Fᵢ` is summable for
`t ∈ [0,T]`. -/
lemma summable_intervalIntegral_energyIntegrand {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun i => ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
  refine (u.summable_integral_norm_energyIntegrand ht).of_norm_bounded ?_
  intro i
  rw [intervalIntegral.integral_of_le ht.1, Real.norm_eq_abs]
  refine (MeasureTheory.abs_integral_le_integral_abs).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ (fun s => (Real.norm_eq_abs _).symm))

/-- **The parabolic energy identity.**  For `0 < T` and `t ∈ [0,T]`,

  `‖repr t‖²_{H^{a+1}} = ‖repr 0‖²_{H^{a+1}} + ∑ᵢ ∫₀ᵗ Fᵢ s ds`,

where `Fᵢ s = 2 (1+λᵢ)^{a+1} cᵢ(s) (lo.deriv s).coeff i`.  This is the eigenmode
tsum of the per-mode scalar fundamental theorem of calculus
(`perMode_energyIdentity`).  No regularity hypothesis beyond the `CrossScaleField`
data is required (`0 < T` makes the produced representative available). -/
theorem energyIdentity (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 = ‖u.repr 0‖ ^ 2 +
      ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hnorm_t := u.normSq_repr hT ht
  have hnorm_0 := u.normSq_repr hT h0
  have hsum_init : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2) :=
    u.summable_coeffFun_sq hT h0
  have hsum_int := u.summable_intervalIntegral_energyIntegrand ht
  rw [hnorm_t]
  have hpermode : (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (u.coeffFun i t) ^ 2) =
      (fun i => (tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2) +
        ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
    funext i
    rw [u.perMode_energyIdentity i ht]
    rfl
  rw [hpermode, hsum_init.tsum_add hsum_int, ← hnorm_0]

/-- **Unconditional sharp Lions–Magenes sup-in-time energy estimate.**  For
`0 < T` and `t ∈ [0,T]`,

  `‖repr t‖²_{H^{a+1}} ≤ ‖repr 0‖²_{H^{a+1}} +
      ∫₀ᵗ 2·‖hiL2 s‖_{H^{a+2}}·‖lo.deriv s‖_{Hᵃ} ds`,

with the continuous intermediate representative `repr` (and in particular its
trace `repr 0 ∈ H^{a+1}`) **produced** from the `L²`-in-time top-scale datum, not
assumed.  This is the energy identity (`energyIdentity`) with its per-mode
integrals' tsum controlled, finite-set by finite-set, by the cross-scale
Cauchy–Schwarz bound; the supremum over `t` (the right side is monotone in `t`)
bounds the sup-in-time `H^{a+1}` norm by the full `∫₀ᵀ` integral. -/
theorem normSq_repr_le_init_add_integral (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.repr 0‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := by
  rw [u.energyIdentity hT ht]
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_eq : (∫ s in (0 : ℝ)..t, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) =
      ∫ s, (2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    rw [intervalIntegral.integral_of_le ht.1]
  rw [hbound_eq]
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hbound_int : Integrable (fun s => 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  have hpartial : ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) ≤
        ∫ s, (2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ∂μ := by
    intro S
    have hfin_int : ∀ i ∈ S, Integrable (u.energyIntegrand i) μ :=
      fun i _ => u.integrableOn_energyIntegrand i ht
    have hrw : ∀ i, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) =
        ∫ s, u.energyIntegrand i s ∂μ := fun i => intervalIntegral.integral_of_le ht.1
    rw [Finset.sum_congr rfl (fun i _ => hrw i),
      ← MeasureTheory.integral_finset_sum S hfin_int]
    refine integral_mono_ae (MeasureTheory.integrable_finset_sum S hfin_int) hbound_int ?_
    filter_upwards [haebnd] with s hs
    calc ∑ i ∈ S, u.energyIntegrand i s
        ≤ ∑ i ∈ S, |u.energyIntegrand i s| :=
          Finset.sum_le_sum (fun i _ => le_abs_self _)
      _ ≤ 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := hs S
  have htsum_le := (u.summable_intervalIntegral_energyIntegrand ht).tsum_le_of_sum_le hpartial
  linarith [htsum_le]

/-- Each per-mode indefinite time integral `t ↦ ∫₀ᵗ Fᵢ` is continuous on
`[0,T]`. -/
lemma continuousOn_intervalIntegral_energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) (Icc (0 : ℝ) T) := by
  rcases le_or_gt 0 T with hT' | hT'
  · have hint : IntegrableOn (u.energyIntegrand i) (uIcc (0 : ℝ) T) volume := by
      rw [uIcc_of_le hT']
      exact (u.integrableOn_energyIntegrand i ⟨hT', le_rfl⟩).congr_set_ae
        (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T) (μ := volume)).symm
    have hcont := continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
      (f := u.energyIntegrand i) (μ := volume) hint
    rwa [uIcc_of_le hT'] at hcont
  · rw [Icc_eq_empty (by linarith)]; exact continuousOn_empty _

/-- The per-mode `L¹`-norm bound `‖∫₀ᵗ Fᵢ‖ ≤ ∫_{Ioc 0 T} ‖Fᵢ‖` on `[0,T]`. -/
lemma norm_intervalIntegral_energyIntegrand_le (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖∫ s in (0 : ℝ)..t, u.energyIntegrand i s‖ ≤
      ∫ s, ‖u.energyIntegrand i s‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) T :=
    fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩
  rw [intervalIntegral.integral_of_le ht.1]
  calc ‖∫ s in Set.Ioc (0 : ℝ) t, u.energyIntegrand i s‖
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖u.energyIntegrand i s‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioc (0 : ℝ) T, ‖u.energyIntegrand i s‖ := by
        refine setIntegral_mono_set
          ((u.integrableOn_energyIntegrand i ⟨hT.le, le_rfl⟩).norm)
          (ae_of_all _ (fun s => norm_nonneg _)) (HasSubset.Subset.eventuallyLE hsub)

/-- **The squared `H^{a+1}` norm of the representative is continuous on `[0,T]`.**
By the energy identity `‖repr t‖² = ‖repr 0‖² + ∑ᵢ ∫₀ᵗ Fᵢ`; each per-mode
indefinite integral `t ↦ ∫₀ᵗ Fᵢ` is continuous, and the mode series converges
uniformly on `[0,T]` (its sup-norm is the summable family `∫_{Ioc 0 T}‖Fᵢ‖`). -/
theorem continuousOn_normSq_repr (hT : 0 < T) :
    ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) := by
  have hT' : (0 : ℝ) ≤ T := hT.le
  have hcont_tsum : ContinuousOn
      (fun t => ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) (Icc (0 : ℝ) T) :=
    continuousOn_tsum
      (fun i => u.continuousOn_intervalIntegral_energyIntegrand i)
      (u.summable_integral_norm_energyIntegrand (t := T) ⟨hT', le_rfl⟩)
      (fun i t ht => u.norm_intervalIntegral_energyIntegrand_le hT i ht)
  have hcont : ContinuousOn
      (fun t => ‖u.repr 0‖ ^ 2 + ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s)
      (Icc (0 : ℝ) T) :=
    continuousOn_const.add hcont_tsum
  refine hcont.congr (fun t ht => ?_)
  rw [u.energyIdentity hT ht]

end CrossScaleField

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
