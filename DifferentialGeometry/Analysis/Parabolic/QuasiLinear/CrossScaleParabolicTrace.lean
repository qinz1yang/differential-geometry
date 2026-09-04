import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Pairing.CrossScale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}


omit [NeZero (Module.finrank ℝ E)] in
lemma abs_coeff_le_norm {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    |T.coeff i| ≤ (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖T‖ := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_pos (I := I) (M := M) i σ
  have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
    Real.sqrt_pos.mpr hw_pos
  have h_term_le : tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum]
    refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) j σ
    positivity
  have hsq : (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i|) ^ 2 ≤ ‖T‖ ^
    2 := by
    rw [mul_pow, Real.sq_sqrt hw_pos.le, sq_abs]; exact h_term_le
  have hle : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| ≤ ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| :=
      mul_nonneg hsqrt_pos.le (abs_nonneg _)
    nlinarith [hsq, h1, norm_nonneg T]
  rw [inv_mul_eq_div, le_div_iff₀ hsqrt_pos, mul_comm]
  exact hle

def coeffCLM {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorHs (I := I) (M := M) g r s σ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.coeff i
      map_add' := fun S T => by simp only [TensorHs.add_coeff]
      map_smul' := fun c T => by simp only [TensorHs.smul_coeff, RingHom.id_apply, smul_eq_mul] }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹
    (fun T => by
      change ‖T.coeff i‖ ≤ _
      rw [Real.norm_eq_abs]
      exact abs_coeff_le_norm (I := I) (M := M) i T)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma coeffCLM_apply {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i T = T.coeff i := rfl

theorem sq_eq_base_add_integral_of_indefinite
    {c d : ℝ → ℝ} {t₀ t : ℝ}
    (hd : IntervalIntegrable d volume t₀ t)
    (hc : ∀ x ∈ uIcc t₀ t, c x - c t₀ = ∫ r in t₀..x, d r) :
    c t ^ 2 = c t₀ ^ 2 + ∫ s in t₀..t, 2 * c s * d s := by
  set e : ℝ → ℝ := (fun _ : ℝ => c t₀) + fun τ => ∫ r in t₀..τ, d r with he_def
  have hce : ∀ x ∈ uIcc t₀ t, c x = e x := by
    intro x hx
    have := hc x hx
    simp only [he_def, Pi.add_apply]
    linarith [this]
  have h0mem : t₀ ∈ uIcc t₀ t := left_mem_uIcc
  have htmem : t ∈ uIcc t₀ t := right_mem_uIcc
  have hac_int : AbsolutelyContinuousOnInterval
      (fun τ => ∫ r in t₀..τ, d r) t₀ t :=
    hd.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hac_const : AbsolutelyContinuousOnInterval (fun _ : ℝ => c t₀) t₀ t :=
    (LipschitzWith.const (c t₀)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hac_e : AbsolutelyContinuousOnInterval e t₀ t := by
    have := hac_const.add hac_int
    rw [he_def]
    exact this
  have hprod := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hac_e hac_e
  have hae_deriv : ∀ᵐ x, x ∈ uIcc t₀ t → deriv e x = d x := by
    filter_upwards [hd.ae_hasDerivAt_integral] with x hx hxmem
    have hxd : HasDerivAt (fun τ => ∫ r in t₀..τ, d r) (d x) x :=
      hx hxmem t₀ h0mem
    have hee : HasDerivAt e (d x) x := by
      have := (hasDerivAt_const x (c t₀)).add hxd
      rw [he_def]
      simpa only [zero_add] using this
    exact hee.deriv
  have hcongr : (∫ x in t₀..t, deriv e x * e x + e x * deriv e x) =
      ∫ x in t₀..t, 2 * c x * d x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hae' : ∀ᵐ x ∂(volume.restrict (uIoc t₀ t)),
        x ∈ uIcc t₀ t → deriv e x = d x :=
      ae_restrict_of_ae hae_deriv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae'
    filter_upwards [hae'] with x hx hxmem
    have hxd : deriv e x = d x := hx hxmem (uIoc_subset_uIcc hxmem)
    have hxce : c x = e x := hce x (uIoc_subset_uIcc hxmem)
    rw [hxd, hxce]; ring
  rw [hcongr] at hprod
  have hct : c t = e t := hce t htmem
  have hct₀ : c t₀ = e t₀ := hce t₀ h0mem
  rw [hct, hct₀]
  nlinarith [hprod]

structure CrossScaleField (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) (T : ℝ) where
  hiL2 : timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T
  lo : timeH1 (TensorHs (I := I) (M := M) g r s a) T
  link : ∀ᵐ t ∂(timeMeasure T),
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (hiL2 t) = lo.toFun t

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

def coeffFun (i : TensorEigenIdx (I := I) (M := M) g r s) (t : ℝ) : ℝ :=
  (u.lo.toFun t).coeff i

omit [NeZero (Module.finrank ℝ E)] in
lemma coeffFun_eq_integral (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u.coeffFun i t =
      u.lo.initial.coeff i + ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcomm : ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
        (∫ s in (0 : ℝ)..t, u.lo.deriv s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
      (u.lo.intervalIntegrable_deriv h0 ht)]
    rfl
  have hval : u.coeffFun i t =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i) (u.lo.toFun t) := rfl
  rw [hval, timeH1.toFun_apply, map_add, hcomm]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma continuousOn_coeffFun (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContinuousOn (u.coeffFun i) (Icc (0 : ℝ) T) := by
  have hcomp : ContinuousOn
      (fun t => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i
        (u.lo.toFun t)) (Icc (0 : ℝ) T) :=
    (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
      i).continuous.comp_continuousOn u.lo.continuousOn_toFun
  change ContinuousOn (fun t => (u.lo.toFun t).coeff i) (Icc (0 : ℝ) T)
  simpa only [coeffCLM_apply] using hcomp

omit [NeZero (Module.finrank ℝ E)] in
lemma ae_coeffFun_eq_hiL2 :
    ∀ᵐ t ∂(timeMeasure T), ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      u.coeffFun i t = (u.hiL2 t).coeff i := by
  filter_upwards [u.link] with t ht i
  have := congrArg (fun T => TensorHs.coeff T i) ht
  simpa only [coeffFun, tensorHsInclusion_coeff_apply] using this.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma ae_finset_top_sq_le (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) :
    ∀ᵐ t ∂(timeMeasure T),
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u.coeffFun i t) ^ 2 ≤
        ‖u.hiL2 t‖ ^ 2 := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with t ht
  have hsum_eq : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u.coeffFun i t) ^ 2 =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hiL2 t).coeff i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [ht i])
  rw [hsum_eq, TensorHs.norm_sq_eq_tsum]
  refine Summable.sum_le_tsum S (fun i _ => ?_) (u.hiL2 t).weighted_summable
  exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
lemma intervalIntegrable_deriv_coeffFun
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ => (u.lo.deriv τ).coeff i) volume t₀ t := by
  have hbase : IntervalIntegrable (fun τ => u.lo.deriv τ) volume t₀ t :=
    u.lo.intervalIntegrable_deriv ht₀ ht
  have hcomp : IntervalIntegrable
      (fun τ => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
        i (u.lo.deriv τ)) volume t₀ t :=
    intervalIntegrable_iff.mpr
      ((coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).integrable_comp
        (intervalIntegrable_iff.mp hbase))
  simpa only [coeffCLM_apply] using hcomp

omit [NeZero (Module.finrank ℝ E)] in
lemma coeffFun_sq_eq (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    (u.coeffFun i t) ^ 2 = (u.coeffFun i t₀) ^ 2 +
      ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  refine sq_eq_base_add_integral_of_indefinite
    (u.intervalIntegrable_deriv_coeffFun i ht₀ ht) (fun x hx => ?_)
  have hxmem : x ∈ Icc (0 : ℝ) T := uIcc_subset_Icc ht₀ ht hx
  rw [u.coeffFun_eq_integral i hxmem, u.coeffFun_eq_integral i ht₀]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (u.intervalIntegrable_deriv_coeffFun i h0 hxmem)
    (u.intervalIntegrable_deriv_coeffFun i h0 ht₀)

omit [NeZero (Module.finrank ℝ E)] in
lemma ae_abs_finset_crossPairing_le :
    ∀ᵐ τ ∂(timeMeasure T),
      ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
        |∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (u.coeffFun i τ * (u.lo.deriv τ).coeff i)| ≤
            ‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖ := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with τ hs S
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) * u.coeffFun i τ with
               hf_def
  set d : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) * (u.lo.deriv τ).coeff i with
               hd_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (u.coeffFun i τ * (u.lo.deriv τ).coeff i) = f i * d i := by
    intro i
    rw [hf_def, hd_def, tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, f i * d i) ^ 2 ≤ (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f d
  have hfsq : ∑ i ∈ S, (f i) ^ 2 ≤ ‖u.hiL2 τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (f i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hiL2 τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hf_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)),
        hs i]
    rw [heq, TensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.hiL2 τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)
  have hdsq : ∑ i ∈ S, (d i) ^ 2 ≤ ‖u.lo.deriv τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (d i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i a)]
    rw [heq, TensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.lo.deriv τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _)
  have hsq_le : (∑ i ∈ S, f i * d i) ^ 2 ≤ (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) ^ 2 := by
    refine le_trans hCS ?_
    rw [mul_pow]
    refine mul_le_mul hfsq hdsq (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
  have hprodnn : 0 ≤ ‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact abs_le_of_sq_le_sq hsq_le hprodnn

omit [NeZero (Module.finrank ℝ E)] in
lemma integrableOn_normMul :
    IntegrableOn (fun s => ‖u.hiL2 s‖ * ‖u.lo.deriv s‖) (Set.Icc (0 : ℝ) T) volume := by
  have hhi : IntegrableOn (fun s => ‖u.hiL2 s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.hiL2 s) 2 (timeMeasure T) := Lp.memLp u.hiL2
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.hiL2 x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.hiL2 x‖ ^ 2) := by
      funext x
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint
    exact hint
  have hlo : IntegrableOn (fun s => ‖u.lo.deriv s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.lo.deriv s) 2 (timeMeasure T) := Lp.memLp u.lo.deriv
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.lo.deriv x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.lo.deriv x‖ ^ 2) := by
      funext x
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint
    exact hint
  have hmeas : AEStronglyMeasurable (fun s => ‖u.hiL2 s‖ * ‖u.lo.deriv s‖)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : AEStronglyMeasurable (fun s => ‖u.hiL2 s‖)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (Lp.aestronglyMeasurable u.hiL2).norm
    have h2 : AEStronglyMeasurable (fun s => ‖u.lo.deriv s‖)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (Lp.aestronglyMeasurable u.lo.deriv).norm
    exact h1.mul h2
  refine Integrable.mono' (g := fun s => (1 / 2) * (‖u.hiL2 s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2))
    ((hhi.add hlo).const_mul (1 / 2)) hmeas (ae_of_all _ (fun s => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖u.hiL2 s‖ - ‖u.lo.deriv s‖), norm_nonneg (u.hiL2 s),
    norm_nonneg (u.lo.deriv s)]

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_uniform_bound (hT : 0 < T) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 ≤ B := by
  have hμ_ne : timeMeasure T ≠ 0 := timeMeasure_ne_zero hT
  have : (ae (timeMeasure T)).NeBot := MeasureTheory.ae_neBot.2 hμ_ne
  have hcombine : ∀ᵐ t₀ ∂(timeMeasure T), t₀ ∈ Icc (0 : ℝ) T ∧
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s, u.coeffFun i t₀ = (u.hiL2 t₀).coeff i) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc, u.ae_coeffFun_eq_hiL2]
      with t₀ hmem hcoeff using ⟨hmem, hcoeff⟩
  obtain ⟨t₀, ht₀mem, ht₀coeff⟩ := hcombine.exists
  set C : ℝ := 2 * ∫ s in Set.Icc (0 : ℝ) T, ‖u.hiL2 s‖ * ‖u.lo.deriv s‖ with hC_def
  set R : ℝ := ‖u.hiL2 t₀‖ ^ 2 with hR_def
  refine ⟨R + C, fun t ht S => ?_⟩
  have hsum_ftc : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 +
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [u.coeffFun_sq_eq i ht₀mem ht, mul_add]
  rw [hsum_ftc]
  have hterm0 : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 ≤
    R := by
    rw [hR_def]
    have heq : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hiL2 t₀).coeff i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [ht₀coeff i])
    rw [heq]
    refine le_trans (Summable.sum_le_tsum S
      (fun i _ => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)) (sq_nonneg _))
      ((tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)).weighted_summable.congr
        (fun i => by rw [tensorHsInclusion_coeff_apply]))) ?_
    have hnormSq : (∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ((u.hiL2 t₀).coeff i) ^ 2) =
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)‖ ^ 2 := by
      rw [TensorHs.norm_sq_eq_tsum]
      exact (tsum_congr (fun i => by rw [tensorHsInclusion_coeff_apply])).symm
    rw [hnormSq]
    have hle := tensorHsInclusion_norm_le (I := I) (M := M)
      (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)
    nlinarith [hle, norm_nonneg (u.hiL2 t₀),
      norm_nonneg (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀))]
  have hterm1 : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i ≤ C := by
    have hintegrable : ∀ i, IntervalIntegrable
        (fun τ => 2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i) volume t₀ t := by
      intro i
      have hcont : ContinuousOn (fun τ => 2 * u.coeffFun i τ) (uIcc t₀ t) :=
        continuousOn_const.mul ((u.continuousOn_coeffFun i).mono (uIcc_subset_Icc ht₀mem ht))
      have hd := u.intervalIntegrable_deriv_coeffFun i ht₀mem ht
      exact hd.continuousOn_mul hcont
    set G : ℝ → ℝ := fun τ => ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i) with hG_def
    have hsum_int : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ∫ τ in t₀..t, 2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i =
        ∫ τ in t₀..t, G τ := by
      rw [hG_def,
        intervalIntegral.integral_finsetSum (s := S) (fun i _ => (hintegrable i).const_mul _)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [intervalIntegral.integral_const_mul]
    rw [hsum_int]
    have hsub : Set.uIoc t₀ t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ht₀mem ht)
    set dom : ℝ → ℝ := fun τ => 2 * (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) with hdom_def
    have hdom_nonneg : ∀ τ, 0 ≤ dom τ := fun τ => by rw [hdom_def]; positivity
    have hGbound : ∀ᵐ τ ∂(volume.restrict (Set.uIoc t₀ t)), ‖G τ‖ ≤ dom τ := by
      have hfull := u.ae_abs_finset_crossPairing_le
      have hae := ae_restrict_of_ae_restrict_of_subset hsub hfull
      filter_upwards [hae] with τ hτ
      have hbnd := hτ S
      have hGeq : G τ = 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (u.coeffFun i τ * (u.lo.deriv τ).coeff i) := by
        rw [hG_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [Real.norm_eq_abs, hGeq, hdom_def, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
      nlinarith [hbnd, abs_nonneg (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (u.coeffFun i τ * (u.lo.deriv τ).coeff i)),
        mul_nonneg (norm_nonneg (u.hiL2 τ)) (norm_nonneg (u.lo.deriv τ))]
    have hdom_int : IntervalIntegrable dom volume t₀ t := by
      rw [intervalIntegrable_iff, hdom_def]
      exact (u.integrableOn_normMul.mono_set (Set.uIoc_subset_uIcc.trans
        (uIcc_subset_Icc ht₀mem ht))).const_mul 2
    have hdom_set_int : IntegrableOn dom (Set.Icc (0 : ℝ) T) volume := by
      rw [hdom_def]; exact u.integrableOn_normMul.const_mul 2
    calc ∫ τ in t₀..t, G τ
        ≤ |∫ τ in t₀..t, G τ| := le_abs_self _
      _ ≤ |∫ τ in t₀..t, dom τ| := by
          have hbnd := intervalIntegral.norm_integral_le_abs_of_norm_le
            (μ := volume) (a := t₀) (b := t) (f := G) (g := dom) hGbound hdom_int
          rwa [Real.norm_eq_abs] at hbnd
      _ = ∫ τ in Set.uIoc t₀ t, dom τ := by
          rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
          exact abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc (fun τ _ => hdom_nonneg τ))
      _ ≤ ∫ τ in Set.Icc (0 : ℝ) T, dom τ :=
          setIntegral_mono_set hdom_set_int (ae_of_all _ hdom_nonneg)
            (LE.le.eventuallyLE hsub)
      _ = C := by rw [hC_def, hdom_def, ← MeasureTheory.integral_const_mul]
  linarith [hterm0, hterm1]

omit [NeZero (Module.finrank ℝ E)] in
lemma summable_coeffFun_sq (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2) := by
  obtain ⟨B, hB⟩ := u.exists_uniform_bound hT
  refine summable_of_sum_le (c := B)
    (fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)) (sq_nonneg _))
    (fun S => hB t ht S)

open Classical in
def repr (t : ℝ) : TensorHs (I := I) (M := M) g r s (a + 1) :=
  if h : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2) then
    { coeff := fun i => u.coeffFun i t, weighted_summable := h }
  else 0

omit [NeZero (Module.finrank ℝ E)] in
lemma repr_coeff_of_summable {t : ℝ}
    (h : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.repr t).coeff i = u.coeffFun i t := by
  rw [repr, dif_pos h]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma repr_coeff (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.repr t).coeff i = u.coeffFun i t :=
  u.repr_coeff_of_summable (u.summable_coeffFun_sq hT ht) i

omit [NeZero (Module.finrank ℝ E)] in
lemma normSq_repr (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 := by
  rw [TensorHs.norm_sq_eq_tsum]
  exact tsum_congr (fun i => by rw [u.repr_coeff hT ht])

end CrossScaleField


end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
