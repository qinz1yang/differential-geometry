import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The damped causal heat resolvent

This file computes the classical Fourier transform of the Euclidean heat
kernel and of its exponentially damped causal spacetime extension.
-/

noncomputable section

open Complex MeasureTheory Real Set
open scoped FourierTransform RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [Nontrivial V] in
/-- The normalized time-one heat Gaussian has symbol
`exp (-4 π² ‖ξ‖²)`. -/
theorem baseHeat_fourier (ξ : V) :
    𝓕 (fun x : V => (baseHeat x : ℂ)) ξ =
      Complex.exp ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  let b : ℂ := ((4 : ℝ)⁻¹ : ℂ)
  let c : ℂ := (baseHeatMass V : ℂ)⁻¹
  have hG := fourier_gaussian_innerProductSpace
    (V := V) (b := b) (by simp [b]) ξ
  rw [fourier_eq'] at hG ⊢
  simp only [smul_eq_mul] at hG ⊢
  calc
    (∫ v : V, Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) *
        (baseHeat v : ℂ)) =
        c * ∫ v : V, Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) *
          Complex.exp (-b * ‖v‖ ^ 2) := by
      calc
        (∫ v : V, Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) *
            (baseHeat v : ℂ)) =
            ∫ v : V, c * (Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) *
              Complex.exp (-b * ‖v‖ ^ 2)) := by
          apply integral_congr_ae
          filter_upwards with v
          dsimp [c, b]
          unfold baseHeat
          push_cast
          ring
        _ = c * ∫ v : V, Complex.exp (((-2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) *
            Complex.exp (-b * ‖v‖ ^ 2) := integral_const_mul c _
    _ = c * ((π / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
          Complex.exp (-π ^ 2 * ‖ξ‖ ^ 2 / b)) := by rw [hG]
    _ = Complex.exp ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      have hmass :
          (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) = (baseHeatMass V : ℂ) := by
        dsimp [b]
        unfold baseHeatMass
        rw [Complex.ofReal_cpow (by positivity)]
        push_cast
        rfl
      rw [hmass]
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
        (baseHeatMass_pos (V := V)).ne')]
      simp only [one_mul]
      congr 1
      dsimp [b]
      push_cast
      ring

omit [Nontrivial V] in
/-- At positive time, the heat kernel has symbol `exp (-4 π² t ‖ξ‖²)`. -/
theorem heatKernel_fourier {t : ℝ} (ht : 0 < t) (ξ : V) :
    𝓕 (fun x : V => (heatKernel t x : ℂ)) ξ =
      Complex.exp ((-(4 * π ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  let r : ℝ := heatScale t
  let n : ℕ := Module.finrank ℝ V
  let phase : V → V → ℂ := fun x η =>
    Complex.exp (((-2 * π * inner ℝ x η : ℝ) : ℂ) * I)
  let f : V → ℂ := fun x => (baseHeat x : ℂ)
  have hr : 0 < r := heatScale_pos ht
  have hphase (x : V) : phase (r⁻¹ • x) (r • ξ) = phase x ξ := by
    dsimp [phase]
    congr 1
    push_cast
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hcv := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure V) (fun y : V => phase y (r • ξ) * f y) hr.le
  have hcv' :
      (∫ x : V, phase (r⁻¹ • x) (r • ξ) * f (r⁻¹ • x)) =
        (((r ^ n : ℝ) : ℂ) * ∫ y : V, phase y (r • ξ) * f y) := by
    simpa only [Function.comp_apply, Complex.real_smul, n] using hcv
  rw [fourier_eq']
  simp only [smul_eq_mul, heatKernel, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow]
  calc
    _ = ∫ x : V, phase x ξ * ((((r ^ n)⁻¹ : ℝ) : ℂ) * f (r⁻¹ • x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [phase, r, n, f]
      push_cast
      ring
    _ =
        (((r ^ n)⁻¹ : ℝ) : ℂ) *
          ∫ x : V, phase x ξ * f (r⁻¹ • x) := by
      calc
        (∫ x : V, phase x ξ * ((((r ^ n)⁻¹ : ℝ) : ℂ) * f (r⁻¹ • x))) =
            ∫ x : V, (((r ^ n)⁻¹ : ℝ) : ℂ) *
              (phase x ξ * f (r⁻¹ • x)) := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = (((r ^ n)⁻¹ : ℝ) : ℂ) *
            ∫ x : V, phase x ξ * f (r⁻¹ • x) := integral_const_mul _ _
    _ = (((r ^ n)⁻¹ : ℝ) : ℂ) *
          ∫ x : V, phase (r⁻¹ • x) (r • ξ) * f (r⁻¹ • x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [hphase]
    _ = (((r ^ n)⁻¹ : ℝ) : ℂ) *
          (((r ^ n : ℝ) : ℂ) * ∫ y : V, phase y (r • ξ) * f y) := by
      rw [hcv']
    _ = ∫ y : V, phase y (r • ξ) * f y := by
      rw [← mul_assoc]
      push_cast
      have hrC : (r : ℂ) ^ n ≠ 0 :=
        pow_ne_zero n (Complex.ofReal_ne_zero.mpr hr.ne')
      field_simp [hrC]
    _ = 𝓕 f (r • ξ) := by
      rw [fourier_eq']
      rfl
    _ = Complex.exp (-((4 : ℂ) * (π : ℂ) ^ 2 * (t : ℂ) * (‖ξ‖ : ℂ) ^ 2)) := by
      rw [baseHeat_fourier]
      congr 1
      have hr2 : r ^ 2 = t := by
        dsimp [r, heatScale]
        exact Real.sq_sqrt ht.le
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      push_cast
      rw [mul_pow, show (r : ℂ) ^ 2 = (t : ℂ) by exact_mod_cast hr2]
      ring

/-- The exponentially damped causal heat kernel on spacetime. -/
def dampHeat (δ : ℝ) (z : WithLp 2 (ℝ × V)) : ℂ :=
  if 0 < z.fst then
    Complex.exp (((-δ * z.fst : ℝ) : ℂ)) * (heatKernel z.fst z.snd : ℂ)
  else 0

/-- Positive damping makes the causal heat kernel integrable on spacetime. -/
theorem dampHeat_int {δ : ℝ} (hδ : 0 < δ) :
    Integrable (dampHeat (V := V) δ) := by
  rw [← (WithLp.volume_preserving_toLp (U := ℝ) (V := V)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × V)).measurableEmbedding]
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable
      (dampHeat (V := V) δ ∘ WithLp.toLp 2)
      ((volume : Measure ℝ).prod (volume : Measure V)) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun z : ℝ × V =>
      if 0 < z.fst then
        Complex.exp (((-δ * z.fst : ℝ) : ℂ)) * (heatKernel z.fst z.snd : ℂ)
      else 0)
    refine Measurable.ite (measurableSet_Ioi.preimage measurable_fst) ?_ measurable_const
    unfold heatKernel heatScale baseHeat
    measurability
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with t
    by_cases ht : 0 < t
    · simpa [dampHeat, ht] using
        ((heatKernel_int (V := V) ht).ofReal.const_mul
          (Complex.exp (((-δ * t : ℝ) : ℂ))))
    · simp [dampHeat, ht]
  · have hout : Integrable (fun t : ℝ =>
        if 0 < t then Real.exp (-δ * t) else 0) := by
      have hi := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0
      have hi' := hi.integrable_indicator measurableSet_Ioi
      simpa [Set.indicator, Set.mem_Ioi] using hi'
    convert hout using 1
    funext t
    by_cases ht : 0 < t
    · simp only [Function.comp_apply, dampHeat, WithLp.toLp_fst, WithLp.toLp_snd,
        ht, ↓reduceIte, norm_mul, Complex.norm_exp, Complex.ofReal_re, neg_mul,
        norm_real, Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (heatKernel_nonneg (V := V) ht _)]
      rw [integral_const_mul, integral_heatKernel (V := V) ht]
      simp
    · simp [Function.comp_apply, dampHeat, ht]

/-- The Fourier transform of the damped causal heat kernel is the parabolic
resolvent `1 / (δ + 4 π² ‖ξ‖² + 2 π i τ)`. -/
theorem dampHeat_fourier {δ : ℝ} (hδ : 0 < δ)
    (q : WithLp 2 (ℝ × V)) :
    𝓕 (dampHeat (V := V) δ) q =
      (((δ + 4 * π ^ 2 * ‖q.snd‖ ^ 2 : ℝ) : ℂ) +
        (((2 * π * q.fst : ℝ) : ℂ) * I))⁻¹ := by
  let raw : ℝ × V → ℂ := fun z =>
    Complex.exp (((-2 * π * inner ℝ (WithLp.toLp 2 z) q : ℝ) : ℂ) * I) *
      dampHeat (V := V) δ (WithLp.toLp 2 z)
  let G : ℝ × V → ℂ := fun z =>
    if 0 < z.fst then
      Complex.exp (((-2 * π *
        (z.fst * q.fst + inner ℝ z.snd q.snd) : ℝ) : ℂ) * I) *
        (Complex.exp (((-δ * z.fst : ℝ) : ℂ)) *
          (heatKernel z.fst z.snd : ℂ))
    else 0
  have hsp : Integrable (fun z : WithLp 2 (ℝ × V) =>
      Complex.exp (((-2 * π * inner ℝ z q : ℝ) : ℂ) * I) *
        dampHeat (V := V) δ z) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (WithLp 2 (ℝ × V))))
      (f := dampHeat (V := V) δ) q).2 (dampHeat_int (V := V) hδ)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul] using h
  have hraw : Integrable raw
      ((volume : Measure ℝ).prod (volume : Measure V)) := by
    have h := hsp
    rw [← (WithLp.volume_preserving_toLp (U := ℝ) (V := V)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (ℝ × V)).measurableEmbedding,
      Measure.volume_eq_prod] at h
    simpa only [raw, Function.comp_apply] using h
  have hEq (z : ℝ × V) : raw z = G z := by
    by_cases ht : 0 < z.fst
    · simp only [raw, G, dampHeat, ht, ↓reduceIte, WithLp.toLp_fst,
        WithLp.toLp_snd]
      rw [WithLp.prod_inner_apply]
      simp only [WithLp.ofLp_fst, WithLp.ofLp_snd]
      have hreal : inner ℝ z.fst q.fst = z.fst * q.fst := by
        change q.fst * z.fst = z.fst * q.fst
        ring
      rw [hreal]
    · simp [raw, G, dampHeat, ht]
  have hGint : Integrable G
      ((volume : Measure ℝ).prod (volume : Measure V)) :=
    hraw.congr (Filter.Eventually.of_forall hEq)
  have hinner (t : ℝ) :
      (∫ x : V, G (t, x)) =
        if 0 < t then
          Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
            Complex.exp (((-δ * t : ℝ) : ℂ)) *
            Complex.exp ((-(4 * π ^ 2 * t * ‖q.snd‖ ^ 2 : ℝ) : ℂ))
        else 0 := by
    by_cases ht : 0 < t
    · simp only [G, ht, ↓reduceIte]
      calc
        (∫ x : V,
            Complex.exp (((-2 * π *
              (t * q.fst + inner ℝ x q.snd) : ℝ) : ℂ) * I) *
              (Complex.exp (((-δ * t : ℝ) : ℂ)) *
                (heatKernel t x : ℂ))) =
            (Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
              Complex.exp (((-δ * t : ℝ) : ℂ))) *
              ∫ x : V, Complex.exp
                (((-2 * π * inner ℝ x q.snd : ℝ) : ℂ) * I) *
                (heatKernel t x : ℂ) := by
          calc
            (∫ x : V,
                Complex.exp (((-2 * π *
                  (t * q.fst + inner ℝ x q.snd) : ℝ) : ℂ) * I) *
                  (Complex.exp (((-δ * t : ℝ) : ℂ)) *
                    (heatKernel t x : ℂ))) =
                ∫ x : V,
                  (Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
                    Complex.exp (((-δ * t : ℝ) : ℂ))) *
                    (Complex.exp
                      (((-2 * π * inner ℝ x q.snd : ℝ) : ℂ) * I) *
                      (heatKernel t x : ℂ)) := by
              apply integral_congr_ae
              filter_upwards with x
              have hsplit :
                  Complex.exp (((-2 * π *
                    (t * q.fst + inner ℝ x q.snd) : ℝ) : ℂ) * I) =
                    Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
                      Complex.exp
                        (((-2 * π * inner ℝ x q.snd : ℝ) : ℂ) * I) := by
                rw [← Complex.exp_add]
                congr 1
                push_cast
                ring
              rw [hsplit]
              ring
            _ = (Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
                  Complex.exp (((-δ * t : ℝ) : ℂ))) *
                  ∫ x : V, Complex.exp
                    (((-2 * π * inner ℝ x q.snd : ℝ) : ℂ) * I) *
                    (heatKernel t x : ℂ) := integral_const_mul _ _
        _ = (Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
              Complex.exp (((-δ * t : ℝ) : ℂ))) *
              𝓕 (fun x : V => (heatKernel t x : ℂ)) q.snd := by
          rw [fourier_eq']
          rfl
        _ = Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
              Complex.exp (((-δ * t : ℝ) : ℂ)) *
              Complex.exp ((-(4 * π ^ 2 * t * ‖q.snd‖ ^ 2 : ℝ) : ℂ)) := by
          rw [heatKernel_fourier ht]
    · simp [G, ht]
  let d : ℂ := ((δ + 4 * π ^ 2 * ‖q.snd‖ ^ 2 : ℝ) : ℂ) +
    (((2 * π * q.fst : ℝ) : ℂ) * I)
  let a : ℂ := -d
  have ha : a.re < 0 := by
    have hnon : 0 ≤ 4 * π ^ 2 * ‖q.snd‖ ^ 2 := by positivity
    dsimp [a, d]
    simp only [mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have htime (t : ℝ) :
      (if 0 < t then
          Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
            Complex.exp (((-δ * t : ℝ) : ℂ)) *
            Complex.exp ((-(4 * π ^ 2 * t * ‖q.snd‖ ^ 2 : ℝ) : ℂ))
        else 0) =
      Set.indicator (Ioi (0 : ℝ)) (fun s : ℝ =>
        Complex.exp (a * (s : ℂ))) t := by
    by_cases ht : 0 < t
    · simp only [ht, ↓reduceIte, Set.indicator_of_mem, Set.mem_Ioi]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      dsimp [a, d]
      push_cast
      ring
    · have htm : t ∉ Ioi (0 : ℝ) := by simpa only [Set.mem_Ioi, not_lt] using ht
      simp [ht, htm]
  rw [fourier_eq']
  rw [← (WithLp.volume_preserving_toLp (U := ℝ) (V := V)).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × V)).measurableEmbedding,
    Measure.volume_eq_prod]
  change (∫ z : ℝ × V, raw z) = _
  calc
    (∫ z : ℝ × V, raw z) = ∫ z : ℝ × V, G z :=
      integral_congr_ae (Filter.Eventually.of_forall hEq)
    _ = ∫ t : ℝ, ∫ x : V, G (t, x) := integral_prod _ hGint
    _ = ∫ t : ℝ, if 0 < t then
          Complex.exp (((-2 * π * t * q.fst : ℝ) : ℂ) * I) *
            Complex.exp (((-δ * t : ℝ) : ℂ)) *
            Complex.exp ((-(4 * π ^ 2 * t * ‖q.snd‖ ^ 2 : ℝ) : ℂ))
        else 0 := by
      apply integral_congr_ae
      filter_upwards with t
      exact hinner t
    _ = ∫ t : ℝ in Ioi 0, Complex.exp (a * (t : ℂ)) := by
      simp_rw [htime]
      rw [integral_indicator measurableSet_Ioi]
    _ = -Complex.exp (a * (0 : ℂ)) / a :=
      integral_exp_mul_complex_Ioi ha 0
    _ = d⁻¹ := by simp [a]
    _ = (((δ + 4 * π ^ 2 * ‖q.snd‖ ^ 2 : ℝ) : ℂ) +
          (((2 * π * q.fst : ℝ) : ℂ) * I))⁻¹ := rfl

end DifferentialGeometry.Analysis.Parabolic.Euclidean
