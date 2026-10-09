import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.FiniteTaylorPolynomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Filter Metric Asymptotics
open scoped Topology ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

private theorem coefficient_zero_of_monomial_littleO {c : ℝ} {n : ℕ}
    (h : (fun t : ℝ => c * t ^ n) =o[𝓝 (0 : ℝ)] (fun t => t ^ n)) : c = 0 := by
  by_contra hc
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖c * t ^ n‖ ≤ |c| / 2 * ‖t ^ n‖ :=
    (h.bound (half_pos hcpos)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hb.and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t)).exists
  have hp : 0 < t ^ n := pow_pos htpos n
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos htpos] at ht
  nlinarith

private theorem taylor_eq_last_of_lower_zero (f : ℝ → ℝ) (n : ℕ)
    (h : ∀ j < n, iteratedDeriv j f 0 = 0) (t : ℝ) :
    taylorWithinEval f n univ 0 t =
      (n.factorial : ℝ)⁻¹ * iteratedDeriv n f 0 * t ^ n := by
  rw [taylor_within_apply, Finset.sum_range_succ]
  have hsum : ∑ j ∈ Finset.range n,
      ((j.factorial : ℝ)⁻¹ * (t - 0) ^ j) • iteratedDerivWithin j f univ 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [iteratedDerivWithin_univ, h j (Finset.mem_range.mp hj), smul_zero]
  rw [hsum]
  simp only [zero_add, sub_zero, iteratedDerivWithin_univ, smul_eq_mul]
  ring

private theorem scalar_jets_of_monomial_asymptotic {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {n : ℕ} {c : ℝ}
    (h : (fun t : ℝ => f t - c * t ^ n) =o[𝓝 (0 : ℝ)] (fun t => t ^ n)) :
    (∀ j < n, iteratedDeriv j f 0 = 0) ∧
      (n.factorial : ℝ)⁻¹ * iteratedDeriv n f 0 = c := by
  have hzero : ∀ j < n, iteratedDeriv j f 0 = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have hbelow : ∀ i < j, iteratedDeriv i f 0 = 0 :=
        fun i hi => ih i hi (lt_trans hi hj)
      have hp : (fun t : ℝ => t ^ n) =o[𝓝 (0 : ℝ)] (fun t => t ^ j) :=
        isLittleO_pow_pow hj
      have hs : f =o[𝓝 (0 : ℝ)] (fun t => t ^ j) := by
        have hh := (h.trans_isBigO hp.isBigO).add (hp.const_mul_left c)
        simpa only [sub_add_cancel] using hh
      have ht := taylor_isLittleO_univ (hf.of_le (m := (j : ℕ∞ω)) (by simp))
        (x₀ := (0 : ℝ))
      simp only [sub_zero, taylor_eq_last_of_lower_zero f j hbelow] at ht
      have hc : (j.factorial : ℝ)⁻¹ * iteratedDeriv j f 0 = 0 := by
        apply coefficient_zero_of_monomial_littleO (n := j)
        have hh := hs.sub ht
        simpa only [sub_sub_cancel] using hh
      exact (mul_eq_zero.mp hc).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j))
  refine ⟨hzero, ?_⟩
  have ht := taylor_isLittleO_univ (hf.of_le (m := (n : ℕ∞ω)) (by simp))
    (x₀ := (0 : ℝ))
  simp only [sub_zero, taylor_eq_last_of_lower_zero f n hzero] at ht
  have hc : (n.factorial : ℝ)⁻¹ * iteratedDeriv n f 0 - c = 0 := by
    apply coefficient_zero_of_monomial_littleO (n := n)
    convert h.sub ht using 1
    ext t
    ring
  exact sub_eq_zero.mp hc


private theorem scalar_jets_of_derivative_factor {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hvalue : f 0 = 0) {k : ℕ} {c : ℝ → ℝ}
    (hc : ContinuousAt c 0)
    (hfactor : deriv f =ᶠ[𝓝 (0 : ℝ)] (fun t => t ^ k * c t)) :
    (∀ j ≤ k, iteratedDeriv j f 0 = 0) ∧
      ((k + 1).factorial : ℝ)⁻¹ * iteratedDeriv (k + 1) f 0 =
        c 0 / ((k + 1 : ℕ) : ℝ) := by
  have hs : (fun t => c t - c 0) =o[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hc.tendsto.sub_const (c 0)
  have hm := hs.mul_isBigO (isBigO_refl (fun t : ℝ => t ^ k) (𝓝 0))
  have ha : (fun t => deriv f t - c 0 * t ^ k) =o[𝓝 (0 : ℝ)]
      (fun t => t ^ k) := by
    apply hm.congr'
    · filter_upwards [hfactor] with t ht
      rw [ht]
      ring
    · exact Eventually.of_forall (fun t => one_mul (t ^ k))
  have hg : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  obtain ⟨hlower, htop⟩ := scalar_jets_of_monomial_asymptotic hg ha
  refine ⟨?_, ?_⟩
  · intro j hj
    cases j with
    | zero => simpa using hvalue
    | succ j =>
      rw [iteratedDeriv_succ']
      exact hlower j (by omega)
  · calc
      _ = (((k + 1 : ℕ) : ℝ))⁻¹ *
          ((k.factorial : ℝ)⁻¹ * iteratedDeriv k (deriv f) 0) := by
        rw [iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
        ring
      _ = c 0 / ((k + 1 : ℕ) : ℝ) := by rw [htop]; ring


variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem exists_smooth_extension_same_germ
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → V} (hv : ContDiffOn ℝ ∞ v Ω) :
    ∃ w : ℂ → V, ContDiff ℝ ∞ w ∧ w =ᶠ[𝓝 a] v := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds ha)
  let χ : ContDiffBump a := {
    rIn := r / 2
    rOut := r
    rIn_pos := half_pos hr
    rIn_lt_rOut := by linarith }
  have hχs : tsupport χ ⊆ Ω := by rw [χ.tsupport_eq]; exact hrΩ
  let w : ℂ → V := fun z => χ z • v z
  refine ⟨w, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ Ω
    · exact χ.contDiffAt.smul (hv.contDiffAt (hΩ.mem_nhds hz))
    · have hn : z ∉ tsupport χ := fun hh => hz (hχs hh)
      have heq : w =ᶠ[𝓝 z] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        simp only [w, hy, zero_smul, Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [ball_mem_nhds a (half_pos hr)] with z hz
    have hχ : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp only [w, hχ, one_smul]


private theorem fderiv_eq_planarComplexGradient_pair (v : ℂ → ℝ) (z B : ℂ) :
    (fderiv ℝ v z B : ℂ) =
      B * planarComplexGradient v z + conj B * conj (planarComplexGradient v z) := by
  have hB : B = B.re • (1 : ℂ) + B.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hB, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [planarComplexGradient, Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring


private theorem fderiv_eq_two_re_planarComplexGradient (v : ℂ → ℝ) (x z : ℂ) :
    fderiv ℝ v x z = 2 * (z * planarComplexGradient v x).re := by
  have h := congrArg Complex.re (fderiv_eq_planarComplexGradient_pair v x z)
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im] at h ⊢
  linarith

private theorem planar_line_jets_of_gradient_factor
    {v : ℂ → ℝ} {a : ℂ} (hv : ContDiff ℝ ∞ v) (hvalue : v a = 0)
    {k : ℕ} {b : ℂ → ℂ} (hb : ContinuousAt b a)
    (hfactor : ∀ᶠ x in 𝓝 a, planarComplexGradient v x = (x - a) ^ k * b x)
    (z : ℂ) :
    (∀ j ≤ k, iteratedFDeriv ℝ j v a (fun _ => z) = 0) ∧
      ((k + 1).factorial : ℝ)⁻¹ * iteratedFDeriv ℝ (k + 1) v a (fun _ => z) =
        (2 / ((k + 1 : ℕ) : ℝ)) * (b a * z ^ (k + 1)).re := by
  let f : ℝ → ℝ := fun t => v (a + t • z)
  let c : ℝ → ℝ := fun t => 2 * (b (a + t • z) * z ^ (k + 1)).re
  have hline : ContDiff ℝ ∞ (fun t : ℝ => a + t • z) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline0 : Tendsto (fun t : ℝ => a + t • z) (𝓝 0) (𝓝 a) := by
    simpa only [zero_smul, add_zero] using hline.continuous.tendsto (0 : ℝ)
  have hf : ContDiff ℝ ∞ f := hv.comp hline
  have hf0 : f 0 = 0 := by simpa only [f, zero_smul, add_zero] using hvalue
  have hbc : ContinuousAt (fun t : ℝ => b (a + t • z)) 0 := by
    change Tendsto (fun t : ℝ => b (a + t • z)) (𝓝 0) (𝓝 (b (a + 0 • z)))
    simpa only [Function.comp_def, zero_smul, add_zero] using hb.tendsto.comp hline0
  have hc : ContinuousAt c 0 :=
    continuousAt_const.mul
      (Complex.continuous_re.continuousAt.comp (hbc.mul_const (z ^ (k + 1))))
  have hdf : deriv f =ᶠ[𝓝 (0 : ℝ)] (fun t => t ^ k * c t) := by
    filter_upwards [hline0.eventually hfactor] with t ht
    have hcurve : HasDerivAt (fun s : ℝ => a + s • z) z t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const z).const_add a
    have hd := (hv.differentiable (by simp) (a + t • z)).hasFDerivAt.comp_hasDerivAt t hcurve
    change deriv (v ∘ fun s : ℝ => a + s • z) t = t ^ k * c t
    rw [hd.deriv, fderiv_eq_two_re_planarComplexGradient, ht]
    have he : z * ((a + t • z - a) ^ k * b (a + t • z)) =
        (t ^ k) • (b (a + t • z) * z ^ (k + 1)) := by
      simp only [add_sub_cancel_left, Complex.real_smul, mul_pow, Complex.ofReal_pow, pow_succ]
      ring
    rw [he]
    simp only [Complex.smul_re, smul_eq_mul, c]
    ring
  obtain ⟨hlower, htop⟩ := scalar_jets_of_derivative_factor hf hf0 hc hdf
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [← iteratedDeriv_line hv.contDiffAt j]
    exact hlower j hj
  · rw [← iteratedDeriv_line hv.contDiffAt (k + 1)]
    change ((k + 1).factorial : ℝ)⁻¹ * iteratedDeriv (k + 1) f 0 = _
    rw [htop]
    simp only [c, zero_smul, add_zero]
    ring

/-- A continuous factor of the actual complex gradient determines the exact
first scalar homogeneous term and all lower real jets of the same smooth scalar.
The whole-jet conclusion uses the genuine finite-Taylor jet matching theorem,
whose proof includes iterated-derivative symmetry. -/
theorem planar_jets_of_complex_gradient_factor
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v Ω) (hvalue : v a = 0)
    {k : ℕ} {b : ℂ → ℂ} (hb : ContinuousOn b Ω)
    (hfactor : ∀ z ∈ Ω, planarComplexGradient v z = (z - a) ^ k * b z) :
    (∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j v a = 0) ∧
    ∀ z : ℂ,
      (((k + 1).factorial : ℝ)⁻¹) *
          iteratedFDeriv ℝ (k + 1) v a (fun _ => z) =
        (2 / ((k + 1 : ℕ) : ℝ)) * (b a * z ^ (k + 1)).re := by
  obtain ⟨w, hw, hwv⟩ := exists_smooth_extension_same_germ hΩ ha hv
  have hw0 : w a = 0 := hwv.eq_of_nhds.trans hvalue
  have hfactorw : ∀ᶠ x in 𝓝 a, planarComplexGradient w x = (x - a) ^ k * b x := by
    filter_upwards [hΩ.mem_nhds ha, hwv.fderiv (𝕜 := ℝ)] with x hx hDx
    simpa only [planarComplexGradient, hDx] using hfactor x hx
  have hline (z : ℂ) := planar_line_jets_of_gradient_factor hw hw0
    (hb.continuousAt (hΩ.mem_nhds ha)) hfactorw z
  have hpoly : finiteTaylorPolynomial w a k = 0 := by
    funext x
    unfold finiteTaylorPolynomial
    apply Finset.sum_eq_zero
    intro j hj
    rw [(hline (x - a)).1 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), smul_zero]
  constructor
  · intro j hj
    rw [← (hwv.iteratedFDeriv ℝ j).eq_of_nhds,
      ← iteratedFDeriv_finiteTaylorPolynomial (hw.contDiffAt.of_le (by simp)) hj,
      hpoly, iteratedFDeriv_zero]
    rfl
  · intro z
    rw [← (hwv.iteratedFDeriv ℝ (k + 1)).eq_of_nhds]
    exact (hline z).2

end DifferentialGeometry.Analysis
