import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclid
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldPolar

/-!
# The apex germs of the compact fold: smoothness and Jacobians

Lane CF, tier 2 (design `docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§0 and §4). The outer germ `compactOuterGerm p z = -(7/2 - ‖z‖^p/2) (z̄/‖z‖)^p` is the base part of
X13's seam model on the outer hole, extended to `0 < |v| < 1 + ε`. In polar form it is
`(7/2 - r^p/2) e^{i(π - p φ)}` (`compactOuterGerm_eq_polar`, any branch of the angle), so it is
smooth off `0` and, by A4's polar Jacobian formula `det_fderiv_polar` along the circle and the ray
through the point, its Jacobian is positive wherever `0 < ‖z‖` and `‖z‖^p < 7`
(`det_fderiv_compactOuterGerm_pos`): the radius decreases and the angle is reversed. The two inner
apex models of a flat shape, `3/2 + rotOne^{p₁}/2` and `-3/2 + rotTwo^{p₂}/2`, are holomorphic with
nonvanishing derivative off their vertex, hence have positive Jacobian there
(`det_fderiv_apexOne_pos`, `det_fderiv_apexTwo_pos`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

theorem contDiffAt_arg_of_mem_slitPlane {z : ℂ} (h : z ∈ slitPlane) :
    ContDiffAt ℝ ∞ (fun u : ℂ => arg u) z := by
  have hl : ContDiffAt ℝ ∞ log z := (contDiffAt_log h).restrict_scalars ℝ
  have e : (fun u : ℂ => arg u) = fun u => (log u).im := by
    funext u
    rw [log_im]
  rw [e]
  exact imCLM.contDiff.contDiffAt.comp z hl

theorem norm_exp_neg_mul_I (α : ℝ) : ‖exp (-((α : ℂ) * I))‖ = 1 := by
  rw [show -((α : ℂ) * I) = ((-α : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

theorem conj_div_norm_eq {u : ℂ} (hu : u ≠ 0) (α : ℝ) :
    conj u / ‖u‖ = exp (-(((arg (u * exp (-((α : ℂ) * I))) + α : ℝ) : ℂ) * I)) := by
  have hn : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu
  have hn' : ‖u * exp (-((α : ℂ) * I))‖ = ‖u‖ := by
    rw [norm_mul, norm_exp_neg_mul_I, mul_one]
  have hp := norm_mul_exp_arg_mul_I (u * exp (-((α : ℂ) * I)))
  rw [hn'] at hp
  have hu' : u = ‖u‖ * exp ((((arg (u * exp (-((α : ℂ) * I))) + α : ℝ) : ℂ) * I)) := by
    push_cast
    rw [add_mul, Complex.exp_add, ← mul_assoc, hp, mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one]
  have hc : conj u = ‖u‖ * exp (-(((arg (u * exp (-((α : ℂ) * I))) + α : ℝ) : ℂ) * I)) := by
    conv_lhs => rw [hu']
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc]
  have : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  field_simp

theorem compactOuterGerm_eq_polar (p : ℕ) (α : ℝ) {u : ℂ} (hu : u ≠ 0) :
    compactOuterGerm p u = 0 + ((7 / 2 - ‖u‖ ^ p / 2 : ℝ) : ℂ) *
      exp (((Real.pi - p * (arg (u * exp (-((α : ℂ) * I))) + α) : ℝ) : ℂ) * I) := by
  rw [compactOuterGerm, conj_div_norm_eq hu α, ← Complex.exp_nat_mul, zero_add]
  rw [show (((Real.pi - p * (arg (u * exp (-((α : ℂ) * I))) + α) : ℝ) : ℂ) * I) =
      Real.pi * I + (p : ℂ) * -(((arg (u * exp (-((α : ℂ) * I))) + α : ℝ) : ℂ) * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem contDiffAt_compactOuterGerm (p : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (compactOuterGerm p) z := by
  have hn : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ hz
  have hn0 : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : ContDiff ℝ ∞ (fun u : ℂ => conj u) := conjCLE.contDiff
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => (((7 / 2 - ‖u‖ ^ p / 2 : ℝ)) : ℂ)) z :=
    hof.contDiffAt.comp z (contDiffAt_const.sub ((hn.pow p).div_const 2))
  have h3 : ContDiffAt ℝ ∞ (fun u : ℂ => ((‖u‖⁻¹ : ℝ) : ℂ)) z :=
    hof.contDiffAt.comp z (hn.inv (norm_ne_zero_iff.2 hz))
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => conj u / (‖u‖ : ℂ)) z := by
    have e : (fun u : ℂ => conj u / (‖u‖ : ℂ)) = fun u => conj u * ((‖u‖⁻¹ : ℝ) : ℂ) := by
      funext u
      push_cast
      rw [div_eq_mul_inv]
    rw [e]
    exact hc.contDiffAt.mul h3
  exact (h1.mul (h2.pow p)).neg

theorem det_fderiv_compactOuterGerm_pos {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ≠ 0)
    (h7 : ‖z‖ ^ p < 7) : 0 < (fderiv ℝ (compactOuterGerm p) z).det := by
  set α := arg z with hα
  set r := ‖z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hz
  set Θ : ℂ → ℝ := fun u => Real.pi - p * (arg (u * exp (-((α : ℂ) * I))) + α) with hΘ
  set S : ℝ → ℝ := fun ρ => 7 / 2 - ρ ^ p / 2 with hS
  have hzr : z * exp (-((α : ℂ) * I)) = (r : ℂ) := by
    have h := norm_mul_exp_arg_mul_I z
    rw [← hα, ← hr] at h
    conv_lhs => rw [← h]
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hslit : z * exp (-((α : ℂ) * I)) ∈ slitPlane := by
    rw [hzr]
    exact ofReal_mem_slitPlane.2 hr0
  have hEq : (fun u => compactOuterGerm p u) =ᶠ[nhds z]
      fun u => 0 + (S ‖u‖ : ℂ) * exp ((Θ u : ℂ) * I) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with u hu
    exact compactOuterGerm_eq_polar p α hu
  have hfd : fderiv ℝ (compactOuterGerm p) z =
      fderiv ℝ (fun u => 0 + (S ‖u‖ : ℂ) * exp ((Θ u : ℂ) * I)) z := hEq.fderiv_eq
  have hSd : HasDerivAt S (-(p * r ^ (p - 1) / 2)) r := by
    have := ((hasDerivAt_pow p r).div_const 2).const_sub (7 / 2)
    simpa [hS, neg_div] using this
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z :=
    (contDiffAt_norm ℝ hz : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z).differentiableAt (by simp)
  have hargd : DifferentiableAt ℝ (fun u : ℂ => arg (u * exp (-((α : ℂ) * I)))) z := by
    have h1 := (contDiffAt_arg_of_mem_slitPlane hslit).differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (fun u : ℂ => u * exp (-((α : ℂ) * I))) z :=
      differentiableAt_id.mul_const _
    exact h1.comp z h2
  have hΘd : DifferentiableAt ℝ Θ z :=
    (differentiableAt_const _).sub ((hargd.add_const α).const_mul _)
  set γ : ℝ → ℂ := fun t => z * exp ((t : ℂ) * I) with hγ
  have hγd : HasDerivAt γ (z * I) 0 := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp.const_mul z
    simpa [hγ] using h
  have hγ0 : γ 0 = z := by simp [hγ]
  have hργ : ∀ᶠ t in nhds (0 : ℝ), ‖γ t‖ = r := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [hγ, norm_mul, show (t : ℂ) * I = ((t : ℝ) : ℂ) * I from rfl, norm_exp_ofReal_mul_I,
      mul_one]
  have hargγ : ∀ᶠ t in nhds (0 : ℝ), arg (γ t * exp (-((α : ℂ) * I))) = t := by
    have hI : Set.Ioo (-Real.pi) Real.pi ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
    filter_upwards [hI] with t ht
    change arg (z * exp ((t : ℂ) * I) * exp (-((α : ℂ) * I))) = t
    rw [mul_right_comm, hzr, arg_real_mul _ hr0, Complex.exp_mul_I,
      arg_cos_add_sin_mul_I ⟨ht.1, ht.2.le⟩]
  have hΘγ : HasDerivAt (fun t => Θ (γ t)) (-(p : ℝ)) 0 := by
    have h : HasDerivAt (fun t : ℝ => Real.pi - p * (t + α)) (-(p : ℝ)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).add_const α).const_mul (p : ℝ)
      simpa using this.const_sub Real.pi
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hargγ] with t ht
    simp only [hΘ, ht]
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * z‖) r 0 := by
    have h : HasDerivAt (fun t : ℝ => (1 + t) * r) r 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const r
    refine h.congr_of_eventuallyEq ?_
    have hI : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [hI] with t ht
    have ht' : 0 < 1 + t := by linarith [show -1 < t from ht]
    rw [show z + (t : ℂ) * z = ((1 + t : ℝ) : ℂ) * z by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']
  have hΘN : HasDerivAt (fun t : ℝ => Θ (z + t * z)) 0 0 := by
    have h : HasDerivAt (fun _ : ℝ => Real.pi - p * (0 + α)) 0 0 := hasDerivAt_const _ _
    refine h.congr_of_eventuallyEq ?_
    have hI : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [hI] with t ht
    have ht' : 0 < 1 + t := by linarith [show -1 < t from ht]
    simp only [hΘ]
    rw [show (z + (t : ℂ) * z) * exp (-((α : ℂ) * I)) = ((1 + t : ℝ) : ℂ) * (r : ℂ) by
      rw [← hzr]; push_cast; ring, arg_real_mul _ ht', arg_ofReal_of_nonneg hr0.le]
  have key := det_fderiv_polar (c := 0) (S := S) (ρ := fun u : ℂ => ‖u‖) (Θ := Θ) (N := z)
    hSd hρ hΘd hγd hγ0 hργ hΘγ hρN hΘN
  rw [← hfd] at key
  have hcross : z.re * (z * I).im - (z * I).re * z.im = r ^ 2 := by
    rw [hr, ← Complex.normSq_eq_norm_sq, normSq_apply]
    simp only [mul_im, mul_re, I_re, I_im]
    ring
  rw [hcross] at key
  have hS0 : 0 < S r := by
    simp only [hS]
    linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpos : 0 < S r * -(p * r ^ (p - 1) / 2) * -(p : ℝ) * r := by
    have : 0 < r ^ (p - 1) := pow_pos hr0 _
    have e : S r * -(p * r ^ (p - 1) / 2) * -(p : ℝ) * r = S r * (p * p * r ^ (p - 1) * r / 2) := by
      ring
    rw [e]
    positivity
  have hr2 : 0 < r ^ 2 := by positivity
  have h' : 0 < (fderiv ℝ (compactOuterGerm p) z).det * r ^ 2 := by
    rw [key]
    exact hpos
  by_contra hneg
  nlinarith [not_lt.1 hneg]

namespace EuclidShape

variable (σ : EuclidShape)

theorem hasDerivAt_rotOne (z : ℂ) : HasDerivAt σ.rotOne (-exp (-((σ.θ₃ : ℂ) * I))) z := by
  have h : HasDerivAt (fun y : ℂ => -(exp (-((σ.θ₃ : ℂ) * I)) * (y - σ.vertexOne)))
      (-(exp (-((σ.θ₃ : ℂ) * I)) * 1)) z :=
    (((hasDerivAt_id' z).sub_const σ.vertexOne).const_mul _).neg
  rw [mul_one] at h
  exact h

theorem hasDerivAt_rotTwo (z : ℂ) : HasDerivAt σ.rotTwo (-exp ((σ.θ₂ : ℂ) * I)) z := by
  have h : HasDerivAt (fun y : ℂ => -(exp ((σ.θ₂ : ℂ) * I) * (y - σ.vertexTwo)))
      (-(exp ((σ.θ₂ : ℂ) * I) * 1)) z :=
    (((hasDerivAt_id' z).sub_const σ.vertexTwo).const_mul _).neg
  rw [mul_one] at h
  exact h

theorem det_fderiv_apexOne_pos {z : ℂ} (hz : z ≠ σ.vertexOne) :
    0 < (fderiv ℝ σ.apexOne z).det := by
  have hd : HasDerivAt σ.apexOne
      ((σ.p₁ : ℂ) * σ.rotOne z ^ (σ.p₁ - 1) * -exp (-((σ.θ₃ : ℂ) * I)) / 2) z := by
    exact (((σ.hasDerivAt_rotOne z).pow σ.p₁).div_const 2).const_add (3 / 2)
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hr : σ.rotOne z ≠ 0 := by
    intro h
    apply hz
    have : exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne) = 0 := neg_eq_zero.1 h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (Complex.exp_ne_zero _)
    · exact sub_eq_zero.1 h1
  have hp : (σ.p₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₁; omega)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hr))
    (neg_ne_zero.2 (Complex.exp_ne_zero _))) two_ne_zero

theorem det_fderiv_apexTwo_pos {z : ℂ} (hz : z ≠ σ.vertexTwo) :
    0 < (fderiv ℝ σ.apexTwo z).det := by
  have hd : HasDerivAt σ.apexTwo
      ((σ.p₂ : ℂ) * σ.rotTwo z ^ (σ.p₂ - 1) * -exp ((σ.θ₂ : ℂ) * I) / 2) z := by
    exact (((σ.hasDerivAt_rotTwo z).pow σ.p₂).div_const 2).const_add (-(3 / 2))
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hr : σ.rotTwo z ≠ 0 := by
    intro h
    apply hz
    have : exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo) = 0 := neg_eq_zero.1 h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (Complex.exp_ne_zero _)
    · exact sub_eq_zero.1 h1
  have hp : (σ.p₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₂; omega)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hr))
    (neg_ne_zero.2 (Complex.exp_ne_zero _))) two_ne_zero

theorem contDiff_apexOne : ContDiff ℝ ∞ σ.apexOne := by
  have h : ContDiff ℂ ∞ σ.apexOne := by
    unfold apexOne rotOne
    fun_prop
  exact h.restrict_scalars ℝ

theorem contDiff_apexTwo : ContDiff ℝ ∞ σ.apexTwo := by
  have h : ContDiff ℂ ∞ σ.apexTwo := by
    unfold apexTwo rotTwo
    fun_prop
  exact h.restrict_scalars ℝ

end EuclidShape

end GC.Seifert
