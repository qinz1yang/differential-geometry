import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPhase
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatScrews
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclid

/-!
# The fibre phase of a closed triangle block on a flat base

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.4, confirmed by review 27). Phase data are the twists `kⱼ = qⱼ/pⱼ` of the three cones (cone `3`
on the outer hole), the connection curvature `c` of the model, the signed fibre step `ℓ` and the
inner vertices `v₁`, `v₂`; `e = -(k₁ + k₂ + k₃)`. With `φ_c = phaseArg c`, smooth cutoffs
`step` (of `Re u`), `eta` and `chi` (of `|u|²`; `eta = 1` on `|u| ≤ 5/2`, `0` on `|u| ≥ 11/4`;
`chi = 0` on `|u| ≤ 11/4`, `1` on `|u| ≥ 3`), the local gauges `ψⱼ z = -c (vⱼ × z)/2`,
`χ₁ = eta·step`, `χ₂ = eta·(1 - step)` and `Λ = -π step - π chi (1 - step)`, the phase is
`Θ(z, u) = (1 - chi)(k₁ φ_{3/2} u + k₂ φ_{-3/2} u) - chi k₃ φ₀ u + (2π/ℓ)(χ₁ ψ₁ z + χ₂ ψ₂ z) + e Λ`.
The three wall rules (`theta_wallZero`, `theta_wallOne`, `theta_wallTwo`; the last one uses the
closing equation `-c (v₁ × v₂) = ℓ e`) and the three vertex formulas (`theta_vertexOne`,
`theta_vertexTwo`, `theta_outer`) are exact identities. The outer formula is the pure
`-k₃ φ₀ - π e`; with `φ₀ (outerGerm_p z) = π - p arg z` (`phaseArg_compactOuterGerm`) it is
`q₃ arg z` up to a constant, which is a sufficient (not a necessary) choice for the outer tube.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped ContDiff ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

structure PhaseData where
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ
  c : ℝ
  ℓ : ℝ
  v₁ : ℂ
  v₂ : ℂ

namespace PhaseData

variable (P : PhaseData)

def e : ℝ := -(P.k₁ + P.k₂ + P.k₃)

def step (u : ℂ) : ℝ := Real.smoothTransition ((u.re + 1) / 2)

def eta (u : ℂ) : ℝ := 1 - Real.smoothTransition ((normSq u - 25 / 4) / (21 / 16))

def chi (u : ℂ) : ℝ := Real.smoothTransition ((normSq u - 121 / 16) / (23 / 16))

def chiOne (u : ℂ) : ℝ := eta u * step u

def chiTwo (u : ℂ) : ℝ := eta u * (1 - step u)

def lam (u : ℂ) : ℝ := -Real.pi * step u - Real.pi * chi u * (1 - step u)

def psi (v z : ℂ) : ℝ := -P.c * planeCrossC v z / 2

def theta (z u : ℂ) : ℝ :=
  (1 - chi u) * (P.k₁ * phaseArg (3 / 2) u + P.k₂ * phaseArg (-(3 / 2)) u) -
      chi u * P.k₃ * phaseArg 0 u +
    2 * Real.pi / P.ℓ * (chiOne u * P.psi P.v₁ z + chiTwo u * P.psi P.v₂ z) + P.e * lam u

theorem step_eq_one {u : ℂ} (h : 1 ≤ u.re) : step u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {u : ℂ} (h : u.re ≤ -1) : step u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem eta_eq_one {u : ℂ} (h : normSq u ≤ 25 / 4) : eta u = 1 := by
  unfold eta
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by norm_num)), sub_zero]

theorem eta_eq_zero {u : ℂ} (h : 121 / 16 ≤ normSq u) : eta u = 0 := by
  unfold eta
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith),
    sub_self]

theorem chi_eq_zero {u : ℂ} (h : normSq u ≤ 121 / 16) : chi u = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by norm_num))

theorem chi_eq_one {u : ℂ} (h : 9 ≤ normSq u) : chi u = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

theorem step_conj (u : ℂ) : step (conj u) = step u := by simp [step]

theorem eta_conj (u : ℂ) : eta (conj u) = eta u := by simp [eta]

theorem chi_conj (u : ℂ) : chi (conj u) = chi u := by simp [chi]

theorem lam_conj (u : ℂ) : lam (conj u) = lam u := by simp [lam, step_conj, chi_conj]

theorem chiOne_conj (u : ℂ) : chiOne (conj u) = chiOne u := by
  simp [chiOne, eta_conj, step_conj]

theorem chiTwo_conj (u : ℂ) : chiTwo (conj u) = chiTwo u := by
  simp [chiTwo, eta_conj, step_conj]

theorem psi_add (v z z' : ℂ) : P.psi v z + P.psi v z' = -P.c * planeCrossC v (z + z') / 2 := by
  simp only [psi, planeCrossC, add_re, add_im]
  ring

theorem theta_wallOne {z z' u : ℂ} (h : 3 / 2 < u.re)
    (hψ : P.psi P.v₁ z' = -P.psi P.v₁ z) :
    P.theta z u + P.theta z' (conj u) = -(2 * Real.pi * P.e) := by
  have hs : step u = 1 := step_eq_one (by linarith)
  have h2 : chiTwo u = 0 := by simp [chiTwo, hs]
  have hl : lam u = -Real.pi := by simp [lam, hs]
  unfold theta
  rw [chi_conj, chiOne_conj, chiTwo_conj, lam_conj, h2, hl,
    phaseArg_conj_of_lt (show ((3 / 2 : ℝ) : ℝ) < u.re by linarith),
    phaseArg_conj_of_lt (show (-(3 / 2) : ℝ) < u.re by linarith),
    phaseArg_conj_of_lt (show (0 : ℝ) < u.re by linarith), hψ]
  ring

theorem theta_wallZero {z z' u : ℂ} (h : u.re < -(3 / 2))
    (hψ : P.psi P.v₂ z' = -P.psi P.v₂ z) :
    P.theta z u + P.theta z' (conj u) = 2 * Real.pi * (P.k₁ + P.k₂) := by
  have hs : step u = 0 := step_eq_zero (by linarith)
  have h1 : chiOne u = 0 := by simp [chiOne, hs]
  have hl : lam u = -Real.pi * chi u := by simp [lam, hs]
  unfold theta
  rw [chi_conj, chiOne_conj, chiTwo_conj, lam_conj, h1, hl,
    phaseArg_conj_of_gt (show u.re < ((3 / 2 : ℝ) : ℝ) by linarith),
    phaseArg_conj_of_gt (show u.re < (-(3 / 2) : ℝ) by linarith),
    phaseArg_conj_of_gt (show u.re < (0 : ℝ) by linarith), hψ]
  unfold e
  ring

theorem theta_wallTwo {z z' u : ℂ} (h1 : -(3 / 2) < u.re) (h2 : u.re < 3 / 2)
    (h3 : normSq u ≤ 25 / 4) (hℓ : P.ℓ ≠ 0) (τ : ℝ)
    (hM : (z + z') / 2 = P.v₁ + τ * (P.v₂ - P.v₁))
    (hclose : -P.c * planeCrossC P.v₁ P.v₂ = P.ℓ * P.e) :
    P.theta z u + P.theta z' (conj u) =
      2 * Real.pi * P.k₁ - 2 * Real.pi * P.c / P.ℓ * planeCrossC P.v₂ ((z + z') / 2) := by
  have he : eta u = 1 := eta_eq_one h3
  have hc : chi u = 0 := chi_eq_zero (by linarith)
  have hsum : chiOne u + chiTwo u = 1 := by simp [chiOne, chiTwo, he]
  have hl : lam u = -Real.pi * step u := by simp [lam, hc]
  have hc1 : chiOne u = step u := by simp [chiOne, he]
  have hpsi : chiOne u * P.psi P.v₁ z + chiTwo u * P.psi P.v₂ z +
      (chiOne u * P.psi P.v₁ z' + chiTwo u * P.psi P.v₂ z') =
        -P.c * planeCrossC P.v₂ ((z + z') / 2) - P.c * chiOne u * planeCrossC P.v₁ P.v₂ := by
    have e1 : chiOne u * P.psi P.v₁ z + chiTwo u * P.psi P.v₂ z +
        (chiOne u * P.psi P.v₁ z' + chiTwo u * P.psi P.v₂ z') =
          chiOne u * (P.psi P.v₁ z + P.psi P.v₁ z') + chiTwo u * (P.psi P.v₂ z + P.psi P.v₂ z') :=
      by ring
    rw [e1, P.psi_add, P.psi_add]
    have hz : z + z' = 2 * (P.v₁ + τ * (P.v₂ - P.v₁)) := by
      rw [← hM]; ring
    have h2' : chiTwo u = 1 - chiOne u := by linarith
    rw [h2', hz]
    simp only [planeCrossC, mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im,
      re_ofNat, im_ofNat, div_ofNat_re, div_ofNat_im]
    ring
  unfold theta
  rw [chi_conj, chiOne_conj, chiTwo_conj, lam_conj, hc, hl,
    phaseArg_conj_of_gt (show u.re < ((3 / 2 : ℝ) : ℝ) by linarith),
    phaseArg_conj_of_lt (show (-(3 / 2) : ℝ) < u.re by linarith)]
  have key : 2 * Real.pi / P.ℓ * (chiOne u * P.psi P.v₁ z + chiTwo u * P.psi P.v₂ z) +
      2 * Real.pi / P.ℓ * (chiOne u * P.psi P.v₁ z' + chiTwo u * P.psi P.v₂ z') =
        2 * Real.pi / P.ℓ * (-P.c * planeCrossC P.v₂ ((z + z') / 2)) +
          2 * Real.pi * P.e * chiOne u := by
    rw [← mul_add, hpsi, mul_sub]
    rw [show P.c * chiOne u * planeCrossC P.v₁ P.v₂ = -(chiOne u * (-P.c *
      planeCrossC P.v₁ P.v₂)) by ring, hclose]
    field_simp
    ring
  linear_combination key + 2 * Real.pi * P.e * hc1

theorem theta_vertexOne {z u w : ℂ} {p : ℕ} (hu : u = 3 / 2 + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    P.theta z u = P.k₁ * (p * arg w) + 2 * Real.pi / P.ℓ * P.psi P.v₁ z +
      P.k₂ * phaseArg (-(3 / 2)) u - Real.pi * P.e := by
  have hnorm : ‖u - 3 / 2‖ ≤ 1 / 2 := by
    rw [hu, add_sub_cancel_left, norm_div, norm_pow]
    norm_num
    linarith
  have hre : 1 ≤ u.re := by
    have := abs_re_le_norm (u - 3 / 2)
    rw [sub_re] at this
    norm_num at this
    linarith [abs_le.mp (this.trans hnorm)]
  have hns : normSq u ≤ 25 / 4 := by
    rw [normSq_eq_norm_sq]
    have := norm_le_norm_add_norm_sub' u (3 / 2)
    have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [e] at this
    nlinarith [norm_nonneg u]
  have hs : step u = 1 := step_eq_one hre
  have he : eta u = 1 := eta_eq_one hns
  have hc : chi u = 0 := chi_eq_zero (by linarith)
  have hap : phaseArg (3 / 2) u = p * arg w := by
    rw [hu]
    have := phaseArg_apex (3 / 2) hw h1 h2
    push_cast at this
    exact this
  unfold theta
  rw [hc, hap]
  simp only [chiOne, chiTwo, lam, hs, he, hc]
  ring

theorem theta_vertexTwo {z u w : ℂ} {p : ℕ} (hu : u = -(3 / 2) + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    P.theta z u = P.k₂ * (p * arg w) + 2 * Real.pi / P.ℓ * P.psi P.v₂ z +
      P.k₁ * phaseArg (3 / 2) u := by
  have hnorm : ‖u + 3 / 2‖ ≤ 1 / 2 := by
    rw [hu, show -(3 / 2 : ℂ) + w ^ p / 2 + 3 / 2 = w ^ p / 2 by ring, norm_div, norm_pow]
    norm_num
    linarith
  have hre : u.re ≤ -1 := by
    have := abs_re_le_norm (u + 3 / 2)
    rw [add_re] at this
    norm_num at this
    linarith [abs_le.mp (this.trans hnorm)]
  have hns : normSq u ≤ 25 / 4 := by
    rw [normSq_eq_norm_sq]
    have := norm_le_norm_add_norm_sub' u (-(3 / 2))
    have e : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
    rw [e, sub_neg_eq_add] at this
    nlinarith [norm_nonneg u]
  have hs : step u = 0 := step_eq_zero hre
  have he : eta u = 1 := eta_eq_one hns
  have hc : chi u = 0 := chi_eq_zero (by linarith)
  have hap : phaseArg (-(3 / 2)) u = p * arg w := by
    rw [hu]
    have := phaseArg_apex (-(3 / 2)) hw h1 h2
    push_cast at this
    exact this
  unfold theta
  rw [hc, hap]
  simp only [chiOne, chiTwo, lam, hs, he, hc]
  ring

theorem theta_outer {z u : ℂ} (h : 9 ≤ normSq u) :
    P.theta z u = -(P.k₃ * phaseArg 0 u) - Real.pi * P.e := by
  have hc : chi u = 1 := chi_eq_one h
  have he : eta u = 0 := eta_eq_zero (by linarith)
  unfold theta
  simp only [chiOne, chiTwo, lam, hc, he]
  ring

theorem contDiff_normSq' : ContDiff ℝ ∞ (fun u : ℂ => normSq u) := by
  have : (fun u : ℂ => normSq u) = fun u => u.re * u.re + u.im * u.im := by
    funext u; rw [normSq_apply]
  rw [this]
  exact (reCLM.contDiff.mul reCLM.contDiff).add (imCLM.contDiff.mul imCLM.contDiff)

theorem contDiff_step : ContDiff ℝ ∞ step :=
  Real.smoothTransition.contDiff.comp ((reCLM.contDiff.add contDiff_const).div_const 2)

theorem contDiff_eta : ContDiff ℝ ∞ eta :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_normSq'.sub contDiff_const).div_const _))

theorem contDiff_chi : ContDiff ℝ ∞ chi :=
  Real.smoothTransition.contDiff.comp ((contDiff_normSq'.sub contDiff_const).div_const _)

theorem contDiff_psi (v : ℂ) : ContDiff ℝ ∞ (P.psi v) := by
  have : P.psi v = fun z => -P.c * (v.re * z.im - v.im * z.re) / 2 := by
    funext z; rfl
  rw [this]
  exact ((contDiff_const.mul ((contDiff_const.mul imCLM.contDiff).sub
    (contDiff_const.mul reCLM.contDiff))).div_const 2)

theorem contDiffAt_chi_mul_phaseArg_zero {u₀ : ℂ}
    (h : u₀ ∈ phaseDomain 0 ∨ normSq u₀ < 121 / 16) :
    ContDiffAt ℝ ∞ (fun u => chi u * phaseArg 0 u) u₀ := by
  rcases h with h | h
  · exact contDiff_chi.contDiffAt.mul (contDiffAt_phaseArg h)
  · have hev : (fun u => chi u * phaseArg 0 u) =ᶠ[nhds u₀] fun _ => (0 : ℝ) := by
      have ho : IsOpen {u : ℂ | normSq u < 121 / 16} :=
        isOpen_lt contDiff_normSq'.continuous continuous_const
      filter_upwards [ho.mem_nhds h] with u hu
      rw [chi_eq_zero (le_of_lt hu), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiffAt_theta {z₀ u₀ : ℂ} (h1 : u₀ ∈ phaseDomain (3 / 2))
    (h2 : u₀ ∈ phaseDomain (-(3 / 2))) (h3 : u₀ ∈ phaseDomain 0 ∨ normSq u₀ < 121 / 16) :
    ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => P.theta x.1 x.2) (z₀, u₀) := by
  have hs := contDiff_step.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have he := contDiff_eta.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have hc := contDiff_chi.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have hp1 := (contDiffAt_phaseArg h1).comp (z₀, u₀) contDiff_snd.contDiffAt
  have hp2 := (contDiffAt_phaseArg h2).comp (z₀, u₀) contDiff_snd.contDiffAt
  have hp0 := (contDiffAt_chi_mul_phaseArg_zero h3).comp (z₀, u₀) contDiff_snd.contDiffAt
  have hψ1 := (P.contDiff_psi P.v₁).contDiffAt.comp (z₀, u₀) contDiff_fst.contDiffAt
  have hψ2 := (P.contDiff_psi P.v₂).contDiffAt.comp (z₀, u₀) contDiff_fst.contDiffAt
  have key : (fun x : ℂ × ℂ => P.theta x.1 x.2) = fun x =>
      (1 - chi x.2) * (P.k₁ * phaseArg (3 / 2) x.2 + P.k₂ * phaseArg (-(3 / 2)) x.2) -
        P.k₃ * (chi x.2 * phaseArg 0 x.2) +
      2 * Real.pi / P.ℓ * (eta x.2 * step x.2 * P.psi P.v₁ x.1 +
        eta x.2 * (1 - step x.2) * P.psi P.v₂ x.1) +
      P.e * (-Real.pi * step x.2 - Real.pi * chi x.2 * (1 - step x.2)) := by
    funext x
    simp only [theta, chiOne, chiTwo, lam]
    ring
  rw [key]
  have hc' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => chi x.2) (z₀, u₀) := hc
  have hs' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => step x.2) (z₀, u₀) := hs
  have he' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => eta x.2) (z₀, u₀) := he
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · exact (contDiffAt_const.sub hc').mul
        ((contDiffAt_const.mul hp1).add (contDiffAt_const.mul hp2)) |>.sub
          (contDiffAt_const.mul hp0)
    · exact contDiffAt_const.mul ((he'.mul hs').mul hψ1 |>.add
        ((he'.mul (contDiffAt_const.sub hs')).mul hψ2))
  · exact contDiffAt_const.mul ((contDiffAt_const.mul hs').sub
      ((contDiffAt_const.mul hc').mul (contDiffAt_const.sub hs')))

end PhaseData

theorem phaseArg_compactOuterGerm {p : ℕ} {z : ℂ} (hz : z ≠ 0) (hzp : ‖z‖ ^ p < 7)
    (h1 : -(Real.pi / 2) ≤ p * arg z) (h2 : p * arg z < 3 * Real.pi / 2) :
    phaseArg 0 (compactOuterGerm p z) = Real.pi - p * arg z := by
  unfold phaseArg compactOuterGerm
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hr : 0 < 7 / 2 - ‖z‖ ^ p / 2 := by linarith
  have hz' := norm_mul_exp_arg_mul_I z
  have hn' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hconj : conj z / ‖z‖ = exp ((-(arg z) : ℝ) * I) := by
    calc conj z / ((‖z‖ : ℝ) : ℂ) =
          conj (((‖z‖ : ℝ) : ℂ) * exp ((arg z : ℂ) * I)) / ((‖z‖ : ℝ) : ℂ) := by rw [hz']
      _ = exp ((-(arg z) : ℝ) * I) := by
        rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_div_cancel_left₀ _ hn']
        congr 1
        simp [map_mul, conj_ofReal, conj_I]
  have hI : I * exp (↑p * (((-arg z : ℝ) : ℂ) * I)) =
      exp (((Real.pi / 2 - p * arg z : ℝ) : ℂ) * I) := by
    rw [show (((Real.pi / 2 - p * arg z : ℝ) : ℂ) * I) =
        (Real.pi : ℂ) / 2 * I + ↑p * (((-arg z : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.exp_add, exp_pi_div_two_mul_I]
  have e : -I * (-(((7 / 2 - ‖z‖ ^ p / 2 : ℝ) : ℂ) * (conj z / ‖z‖) ^ p) - ((0 : ℝ) : ℂ)) =
      ((7 / 2 - ‖z‖ ^ p / 2 : ℝ) : ℂ) * exp (((Real.pi / 2 - p * arg z : ℝ) : ℂ) * I) := by
    rw [hconj, ← Complex.exp_nat_mul, ← hI]
    push_cast
    ring
  rw [e, arg_real_mul _ hr, exp_mul_I, arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩]
  ring

end ClosedTriangle

end GC.Seifert
