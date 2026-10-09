import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypBridges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldAngles

/-!
# Hyperbolic circles about a point of the disc

Lane CF-H, tier 2 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4, curvature `-1`).
The hyperbolic circle about `v` through `z` is `hcirc v z t = mobInv v (mob v z · e^{it})`: in
the disc coordinate at `v` it is the Euclidean rotation (`mob_hcirc`), so the pseudo-hyperbolic
distance to `v` is constant along it (`norm_mob_hcirc`), and the distance to another point `a` is
the distance from `mob v a` to the rotating point (`norm_mob_hcirc_other`). Its velocity at `t = 0`
is `I · hrad v z` (`hasDerivAt_hcirc`), where the radial vector `hrad v z` is sent by the
derivative of `mob v` to `mob v z` (`hasDerivAt_mob_hrad`): the pair `(hrad, I · hrad)` is the
polar frame used with A4's `det_fderiv_polar`.

The distance to `a` has the explicit derivative `Im(conj(mob v a) · mob v z) · (positive)` along
the circle (`hasDerivAt_norm_mob_hcirc`), and the canonical form `(d - τ)/(1 - dτ)` multiplies it
by `(1 - τ²)/(1 - dτ)²` (`hasDerivAt_canonForm`). The angle derivative of A4 for a `twoCircle`
whose first radius is constant along a curve is restated for an arbitrary differentiable curve
(`hasDerivAt_halfArg_curve`, `hasDerivAt_negHalfArg_curve`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

def hcirc (v z : ℂ) (t : ℝ) : ℂ := mobInv v (mob v z * exp ((t : ℂ) * I))

def hrad (v z : ℂ) : ℂ := mob v z * (1 - conj v * z) ^ 2 / (1 - (normSq v : ℂ))

theorem norm_mul_exp (m : ℂ) (t : ℝ) : ‖m * exp ((t : ℂ) * I)‖ = ‖m‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

section Disc

variable {v z : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ < 1)
include hv hz

theorem hcirc_zero : hcirc v z 0 = z := by
  rw [hcirc, ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    mobInv_mob (normSq_lt_one_of_norm_lt hv).ne (one_sub_conj_mul_ne_zero hv hz)]

theorem norm_mob_mul_exp_lt (t : ℝ) : ‖mob v z * exp ((t : ℂ) * I)‖ < 1 := by
  rw [norm_mul_exp]
  exact norm_mob_lt_one hv hz

theorem norm_hcirc_lt_one (t : ℝ) : ‖hcirc v z t‖ < 1 :=
  norm_mobInv_lt_one hv (norm_mob_mul_exp_lt hv hz t)

theorem mob_hcirc (t : ℝ) : mob v (hcirc v z t) = mob v z * exp ((t : ℂ) * I) :=
  mob_mobInv (normSq_lt_one_of_norm_lt hv).ne
    (one_add_conj_mul_ne_zero hv (norm_mob_mul_exp_lt hv hz t))

theorem norm_mob_hcirc (t : ℝ) : ‖mob v (hcirc v z t)‖ = ‖mob v z‖ := by
  rw [mob_hcirc hv hz, norm_mul_exp]

theorem norm_mob_hcirc_other {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    ‖mob a (hcirc v z t)‖ = ‖mob (mob v a) (mob v z * exp ((t : ℂ) * I))‖ := by
  have hc := norm_hcirc_lt_one hv hz t
  rw [← mob_hcirc hv hz t, norm_mob_mob_mob (normSq_lt_one_of_norm_lt hv).ne
    (one_sub_conj_mul_ne_zero hv ha) (one_sub_conj_mul_ne_zero hv hc)
    (one_sub_conj_mul_ne_zero ha hc)]

theorem hasDerivAt_hcirc : HasDerivAt (hcirc v z) (I * hrad v z) 0 := by
  have hv1 := normSq_lt_one_of_norm_lt hv
  have hD : 1 - conj v * z ≠ 0 := one_sub_conj_mul_ne_zero hv hz
  have hm := norm_mob_lt_one hv hz
  have hE : HasDerivAt (fun t : ℝ => mob v z * exp ((t : ℂ) * I)) (mob v z * I) 0 := by
    have he : HasDerivAt (fun t : ℝ => exp ((t : ℂ) * I)) I 0 := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp
      simpa using this
    exact he.const_mul _
  have hden : 1 + conj v * (mob v z * exp (((0 : ℝ) : ℂ) * I)) ≠ 0 := by
    simpa using one_add_conj_mul_ne_zero hv hm
  have hN : HasDerivAt (fun t : ℝ => mob v z * exp ((t : ℂ) * I) + v) (mob v z * I) 0 :=
    hE.add_const v
  have hDd : HasDerivAt (fun t : ℝ => 1 + conj v * (mob v z * exp ((t : ℂ) * I)))
      (conj v * (mob v z * I)) 0 := (hE.const_mul _).const_add 1
  have h := hN.div hDd hden
  refine h.congr_deriv ?_
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have e1 := one_add_conj_mul_mob hD
  have hv0 : (1 : ℂ) - (normSq v : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [e1, hrad]
  have hD' : 1 - z * conj v ≠ 0 := by rwa [mul_comm]
  have e2 : mob v z + v = z * (1 - (normSq v : ℂ)) / (1 - conj v * z) := by
    rw [mob, Complex.normSq_eq_conj_mul_self]
    field_simp
    ring
  rw [e2]
  field_simp

theorem hasDerivAt_mob_hrad :
    HasDerivAt (fun s : ℝ => mob v (z + (s : ℂ) * hrad v z)) (mob v z) 0 := by
  have hD : 1 - conj v * z ≠ 0 := one_sub_conj_mul_ne_zero hv hz
  have hl : HasDerivAt (fun s : ℝ => z + (s : ℂ) * hrad v z) (hrad v z) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (hrad v z)).const_add z
  have hM : HasDerivAt (mob v) ((1 - conj v * v) / (1 - conj v * z) ^ 2)
      (z + ((0 : ℝ) : ℂ) * hrad v z) := by
    simpa using hasDerivAt_mob hD
  have h := (hM.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hl
  refine h.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  have hv0 : (1 : ℂ) - (normSq v : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith [normSq_lt_one_of_norm_lt hv]
  rw [hrad, Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_conj_mul_self] at hv0
  field_simp

theorem hrad_ne_zero (hne : mob v z ≠ 0) : hrad v z ≠ 0 := by
  have hD : 1 - conj v * z ≠ 0 := one_sub_conj_mul_ne_zero hv hz
  have hv0 : (1 : ℂ) - (normSq v : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith [normSq_lt_one_of_norm_lt hv]
  rw [hrad]
  exact div_ne_zero (mul_ne_zero hne (pow_ne_zero 2 hD)) hv0

theorem continuousAt_hcirc : ContinuousAt (hcirc v z) 0 :=
  (hasDerivAt_hcirc hv hz).continuousAt

theorem eventually_hcirc_mem {s : Set ℂ} (hs : IsOpen s) (hzs : z ∈ s) :
    ∀ᶠ t in 𝓝 (0 : ℝ), hcirc v z t ∈ s := by
  have hc := continuousAt_hcirc hv hz
  rw [ContinuousAt, hcirc_zero hv hz] at hc
  exact hc (hs.mem_nhds hzs)

theorem differentiableAt_comp_hcirc {f : ℂ → ℝ} (hf : ContDiffAt ℝ ∞ f z) :
    DifferentiableAt ℝ (fun t => f (hcirc v z t)) 0 := by
  have hf' : DifferentiableAt ℝ f (hcirc v z 0) := by
    rw [hcirc_zero hv hz]
    exact hf.differentiableAt (by simp)
  exact hf'.comp 0 (hasDerivAt_hcirc hv hz).differentiableAt

end Disc

theorem hasDerivAt_norm_mob_circle {q m : ℂ} (h : 1 - conj q * m ≠ 0) (hne : mob q m ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖mob q (m * exp ((t : ℂ) * I))‖)
      ((conj q * m).im * (1 - normSq q) * (1 - normSq m) /
        (normSq (1 - conj q * m) ^ 2 * ‖mob q m‖)) 0 := by
  have hn := hasDerivAt_normSq_mob_circle h
  have h0 : normSq (mob q (m * exp (((0 : ℝ) : ℂ) * I))) ≠ 0 := by
    simpa using normSq_eq_zero.not.2 hne
  have hs := hn.sqrt h0
  have e : (fun t : ℝ => ‖mob q (m * exp ((t : ℂ) * I))‖) =
      fun t : ℝ => Real.sqrt (normSq (mob q (m * exp ((t : ℂ) * I)))) := by
    funext t
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  refine hs.congr_deriv ?_
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [Complex.normSq_eq_norm_sq (mob q m), Real.sqrt_sq (norm_nonneg _)]
  have hm : ‖mob q m‖ ≠ 0 := norm_ne_zero_iff.2 hne
  have hN : normSq (1 - conj q * m) ≠ 0 := normSq_eq_zero.not.2 h
  field_simp

theorem hasDerivAt_norm_mob_hcirc {v z a : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ < 1) (ha : ‖a‖ < 1)
    (hne : mob a z ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖mob a (hcirc v z t)‖)
      ((conj (mob v a) * mob v z).im * (1 - normSq (mob v a)) * (1 - normSq (mob v z)) /
        (normSq (1 - conj (mob v a) * mob v z) ^ 2 * ‖mob a z‖)) 0 := by
  have hq := norm_mob_lt_one hv ha
  have hm := norm_mob_lt_one hv hz
  have h1 : 1 - conj (mob v a) * mob v z ≠ 0 := one_sub_conj_mul_ne_zero hq hm
  have hnn : ‖mob (mob v a) (mob v z)‖ = ‖mob a z‖ :=
    norm_mob_mob_mob (normSq_lt_one_of_norm_lt hv).ne (one_sub_conj_mul_ne_zero hv ha)
      (one_sub_conj_mul_ne_zero hv hz) (one_sub_conj_mul_ne_zero ha hz)
  have hne' : mob (mob v a) (mob v z) ≠ 0 := by
    rw [← norm_ne_zero_iff, hnn]
    exact norm_ne_zero_iff.2 hne
  have h := hasDerivAt_norm_mob_circle h1 hne'
  rw [hnn] at h
  refine h.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun t => norm_mob_hcirc_other hv hz ha t

theorem hasDerivAt_canonForm {d : ℝ → ℝ} {d' τ : ℝ} (hd : HasDerivAt d d' 0)
    (hden : 1 - d 0 * τ ≠ 0) :
    HasDerivAt (fun t => (d t - τ) / (1 - d t * τ)) ((1 - τ ^ 2) / (1 - d 0 * τ) ^ 2 * d') 0 := by
  have h := (hd.sub_const τ).div ((hd.mul_const τ).const_sub 1) hden
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_halfArg_curve {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ} {z : ℂ}
    {γ : ℝ → ℂ} (hγ0 : γ 0 = z) (hγ : DifferentiableAt ℝ γ 0)
    {κ w' : ℝ} (hA0 : 0 < A z) (hA : ∀ t, A (γ t) = A z)
    (hB : HasDerivAt (fun t => B (γ t)) (W z * κ) 0)
    (hW : HasDerivAt (fun t => W (γ t)) w' 0) (hP : ContDiffAt ℝ ∞ P z)
    {s : Set ℂ} (hs : IsOpen s) (hz : z ∈ s) (hPs : ∀ u ∈ s, 0 < P u)
    (hH : ∀ u ∈ s, ((A u + B u) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A u - B u) ^ 2) =
      W u ^ 2 * P u)
    (hpos : 0 < A z + ((twoCircle a b (A z) (B z) (W z) (P z)).re - a)) :
    HasDerivAt (fun t => halfArg (A (γ t))
        ((twoCircle a b (A (γ t)) (B (γ t)) (W (γ t)) (P (γ t))).re - a)
        (twoCircle a b (A (γ t)) (B (γ t)) (W (γ t)) (P (γ t))).im)
      (if W z = 0 then w' * Real.sqrt (P z) / (2 * |b - a| * A z)
        else 2 * |b - a| * B z * κ / ((b - a) * Real.sqrt (P z))) 0 := by
  simp only [hA]
  have hc : ContinuousAt γ 0 := hγ.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ s := by
    rw [ContinuousAt, hγ0] at hc
    exact hc (hs.mem_nhds hz)
  have hB' : HasDerivAt (fun t => B (γ t)) ((fun t => W (γ t)) 0 * κ) 0 := by
    simpa only [hγ0] using hB
  have hPd : DifferentiableAt ℝ (fun t => P (γ t)) 0 := by
    have hP' : DifferentiableAt ℝ P (γ 0) := by
      rw [hγ0]
      exact hP.differentiableAt (by simp)
    exact hP'.comp 0 hγ
  have h := hasDerivAt_halfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (γ t)) (w := fun t => W (γ t)) (P := fun t => P (γ t))
    hab hA0 hB' hW hPd (hev.mono fun t ht => hPs _ ht)
    (hev.mono fun t ht => by rw [← hA t]; exact hH _ ht) (by simpa only [hγ0] using hpos)
  simpa only [hγ0] using h

theorem hasDerivAt_negHalfArg_curve {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ} {z : ℂ}
    {γ : ℝ → ℂ} (hγ0 : γ 0 = z) (hγ : DifferentiableAt ℝ γ 0)
    {κ w' : ℝ} (hA0 : 0 < A z) (hA : ∀ t, A (γ t) = A z)
    (hB : HasDerivAt (fun t => B (γ t)) (W z * κ) 0)
    (hW : HasDerivAt (fun t => W (γ t)) w' 0) (hP : ContDiffAt ℝ ∞ P z)
    {s : Set ℂ} (hs : IsOpen s) (hz : z ∈ s) (hPs : ∀ u ∈ s, 0 < P u)
    (hH : ∀ u ∈ s, ((A u + B u) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A u - B u) ^ 2) =
      W u ^ 2 * P u)
    (hpos : 0 < A z - ((twoCircle a b (A z) (B z) (W z) (P z)).re - a)) :
    HasDerivAt (fun t => negHalfArg (A (γ t))
        ((twoCircle a b (A (γ t)) (B (γ t)) (W (γ t)) (P (γ t))).re - a)
        (twoCircle a b (A (γ t)) (B (γ t)) (W (γ t)) (P (γ t))).im)
      (if W z = 0 then -(w' * Real.sqrt (P z) / (2 * |b - a| * A z))
        else 2 * |b - a| * B z * κ / ((b - a) * Real.sqrt (P z))) 0 := by
  simp only [hA]
  have hc : ContinuousAt γ 0 := hγ.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ s := by
    rw [ContinuousAt, hγ0] at hc
    exact hc (hs.mem_nhds hz)
  have hB' : HasDerivAt (fun t => B (γ t)) ((fun t => W (γ t)) 0 * κ) 0 := by
    simpa only [hγ0] using hB
  have hPd : DifferentiableAt ℝ (fun t => P (γ t)) 0 := by
    have hP' : DifferentiableAt ℝ P (γ 0) := by
      rw [hγ0]
      exact hP.differentiableAt (by simp)
    exact hP'.comp 0 hγ
  have h := hasDerivAt_negHalfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (γ t)) (w := fun t => W (γ t)) (P := fun t => P (γ t))
    hab hA0 hB' hW hPd (hev.mono fun t ht => hPs _ ht)
    (hev.mono fun t ht => by rw [← hA t]; exact hH _ ht) (by simpa only [hγ0] using hpos)
  simpa only [hγ0] using h

end HypFold

end GC.Seifert
