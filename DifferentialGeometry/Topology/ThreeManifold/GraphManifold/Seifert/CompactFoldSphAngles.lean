import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCircle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldAngles

/-!
# Angles of the spherical bridges along circles about the vertices

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The profile functions are
`sphCanon j = sphCanonF τⱼ ϖⱼ` with `sphCanonF τ x = (x - τ)/(1 + x τ)`, increasing in `x`
(`hasDerivAt_sphCanonF`). Along the circle `sphCirc a z` about a vertex `a` the profile of another
vertex `b` changes at the rate `Im (b̄' ω) · K` with `K > 0`, `ω`, `b'` the disc coordinates of
`z`, `b` at `a` (`exists_hasDerivAt_sphCanon_sphCirc`).

The angle of a `twoCircle` bridge about one of its centres, written with A4's `halfArg` or
`negHalfArg`, has an explicit derivative along any curve on which the radius about that centre is
constant (`hasDerivAt_halfArg_curve_sph`, `hasDerivAt_negHalfArg_curve_sph`, the curve form of
`hasDerivAt_halfArg_twoCircle'`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def sphCanonF (τ x : ℝ) : ℝ := (x - τ) / (1 + x * τ)

theorem hasDerivAt_sphCanonF {τ : ℝ} {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t)
    (h : 1 + f t * τ ≠ 0) :
    HasDerivAt (fun s => sphCanonF τ (f s)) ((1 + τ ^ 2) / (1 + f t * τ) ^ 2 * f') t := by
  have h1 : HasDerivAt (fun s => f s - τ) f' t := hf.sub_const τ
  have h2 : HasDerivAt (fun s => 1 + f s * τ) (f' * τ) t := (hf.mul_const τ).const_add 1
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_halfArg_curve_sph {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ} {γ : ℝ → ℂ}
    {z V : ℂ} {κ w' : ℝ} (hγ : HasDerivAt γ V 0) (hγ0 : γ 0 = z) (hA0 : 0 < A z)
    (hA : ∀ᶠ t in 𝓝 (0 : ℝ), A (γ t) = A z)
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
  have hc : ContinuousAt γ 0 := hγ.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ s := by
    rw [ContinuousAt, hγ0] at hc
    exact hc (hs.mem_nhds hz)
  have hPd : DifferentiableAt ℝ (fun t => P (γ t)) 0 := by
    have hP' : DifferentiableAt ℝ P (γ 0) := by
      rw [hγ0]
      exact hP.differentiableAt (by simp)
    exact hP'.comp 0 hγ.differentiableAt
  have hB' : HasDerivAt (fun t => B (γ t)) ((fun t => W (γ t)) 0 * κ) 0 := by
    simpa only [hγ0] using hB
  have h := hasDerivAt_halfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (γ t)) (w := fun t => W (γ t)) (P := fun t => P (γ t))
    hab hA0 hB' hW hPd (hev.mono fun t ht => hPs _ ht)
    (by filter_upwards [hev, hA] with t ht ht'; rw [← ht']; exact hH _ ht)
    (by simpa only [hγ0] using hpos)
  simp only [hγ0] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hA] with t ht
  rw [ht]

theorem hasDerivAt_negHalfArg_curve_sph {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ}
    {γ : ℝ → ℂ} {z V : ℂ} {κ w' : ℝ} (hγ : HasDerivAt γ V 0) (hγ0 : γ 0 = z) (hA0 : 0 < A z)
    (hA : ∀ᶠ t in 𝓝 (0 : ℝ), A (γ t) = A z)
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
  have hc : ContinuousAt γ 0 := hγ.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ s := by
    rw [ContinuousAt, hγ0] at hc
    exact hc (hs.mem_nhds hz)
  have hPd : DifferentiableAt ℝ (fun t => P (γ t)) 0 := by
    have hP' : DifferentiableAt ℝ P (γ 0) := by
      rw [hγ0]
      exact hP.differentiableAt (by simp)
    exact hP'.comp 0 hγ.differentiableAt
  have hB' : HasDerivAt (fun t => B (γ t)) ((fun t => W (γ t)) 0 * κ) 0 := by
    simpa only [hγ0] using hB
  have h := hasDerivAt_negHalfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (γ t)) (w := fun t => W (γ t)) (P := fun t => P (γ t))
    hab hA0 hB' hW hPd (hev.mono fun t ht => hPs _ ht)
    (by filter_upwards [hev, hA] with t ht ht'; rw [← ht']; exact hH _ ht)
    (by simpa only [hγ0] using hpos)
  simp only [hγ0] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hA] with t ht
  rw [ht]

theorem exists_hasDerivAt_canonF_sphCirc {a b z : ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h1 : 1 + conj a * z ≠ 0) (h2 : 1 + conj a * b ≠ 0) (h3 : 1 + conj b * z ≠ 0)
    (h0 : sphMoeb b z ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ HasDerivAt (fun t => sphCanonF τ ‖sphMoeb b (sphCirc a z t)‖)
      ((conj (sphMoeb a b) * sphMoeb a z).im * K) 0 := by
  have hd := hasDerivAt_norm_sphMoeb_sphCirc h1 h2 h3 h0
  have hz := sphCirc_zero h1
  have hpos : 0 < 1 + ‖sphMoeb b (sphCirc a z 0)‖ * τ := by
    have := mul_nonneg (norm_nonneg (sphMoeb b (sphCirc a z 0))) hτ
    linarith
  have h := hasDerivAt_sphCanonF (τ := τ) hd hpos.ne'
  rw [hz] at hpos h
  have hD := one_add_conj_sphMoeb_ne h1 h2 h3
  have hn := norm_pos_iff.2 h0
  have hDn := norm_pos_iff.2 hD
  refine ⟨(1 + τ ^ 2) / (1 + ‖sphMoeb b z‖ * τ) ^ 2 * ((1 + ‖sphMoeb a z‖ ^ 2) *
    (1 + ‖sphMoeb a b‖ ^ 2) / (‖1 + conj (sphMoeb a b) * sphMoeb a z‖ ^ 4 * ‖sphMoeb b z‖)),
    by positivity, h.congr_deriv (by ring)⟩


theorem re_pos_of_im_eq_zero_sph {w : ℂ} (h : 0 < ‖w‖ + w.re) (hi : w.im = 0) : 0 < w.re := by
  have hn : ‖w‖ = |w.re| := by
    rw [← Complex.re_add_im w, hi]
    simp
  rw [hn] at h
  rcases le_or_gt 0 w.re with h' | h'
  · rcases h'.lt_or_eq with h'' | h''
    · exact h''
    · rw [← h''] at h
      simp at h
  · rw [abs_of_neg h'] at h
    linarith

theorem twoCircle_div_sqrt_pos_sph {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : 0 < κ / d) : 0 < 2 * |d| * B * κ / (d * Real.sqrt P) := by
  have hs := Real.sqrt_pos.2 hP
  have e : 2 * |d| * B * κ / (d * Real.sqrt P) = 2 * |d| * B * (κ / d) / Real.sqrt P := by
    field_simp
  rw [e]
  have := abs_pos.2 hd
  positivity

theorem twoCircle_div_sqrt_neg_sph {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : κ / d < 0) : 2 * |d| * B * κ / (d * Real.sqrt P) < 0 := by
  have h := twoCircle_div_sqrt_pos_sph hd hB hP (κ := -κ) (by rw [neg_div]; linarith)
  have e : 2 * |d| * B * -κ / (d * Real.sqrt P) = -(2 * |d| * B * κ / (d * Real.sqrt P)) := by
    ring
  linarith

theorem sphCirc_center_zero (z : ℂ) (t : ℝ) : sphCirc 0 z t = z * exp ((t : ℂ) * I) := by
  simp [sphCirc, sphMoeb, sphMoebInv]

theorem hasDerivAt_sphCirc_center_zero (z : ℂ) : HasDerivAt (sphCirc 0 z) (z * I) 0 := by
  have h := hasDerivAt_sphCirc (a := 0) (z := z) (by simp)
  simpa [sphMoeb] using h

theorem hasDerivAt_im_curve_sph {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => (γ t).im) V.im 0 := by
  refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
  simp

theorem hasDerivAt_re_curve_sph {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => (γ t).re) V.re 0 := by
  refine (reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
  simp


theorem re_lt_of_pairDom_im_zero {t : ℝ} {ζ : ℂ} (hζ : ζ ∈ sphPairDom t) (hY : ζ.im = 0) :
    ζ.re < t := by
  obtain ⟨-, h2, h3, -, -, -⟩ := hζ
  by_contra hc
  push Not at hc
  have hz : ζ = (ζ.re : ℂ) := eq_ofReal_re_of_im_sph hY
  have hm : ‖sphMoeb t ζ‖ = (ζ.re - t) / (1 + t * ζ.re) := by
    rw [hz, sphMoeb_ofReal, ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by linarith) h2.le)]
  unfold sphPairNum at h3
  rw [hm, mul_div_cancel₀ _ h2.ne'] at h3
  linarith


theorem hasDerivAt_normSq_curve_sph {δ : ℝ → ℂ} {D : ℂ} (hδ : HasDerivAt δ D 0) :
    HasDerivAt (fun t => Complex.normSq (δ t))
      (2 * ((δ 0).re * D.re + (δ 0).im * D.im)) 0 := by
  have e : (fun t => Complex.normSq (δ t)) = fun t => (δ t).re ^ 2 + (δ t).im ^ 2 := by
    funext t
    rw [Complex.normSq_apply]
    ring
  rw [e]
  refine (((hasDerivAt_re_curve_sph hδ).pow 2).add ((hasDerivAt_im_curve_sph hδ).pow 2)).congr_deriv
    ?_
  simp
  ring

namespace CompactShape

variable {σ : CompactShape}

def sphAngleOneAtOne (σ : CompactShape) (z : ℂ) : ℝ :=
  halfArg (σ.sphModOne z) ((σ.sphBridgeOne z).re - 3 / 2) (σ.sphBridgeOne z).im

def sphAngleTwoAtOne (σ : CompactShape) (z : ℂ) : ℝ :=
  negHalfArg (σ.sphModOne z) ((σ.sphBridgeTwo z).re - 3 / 2) (σ.sphBridgeTwo z).im

def sphAngleTwoAtTwo (σ : CompactShape) (z : ℂ) : ℝ :=
  halfArg (σ.sphModTwo z) ((σ.sphBridgeTwo z).re + 3 / 2) (σ.sphBridgeTwo z).im

def sphAngleZeroAtTwo (σ : CompactShape) (z : ℂ) : ℝ :=
  negHalfArg (σ.sphModTwo z) ((σ.sphBridgeZero z).re + 3 / 2) (σ.sphBridgeZero z).im

def sphAngleOneAtThree (σ : CompactShape) (z : ℂ) : ℝ :=
  halfArg (σ.sphModThree z) (σ.sphBridgeOne z).re (σ.sphBridgeOne z).im

def sphAngleZeroAtThree (σ : CompactShape) (z : ℂ) : ℝ :=
  negHalfArg (σ.sphModThree z) (σ.sphBridgeZero z).re (σ.sphBridgeZero z).im

theorem sphCanon_two_eq_F (u : ℂ) :
    σ.sphCanon 2 u = sphCanonF (σ.sphTau 2) ‖sphMoeb 0 u‖ := by
  rw [sphMoeb_zero]
  rfl

theorem hasDerivAt_wallSide_one_curve_sph {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => σ.wallSide 1 (γ t))
      (Real.sin σ.θ₃ * V.re - Real.cos σ.θ₃ * V.im) 0 := by
  have e : (fun t => σ.wallSide 1 (γ t)) =
      fun t => Real.sin σ.θ₃ * (γ t).re - Real.cos σ.θ₃ * (γ t).im := by
    funext t
    rw [wallSide_one_apply_sph]
  rw [e]
  exact ((hasDerivAt_re_curve_sph hγ).const_mul _).sub ((hasDerivAt_im_curve_sph hγ).const_mul _)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphCanon_one_eq_F (u : ℂ) :
    σ.sphCanon 1 u = sphCanonF (σ.sphTau 1) ‖sphMoeb σ.vertexTwo u‖ := by
  rw [← norm_rotTwo_sph hs]
  rfl

theorem sphCanon_zero_eq_F (u : ℂ) :
    σ.sphCanon 0 u = sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne u‖ := by
  rw [← norm_rotOne_sph hs]
  rfl

theorem contDiffAt_sphCofBridgeOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ContDiffAt ℝ ∞ σ.sphCofBridgeOne z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hL := contDiffAt_exp_neg_mul (σ := σ) z
  have c0 : ContDiffAt ℝ ∞ (σ.sphCanon 0) z :=
    contDiffAt_sphCanon_of hs
      (d := fun w => ‖sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * w)‖)
      ((contDiffAt_norm_sphMoeb_real h2 hne).comp z hL)
      (Filter.Eventually.of_forall (sphDist_zero_eq hs))
  have c2 : ContDiffAt ℝ ∞ (σ.sphCanon 2) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖exp (-((σ.θ₃ : ℂ) * I)) * w‖)
      ((contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)).comp z hL)
      (Filter.Eventually.of_forall sphDist_two_eq)
  have hA : ContDiffAt ℝ ∞ σ.sphModThree z := contDiffAt_const.sub (contDiffAt_const.mul c2)
  have hB : ContDiffAt ℝ ∞ σ.sphModOne z := contDiffAt_const.add (contDiffAt_const.mul c0)
  have hC : ContDiffAt ℝ ∞ σ.sphCofOne z :=
    (contDiffAt_pairCof_sph (sphTau_pos hs 2).le (sphTau_pos hs 0).le hz).comp z hL
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul hC)

theorem contDiffAt_sphCofBridgeZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ContDiffAt ℝ ∞ σ.sphCofBridgeZero z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have c1 : ContDiffAt ℝ ∞ (σ.sphCanon 1) z :=
    contDiffAt_sphCanon_of hs (contDiffAt_norm_sphMoeb_real h2 hne)
      (Filter.Eventually.of_forall (sphDist_one_eq hs))
  have c2 : ContDiffAt ℝ ∞ (σ.sphCanon 2) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖w‖)
      (contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1))
      (Filter.Eventually.of_forall fun w => rfl)
  have hA : ContDiffAt ℝ ∞ σ.sphModThree z := contDiffAt_const.sub (contDiffAt_const.mul c2)
  have hB : ContDiffAt ℝ ∞ σ.sphModTwo z := contDiffAt_const.add (contDiffAt_const.mul c1)
  have hC : ContDiffAt ℝ ∞ σ.sphCofZero z :=
    contDiffAt_pairCof_sph (sphTau_pos hs 2).le (sphTau_pos hs 1).le hz
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul hC)

omit hs in
theorem one_add_conj_vertexOne_ne_of_domOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    1 + conj σ.vertexOne * z ≠ 0 := by
  have h2 := hz.2.1
  have e : 1 + conj σ.vertexOne * z = 1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
    rw [conj_vertexOne_sph]
    ring
  rw [e]
  exact one_add_real_mul_ne_sph h2

theorem sphMoeb_vertexOne_ne_of_domOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    sphMoeb σ.vertexOne z ≠ 0 := by
  have hne := sphMoeb_ne_zero_of_pairNum hz.2.1 hz.2.2.1
  rw [← norm_ne_zero_iff, ← norm_rotOne_sph hs, rotOne_eq_neg_sphMoeb hs, norm_neg,
    norm_ne_zero_iff]
  exact hne

omit hs in
theorem sphMoeb_vertexTwo_ne_of_domZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    sphMoeb σ.vertexTwo z ≠ 0 := by
  have hne := sphMoeb_ne_zero_of_pairNum hz.2.1 hz.2.2.1
  rwa [vertexTwo_eq_sph]

omit hs in
theorem one_add_vertexTwo_ne_of_domZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    1 + conj σ.vertexTwo * z ≠ 0 := by
  rw [conj_vertexTwo_sph, vertexTwo_eq_sph]
  exact one_add_real_mul_ne_sph hz.2.1

omit hs in
theorem im_conj_vertexOne_mul (z : ℂ) :
    (conj σ.vertexOne * z).im = -(σ.sphTOneThree * σ.wallSide 1 z) := by
  rw [wallSide_one_eq_neg_im_sph, conj_vertexOne_sph, mul_assoc, Complex.im_ofReal_mul]
  ring

omit hs in
theorem im_conj_vertexTwo_mul (z : ℂ) :
    (conj σ.vertexTwo * z).im = σ.sphTTwoThree * σ.wallSide 0 z := by
  rw [conj_vertexTwo_sph, vertexTwo_eq_sph, Complex.im_ofReal_mul, wallSide_zero_apply_sph]

theorem exists_hasDerivAt_sphAngleOneAtThree {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => σ.sphAngleOneAtThree (sphCirc 0 z t)) d 0 := by
  have hγ := hasDerivAt_sphCirc_center_zero z
  have hγ0 : sphCirc 0 z 0 = z := sphCirc_zero (by simp)
  have hA0 := sphModThree_pos (sphCanon_bounds_one hs hz).2
  have hP0 := sphCofBridgeOne_pos hs hz
  have hB0 := sphModOne_pos hs z
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ), σ.sphModThree (sphCirc 0 z t) = σ.sphModThree z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc (a := 0) (z := z) (by simp)] with t ht
    rw [sphModThree, sphModThree, sphCanon_two_eq_F, sphCanon_two_eq_F, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := 0) (b := σ.vertexOne) (z := z)
    (sphTau_pos hs 0).le (by simp) (by simp) (one_add_conj_vertexOne_ne_of_domOne hz)
    (sphMoeb_vertexOne_ne_of_domOne hs hz)
  have hB : HasDerivAt (fun t => σ.sphModOne (sphCirc 0 z t))
      (σ.wallSide 1 z * (-(compactProfileSlope * σ.sphTOneThree * K))) 0 := by
    have e : (fun t => σ.sphModOne (sphCirc 0 z t)) = fun t => 3 / 2 + compactProfileSlope *
        sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne (sphCirc 0 z t)‖ := by
      funext t
      rw [sphModOne, sphCanon_zero_eq_F hs]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_add (3 / 2)).congr_deriv ?_
    rw [sphMoeb_zero, sphMoeb_zero, im_conj_vertexOne_mul]
    ring
  have hW := hasDerivAt_wallSide_one_curve_sph (σ := σ) hγ
  have h := hasDerivAt_halfArg_curve_sph (a := 0) (b := 3 / 2) (by norm_num) (A := σ.sphModThree)
    (B := σ.sphModOne) (W := σ.wallSide 1) (P := σ.sphCofBridgeOne) hγ hγ0 hA0 hA hB hW
    (contDiffAt_sphCofBridgeOne hs hz) isOpen_sphDomOne hz
    (fun u hu => sphCofBridgeOne_pos hs hu) (fun u hu => heron_sphBridgeOne hs hu)
    (by simpa [sphBridgeOne] using hpos)
  have e : (fun t => σ.sphAngleOneAtThree (sphCirc 0 z t)) = fun t =>
      halfArg (σ.sphModThree (sphCirc 0 z t))
        ((twoCircle 0 (3 / 2) (σ.sphModThree (sphCirc 0 z t)) (σ.sphModOne (sphCirc 0 z t))
          (σ.wallSide 1 (sphCirc 0 z t)) (σ.sphCofBridgeOne (sphCirc 0 z t))).re - 0)
        (twoCircle 0 (3 / 2) (σ.sphModThree (sphCirc 0 z t)) (σ.sphModOne (sphCirc 0 z t))
          (σ.wallSide 1 (sphCirc 0 z t)) (σ.sphCofBridgeOne (sphCirc 0 z t))).im := by
    funext t
    rw [sphAngleOneAtThree, sphBridgeOne, sub_zero]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hζ : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
      refine re_pos_of_im_eq_zero_sph hz.1 ?_
      rw [wallSide_one_eq_neg_im_sph] at hw
      linarith
    have hw' : Real.sin σ.θ₃ * (z * I).re - Real.cos σ.θ₃ * (z * I).im =
        -(exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
      rw [exp_neg_ofReal_mul_I_sph]
      simp only [mul_re, mul_im, I_re, I_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
      ring
    rw [hw']
    have := Real.sqrt_pos.2 hP0
    have hd : 0 < 2 * |(3 / 2 : ℝ) - 0| * σ.sphModThree z := by positivity
    have : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re * Real.sqrt (σ.sphCofBridgeOne z) := by positivity
    rw [neg_mul]
    exact div_neg_of_neg_of_pos (by linarith) hd
  · apply twoCircle_div_sqrt_neg_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * σ.sphTOneThree * K := by
      have := tOneThree_pos_sph hs
      unfold compactProfileSlope
      positivity
    have h2 := div_pos this (by norm_num : (0 : ℝ) < 3 / 2 - 0)
    rw [neg_div]
    linarith

theorem exists_hasDerivAt_sphAngleZeroAtThree {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => σ.sphAngleZeroAtThree (sphCirc 0 z t)) d 0 := by
  have hγ := hasDerivAt_sphCirc_center_zero z
  have hγ0 : sphCirc 0 z 0 = z := sphCirc_zero (by simp)
  have hA0 := sphModThree_pos (sphCanon_bounds_zero hs hz).2
  have hP0 := sphCofBridgeZero_pos hs hz
  have hB0 := sphModTwo_pos hs z
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ), σ.sphModThree (sphCirc 0 z t) = σ.sphModThree z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc (a := 0) (z := z) (by simp)] with t ht
    rw [sphModThree, sphModThree, sphCanon_two_eq_F, sphCanon_two_eq_F, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := 0) (b := σ.vertexTwo) (z := z)
    (sphTau_pos hs 1).le (by simp) (by simp) (one_add_vertexTwo_ne_of_domZero hz)
    (sphMoeb_vertexTwo_ne_of_domZero hz)
  have hB : HasDerivAt (fun t => σ.sphModTwo (sphCirc 0 z t))
      (σ.wallSide 0 z * (compactProfileSlope * σ.sphTTwoThree * K)) 0 := by
    have e : (fun t => σ.sphModTwo (sphCirc 0 z t)) = fun t => 3 / 2 + compactProfileSlope *
        sphCanonF (σ.sphTau 1) ‖sphMoeb σ.vertexTwo (sphCirc 0 z t)‖ := by
      funext t
      rw [sphModTwo, sphCanon_one_eq_F hs]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_add (3 / 2)).congr_deriv ?_
    rw [sphMoeb_zero, sphMoeb_zero, im_conj_vertexTwo_mul]
    ring
  have hW : HasDerivAt (fun t => σ.wallSide 0 (sphCirc 0 z t)) (z * I).im 0 :=
    hasDerivAt_im_curve_sph hγ
  have h := hasDerivAt_negHalfArg_curve_sph (a := 0) (b := -(3 / 2)) (by norm_num)
    (A := σ.sphModThree) (B := σ.sphModTwo) (W := σ.wallSide 0) (P := σ.sphCofBridgeZero) hγ
    hγ0 hA0 hA hB hW (contDiffAt_sphCofBridgeZero hs hz) isOpen_sphDomZero hz
    (fun u hu => sphCofBridgeZero_pos hs hu) (fun u hu => heron_sphBridgeZero hs hu)
    (by simpa [sphBridgeZero] using hpos)
  have e : (fun t => σ.sphAngleZeroAtThree (sphCirc 0 z t)) = fun t =>
      negHalfArg (σ.sphModThree (sphCirc 0 z t))
        ((twoCircle 0 (-(3 / 2)) (σ.sphModThree (sphCirc 0 z t)) (σ.sphModTwo (sphCirc 0 z t))
          (σ.wallSide 0 (sphCirc 0 z t)) (σ.sphCofBridgeZero (sphCirc 0 z t))).re - 0)
        (twoCircle 0 (-(3 / 2)) (σ.sphModThree (sphCirc 0 z t)) (σ.sphModTwo (sphCirc 0 z t))
          (σ.wallSide 0 (sphCirc 0 z t)) (σ.sphCofBridgeZero (sphCirc 0 z t))).im := by
    funext t
    rw [sphAngleZeroAtThree, sphBridgeZero, sub_zero]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < z.re := re_pos_of_im_eq_zero_sph hz.1 hw
    have hw' : (z * I).im = z.re := by simp
    rw [hw']
    have := Real.sqrt_pos.2 hP0
    have : 0 < z.re * Real.sqrt (σ.sphCofBridgeZero z) / (2 * |-(3 / 2 : ℝ) - 0| *
      σ.sphModThree z) := by positivity
    linarith
  · apply twoCircle_div_sqrt_neg_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * σ.sphTTwoThree * K := by
      have := tTwoThree_pos_sph hs
      unfold compactProfileSlope
      positivity
    exact div_neg_of_pos_of_neg this (by norm_num)


omit hs in
theorem one_add_vertexTwo_ne_of_domTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    1 + conj σ.vertexTwo * z ≠ 0 := by
  rw [conj_vertexTwo_sph]
  exact hz.1

theorem sphMoeb_vertexOne_ne_of_domTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    sphMoeb σ.vertexOne z ≠ 0 := by
  have hne := sphMoeb_ne_zero_of_pairNum hz.2.2.2.1 hz.2.2.2.2.1
  rw [← norm_ne_zero_iff, ← norm_rotOne_sph hs, norm_rotOne_eq_sphMoeb_rotTwo hs hz.2.1
    (one_add_vertexTwo_ne_of_domTwo hz), norm_ne_zero_iff]
  exact hne

theorem conj_sphMoeb_vertexTwo_vertexOne_mul (z : ℂ) :
    conj (sphMoeb σ.vertexTwo σ.vertexOne) * sphMoeb σ.vertexTwo z = σ.sphTOneTwo * σ.rotTwo z := by
  rw [sphMoeb_vertexTwo_vertexOne hs, rotTwo_eq_mul_sph hs, map_neg, map_mul, conj_exp_neg_sph,
    Complex.conj_ofReal]
  ring

theorem eventually_rotTwo_sphCirc {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), σ.rotTwo (sphCirc σ.vertexTwo z t) = σ.rotTwo z * exp ((t : ℂ) * I) := by
  have h' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  filter_upwards [eventually_sphMoeb_sphCirc h'] with t ht
  rw [rotTwo_eq_mul_sph hs, rotTwo_eq_mul_sph hs, ht]
  ring

theorem hasDerivAt_sphSideTwo_sphCirc {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    HasDerivAt (fun t => σ.sphSideTwo (sphCirc σ.vertexTwo z t)) (σ.rotTwo z).re 0 := by
  have hd := hasDerivAt_im_curve_sph (hasDerivAt_rot_sph (σ.rotTwo z))
  have e : (σ.rotTwo z * I).im = (σ.rotTwo z).re := by simp
  rw [e] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_rotTwo_sphCirc hs h] with t ht
  rw [sphSideTwo, ht]

theorem contDiffAt_sphCofBridgeTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ContDiffAt ℝ ∞ σ.sphCofBridgeTwo z := by
  obtain ⟨hv2, hv1, h1, h2, h3, h4, h5, h6⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hR := contDiffAt_rotTwo_sph hs hv2
  have hev : ∀ᶠ w in 𝓝 z, σ.sphDist 0 w = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo w)‖ := by
    have c1 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
    have c2 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
    filter_upwards [c1.eventually_ne hv2, c2.eventually_ne hv1] with w e1 e2
    exact sphDist_zero_eq_two hs e2 e1
  have c0 : ContDiffAt ℝ ∞ (σ.sphCanon 0) z :=
    contDiffAt_sphCanon_of hs ((contDiffAt_norm_sphMoeb_real h2 hne).comp z hR) hev
  have c1 : ContDiffAt ℝ ∞ (σ.sphCanon 1) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖σ.rotTwo w‖)
      (hR.norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)) (Filter.Eventually.of_forall fun w => rfl)
  have hA : ContDiffAt ℝ ∞ σ.sphModOne z := contDiffAt_const.add (contDiffAt_const.mul c0)
  have hB : ContDiffAt ℝ ∞ σ.sphModTwo z := contDiffAt_const.add (contDiffAt_const.mul c1)
  have hC : ContDiffAt ℝ ∞ σ.sphCofTwo z :=
    (contDiffAt_pairCof_sph (sphTau_pos hs 1).le (sphTau_pos hs 0).le hz.2.2).comp z hR
  exact (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
    (contDiffAt_const.mul hC)

theorem exists_hasDerivAt_sphAngleTwoAtTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧
      HasDerivAt (fun t => σ.sphAngleTwoAtTwo (sphCirc σ.vertexTwo z t)) d 0 := by
  have hv2 := one_add_vertexTwo_ne_of_domTwo hz
  have hγ := hasDerivAt_sphCirc hv2
  have hγ0 : sphCirc σ.vertexTwo z 0 = z := sphCirc_zero hv2
  have hA0 := sphModTwo_pos hs z
  have hP0 := sphCofBridgeTwo_pos hs hz
  have hB0 := sphModOne_pos hs z
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ),
      σ.sphModTwo (sphCirc σ.vertexTwo z t) = σ.sphModTwo z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc hv2] with t ht
    rw [sphModTwo, sphModTwo, sphCanon_one_eq_F hs, sphCanon_one_eq_F hs, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := σ.vertexTwo) (b := σ.vertexOne)
    (z := z) (sphTau_pos hs 0).le hv2
    (by rw [conj_vertexTwo_sph]; exact one_add_vertexTwo_mul_vertexOne_ne_sph hs) hz.2.1
    (sphMoeb_vertexOne_ne_of_domTwo hs hz)
  have hB : HasDerivAt (fun t => σ.sphModOne (sphCirc σ.vertexTwo z t))
      (σ.sphSideTwo z * (compactProfileSlope * σ.sphTOneTwo * K)) 0 := by
    have e : (fun t => σ.sphModOne (sphCirc σ.vertexTwo z t)) = fun t => 3 / 2 +
        compactProfileSlope * sphCanonF (σ.sphTau 0)
          ‖sphMoeb σ.vertexOne (sphCirc σ.vertexTwo z t)‖ := by
      funext t
      rw [sphModOne, sphCanon_zero_eq_F hs]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_add (3 / 2)).congr_deriv ?_
    rw [conj_sphMoeb_vertexTwo_vertexOne_mul hs, Complex.im_ofReal_mul, sphSideTwo]
    ring
  have hW := hasDerivAt_sphSideTwo_sphCirc hs hz.1
  have h := hasDerivAt_halfArg_curve_sph (a := -(3 / 2)) (b := 3 / 2) (by norm_num)
    (A := σ.sphModTwo) (B := σ.sphModOne) (W := σ.sphSideTwo) (P := σ.sphCofBridgeTwo) hγ hγ0
    hA0 hA hB hW (contDiffAt_sphCofBridgeTwo hs hz) (isOpen_sphDomTwo hs) hz
    (fun u hu => sphCofBridgeTwo_pos hs hu)
    (fun u hu => by have := heron_sphBridgeTwo hs hu; linear_combination this)
    (by rw [← twoCircle_swap]; simpa [sphBridgeTwo] using hpos)
  have e : (fun t => σ.sphAngleTwoAtTwo (sphCirc σ.vertexTwo z t)) = fun t =>
      halfArg (σ.sphModTwo (sphCirc σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) (3 / 2) (σ.sphModTwo (sphCirc σ.vertexTwo z t))
          (σ.sphModOne (sphCirc σ.vertexTwo z t)) (σ.sphSideTwo (sphCirc σ.vertexTwo z t))
          (σ.sphCofBridgeTwo (sphCirc σ.vertexTwo z t))).re - -(3 / 2))
        (twoCircle (-(3 / 2)) (3 / 2) (σ.sphModTwo (sphCirc σ.vertexTwo z t))
          (σ.sphModOne (sphCirc σ.vertexTwo z t)) (σ.sphSideTwo (sphCirc σ.vertexTwo z t))
          (σ.sphCofBridgeTwo (sphCirc σ.vertexTwo z t))).im := by
    funext t
    rw [sphAngleTwoAtTwo, sphBridgeTwo, twoCircle_swap, sub_neg_eq_add]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < (σ.rotTwo z).re := re_pos_of_im_eq_zero_sph hz.2.2.1 hw
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply twoCircle_div_sqrt_pos_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * σ.sphTOneTwo * K := by
      have := tOneTwo_pos_sph hs
      unfold compactProfileSlope
      positivity
    exact div_pos this (by norm_num)

omit hs in
theorem im_conj_sphMoeb_vertexTwo_zero_mul (z : ℂ) :
    (conj (sphMoeb σ.vertexTwo 0) * sphMoeb σ.vertexTwo z).im *
        Complex.normSq (1 + σ.sphTTwoThree * z) =
      -(σ.sphTTwoThree * (1 + σ.sphTTwoThree ^ 2) * σ.wallSide 0 z) := by
  have e : conj (sphMoeb σ.vertexTwo 0) = -σ.sphTTwoThree := by
    simp [sphMoeb, vertexTwo_eq_sph]
  rw [e, vertexTwo_eq_sph, neg_mul, neg_im, Complex.im_ofReal_mul, neg_mul, mul_assoc,
    im_sphMoeb_real, wallSide_zero_apply_sph]
  ring

theorem exists_hasDerivAt_sphAngleZeroAtTwo {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧
      HasDerivAt (fun t => σ.sphAngleZeroAtTwo (sphCirc σ.vertexTwo z t)) d 0 := by
  have hv2 := one_add_vertexTwo_ne_of_domZero hz
  have hγ := hasDerivAt_sphCirc hv2
  have hγ0 : sphCirc σ.vertexTwo z 0 = z := sphCirc_zero hv2
  have hA0 := sphModTwo_pos hs z
  have hP0 := sphCofBridgeZero_pos hs hz
  have hB0 := sphModThree_pos (sphCanon_bounds_zero hs hz).2
  have hz0 : z ≠ 0 := ne_zero_of_pos_norm_add_re_sph hz.1
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ),
      σ.sphModTwo (sphCirc σ.vertexTwo z t) = σ.sphModTwo z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc hv2] with t ht
    rw [sphModTwo, sphModTwo, sphCanon_one_eq_F hs, sphCanon_one_eq_F hs, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := σ.vertexTwo) (b := 0)
    (z := z) (sphTau_pos hs 2).le hv2 (by simp) (by simp) (by rwa [sphMoeb_zero])
  have hN : 0 < Complex.normSq (1 + σ.sphTTwoThree * z) := by
    rw [normSq_one_add_real_sph]
    have := hz.2.1
    positivity
  have hB : HasDerivAt (fun t => σ.sphModThree (sphCirc σ.vertexTwo z t))
      (σ.wallSide 0 z * (compactProfileSlope * K *
        (σ.sphTTwoThree * (1 + σ.sphTTwoThree ^ 2)) / Complex.normSq (1 + σ.sphTTwoThree * z)))
      0 := by
    have e : (fun t => σ.sphModThree (sphCirc σ.vertexTwo z t)) = fun t => 3 -
        compactProfileSlope * sphCanonF (σ.sphTau 2) ‖sphMoeb 0 (sphCirc σ.vertexTwo z t)‖ := by
      funext t
      rw [sphModThree, sphCanon_two_eq_F]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_sub 3).congr_deriv ?_
    have key := im_conj_sphMoeb_vertexTwo_zero_mul (σ := σ) z
    field_simp
    linear_combination (-compactProfileSlope) * key
  have hW : HasDerivAt (fun t => σ.wallSide 0 (sphCirc σ.vertexTwo z t))
      ((1 + conj σ.vertexTwo * σ.vertexTwo) / (1 - conj σ.vertexTwo * sphMoeb σ.vertexTwo z) ^ 2 *
        (sphMoeb σ.vertexTwo z * I)).im 0 :=
    hasDerivAt_im_curve_sph hγ
  have h := hasDerivAt_negHalfArg_curve_sph (a := -(3 / 2)) (b := 0) (by norm_num)
    (A := σ.sphModTwo) (B := σ.sphModThree) (W := σ.wallSide 0) (P := σ.sphCofBridgeZero) hγ
    hγ0 hA0 hA hB hW (contDiffAt_sphCofBridgeZero hs hz) isOpen_sphDomZero hz
    (fun u hu => sphCofBridgeZero_pos hs hu)
    (fun u hu => by have := heron_sphBridgeZero hs hu; linear_combination this)
    (by rw [← twoCircle_swap]; simpa [sphBridgeZero] using hpos)
  have e : (fun t => σ.sphAngleZeroAtTwo (sphCirc σ.vertexTwo z t)) = fun t =>
      negHalfArg (σ.sphModTwo (sphCirc σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) 0 (σ.sphModTwo (sphCirc σ.vertexTwo z t))
          (σ.sphModThree (sphCirc σ.vertexTwo z t)) (σ.wallSide 0 (sphCirc σ.vertexTwo z t))
          (σ.sphCofBridgeZero (sphCirc σ.vertexTwo z t))).re - -(3 / 2))
        (twoCircle (-(3 / 2)) 0 (σ.sphModTwo (sphCirc σ.vertexTwo z t))
          (σ.sphModThree (sphCirc σ.vertexTwo z t)) (σ.wallSide 0 (sphCirc σ.vertexTwo z t))
          (σ.sphCofBridgeZero (sphCirc σ.vertexTwo z t))).im := by
    funext t
    rw [sphAngleZeroAtTwo, sphBridgeZero, twoCircle_swap, sub_neg_eq_add]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hx := re_lt_of_pairDom_im_zero hz hw
    have hzr : z = (z.re : ℂ) := eq_ofReal_re_of_im_sph hw
    set x := z.re
    set t := σ.sphTTwoThree
    have h2 : 0 < 1 + t * x := hz.2.1
    have hω : sphMoeb σ.vertexTwo z = (((x - t) / (1 + t * x) : ℝ) : ℂ) := by
      rw [vertexTwo_eq_sph, hzr, sphMoeb_ofReal]
    have hρ : (x - t) / (1 + t * x) < 0 := div_neg_of_neg_of_pos (by linarith) h2
    set ρ := (x - t) / (1 + t * x)
    have hden : 1 - t * ρ ≠ 0 := by nlinarith [tTwoThree_pos_sph hs]
    have hV : ((1 + conj σ.vertexTwo * σ.vertexTwo) /
        (1 - conj σ.vertexTwo * sphMoeb σ.vertexTwo z) ^ 2 * (sphMoeb σ.vertexTwo z * I)).im =
        (1 + t ^ 2) / (1 - t * ρ) ^ 2 * ρ := by
      rw [hω, conj_vertexTwo_sph, vertexTwo_eq_sph]
      have e2 : ((1 : ℂ) + (t : ℂ) * t) / (1 - (t : ℂ) * (ρ : ℂ)) ^ 2 * ((ρ : ℂ) * I) =
          (((1 + t ^ 2) / (1 - t * ρ) ^ 2 * ρ : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [e2, Complex.im_ofReal_mul, I_im, mul_one]
    rw [hV]
    have := Real.sqrt_pos.2 hP0
    have hneg : (1 + t ^ 2) / (1 - t * ρ) ^ 2 * ρ < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hρ
    have : (1 + t ^ 2) / (1 - t * ρ) ^ 2 * ρ * Real.sqrt (σ.sphCofBridgeZero z) /
        (2 * |(0 : ℝ) - -(3 / 2)| * σ.sphModTwo z) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg this) (by positivity)
    linarith
  · apply twoCircle_div_sqrt_pos_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * K * (σ.sphTTwoThree * (1 + σ.sphTTwoThree ^ 2)) /
        Complex.normSq (1 + σ.sphTTwoThree * z) := by
      have := tTwoThree_pos_sph hs
      unfold compactProfileSlope
      positivity
    exact div_pos this (by norm_num)


theorem sphMoeb_vertexOne_eq_rotOne (z : ℂ) :
    sphMoeb σ.vertexOne z = -(exp ((σ.θ₃ : ℂ) * I) * σ.rotOne z) := by
  rw [rotOne_eq_mul_sph hs]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (-sphMoeb σ.vertexOne z) * this

theorem eventually_rotOne_sphCirc {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), σ.rotOne (sphCirc σ.vertexOne z t) = σ.rotOne z * exp ((t : ℂ) * I) := by
  filter_upwards [eventually_sphMoeb_sphCirc h] with t ht
  rw [rotOne_eq_mul_sph hs, rotOne_eq_mul_sph hs, ht]
  ring

theorem conj_sphMoeb_vertexOne_zero_mul (z : ℂ) :
    conj (sphMoeb σ.vertexOne 0) * sphMoeb σ.vertexOne z = σ.sphTOneThree * σ.rotOne z := by
  have e : sphMoeb σ.vertexOne 0 = -σ.vertexOne := by simp [sphMoeb]
  rw [e, sphMoeb_vertexOne_eq_rotOne hs, map_neg, conj_vertexOne_sph]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (σ.sphTOneThree * σ.rotOne z) * this

theorem conj_sphMoeb_vertexOne_vertexTwo_mul (z : ℂ) :
    conj (sphMoeb σ.vertexOne σ.vertexTwo) * sphMoeb σ.vertexOne z =
      σ.sphTOneTwo * (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) := by
  rw [sphMoeb_vertexOne_eq_rotOne hs, sphMoeb_vertexOne_eq_rotOne hs, rotOne_vertexTwo_sph hs,
    map_neg, map_mul, map_mul, conj_exp_ofReal_mul_I_sph, conj_exp_ofReal_mul_I_sph,
    Complex.conj_ofReal]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (σ.sphTOneTwo * exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) * this

theorem exists_hasDerivAt_sphAngleOneAtOne {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧
      HasDerivAt (fun t => σ.sphAngleOneAtOne (sphCirc σ.vertexOne z t)) d 0 := by
  have hv1 := one_add_conj_vertexOne_ne_of_domOne hz
  have hγ := hasDerivAt_sphCirc hv1
  have hγ0 : sphCirc σ.vertexOne z 0 = z := sphCirc_zero hv1
  have hA0 := sphModOne_pos hs z
  have hP0 := sphCofBridgeOne_pos hs hz
  have hB0 := sphModThree_pos (sphCanon_bounds_one hs hz).2
  have hz0 : z ≠ 0 := by
    intro h0
    have := hz.1
    rw [h0, mul_zero] at this
    simp at this
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ),
      σ.sphModOne (sphCirc σ.vertexOne z t) = σ.sphModOne z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc hv1] with t ht
    rw [sphModOne, sphModOne, sphCanon_zero_eq_F hs, sphCanon_zero_eq_F hs, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := σ.vertexOne) (b := 0)
    (z := z) (sphTau_pos hs 2).le hv1 (by simp) (by simp) (by rwa [sphMoeb_zero])
  have hN : 0 < Complex.normSq (1 + conj σ.vertexOne * z) := Complex.normSq_pos.2 hv1
  have hB : HasDerivAt (fun t => σ.sphModThree (sphCirc σ.vertexOne z t))
      (σ.wallSide 1 z * (-(compactProfileSlope * K *
        (σ.sphTOneThree * (1 + σ.sphTOneThree ^ 2)) /
          Complex.normSq (1 + conj σ.vertexOne * z)))) 0 := by
    have e : (fun t => σ.sphModThree (sphCirc σ.vertexOne z t)) = fun t => 3 -
        compactProfileSlope * sphCanonF (σ.sphTau 2) ‖sphMoeb 0 (sphCirc σ.vertexOne z t)‖ := by
      funext t
      rw [sphModThree, sphCanon_two_eq_F]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_sub 3).congr_deriv ?_
    have key := wallSide_one_eq_rotOne_sph hs z
    rw [conj_sphMoeb_vertexOne_zero_mul hs, Complex.im_ofReal_mul]
    field_simp
    linear_combination (compactProfileSlope * σ.sphTOneThree) * key
  have hW := hasDerivAt_wallSide_one_curve_sph (σ := σ) hγ
  have h := hasDerivAt_halfArg_curve_sph (a := 3 / 2) (b := 0) (by norm_num)
    (A := σ.sphModOne) (B := σ.sphModThree) (W := σ.wallSide 1) (P := σ.sphCofBridgeOne) hγ
    hγ0 hA0 hA hB hW (contDiffAt_sphCofBridgeOne hs hz) isOpen_sphDomOne hz
    (fun u hu => sphCofBridgeOne_pos hs hu)
    (fun u hu => by have := heron_sphBridgeOne hs hu; linear_combination this)
    (by rw [← twoCircle_swap]; simpa [sphBridgeOne] using hpos)
  have e : (fun t => σ.sphAngleOneAtOne (sphCirc σ.vertexOne z t)) = fun t =>
      halfArg (σ.sphModOne (sphCirc σ.vertexOne z t))
        ((twoCircle (3 / 2) 0 (σ.sphModOne (sphCirc σ.vertexOne z t))
          (σ.sphModThree (sphCirc σ.vertexOne z t)) (σ.wallSide 1 (sphCirc σ.vertexOne z t))
          (σ.sphCofBridgeOne (sphCirc σ.vertexOne z t))).re - 3 / 2)
        (twoCircle (3 / 2) 0 (σ.sphModOne (sphCirc σ.vertexOne z t))
          (σ.sphModThree (sphCirc σ.vertexOne z t)) (σ.wallSide 1 (sphCirc σ.vertexOne z t))
          (σ.sphCofBridgeOne (sphCirc σ.vertexOne z t))).im := by
    funext t
    rw [sphAngleOneAtOne, sphBridgeOne, twoCircle_swap]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · set V := (1 + conj σ.vertexOne * σ.vertexOne) /
      (1 - conj σ.vertexOne * sphMoeb σ.vertexOne z) ^ 2 * (sphMoeb σ.vertexOne z * I)
    have hδ : HasDerivAt (fun t => 1 + conj σ.vertexOne * sphCirc σ.vertexOne z t)
        (conj σ.vertexOne * V) 0 := (hγ.const_mul _).const_add 1
    have hNd := hasDerivAt_normSq_curve_sph hδ
    have hR := hasDerivAt_im_curve_sph (hasDerivAt_rot_sph (σ.rotOne z))
    have h1 := (hR.mul hNd)
    have h2 := hW.mul_const (1 + σ.sphTOneThree ^ 2)
    have heq : (fun t => σ.wallSide 1 (sphCirc σ.vertexOne z t) * (1 + σ.sphTOneThree ^ 2)) =ᶠ[𝓝 0]
        fun t => (σ.rotOne z * exp ((t : ℂ) * I)).im *
          Complex.normSq (1 + conj σ.vertexOne * sphCirc σ.vertexOne z t) := by
      filter_upwards [eventually_rotOne_sphCirc hs hv1] with t ht
      rw [wallSide_one_eq_rotOne_sph hs, ht]
    have hu := (h2.congr_of_eventuallyEq heq.symm).unique h1
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, hγ0] at hu
    have him : (σ.rotOne z).im = 0 := by
      have key := wallSide_one_eq_rotOne_sph hs z
      rw [hw, zero_mul] at key
      exact (mul_eq_zero.1 key.symm).resolve_right hN.ne'
    have hre : 0 < (σ.rotOne z).re := by
      have hY : (exp (-((σ.θ₃ : ℂ) * I)) * z).im = 0 := by
        rw [wallSide_one_eq_neg_im_sph] at hw
        linarith
      have hX0 := re_pos_of_im_eq_zero_sph hz.1 hY
      have hXt := re_lt_of_pairDom_im_zero hz hY
      rw [rotOne_eq_neg_sphMoeb hs, eq_ofReal_re_of_im_sph hY, sphMoeb_ofReal, neg_re, ofReal_re]
      have h2' : 0 < 1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z).re := hz.2.1
      rw [neg_pos]
      exact div_neg_of_neg_of_pos (by linarith) h2'
    have hw' : Real.sin σ.θ₃ * V.re - Real.cos σ.θ₃ * V.im =
        (σ.rotOne z).re * Complex.normSq (1 + conj σ.vertexOne * z) /
          (1 + σ.sphTOneThree ^ 2) := by
      have e2 : (σ.rotOne z * I).im = (σ.rotOne z).re := by simp
      rw [e2, him, zero_mul, add_zero] at hu
      field_simp
      linarith
    rw [hw']
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply twoCircle_div_sqrt_pos_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * K * (σ.sphTOneThree * (1 + σ.sphTOneThree ^ 2)) /
        Complex.normSq (1 + conj σ.vertexOne * z) := by
      have := tOneThree_pos_sph hs
      unfold compactProfileSlope
      positivity
    exact div_pos_of_neg_of_neg (neg_neg_of_pos this) (by norm_num)


theorem sphMoeb_vertexTwo_ne_of_domTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    sphMoeb σ.vertexTwo z ≠ 0 := by
  rw [← norm_ne_zero_iff, ← norm_rotTwo_sph hs, norm_ne_zero_iff]
  exact ne_zero_of_pos_norm_add_re_sph hz.2.2.1

omit hs in
theorem normSq_one_add_rotTwo_pos {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    0 < Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) := by
  rw [normSq_one_add_real_sph]
  have := hz.2.2.2.1
  positivity

omit hs in
theorem im_exp_neg_mul_eq (θ : ℝ) (ρ : ℂ) :
    (exp (-((θ : ℂ) * I)) * ρ).im = -(exp ((θ : ℂ) * I) * conj ρ).im := by
  rw [← conj_exp_neg_sph, ← map_mul, Complex.conj_im, neg_neg]

theorem exists_hasDerivAt_sphAngleTwoAtOne {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧
      HasDerivAt (fun t => σ.sphAngleTwoAtOne (sphCirc σ.vertexOne z t)) d 0 := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz.2.1
  have hv2 := one_add_vertexTwo_ne_of_domTwo hz
  have hγ := hasDerivAt_sphCirc hv1
  have hγ0 : sphCirc σ.vertexOne z 0 = z := sphCirc_zero hv1
  have hA0 := sphModOne_pos hs z
  have hP0 := sphCofBridgeTwo_pos hs hz
  have hB0 := sphModTwo_pos hs z
  have hM := normSq_one_add_rotTwo_pos hz
  have key2 := wallSide_two_eq_rotOne_sph hs hv1 hv2
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ),
      σ.sphModOne (sphCirc σ.vertexOne z t) = σ.sphModOne z := by
    filter_upwards [eventually_norm_sphMoeb_sphCirc hv1] with t ht
    rw [sphModOne, sphModOne, sphCanon_zero_eq_F hs, sphCanon_zero_eq_F hs, ht]
  obtain ⟨K, hK, hd⟩ := exists_hasDerivAt_canonF_sphCirc (a := σ.vertexOne) (b := σ.vertexTwo)
    (z := z) (sphTau_pos hs 1).le hv1 (one_add_conj_vertexOne_mul_vertexTwo_ne_sph hs) hv2
    (sphMoeb_vertexTwo_ne_of_domTwo hs hz)
  have hc : (exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z)).im =
      (1 + σ.sphTOneTwo ^ 2) * (σ.rotTwo z).im / Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) :=
    eq_div_of_mul_eq hM.ne' key2
  have hB : HasDerivAt (fun t => σ.sphModTwo (sphCirc σ.vertexOne z t))
      (σ.sphSideTwo z * (-(compactProfileSlope * K * (σ.sphTOneTwo * (1 + σ.sphTOneTwo ^ 2)) /
        Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z)))) 0 := by
    have e : (fun t => σ.sphModTwo (sphCirc σ.vertexOne z t)) = fun t => 3 / 2 +
        compactProfileSlope * sphCanonF (σ.sphTau 1)
          ‖sphMoeb σ.vertexTwo (sphCirc σ.vertexOne z t)‖ := by
      funext t
      rw [sphModTwo, sphCanon_one_eq_F hs]
    rw [e]
    refine ((hd.const_mul compactProfileSlope).const_add (3 / 2)).congr_deriv ?_
    rw [conj_sphMoeb_vertexOne_vertexTwo_mul hs, Complex.im_ofReal_mul, im_exp_neg_mul_eq, hc,
      sphSideTwo]
    ring
  have hdiff : DifferentiableAt ℝ σ.rotTwo z :=
    (contDiffAt_rotTwo_sph hs hz.1).differentiableAt (by simp)
  have hl : HasFDerivAt σ.rotTwo (fderiv ℝ σ.rotTwo z) (sphCirc σ.vertexOne z 0) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hR2 := hl.comp_hasDerivAt (0 : ℝ) hγ
  have hW : HasDerivAt (fun t => σ.sphSideTwo (sphCirc σ.vertexOne z t))
      (fderiv ℝ σ.rotTwo z ((1 + conj σ.vertexOne * σ.vertexOne) /
        (1 - conj σ.vertexOne * sphMoeb σ.vertexOne z) ^ 2 * (sphMoeb σ.vertexOne z * I))).im 0 :=
    hasDerivAt_im_curve_sph hR2
  have h := hasDerivAt_negHalfArg_curve_sph (a := 3 / 2) (b := -(3 / 2)) (by norm_num)
    (A := σ.sphModOne) (B := σ.sphModTwo) (W := σ.sphSideTwo) (P := σ.sphCofBridgeTwo) hγ
    hγ0 hA0 hA hB hW (contDiffAt_sphCofBridgeTwo hs hz) (isOpen_sphDomTwo hs) hz
    (fun u hu => sphCofBridgeTwo_pos hs hu) (fun u hu => heron_sphBridgeTwo hs hu)
    (by simpa [sphBridgeTwo] using hpos)
  have e : (fun t => σ.sphAngleTwoAtOne (sphCirc σ.vertexOne z t)) = fun t =>
      negHalfArg (σ.sphModOne (sphCirc σ.vertexOne z t))
        ((twoCircle (3 / 2) (-(3 / 2)) (σ.sphModOne (sphCirc σ.vertexOne z t))
          (σ.sphModTwo (sphCirc σ.vertexOne z t)) (σ.sphSideTwo (sphCirc σ.vertexOne z t))
          (σ.sphCofBridgeTwo (sphCirc σ.vertexOne z t))).re - 3 / 2)
        (twoCircle (3 / 2) (-(3 / 2)) (σ.sphModOne (sphCirc σ.vertexOne z t))
          (σ.sphModTwo (sphCirc σ.vertexOne z t)) (σ.sphSideTwo (sphCirc σ.vertexOne z t))
          (σ.sphCofBridgeTwo (sphCirc σ.vertexOne z t))).im := by
    funext t
    rw [sphAngleTwoAtOne, sphBridgeTwo]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · set w' := (fderiv ℝ σ.rotTwo z ((1 + conj σ.vertexOne * σ.vertexOne) /
        (1 - conj σ.vertexOne * sphMoeb σ.vertexOne z) ^ 2 * (sphMoeb σ.vertexOne z * I))).im
    set c := exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z) with hcdef
    have him : c.im = 0 := by
      rw [hc]
      change (1 + σ.sphTOneTwo ^ 2) * σ.sphSideTwo z / _ = 0
      rw [hw, mul_zero, zero_div]
    have hδ : HasDerivAt (fun t => 1 + σ.sphTOneTwo * σ.rotTwo (sphCirc σ.vertexOne z t))
        (σ.sphTOneTwo * fderiv ℝ σ.rotTwo z ((1 + conj σ.vertexOne * σ.vertexOne) /
          (1 - conj σ.vertexOne * sphMoeb σ.vertexOne z) ^ 2 * (sphMoeb σ.vertexOne z * I))) 0 :=
      (hR2.const_mul _).const_add 1
    have hNd := hasDerivAt_normSq_curve_sph hδ
    have hR := hasDerivAt_im_curve_sph (hasDerivAt_rot_sph (conj c))
    have h1 := (hR.neg).mul hNd
    have h2 := hW.mul_const (1 + σ.sphTOneTwo ^ 2)
    have heq : (fun t => σ.sphSideTwo (sphCirc σ.vertexOne z t) * (1 + σ.sphTOneTwo ^ 2)) =ᶠ[𝓝 0]
        fun t => -(conj c * exp ((t : ℂ) * I)).im *
          Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo (sphCirc σ.vertexOne z t)) := by
      filter_upwards [eventually_rotOne_sphCirc hs hv1, eventually_ne_sphCirc (b := σ.vertexOne)
        hv1 hv1, eventually_ne_sphCirc (b := σ.vertexTwo) hv1 hv2] with t ht e1 e2
      have k := wallSide_two_eq_rotOne_sph hs e1 e2
      rw [ht] at k
      have e3 : -(conj c * exp ((t : ℂ) * I)).im =
          (exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z * exp ((t : ℂ) * I))).im := by
        have h3 : conj (conj c * exp ((t : ℂ) * I)) =
            exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z * exp ((t : ℂ) * I)) := by
          rw [map_mul, Complex.conj_conj, hcdef, map_mul (starRingEnd ℂ) (σ.rotOne z)]
          ring
        rw [← h3, Complex.conj_im]
      rw [e3, k, sphSideTwo]
      ring
    have hu := (h2.congr_of_eventuallyEq heq.symm).unique h1
    simp only [Pi.neg_apply, ofReal_zero, zero_mul, Complex.exp_zero, mul_one, hγ0,
      Complex.conj_im, him, neg_zero, add_zero, Complex.mul_I_im, Complex.conj_re] at hu
    have hre : 0 < c.re := by
      have hY : (σ.rotTwo z).im = 0 := hw
      have hX0 := re_pos_of_im_eq_zero_sph hz.2.2.1 hY
      have hXt := re_lt_of_pairDom_im_zero hz.2.2 hY
      have h2' : 0 < 1 + σ.sphTOneTwo * (σ.rotTwo z).re := hz.2.2.2.1
      rw [hcdef, rotOne_eq_rotTwo_sph hs hv1 hv2, eq_ofReal_re_of_im_sph hY, sphMoeb_ofReal,
        map_neg, map_mul, Complex.conj_ofReal, conj_exp_ofReal_mul_I_sph, mul_neg, ← mul_assoc,
        exp_mul_exp_neg_sph, one_mul, neg_re, ofReal_re, neg_pos]
      exact div_neg_of_neg_of_pos (by linarith) h2'
    have hw' : w' = -c.re * Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) /
        (1 + σ.sphTOneTwo ^ 2) := by
      field_simp
      linarith
    rw [hw']
    have := Real.sqrt_pos.2 hP0
    have : 0 < c.re * Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) /
        (1 + σ.sphTOneTwo ^ 2) * Real.sqrt (σ.sphCofBridgeTwo z) /
          (2 * |-(3 / 2 : ℝ) - 3 / 2| * σ.sphModOne z) := by positivity
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_neg]
    exact this
  · apply twoCircle_div_sqrt_pos_sph (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * K * (σ.sphTOneTwo * (1 + σ.sphTOneTwo ^ 2)) /
        Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) := by
      have := tOneTwo_pos_sph hs
      unfold compactProfileSlope
      positivity
    exact div_pos_of_neg_of_neg (neg_neg_of_pos this) (by norm_num)

end Spherical

end CompactShape

end GC.Seifert
