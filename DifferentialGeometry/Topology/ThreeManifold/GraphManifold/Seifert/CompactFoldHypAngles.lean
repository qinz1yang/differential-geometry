import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCircle

/-!
# Angles of the hyperbolic bridges along circles about the vertices

Lane CF-H, tier 2 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4, curvature `-1`).
As in the flat case the angles of the bridges about the centres of the target are A4's `halfArg`
(bridge point on the positive side of the centre) and `negHalfArg` (negative side): about `+3/2`
`angleOneAtOne` (`0` on wall 1) and `angleTwoAtOne` (`π` on wall 2), about `-3/2` `angleTwoAtTwo`
(`0` on wall 2) and `angleZeroAtTwo` (`π` on wall 0), about `0` `angleOneAtThree` (`0` on wall 1)
and `angleZeroAtThree` (`π` on wall 0).

Along the hyperbolic circle `hcirc vⱼ z` the modulus of the vertex `vⱼ` is constant
(`canon_hcirc`), and the canonical coordinate of another vertex has derivative
`Im(e^{-iα} φ(z)) · c` with `c > 0`, where `φ` is the rotated disc coordinate at `vⱼ` and
`s e^{iα}` the position of the other vertex in it (`exists_hasDerivAt_canon_hcirc`). The side
function of a bridge is a positive multiple of `Im(e^{-iα} φ)` (`wallSide_one_eq_g`,
`wallSide_zero_eq_g`, `sideTwo_eq_g`), and a `twoCircle` is unchanged when its side function is
divided and its cofactor multiplied by the square of a positive factor (`twoCircle_rescale`), so
each angle is A4's angle of a `twoCircle` whose side function rotates rigidly along the circle.
With A4's derivative formula (`hasDerivAt_halfArg_curve`) the angles about `±3/2` strictly
increase and the angles about `0` strictly decrease along these circles, including at the walls
(`exists_hasDerivAt_angleOneAtOne` and its five siblings).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem twoCircle_rescale (a b A B w P g : ℝ) (hg : 0 < g) :
    twoCircle a b A B (w * g) P = twoCircle a b A B w (P * g ^ 2) := by
  apply Complex.ext
  · simp only [twoCircle_re]
  · simp only [twoCircle_im]
    rcases le_or_gt 0 P with hP | hP
    · rw [Real.sqrt_mul hP, Real.sqrt_sq hg.le]
      ring
    · rw [Real.sqrt_eq_zero'.2 hP.le, Real.sqrt_eq_zero'.2 (by nlinarith)]
      ring

theorem div_sqrt_pos_aux {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : 0 < κ / d) : 0 < 2 * |d| * B * κ / (d * Real.sqrt P) := by
  have hs := Real.sqrt_pos.2 hP
  have e : 2 * |d| * B * κ / (d * Real.sqrt P) = 2 * |d| * B * (κ / d) / Real.sqrt P := by
    field_simp
  rw [e]
  have := abs_pos.2 hd
  positivity

theorem div_sqrt_neg_aux {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : κ / d < 0) : 2 * |d| * B * κ / (d * Real.sqrt P) < 0 := by
  have h := div_sqrt_pos_aux hd hB hP (κ := -κ) (by rw [neg_div]; linarith)
  have e : 2 * |d| * B * -κ / (d * Real.sqrt P) = -(2 * |d| * B * κ / (d * Real.sqrt P)) := by
    ring
  linarith

theorem hasDerivAt_im_curve {γ : ℝ → ℂ} {V : ℂ} (h : HasDerivAt γ V 0) :
    HasDerivAt (fun t => (γ t).im) V.im 0 := by
  refine (imCLM.hasFDerivAt.comp_hasDerivAt 0 h).congr_deriv ?_
  simp

theorem hasDerivAt_mul_exp (c : ℂ) :
    HasDerivAt (fun t : ℝ => c * exp ((t : ℂ) * I)) (c * I) 0 := by
  have he : HasDerivAt (fun t : ℝ => exp ((t : ℂ) * I)) I 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp
    simpa using this
  exact he.const_mul c

theorem hasDerivAt_im_rot_circle (c φ : ℂ) :
    HasDerivAt (fun t : ℝ => (c * (φ * exp ((t : ℂ) * I))).im) (c * φ).re 0 := by
  have h := hasDerivAt_im_curve ((hasDerivAt_mul_exp φ).const_mul c)
  refine h.congr_deriv ?_
  simp [mul_im, I_re, I_im, mul_re]
  ring

theorem hcirc_zero_left (z : ℂ) (t : ℝ) : hcirc 0 z t = z * exp ((t : ℂ) * I) := by
  simp [hcirc, mobInv, mob]

theorem hasDerivAt_norm_mob_hcirc_coord {v z a u : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ < 1)
    (hz : ‖z‖ < 1) (ha : ‖a‖ < 1) (hne : mob a z ≠ 0) {s α : ℝ}
    (hφ : u * mob v a = (s : ℂ) * exp ((α : ℂ) * I)) :
    HasDerivAt (fun t : ℝ => ‖mob a (hcirc v z t)‖)
      (s * (exp (-((α : ℂ) * I)) * (u * mob v z)).im *
        ((1 - s ^ 2) * (1 - normSq (mob v z)) /
          (normSq (1 - conj (mob v a) * mob v z) ^ 2 * ‖mob a z‖))) 0 := by
  have h := hasDerivAt_norm_mob_hcirc hv hz ha hne
  have hcu : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hq : mob v a = conj u * ((s : ℂ) * exp ((α : ℂ) * I)) := by
    rw [← hφ, ← mul_assoc, hcu, one_mul]
  have e1 : conj (mob v a) * mob v z =
      (s : ℂ) * (exp (-((α : ℂ) * I)) * (u * mob v z)) := by
    rw [hq, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have e2 : normSq (mob v a) = s ^ 2 := by
    rw [hq, map_mul, map_mul, Complex.normSq_conj, Complex.normSq_eq_norm_sq u, hu,
      normSq_ofReal, Complex.normSq_eq_norm_sq (exp _), Complex.norm_exp_ofReal_mul_I]
    ring
  refine h.congr_deriv ?_
  rw [e1, e2, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  ring

theorem re_pos_of_norm_add_re_pos {w : ℂ} (h : 0 < ‖w‖ + w.re) (hi : w.im = 0) :
    0 < w.re := by
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

theorem contDiffAt_normSq_comp {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun u => normSq (f u)) z := by
  have hr : ContDiffAt ℝ ∞ (fun u => (f u).re) z := reCLM.contDiff.contDiffAt.comp z hf
  have hi : ContDiffAt ℝ ∞ (fun u => (f u).im) z := imCLM.contDiff.contDiffAt.comp z hf
  simp only [normSq_apply]
  exact (hr.mul hr).add (hi.mul hi)

variable (σ : CompactShape)

def angleOneAtOne (z : ℂ) : ℝ :=
  halfArg (modOne σ z) ((bridgeOne σ z).re - 3 / 2) (bridgeOne σ z).im

def angleTwoAtOne (z : ℂ) : ℝ :=
  negHalfArg (modOne σ z) ((bridgeTwo σ z).re - 3 / 2) (bridgeTwo σ z).im

def angleTwoAtTwo (z : ℂ) : ℝ :=
  halfArg (modTwo σ z) ((bridgeTwo σ z).re + 3 / 2) (bridgeTwo σ z).im

def angleZeroAtTwo (z : ℂ) : ℝ :=
  negHalfArg (modTwo σ z) ((bridgeZero σ z).re + 3 / 2) (bridgeZero σ z).im

def angleOneAtThree (z : ℂ) : ℝ :=
  halfArg (modThree σ z) (bridgeOne σ z).re (bridgeOne σ z).im

def angleZeroAtThree (z : ℂ) : ℝ :=
  negHalfArg (modThree σ z) (bridgeZero σ z).re (bridgeZero σ z).im

def gOne (z : ℂ) : ℝ := normSq (1 - conj σ.vertexOne * z) / (1 - sideOneThree σ ^ 2)

def gZero (z : ℂ) : ℝ := normSq (1 - σ.vertexTwo * z) / (1 - sideTwoThree σ ^ 2)

def gTwo (z : ℂ) : ℝ :=
  normSq (1 - (sideOneTwo σ : ℂ) * σ.rotTwo z) / (1 - sideOneTwo σ ^ 2)

def vtx : Fin 3 → ℂ
  | 0 => σ.vertexOne
  | 1 => σ.vertexTwo
  | 2 => 0

variable {σ}

theorem hd_eq (j : Fin 3) (u : ℂ) : hd σ j u = ‖mob (vtx σ j) u‖ := by
  fin_cases j
  · rfl
  · rfl
  · change ‖u‖ = ‖mob 0 u‖
    rw [mob_zero_left]

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem norm_vtx_lt_one (j : Fin 3) : ‖vtx σ j‖ < 1 := by
  fin_cases j
  · exact norm_vertexOne_lt_one h
  · exact norm_vertexTwo_lt_one h
  · change ‖(0 : ℂ)‖ < 1
    simp

theorem exists_hasDerivAt_canon_hcirc (j : Fin 3) {v z u : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ < 1)
    (hz : ‖z‖ < 1) (hne : hd σ j z ≠ 0) {s α : ℝ} (hs0 : 0 < s)
    (hφ : u * mob v (vtx σ j) = (s : ℂ) * exp ((α : ℂ) * I)) :
    ∃ c : ℝ, 0 < c ∧ HasDerivAt (fun t => canon σ j (hcirc v z t))
      ((exp (-((α : ℂ) * I)) * (u * mob v z)).im * c) 0 := by
  have ha := norm_vtx_lt_one h j
  have hne' : mob (vtx σ j) z ≠ 0 := by
    rw [hd_eq] at hne
    exact norm_ne_zero_iff.1 hne
  have hdd := hasDerivAt_norm_mob_hcirc_coord hu hv hz ha hne' hφ
  have hs1 : s < 1 := by
    have h1 : ‖(s : ℂ) * exp ((α : ℂ) * I)‖ = s := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
    rw [← h1, ← hφ, norm_mul, hu, one_mul]
    exact norm_mob_lt_one hv ha
  obtain ⟨t0, t1⟩ := tau_mem h j
  have hd0 : ‖mob (vtx σ j) (hcirc v z 0)‖ = hd σ j z := by
    rw [hcirc_zero hv hz, hd_eq]
  have hd1 := hd_lt_one h j hz
  have hdn := hd_nonneg (σ := σ) j z
  have hden : 1 - ‖mob (vtx σ j) (hcirc v z 0)‖ * tau σ j ≠ 0 := by
    rw [hd0]
    nlinarith
  have hc := hasDerivAt_canonForm hdd hden
  have hm := norm_mob_lt_one hv hz
  have hm2 : 0 < 1 - normSq (mob v z) := by
    have := normSq_lt_one_of_norm_lt hm
    linarith
  have hq : 1 - conj (mob v (vtx σ j)) * mob v z ≠ 0 :=
    one_sub_conj_mul_ne_zero (norm_mob_lt_one hv ha) hm
  have hN : 0 < normSq (1 - conj (mob v (vtx σ j)) * mob v z) := normSq_pos.2 hq
  have hmz : 0 < ‖mob (vtx σ j) z‖ := norm_pos_iff.2 hne'
  refine ⟨(1 - tau σ j ^ 2) / (1 - hd σ j z * tau σ j) ^ 2 * s *
    ((1 - s ^ 2) * (1 - normSq (mob v z)) /
      (normSq (1 - conj (mob v (vtx σ j)) * mob v z) ^ 2 * ‖mob (vtx σ j) z‖)), ?_, ?_⟩
  · have a1 : 0 < 1 - tau σ j ^ 2 := by nlinarith
    have a2 : 0 < 1 - s ^ 2 := by nlinarith
    have a3 : 0 < 1 - hd σ j z * tau σ j := by nlinarith
    positivity
  · have e : (fun t => canon σ j (hcirc v z t)) = fun t =>
        (‖mob (vtx σ j) (hcirc v z t)‖ - tau σ j) /
          (1 - ‖mob (vtx σ j) (hcirc v z t)‖ * tau σ j) := by
      funext t
      rw [canon, hd_eq]
    rw [e]
    refine hc.congr_deriv ?_
    rw [hd0]
    ring

theorem canon_hcirc (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    canon σ j (hcirc (vtx σ j) z t) = canon σ j z := by
  rw [canon, canon, hd_eq, hd_eq, norm_mob_hcirc (norm_vtx_lt_one h j) hz]

theorem modThree_hcirc {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    modThree σ (hcirc 0 z t) = modThree σ z := by
  rw [modThree, modThree, ← canon_hcirc h 2 hz t]
  rfl

theorem modTwo_hcirc {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    modTwo σ (hcirc σ.vertexTwo z t) = modTwo σ z := by
  rw [modTwo, modTwo, ← canon_hcirc h 1 hz t]
  rfl

theorem modOne_hcirc {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    modOne σ (hcirc σ.vertexOne z t) = modOne σ z := by
  rw [modOne, modOne, ← canon_hcirc h 0 hz t]
  rfl

theorem contDiffAt_cofBridgeOne {z : ℂ} (hz : z ∈ domOneThree σ) :
    ContDiffAt ℝ ∞ (cofBridgeOne σ) z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hv := hd_ne_zero_of_domOneThree h hz
  have hA : ContDiffAt ℝ ∞ (modThree σ) z :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_canon h 2 hz1 hv.1))
  have hB : ContDiffAt ℝ ∞ (modOne σ) z :=
    contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 0 hz1 hv.2))
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul (contDiffAt_cofOneThree h hz))

theorem contDiffAt_cofBridgeZero {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ContDiffAt ℝ ∞ (cofBridgeZero σ) z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hv := hd_ne_zero_of_domZeroThree h hz
  have hA : ContDiffAt ℝ ∞ (modThree σ) z :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_canon h 2 hz1 hv.1))
  have hB : ContDiffAt ℝ ∞ (modTwo σ) z :=
    contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 1 hz1 hv.2))
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul (contDiffAt_cofZeroThree h hz))

theorem contDiffAt_cofBridgeTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    ContDiffAt ℝ ∞ (cofBridgeTwo σ) z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hv := hd_ne_zero_of_domOneTwo h hz
  have hA : ContDiffAt ℝ ∞ (modOne σ) z :=
    contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 0 hz1 hv.2))
  have hB : ContDiffAt ℝ ∞ (modTwo σ) z :=
    contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 1 hz1 hv.1))
  exact (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
    (contDiffAt_const.mul (contDiffAt_cofTwo h hz))

theorem exists_hasDerivAt_angleOneAtThree {z : ℂ} (hz : z ∈ domOneThree σ)
    (hpos : 0 < modThree σ z + (bridgeOne σ z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => angleOneAtThree σ (hcirc 0 z t)) d 0 := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hv := hd_ne_zero_of_domOneThree h hz
  have hA0 : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hB0 : 0 < modOne σ z := by linarith [(modOne_mem h hz1).1]
  have hP0 := cofBridgeOne_pos h hz
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 0 (u := 1) norm_one h00 hz1 hv.2
    (sideOneThree_pos h) (α := σ.θ₃) (by rw [one_mul, mob_zero_left]; rfl)
  have hB' : HasDerivAt (fun t => modOne σ (hcirc 0 z t))
      (σ.wallSide 1 z * (-(compactProfileSlope * c))) 0 := by
    have := (hc.const_mul compactProfileSlope).const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [one_mul, mob_zero_left, wallSide_one_eq_neg_im]
    ring
  have hW : HasDerivAt (fun t => σ.wallSide 1 (hcirc 0 z t))
      (-(exp (-((σ.θ₃ : ℂ) * I)) * z).re) 0 := by
    have e : (fun t => σ.wallSide 1 (hcirc 0 z t)) =
        fun t : ℝ => -(exp (-((σ.θ₃ : ℂ) * I)) * (z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [hcirc_zero_left, wallSide_one_eq_neg_im]
    rw [e]
    exact (hasDerivAt_im_rot_circle _ z).neg
  have h' := hasDerivAt_halfArg_curve (a := 0) (b := 3 / 2) (by norm_num) (A := modThree σ)
    (B := modOne σ) (W := σ.wallSide 1) (P := cofBridgeOne σ) (hcirc_zero h00 hz1)
    (hasDerivAt_hcirc h00 hz1).differentiableAt hA0 (modThree_hcirc h hz1) hB' hW
    (contDiffAt_cofBridgeOne h hz) (isOpen_domOneThree h) hz
    (fun u hu => cofBridgeOne_pos h hu) (fun u hu => heron_bridgeOne h hu)
    (by rw [sub_zero]; exact hpos)
  have e : (fun t => angleOneAtThree σ (hcirc 0 z t)) = fun t =>
      halfArg (modThree σ (hcirc 0 z t))
        ((twoCircle 0 (3 / 2) (modThree σ (hcirc 0 z t)) (modOne σ (hcirc 0 z t))
          (σ.wallSide 1 (hcirc 0 z t)) (cofBridgeOne σ (hcirc 0 z t))).re - 0)
        (twoCircle 0 (3 / 2) (modThree σ (hcirc 0 z t)) (modOne σ (hcirc 0 z t))
          (σ.wallSide 1 (hcirc 0 z t)) (cofBridgeOne σ (hcirc 0 z t))).im := by
    funext t
    rw [angleOneAtThree, bridgeOne, sub_zero]
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
      apply re_pos_of_norm_add_re_pos hz.2.1
      have := wallSide_one_eq_neg_im (σ := σ) z
      rw [hw] at this
      linarith
    have := Real.sqrt_pos.2 hP0
    have : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re * Real.sqrt (cofBridgeOne σ z) /
        (2 * |3 / 2 - 0| * modThree σ z) := by positivity
    have e : -(exp (-((σ.θ₃ : ℂ) * I)) * z).re * Real.sqrt (cofBridgeOne σ z) /
        (2 * |3 / 2 - 0| * modThree σ z) = -((exp (-((σ.θ₃ : ℂ) * I)) * z).re *
        Real.sqrt (cofBridgeOne σ z) / (2 * |3 / 2 - 0| * modThree σ z)) := by ring
    rw [e]
    linarith
  · apply div_sqrt_neg_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (3 / 2 - 0 : ℝ) = 3 / 2 by norm_num, neg_div]
    have := div_pos this (by norm_num : (0 : ℝ) < 3 / 2)
    linarith

theorem exists_hasDerivAt_angleZeroAtThree {z : ℂ} (hz : z ∈ domZeroThree σ)
    (hpos : 0 < modThree σ z - (bridgeZero σ z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => angleZeroAtThree σ (hcirc 0 z t)) d 0 := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hv := hd_ne_zero_of_domZeroThree h hz
  have hA0 : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hB0 : 0 < modTwo σ z := by linarith [(modTwo_mem h hz1).1]
  have hP0 := cofBridgeZero_pos h hz
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 1 (u := 1) norm_one h00 hz1 hv.2
    (sideTwoThree_pos h) (α := 0) (by
      rw [one_mul, mob_zero_left, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]; rfl)
  have hB' : HasDerivAt (fun t => modTwo σ (hcirc 0 z t))
      (σ.wallSide 0 z * (compactProfileSlope * c)) 0 := by
    have := (hc.const_mul compactProfileSlope).const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [one_mul, mob_zero_left, ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    change compactProfileSlope * (z.im * c) = z.im * (compactProfileSlope * c)
    ring
  have hW : HasDerivAt (fun t => σ.wallSide 0 (hcirc 0 z t)) z.re 0 := by
    have e : (fun t => σ.wallSide 0 (hcirc 0 z t)) =
        fun t : ℝ => ((1 : ℂ) * (z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [hcirc_zero_left, one_mul]
      rfl
    rw [e]
    have := hasDerivAt_im_rot_circle 1 z
    rwa [one_mul] at this
  have h' := hasDerivAt_negHalfArg_curve (a := 0) (b := -(3 / 2)) (by norm_num)
    (A := modThree σ) (B := modTwo σ) (W := σ.wallSide 0) (P := cofBridgeZero σ)
    (hcirc_zero h00 hz1) (hasDerivAt_hcirc h00 hz1).differentiableAt hA0 (modThree_hcirc h hz1)
    hB' hW (contDiffAt_cofBridgeZero h hz) (isOpen_domZeroThree h) hz
    (fun u hu => cofBridgeZero_pos h hu) (fun u hu => heron_bridgeZero h hu)
    (by rw [sub_zero]; exact hpos)
  have e : (fun t => angleZeroAtThree σ (hcirc 0 z t)) = fun t =>
      negHalfArg (modThree σ (hcirc 0 z t))
        ((twoCircle 0 (-(3 / 2)) (modThree σ (hcirc 0 z t)) (modTwo σ (hcirc 0 z t))
          (σ.wallSide 0 (hcirc 0 z t)) (cofBridgeZero σ (hcirc 0 z t))).re - 0)
        (twoCircle 0 (-(3 / 2)) (modThree σ (hcirc 0 z t)) (modTwo σ (hcirc 0 z t))
          (σ.wallSide 0 (hcirc 0 z t)) (cofBridgeZero σ (hcirc 0 z t))).im := by
    funext t
    rw [angleZeroAtThree, bridgeZero, sub_zero]
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < z.re := re_pos_of_norm_add_re_pos hz.2.1 hw
    have := Real.sqrt_pos.2 hP0
    have : 0 < z.re * Real.sqrt (cofBridgeZero σ z) /
        (2 * |-(3 / 2) - 0| * modThree σ z) := by positivity
    linarith
  · apply div_sqrt_neg_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (-(3 / 2) - 0 : ℝ) = -(3 / 2) by norm_num, div_neg]
    have := div_pos this (by norm_num : (0 : ℝ) < 3 / 2)
    linarith

theorem rotTwo_hcirc {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    σ.rotTwo (hcirc σ.vertexTwo z t) = σ.rotTwo z * exp ((t : ℂ) * I) := by
  rw [rotTwo_eq_mul_mob h, rotTwo_eq_mul_mob h, mob_hcirc (norm_vertexTwo_lt_one h) hz]
  ring

theorem rotOne_hcirc {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    σ.rotOne (hcirc σ.vertexOne z t) = σ.rotOne z * exp ((t : ℂ) * I) := by
  rw [rotOne_eq_mul_mob h, rotOne_eq_mul_mob h, mob_hcirc (norm_vertexOne_lt_one h) hz]
  ring

theorem exists_hasDerivAt_angleTwoAtTwo {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hpos : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => angleTwoAtTwo σ (hcirc σ.vertexTwo z t)) d 0 := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hv := hd_ne_zero_of_domOneTwo h hz
  have hv2 := norm_vertexTwo_lt_one h
  have hA0 : 0 < modTwo σ z := by linarith [(modTwo_mem h hz1).1]
  have hB0 : 0 < modOne σ z := by linarith [(modOne_mem h hz1).1]
  have hP0 := cofBridgeTwo_pos h hz
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 0 (u := -exp ((σ.θ₂ : ℂ) * I))
    (norm_neg_exp σ.θ₂) hv2 hz1 hv.2 (sideOneTwo_pos h) (α := 0) (by
      rw [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, ← rotTwo_eq_mul_mob h]
      exact rotTwo_vertexOne h)
  have hB' : HasDerivAt (fun t => modOne σ (hcirc σ.vertexTwo z t))
      (sideTwo σ z * (compactProfileSlope * c)) 0 := by
    have := (hc.const_mul compactProfileSlope).const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, ← rotTwo_eq_mul_mob h]
    change compactProfileSlope * ((σ.rotTwo z).im * c) = (σ.rotTwo z).im * _
    ring
  have hW : HasDerivAt (fun t => sideTwo σ (hcirc σ.vertexTwo z t)) (σ.rotTwo z).re 0 := by
    have e : (fun t => sideTwo σ (hcirc σ.vertexTwo z t)) =
        fun t : ℝ => ((1 : ℂ) * (σ.rotTwo z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [sideTwo, rotTwo_hcirc h hz1, one_mul]
    rw [e]
    have := hasDerivAt_im_rot_circle 1 (σ.rotTwo z)
    rwa [one_mul] at this
  have h' := hasDerivAt_halfArg_curve (a := -(3 / 2)) (b := 3 / 2) (by norm_num)
    (A := modTwo σ) (B := modOne σ) (W := sideTwo σ) (P := cofBridgeTwo σ)
    (hcirc_zero hv2 hz1) (hasDerivAt_hcirc hv2 hz1).differentiableAt hA0
    (modTwo_hcirc h hz1) hB' hW (contDiffAt_cofBridgeTwo h hz) (isOpen_domOneTwo h) hz
    (fun u hu => cofBridgeTwo_pos h hu) (fun u hu => by
      have := heron_bridgeTwo h hu
      linear_combination this)
    (by rw [← twoCircle_swap, sub_neg_eq_add]; exact hpos)
  have e : (fun t => angleTwoAtTwo σ (hcirc σ.vertexTwo z t)) = fun t =>
      halfArg (modTwo σ (hcirc σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) (3 / 2) (modTwo σ (hcirc σ.vertexTwo z t))
          (modOne σ (hcirc σ.vertexTwo z t)) (sideTwo σ (hcirc σ.vertexTwo z t))
          (cofBridgeTwo σ (hcirc σ.vertexTwo z t))).re - -(3 / 2))
        (twoCircle (-(3 / 2)) (3 / 2) (modTwo σ (hcirc σ.vertexTwo z t))
          (modOne σ (hcirc σ.vertexTwo z t)) (sideTwo σ (hcirc σ.vertexTwo z t))
          (cofBridgeTwo σ (hcirc σ.vertexTwo z t))).im := by
    funext t
    rw [angleTwoAtTwo, bridgeTwo, twoCircle_swap, sub_neg_eq_add]
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < (σ.rotTwo z).re := re_pos_of_norm_add_re_pos hz.2.2.1 hw
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply div_sqrt_pos_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (3 / 2 - -(3 / 2) : ℝ) = 3 by norm_num]
    positivity

theorem gOne_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < gOne σ z := by
  have a := normSq_pos_of_ne (one_sub_conj_vertexOne_mul_ne_zero h hz)
  have b := sideOneThree_lt_one h
  have c := sideOneThree_pos h
  have : 0 < 1 - sideOneThree σ ^ 2 := by nlinarith
  exact div_pos a this

theorem gZero_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < gZero σ z := by
  have a := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz)
  have b := sideTwoThree_lt_one h
  have c := sideTwoThree_pos h
  have : 0 < 1 - sideTwoThree σ ^ 2 := by nlinarith
  exact div_pos a this

theorem one_sub_sideOneTwo_mul_rotTwo_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    1 - (sideOneTwo σ : ℂ) * σ.rotTwo z ≠ 0 :=
  one_sub_ofReal_mul_ne_zero (sideOneTwo_pos h) (sideOneTwo_lt_one h) (norm_rotTwo_lt_one h hz)

theorem gTwo_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < gTwo σ z := by
  have a := normSq_pos_of_ne (one_sub_sideOneTwo_mul_rotTwo_ne_zero h hz)
  have b := sideOneTwo_lt_one h
  have c := sideOneTwo_pos h
  have : 0 < 1 - sideOneTwo σ ^ 2 := by nlinarith
  exact div_pos a this

theorem wallSide_one_eq_g {z : ℂ} (hz : ‖z‖ < 1) :
    σ.wallSide 1 z = (σ.rotOne z).im * gOne σ z := by
  have e := rotOne_im_mul_normSq h hz
  have b := sideOneThree_lt_one h
  have c := sideOneThree_pos h
  have : 1 - sideOneThree σ ^ 2 ≠ 0 := by nlinarith
  rw [gOne, ← mul_div_assoc, e]
  field_simp

theorem wallSide_zero_eq_g (z : ℂ) :
    σ.wallSide 0 z = -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im * gZero σ z := by
  have e := rotTwo_rot_im_mul_normSq h z
  have b := sideTwoThree_lt_one h
  have c := sideTwoThree_pos h
  have : 1 - sideTwoThree σ ^ 2 ≠ 0 := by nlinarith
  rw [gZero, neg_mul, ← mul_div_assoc, e]
  field_simp

theorem sideTwo_eq_g {z : ℂ} (hz : ‖z‖ < 1) :
    sideTwo σ z = -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im * gTwo σ z := by
  have e := rotOne_rot_im_mul_normSq h hz
  have b := sideOneTwo_lt_one h
  have c := sideOneTwo_pos h
  have : 1 - sideOneTwo σ ^ 2 ≠ 0 := by nlinarith
  rw [gTwo, neg_mul, ← mul_div_assoc, e, sideTwo]
  field_simp

omit h in
theorem contDiffAt_gOne (z : ℂ) : ContDiffAt ℝ ∞ (gOne σ) z :=
  (contDiffAt_normSq_comp (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))).div_const _

omit h in
theorem contDiffAt_gZero (z : ℂ) : ContDiffAt ℝ ∞ (gZero σ) z :=
  (contDiffAt_normSq_comp (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))).div_const _

theorem contDiffAt_gTwo {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ (gTwo σ) z :=
  (contDiffAt_normSq_comp (contDiffAt_const.sub (contDiffAt_const.mul
    (contDiffAt_rotTwo h hz)))).div_const _

theorem angleOneAtOne_eq {z : ℂ} (hz : ‖z‖ < 1) : angleOneAtOne σ z =
    halfArg (modOne σ z)
      ((twoCircle (3 / 2) 0 (modOne σ z) (modThree σ z) (σ.rotOne z).im
        (cofBridgeOne σ z * gOne σ z ^ 2)).re - 3 / 2)
      (twoCircle (3 / 2) 0 (modOne σ z) (modThree σ z) (σ.rotOne z).im
        (cofBridgeOne σ z * gOne σ z ^ 2)).im := by
  rw [angleOneAtOne, bridgeOne, twoCircle_swap, wallSide_one_eq_g h hz,
    twoCircle_rescale _ _ _ _ _ _ _ (gOne_pos h hz)]

theorem angleZeroAtTwo_eq {z : ℂ} (hz : ‖z‖ < 1) : angleZeroAtTwo σ z =
    negHalfArg (modTwo σ z)
      ((twoCircle (-(3 / 2)) 0 (modTwo σ z) (modThree σ z)
        (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im) (cofBridgeZero σ z * gZero σ z ^ 2)).re -
          -(3 / 2))
      (twoCircle (-(3 / 2)) 0 (modTwo σ z) (modThree σ z)
        (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im) (cofBridgeZero σ z * gZero σ z ^ 2)).im := by
  rw [angleZeroAtTwo, bridgeZero, twoCircle_swap, wallSide_zero_eq_g h,
    twoCircle_rescale _ _ _ _ _ _ _ (gZero_pos h hz), sub_neg_eq_add]

theorem angleTwoAtOne_eq {z : ℂ} (hz : ‖z‖ < 1) : angleTwoAtOne σ z =
    negHalfArg (modOne σ z)
      ((twoCircle (3 / 2) (-(3 / 2)) (modOne σ z) (modTwo σ z)
        (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im) (cofBridgeTwo σ z * gTwo σ z ^ 2)).re -
          3 / 2)
      (twoCircle (3 / 2) (-(3 / 2)) (modOne σ z) (modTwo σ z)
        (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im) (cofBridgeTwo σ z * gTwo σ z ^ 2)).im := by
  rw [angleTwoAtOne, bridgeTwo, sideTwo_eq_g h hz,
    twoCircle_rescale _ _ _ _ _ _ _ (gTwo_pos h hz)]

theorem exists_hasDerivAt_angleOneAtOne {z : ℂ} (hz : z ∈ domOneThree σ)
    (hpos : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => angleOneAtOne σ (hcirc σ.vertexOne z t)) d 0 := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hv := hd_ne_zero_of_domOneThree h hz
  have hv1 := norm_vertexOne_lt_one h
  have hA0 : 0 < modOne σ z := by linarith [(modOne_mem h hz1).1]
  have hB0 : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hP0 : 0 < cofBridgeOne σ z * gOne σ z ^ 2 :=
    mul_pos (cofBridgeOne_pos h hz) (pow_pos (gOne_pos h hz1) 2)
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 2 (u := -exp (-((σ.θ₃ : ℂ) * I)))
    (norm_neg_exp_neg σ.θ₃) hv1 hz1 hv.1 (sideOneThree_pos h) (α := 0) (by
      rw [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, ← rotOne_eq_mul_mob h]
      exact rotOne_zero_eq)
  have hB' : HasDerivAt (fun t => modThree σ (hcirc σ.vertexOne z t))
      ((σ.rotOne z).im * (-(compactProfileSlope * c))) 0 := by
    have := (hc.const_mul compactProfileSlope).const_sub 3
    refine this.congr_deriv ?_
    rw [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, ← rotOne_eq_mul_mob h]
    ring
  have hW : HasDerivAt (fun t => (σ.rotOne (hcirc σ.vertexOne z t)).im) (σ.rotOne z).re 0 := by
    have e : (fun t => (σ.rotOne (hcirc σ.vertexOne z t)).im) =
        fun t : ℝ => ((1 : ℂ) * (σ.rotOne z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [rotOne_hcirc h hz1, one_mul]
    rw [e]
    have := hasDerivAt_im_rot_circle 1 (σ.rotOne z)
    rwa [one_mul] at this
  have hPc : ContDiffAt ℝ ∞ (fun u => cofBridgeOne σ u * gOne σ u ^ 2) z :=
    (contDiffAt_cofBridgeOne h hz).mul ((contDiffAt_gOne z).pow 2)
  have h' := hasDerivAt_halfArg_curve (a := 3 / 2) (b := 0) (by norm_num)
    (A := modOne σ) (B := modThree σ) (W := fun u => (σ.rotOne u).im)
    (P := fun u => cofBridgeOne σ u * gOne σ u ^ 2)
    (hcirc_zero hv1 hz1) (hasDerivAt_hcirc hv1 hz1).differentiableAt hA0
    (modOne_hcirc h hz1) hB' hW hPc (isOpen_domOneThree h) hz
    (fun u hu => mul_pos (cofBridgeOne_pos h hu)
      (pow_pos (gOne_pos h (norm_lt_one_of_domOneThree hu)) 2))
    (fun u hu => by
      have e := heron_bridgeOne h hu
      rw [wallSide_one_eq_g h (norm_lt_one_of_domOneThree hu)] at e
      linear_combination e)
    (by
      rw [show twoCircle (3 / 2) 0 (modOne σ z) (modThree σ z) (σ.rotOne z).im
          (cofBridgeOne σ z * gOne σ z ^ 2) = bridgeOne σ z by
        rw [bridgeOne, twoCircle_swap, wallSide_one_eq_g h hz1,
          twoCircle_rescale _ _ _ _ _ _ _ (gOne_pos h hz1)]]
      exact hpos)
  have e : (fun t => angleOneAtOne σ (hcirc σ.vertexOne z t)) = fun t =>
      halfArg (modOne σ (hcirc σ.vertexOne z t))
        ((twoCircle (3 / 2) 0 (modOne σ (hcirc σ.vertexOne z t))
          (modThree σ (hcirc σ.vertexOne z t)) (σ.rotOne (hcirc σ.vertexOne z t)).im
          (cofBridgeOne σ (hcirc σ.vertexOne z t) *
            gOne σ (hcirc σ.vertexOne z t) ^ 2)).re - 3 / 2)
        (twoCircle (3 / 2) 0 (modOne σ (hcirc σ.vertexOne z t))
          (modThree σ (hcirc σ.vertexOne z t)) (σ.rotOne (hcirc σ.vertexOne z t)).im
          (cofBridgeOne σ (hcirc σ.vertexOne z t) * gOne σ (hcirc σ.vertexOne z t) ^ 2)).im := by
    funext t
    exact angleOneAtOne_eq h (norm_hcirc_lt_one hv1 hz1 t)
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < (σ.rotOne z).re := re_pos_of_norm_add_re_pos hψ hw
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply div_sqrt_pos_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (0 - 3 / 2 : ℝ) = -(3 / 2) by norm_num, div_neg, neg_div, neg_neg]
    positivity

theorem exists_hasDerivAt_angleZeroAtTwo {z : ℂ} (hz : z ∈ domZeroThree σ)
    (hpos : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2))
    (hψ : 0 < ‖exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z‖ +
      (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => angleZeroAtTwo σ (hcirc σ.vertexTwo z t)) d 0 := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hv := hd_ne_zero_of_domZeroThree h hz
  have hv2 := norm_vertexTwo_lt_one h
  have hA0 : 0 < modTwo σ z := by linarith [(modTwo_mem h hz1).1]
  have hB0 : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hP0 : 0 < cofBridgeZero σ z * gZero σ z ^ 2 :=
    mul_pos (cofBridgeZero_pos h hz) (pow_pos (gZero_pos h hz1) 2)
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 2 (u := -exp ((σ.θ₂ : ℂ) * I))
    (norm_neg_exp σ.θ₂) hv2 hz1 hv.1 (sideTwoThree_pos h) (α := σ.θ₂) (by
      rw [← rotTwo_eq_mul_mob h]
      exact rotTwo_zero_eq)
  have hB' : HasDerivAt (fun t => modThree σ (hcirc σ.vertexTwo z t))
      ((-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im) * (compactProfileSlope * c)) 0 := by
    have := (hc.const_mul compactProfileSlope).const_sub 3
    refine this.congr_deriv ?_
    rw [← rotTwo_eq_mul_mob h]
    ring
  have hW : HasDerivAt (fun t => -(exp (-((σ.θ₂ : ℂ) * I)) *
      σ.rotTwo (hcirc σ.vertexTwo z t)).im) (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re) 0 := by
    have e : (fun t => -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo (hcirc σ.vertexTwo z t)).im) =
        fun t : ℝ => -(exp (-((σ.θ₂ : ℂ) * I)) * (σ.rotTwo z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [rotTwo_hcirc h hz1]
    rw [e]
    exact (hasDerivAt_im_rot_circle _ _).neg
  have hPc : ContDiffAt ℝ ∞ (fun u => cofBridgeZero σ u * gZero σ u ^ 2) z :=
    (contDiffAt_cofBridgeZero h hz).mul ((contDiffAt_gZero z).pow 2)
  have h' := hasDerivAt_negHalfArg_curve (a := -(3 / 2)) (b := 0) (by norm_num)
    (A := modTwo σ) (B := modThree σ)
    (W := fun u => -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo u).im)
    (P := fun u => cofBridgeZero σ u * gZero σ u ^ 2)
    (hcirc_zero hv2 hz1) (hasDerivAt_hcirc hv2 hz1).differentiableAt hA0
    (modTwo_hcirc h hz1) hB' hW hPc (isOpen_domZeroThree h) hz
    (fun u hu => mul_pos (cofBridgeZero_pos h hu)
      (pow_pos (gZero_pos h (norm_lt_one_of_domZeroThree hu)) 2))
    (fun u hu => by
      have e := heron_bridgeZero h hu
      rw [wallSide_zero_eq_g h u] at e
      linear_combination e)
    (by
      rw [show twoCircle (-(3 / 2)) 0 (modTwo σ z) (modThree σ z)
          (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im) (cofBridgeZero σ z * gZero σ z ^ 2) =
          bridgeZero σ z by
        rw [bridgeZero, twoCircle_swap, wallSide_zero_eq_g h,
          twoCircle_rescale _ _ _ _ _ _ _ (gZero_pos h hz1)], sub_neg_eq_add]
      exact hpos)
  have e : (fun t => angleZeroAtTwo σ (hcirc σ.vertexTwo z t)) = fun t =>
      negHalfArg (modTwo σ (hcirc σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) 0 (modTwo σ (hcirc σ.vertexTwo z t))
          (modThree σ (hcirc σ.vertexTwo z t))
          (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo (hcirc σ.vertexTwo z t)).im)
          (cofBridgeZero σ (hcirc σ.vertexTwo z t) *
            gZero σ (hcirc σ.vertexTwo z t) ^ 2)).re - -(3 / 2))
        (twoCircle (-(3 / 2)) 0 (modTwo σ (hcirc σ.vertexTwo z t))
          (modThree σ (hcirc σ.vertexTwo z t))
          (-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo (hcirc σ.vertexTwo z t)).im)
          (cofBridgeZero σ (hcirc σ.vertexTwo z t) *
            gZero σ (hcirc σ.vertexTwo z t) ^ 2)).im := by
    funext t
    exact angleZeroAtTwo_eq h (norm_hcirc_lt_one hv2 hz1 t)
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re :=
      re_pos_of_norm_add_re_pos hψ (by linarith)
    have := Real.sqrt_pos.2 hP0
    have : 0 < (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re * Real.sqrt
        (cofBridgeZero σ z * gZero σ z ^ 2) / (2 * |0 - -(3 / 2)| * modTwo σ z) := by
      positivity
    have e2 : -(-(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re * Real.sqrt
        (cofBridgeZero σ z * gZero σ z ^ 2) / (2 * |0 - -(3 / 2)| * modTwo σ z)) =
        (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re * Real.sqrt
        (cofBridgeZero σ z * gZero σ z ^ 2) / (2 * |0 - -(3 / 2)| * modTwo σ z) := by ring
    rw [e2]
    exact this
  · apply div_sqrt_pos_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (0 - -(3 / 2) : ℝ) = 3 / 2 by norm_num]
    positivity

theorem exists_hasDerivAt_angleTwoAtOne {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hpos : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2))
    (hψ : 0 < ‖exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z‖ +
      (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => angleTwoAtOne σ (hcirc σ.vertexOne z t)) d 0 := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hv := hd_ne_zero_of_domOneTwo h hz
  have hv1 := norm_vertexOne_lt_one h
  have hA0 : 0 < modOne σ z := by linarith [(modOne_mem h hz1).1]
  have hB0 : 0 < modTwo σ z := by linarith [(modTwo_mem h hz1).1]
  have hP0 : 0 < cofBridgeTwo σ z * gTwo σ z ^ 2 :=
    mul_pos (cofBridgeTwo_pos h hz) (pow_pos (gTwo_pos h hz1) 2)
  obtain ⟨c, hc0, hc⟩ := exists_hasDerivAt_canon_hcirc h 1 (u := -exp (-((σ.θ₃ : ℂ) * I)))
    (norm_neg_exp_neg σ.θ₃) hv1 hz1 hv.1 (sideOneTwo_pos h) (α := σ.θ₁) (by
      rw [← rotOne_eq_mul_mob h]
      exact rotOne_vertexTwo h)
  have hB' : HasDerivAt (fun t => modTwo σ (hcirc σ.vertexOne z t))
      ((-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im) * (-(compactProfileSlope * c))) 0 := by
    have := (hc.const_mul compactProfileSlope).const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [← rotOne_eq_mul_mob h]
    ring
  have hW : HasDerivAt (fun t => -(exp (-((σ.θ₁ : ℂ) * I)) *
      σ.rotOne (hcirc σ.vertexOne z t)).im) (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re) 0 := by
    have e : (fun t => -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne (hcirc σ.vertexOne z t)).im) =
        fun t : ℝ => -(exp (-((σ.θ₁ : ℂ) * I)) * (σ.rotOne z * exp ((t : ℂ) * I))).im := by
      funext t
      rw [rotOne_hcirc h hz1]
    rw [e]
    exact (hasDerivAt_im_rot_circle _ _).neg
  have hPc : ContDiffAt ℝ ∞ (fun u => cofBridgeTwo σ u * gTwo σ u ^ 2) z :=
    (contDiffAt_cofBridgeTwo h hz).mul ((contDiffAt_gTwo h hz1).pow 2)
  have h' := hasDerivAt_negHalfArg_curve (a := 3 / 2) (b := -(3 / 2)) (by norm_num)
    (A := modOne σ) (B := modTwo σ)
    (W := fun u => -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne u).im)
    (P := fun u => cofBridgeTwo σ u * gTwo σ u ^ 2)
    (hcirc_zero hv1 hz1) (hasDerivAt_hcirc hv1 hz1).differentiableAt hA0
    (modOne_hcirc h hz1) hB' hW hPc (isOpen_domOneTwo h) hz
    (fun u hu => mul_pos (cofBridgeTwo_pos h hu)
      (pow_pos (gTwo_pos h (norm_lt_one_of_domOneTwo hu)) 2))
    (fun u hu => by
      have e := heron_bridgeTwo h hu
      rw [sideTwo_eq_g h (norm_lt_one_of_domOneTwo hu)] at e
      linear_combination e)
    (by
      rw [show twoCircle (3 / 2) (-(3 / 2)) (modOne σ z) (modTwo σ z)
          (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im) (cofBridgeTwo σ z * gTwo σ z ^ 2) =
          bridgeTwo σ z by
        rw [bridgeTwo, sideTwo_eq_g h hz1, twoCircle_rescale _ _ _ _ _ _ _ (gTwo_pos h hz1)]]
      exact hpos)
  have e : (fun t => angleTwoAtOne σ (hcirc σ.vertexOne z t)) = fun t =>
      negHalfArg (modOne σ (hcirc σ.vertexOne z t))
        ((twoCircle (3 / 2) (-(3 / 2)) (modOne σ (hcirc σ.vertexOne z t))
          (modTwo σ (hcirc σ.vertexOne z t))
          (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne (hcirc σ.vertexOne z t)).im)
          (cofBridgeTwo σ (hcirc σ.vertexOne z t) *
            gTwo σ (hcirc σ.vertexOne z t) ^ 2)).re - 3 / 2)
        (twoCircle (3 / 2) (-(3 / 2)) (modOne σ (hcirc σ.vertexOne z t))
          (modTwo σ (hcirc σ.vertexOne z t))
          (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne (hcirc σ.vertexOne z t)).im)
          (cofBridgeTwo σ (hcirc σ.vertexOne z t) *
            gTwo σ (hcirc σ.vertexOne z t) ^ 2)).im := by
    funext t
    exact angleTwoAtOne_eq h (norm_hcirc_lt_one hv1 hz1 t)
  rw [e]
  refine ⟨_, ?_, h'⟩
  split_ifs with hw
  · have hr : 0 < (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re :=
      re_pos_of_norm_add_re_pos hψ (by linarith)
    have := Real.sqrt_pos.2 hP0
    have : 0 < (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re * Real.sqrt
        (cofBridgeTwo σ z * gTwo σ z ^ 2) / (2 * |-(3 / 2) - 3 / 2| * modOne σ z) := by
      positivity
    have e2 : -(-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re * Real.sqrt
        (cofBridgeTwo σ z * gTwo σ z ^ 2) / (2 * |-(3 / 2) - 3 / 2| * modOne σ z)) =
        (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re * Real.sqrt
        (cofBridgeTwo σ z * gTwo σ z ^ 2) / (2 * |-(3 / 2) - 3 / 2| * modOne σ z) := by ring
    rw [e2]
    exact this
  · apply div_sqrt_pos_aux (by norm_num) hB0 hP0
    have : 0 < compactProfileSlope * c := by unfold compactProfileSlope; positivity
    rw [show (-(3 / 2) - 3 / 2 : ℝ) = -3 by norm_num, div_neg, neg_div, neg_neg]
    positivity

end Hyp

end HypFold

end GC.Seifert
