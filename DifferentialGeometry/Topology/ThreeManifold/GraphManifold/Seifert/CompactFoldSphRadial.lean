import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphPolar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCorners

/-!
# Radial profiles and the polar Jacobian in the spherical chart

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The corners of the spherical fold are polar maps
`c + S(ϖ) e^{iΘ}` about the image of a vertex `a`, with `ϖ = ‖sphMoeb a ·‖` the chordal distance to
`a`. The radial profiles blend the apex modulus with the bridge modulus:
`sphInnerRadial p a b τ ϖ = (1 - step) ϖ^p/2 + step (3/2 + κ sphCanonF τ ϖ)`, strictly increasing
for `0 < ϖ` when `b ≤ 1` (`exists_hasDerivAt_sphInnerRadial`), and
`sphOuterRadial p a b τ ϖ = (1 - step)(7/2 - ϖ^p/2) + step (3 - κ sphCanonF τ ϖ)`, strictly
decreasing when `b ≤ 1/5` (`exists_hasDerivAt_sphOuterRadial`).

For A4's polar Jacobian formula the curve is the circle `sphCirc a z` with velocity `N · I`, and the
transversal direction is `N = (1 + ā a)/(1 - ā ω)² ω`, `ω = sphMoeb a z`, along which the chordal
distance has derivative `‖ω‖ > 0` (`hasDerivAt_norm_sphMoeb_ray`): the Jacobian of a polar map whose
profile and angle are strictly monotone along the circle and the ray is positive
(`det_fderiv_polar_sph_pos`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def sphInnerRadial (p : ℕ) (a b τ x : ℝ) : ℝ :=
  (1 - coneStep a b x) * x ^ p / 2 + coneStep a b x * (3 / 2 + compactProfileSlope * sphCanonF τ x)

def sphOuterRadial (p : ℕ) (a b τ x : ℝ) : ℝ :=
  (1 - coneStep a b x) * (7 / 2 - x ^ p / 2) +
    coneStep a b x * (3 - compactProfileSlope * sphCanonF τ x)

theorem sphCanonF_ge {τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hx : 0 ≤ x) : -1 < sphCanonF τ x := by
  have hd : 0 < 1 + x * τ := by nlinarith
  rw [sphCanonF, lt_div_iff₀ hd]
  nlinarith

theorem sphCanonF_lt {τ x : ℝ} (hτ0 : 0 ≤ τ) (hx : 0 ≤ x) (hx2 : x < 2) :
    sphCanonF τ x < 2 := by
  have hd : 0 < 1 + x * τ := by nlinarith
  rw [sphCanonF, div_lt_iff₀ hd]
  nlinarith

theorem hasDerivAt_sphCanonF_id {τ x : ℝ} (h : 1 + x * τ ≠ 0) :
    HasDerivAt (sphCanonF τ) ((1 + τ ^ 2) / (1 + x * τ) ^ 2) x := by
  have := hasDerivAt_sphCanonF (τ := τ) (f := id) (hasDerivAt_id x) h
  simpa using this

theorem contDiffAt_sphCanonF {τ x : ℝ} (h : 1 + x * τ ≠ 0) :
    ContDiffAt ℝ ∞ (sphCanonF τ) x := by
  unfold sphCanonF
  exact (contDiffAt_id.sub contDiffAt_const).div
    (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)) h

theorem sphInnerRadial_pos {p : ℕ} {a b τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hx : 0 < x) :
    0 < sphInnerRadial p a b τ x := by
  have hs0 := coneStep_nonneg a b x
  have hs1 := coneStep_le_one a b x
  have hF := sphCanonF_ge hτ0 hτ1 hx.le
  have hR : 0 < 3 / 2 + compactProfileSlope * sphCanonF τ x := by
    unfold compactProfileSlope
    linarith
  have hp : 0 < x ^ p / 2 := by positivity
  have := convex_comb_pos hs0 hs1 hp hR
  unfold sphInnerRadial
  linarith [show (1 - coneStep a b x) * x ^ p / 2 = (1 - coneStep a b x) * (x ^ p / 2) by ring]

theorem exists_hasDerivAt_sphInnerRadial {p : ℕ} (hp : 1 ≤ p) {a b τ x : ℝ} (hab : a < b)
    (hb : b ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hx : 0 < x) :
    ∃ S' : ℝ, 0 < S' ∧ HasDerivAt (sphInnerRadial p a b τ) S' x := by
  have hd : 0 < 1 + x * τ := by nlinarith
  have hs := hasDerivAt_coneStep a b x
  have hF := hasDerivAt_sphCanonF_id (τ := τ) hd.ne'
  have h := (((hasDerivAt_const x (1 : ℝ)).sub hs).mul ((hasDerivAt_pow p x).div_const 2)).add
    (hs.mul ((hasDerivAt_const x (3 / 2 : ℝ)).add (hF.const_mul compactProfileSlope)))
  have h' : HasDerivAt (sphInnerRadial p a b τ)
      (deriv (coneStep a b) x * (3 / 2 + compactProfileSlope * sphCanonF τ x - x ^ p / 2) +
        ((1 - coneStep a b x) * ((p : ℝ) * x ^ (p - 1) / 2) +
          coneStep a b x * (compactProfileSlope * ((1 + τ ^ 2) / (1 + x * τ) ^ 2)))) x := by
    convert h using 1
    · funext s
      simp only [sphInnerRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    · simp only [Pi.sub_apply, Pi.add_apply]
      ring
  refine ⟨_, ?_, h'⟩
  have hs0 := coneStep_nonneg a b x
  have hs1 := coneStep_le_one a b x
  have hs' := deriv_coneStep_nonneg hab x
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hFg := sphCanonF_ge hτ0 hτ1 hx.le
  have h1 : 0 ≤ deriv (coneStep a b) x *
      (3 / 2 + compactProfileSlope * sphCanonF τ x - x ^ p / 2) := by
    rcases le_or_gt x b with hxb | hxb
    · have : x ^ p ≤ 1 := pow_le_one₀ hx.le (le_trans hxb hb)
      apply mul_nonneg hs'
      unfold compactProfileSlope
      nlinarith
    · rw [deriv_coneStep_eq_zero_of_lt hab hxb, zero_mul]
  have h2 : 0 < (p : ℝ) * x ^ (p - 1) / 2 := by positivity
  have h3 : 0 < compactProfileSlope * ((1 + τ ^ 2) / (1 + x * τ) ^ 2) := by
    unfold compactProfileSlope
    positivity
  have := convex_comb_pos hs0 hs1 h2 h3
  linarith

theorem sphOuterRadial_pos {p : ℕ} {a b τ x : ℝ} (hab : a < b) (hb : b ≤ 1 / 5) (hτ0 : 0 ≤ τ)
    (hx0 : 0 ≤ x) (hx : x < 2) : 0 < sphOuterRadial p a b τ x := by
  have hF := sphCanonF_lt hτ0 hx0 hx
  have hR : 0 < 3 - compactProfileSlope * sphCanonF τ x := by
    unfold compactProfileSlope
    linarith
  rcases lt_or_ge x b with hxb | hxb
  · have hs0 := coneStep_nonneg a b x
    have hs1 := coneStep_le_one a b x
    have hx1 : x ^ p ≤ 1 := pow_le_one₀ hx0 (by linarith)
    have := convex_comb_pos hs0 hs1 (by linarith : (0 : ℝ) < 7 / 2 - x ^ p / 2) hR
    unfold sphOuterRadial
    linarith
  · unfold sphOuterRadial
    rw [coneStep_eq_one hab hxb]
    linarith

theorem exists_hasDerivAt_sphOuterRadial {p : ℕ} (hp : 1 ≤ p) {a b τ x : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hx : 0 < x) :
    ∃ S' : ℝ, S' < 0 ∧ HasDerivAt (sphOuterRadial p a b τ) S' x := by
  have hd : 0 < 1 + x * τ := by nlinarith
  have hs := hasDerivAt_coneStep a b x
  have hF := hasDerivAt_sphCanonF_id (τ := τ) hd.ne'
  have h := (((hasDerivAt_const x (1 : ℝ)).sub hs).mul ((hasDerivAt_const x (7 / 2 : ℝ)).sub
    ((hasDerivAt_pow p x).div_const 2))).add (hs.mul ((hasDerivAt_const x (3 : ℝ)).sub
      (hF.const_mul compactProfileSlope)))
  have h' : HasDerivAt (sphOuterRadial p a b τ)
      (deriv (coneStep a b) x * ((3 - compactProfileSlope * sphCanonF τ x) - (7 / 2 - x ^ p / 2)) +
        ((1 - coneStep a b x) * -((p : ℝ) * x ^ (p - 1) / 2) +
          coneStep a b x * -(compactProfileSlope * ((1 + τ ^ 2) / (1 + x * τ) ^ 2)))) x := by
    convert h using 1
    · funext s
      simp only [sphOuterRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    · simp only [Pi.sub_apply]
      ring
  refine ⟨_, ?_, h'⟩
  have hs0 := coneStep_nonneg a b x
  have hs1 := coneStep_le_one a b x
  have hs' := deriv_coneStep_nonneg hab x
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hFg := sphCanonF_ge hτ0 hτ1 hx.le
  have h1 : deriv (coneStep a b) x * ((3 - compactProfileSlope * sphCanonF τ x) -
      (7 / 2 - x ^ p / 2)) ≤ 0 := by
    rcases le_or_gt x b with hxb | hxb
    · have hx1 : x ^ p ≤ x := pow_le_of_le_one hx.le (by linarith) (by omega)
      apply mul_nonpos_of_nonneg_of_nonpos hs'
      unfold compactProfileSlope
      nlinarith
    · rw [deriv_coneStep_eq_zero_of_lt hab hxb, zero_mul]
  have h2 : 0 < (p : ℝ) * x ^ (p - 1) / 2 := by positivity
  have h3 : 0 < compactProfileSlope * ((1 + τ ^ 2) / (1 + x * τ) ^ 2) := by
    unfold compactProfileSlope
    positivity
  have := convex_comb_pos hs0 hs1 h2 h3
  linarith

def sphRayDir (a z : ℂ) : ℂ :=
  (1 + conj a * a) / (1 - conj a * sphMoeb a z) ^ 2 * sphMoeb a z

theorem hasDerivAt_sphMoeb_line {a z N : ℂ} (h : 1 + conj a * z ≠ 0) :
    HasDerivAt (fun t : ℝ => sphMoeb a (z + t * N)) ((1 + conj a * a) / (1 + conj a * z) ^ 2 * N)
      0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * N) N 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const N).const_add z
  have h1 : HasDerivAt (fun u : ℂ => u - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun u : ℂ => 1 + conj a * u) (conj a) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_add 1
  have hm : HasDerivAt (sphMoeb a) ((1 + conj a * a) / (1 + conj a * z) ^ 2) z := by
    refine (h1.div h2 h).congr_deriv ?_
    field_simp
    ring
  have hm' : HasDerivAt (sphMoeb a) ((1 + conj a * a) / (1 + conj a * z) ^ 2)
      (z + ((0 : ℝ) : ℂ) * N) := by
    simpa using hm
  exact hm'.comp (0 : ℝ) hl

theorem sphRayDir_mul {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    (1 + conj a * a) / (1 + conj a * z) ^ 2 * sphRayDir a z = sphMoeb a z := by
  have ha := one_add_conj_mul_self_ne_sph a
  rw [sphRayDir, one_sub_conj_mul_sphMoeb h]
  field_simp

theorem hasDerivAt_norm_sphMoeb_ray {a z : ℂ} (h : 1 + conj a * z ≠ 0)
    (h0 : sphMoeb a z ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖sphMoeb a (z + t * sphRayDir a z)‖) ‖sphMoeb a z‖ 0 := by
  have hd := hasDerivAt_sphMoeb_line (N := sphRayDir a z) h
  rw [sphRayDir_mul h] at hd
  have hn := hasDerivAt_normSq_curve_sph hd
  simp only [ofReal_zero, zero_mul, add_zero] at hn
  have hpos : Complex.normSq (sphMoeb a (z + ((0 : ℝ) : ℂ) * sphRayDir a z)) ≠ 0 := by
    simpa using (Complex.normSq_pos.2 h0).ne'
  have hs := hn.sqrt hpos
  have e : (fun t : ℝ => ‖sphMoeb a (z + t * sphRayDir a z)‖) =
      fun t : ℝ => Real.sqrt (Complex.normSq (sphMoeb a (z + (t : ℂ) * sphRayDir a z))) := by
    funext t
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  refine hs.congr_deriv ?_
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hq := CompactShape.sq_norm_eq_sph (sphMoeb a z)
  have := norm_pos_iff.2 h0
  field_simp
  linarith

theorem sphCirc_deriv_eq {a z : ℂ} :
    (1 + conj a * a) / (1 - conj a * sphMoeb a z) ^ 2 * (sphMoeb a z * I) = sphRayDir a z * I := by
  rw [sphRayDir]
  ring

end GC.Seifert
