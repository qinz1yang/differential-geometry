import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidAngles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGerms

/-!
# The three corners of the flat compact fold

Lane CF, tier 2, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). All three corners are polar maps about the
image of their vertex, `c + S(d) e^{iΘ}`, with a radial profile `S` depending on the distance `d`
to the vertex only and an angle `Θ` blending the apex angle with the bridge angles:
* at `v₁` (about `+3/2`): `S = (1 - τ) d^{p₁}/2 + τ modOne`, `Θ = (1 - τ) p₁ ψ₁ +
  τ (s angleOneAtOne + (1 - s) angleTwoAtOne)`, where `τ = coneStep a b d`, `ψ₁` is the argument of
  `rotOne` and `s = lensSwitch β β'` is `0` within `β` of wall 2 and `1` beyond `β'`;
* at `v₂` (about `-3/2`): the same with `p₂`, `ψ₂`, `angleTwoAtTwo` (weight `1 - s`) and
  `angleZeroAtTwo` (weight `s`);
* at `v₃ = 0` (about `0`): `S = (1 - τ)(7/2 - d^{p₃}/2) + τ modThree`, decreasing in `d`, and
  `Θ = (1 - τ)(π - p₃ ψ₃) + τ ((1 - ν) angleZeroAtThree + ν angleOneAtThree)` with the outer weight
  `ν = coneStep (-w) w (w (2 ψ₃/θ₃ - 1) + (w/δ)(canon₂ - canon₁))`.
Near the vertex each corner is its apex model (`cornerOne_eq_apexOne`, `cornerTwo_eq_apexTwo`,
`cornerThree_eq_outerGerm`); where `τ = 1` and the angular weight is `0` or `1` it is the
corresponding bridge (`cornerOne_eq_bridgeOne`, …). The Jacobian is positive off the vertex
(`det_fderiv_cornerOne_pos`, …) by A4's polar formula along the circle and the ray through the
point: the profile is monotone, and the angle is strictly monotone along the circles because the
bridge angles are (`CompactFoldEuclidAngles`), the weights move in the right direction and the
bridge angles are ordered. The wall identities `corner ∘ refl = conj ∘ corner` hold where the
angular weights are constant on both points (`cornerOne_refl_one`, …).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def innerRadial (p : ℕ) (a b r₀ d : ℝ) : ℝ :=
  (1 - coneStep a b d) * d ^ p / 2 + coneStep a b d * (3 / 2 + EuclidShape.profileSlope * (d - r₀))

theorem innerRadial_pos {p : ℕ} {a b r₀ d : ℝ} (hr₀ : r₀ < 1) (hd : 0 < d) :
    0 < innerRadial p a b r₀ d := by
  have hτ0 := coneStep_nonneg a b d
  have hτ1 := coneStep_le_one a b d
  have hR : 0 < 3 / 2 + EuclidShape.profileSlope * (d - r₀) := by
    unfold EuclidShape.profileSlope
    nlinarith
  have hp : 0 < d ^ p / 2 := by positivity
  have := convex_comb_pos hτ0 hτ1 hp hR
  unfold innerRadial
  linarith [show (1 - coneStep a b d) * d ^ p / 2 = (1 - coneStep a b d) * (d ^ p / 2) by ring]

theorem exists_hasDerivAt_innerRadial {p : ℕ} (hp : 1 ≤ p) {a b r₀ d : ℝ} (hab : a < b)
    (hb : b ≤ 1) (hr₀ : r₀ < 1) (hd : 0 < d) :
    ∃ S' : ℝ, 0 < S' ∧ HasDerivAt (innerRadial p a b r₀) S' d := by
  have hτ := hasDerivAt_coneStep a b d
  have h := (((hasDerivAt_const d (1 : ℝ)).sub hτ).mul ((hasDerivAt_pow p d).div_const 2)).add
    (hτ.mul ((hasDerivAt_const d (3 / 2 : ℝ)).add
      (((hasDerivAt_id' d).sub_const r₀).const_mul EuclidShape.profileSlope)))
  have h' : HasDerivAt (innerRadial p a b r₀)
      (deriv (coneStep a b) d * (3 / 2 + EuclidShape.profileSlope * (d - r₀) - d ^ p / 2) +
        ((1 - coneStep a b d) * ((p : ℝ) * d ^ (p - 1) / 2) +
          coneStep a b d * EuclidShape.profileSlope)) d := by
    convert h using 1
    · funext s
      simp only [innerRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    · simp only [Pi.sub_apply, Pi.add_apply, mul_one]
      ring
  refine ⟨_, ?_, h'⟩
  have hτ0 := coneStep_nonneg a b d
  have hτ1 := coneStep_le_one a b d
  have hτ' := deriv_coneStep_nonneg hab d
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : 0 ≤ deriv (coneStep a b) d *
      (3 / 2 + EuclidShape.profileSlope * (d - r₀) - d ^ p / 2) := by
    rcases le_or_gt d b with hdb | hdb
    · have : d ^ p ≤ 1 := pow_le_one₀ hd.le (le_trans hdb hb)
      apply mul_nonneg hτ'
      unfold EuclidShape.profileSlope
      nlinarith
    · rw [deriv_coneStep_eq_zero_of_lt hab hdb, zero_mul]
  have h2 : 0 < (p : ℝ) * d ^ (p - 1) / 2 := by positivity
  have h3 : (0 : ℝ) < EuclidShape.profileSlope := by unfold EuclidShape.profileSlope; norm_num
  have := convex_comb_pos hτ0 hτ1 h2 h3
  linarith

def outerRadial (p : ℕ) (a b r₀ d : ℝ) : ℝ :=
  (1 - coneStep a b d) * (7 / 2 - d ^ p / 2) +
    coneStep a b d * (3 - EuclidShape.profileSlope * (d - r₀))

theorem outerRadial_pos {p : ℕ} {a b r₀ d : ℝ} (hab : a < b) (hb : b ≤ 1 / 5)
    (hr₀ : 0 ≤ r₀) (hd0 : 0 ≤ d) (hd : d < 2) : 0 < outerRadial p a b r₀ d := by
  have hR : 0 < 3 - EuclidShape.profileSlope * (d - r₀) := by
    unfold EuclidShape.profileSlope
    nlinarith
  rcases lt_or_ge d b with hdb | hdb
  · have hτ0 := coneStep_nonneg a b d
    have hτ1 := coneStep_le_one a b d
    have hd1 : d ^ p ≤ 1 := pow_le_one₀ hd0 (by linarith)
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < 7 / 2 - d ^ p / 2) hR
    unfold outerRadial
    linarith
  · unfold outerRadial
    rw [coneStep_eq_one hab hdb]
    linarith

theorem exists_hasDerivAt_outerRadial {p : ℕ} (hp : 1 ≤ p) {a b r₀ d : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hr₀ : r₀ < 1) (hd : 0 < d) :
    ∃ S' : ℝ, S' < 0 ∧ HasDerivAt (outerRadial p a b r₀) S' d := by
  have hτ := hasDerivAt_coneStep a b d
  have h := (((hasDerivAt_const d (1 : ℝ)).sub hτ).mul ((hasDerivAt_const d (7 / 2 : ℝ)).sub
    ((hasDerivAt_pow p d).div_const 2))).add (hτ.mul ((hasDerivAt_const d (3 : ℝ)).sub
      (((hasDerivAt_id' d).sub_const r₀).const_mul EuclidShape.profileSlope)))
  have h' : HasDerivAt (outerRadial p a b r₀)
      (deriv (coneStep a b) d * ((3 - EuclidShape.profileSlope * (d - r₀)) - (7 / 2 - d ^ p / 2)) +
        ((1 - coneStep a b d) * -((p : ℝ) * d ^ (p - 1) / 2) +
          coneStep a b d * -EuclidShape.profileSlope)) d := by
    convert h using 1
    · funext s
      simp only [outerRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    · simp only [Pi.sub_apply, mul_one]
      ring
  refine ⟨_, ?_, h'⟩
  have hτ0 := coneStep_nonneg a b d
  have hτ1 := coneStep_le_one a b d
  have hτ' := deriv_coneStep_nonneg hab d
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : deriv (coneStep a b) d * ((3 - EuclidShape.profileSlope * (d - r₀)) -
      (7 / 2 - d ^ p / 2)) ≤ 0 := by
    rcases le_or_gt d b with hdb | hdb
    · have hd1 : d ^ p ≤ d := pow_le_of_le_one hd.le (by linarith) (by omega)
      apply mul_nonpos_of_nonneg_of_nonpos hτ'
      unfold EuclidShape.profileSlope
      nlinarith
    · rw [deriv_coneStep_eq_zero_of_lt hab hdb, zero_mul]
  have h2 : 0 < (p : ℝ) * d ^ (p - 1) / 2 := by positivity
  have h3 : (0 : ℝ) < EuclidShape.profileSlope := by unfold EuclidShape.profileSlope; norm_num
  have := convex_comb_pos hτ0 hτ1 h2 h3
  linarith

namespace EuclidShape

variable (σ : EuclidShape)

def lensSwitch (β β' : ℝ) (z : ℂ) : ℝ := coneStep β β' (σ.wallSide 2 z)

def angleCornerOne (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖z - σ.vertexOne‖) * (σ.p₁ * σ.psiOne z) +
    coneStep a b ‖z - σ.vertexOne‖ * (σ.lensSwitch β β' z * σ.angleOneAtOne z +
      (1 - σ.lensSwitch β β' z) * σ.angleTwoAtOne z)

def cornerOne (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) + (innerRadial σ.p₁ a b σ.radOne ‖z - σ.vertexOne‖ : ℂ) *
    exp ((σ.angleCornerOne a b β β' z : ℂ) * I)

theorem modOne_eq (z : ℂ) : σ.modOne z = 3 / 2 + profileSlope * (‖z - σ.vertexOne‖ - σ.radOne) :=
  rfl

theorem norm_rotOne (z : ℂ) : ‖σ.rotOne z‖ = ‖z - σ.vertexOne‖ := by
  rw [rotOne, norm_neg, norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by
    push_cast; ring, norm_exp_mul_I, one_mul]

theorem norm_rotTwo (z : ℂ) : ‖σ.rotTwo z‖ = ‖z - σ.vertexTwo‖ := by
  rw [rotTwo, norm_neg, norm_mul, norm_exp_mul_I, one_mul]

theorem contDiffAt_lensSwitch (β β' : ℝ) (z : ℂ) : ContDiffAt ℝ ∞ (σ.lensSwitch β β') z :=
  (contDiff_coneStep β β').contDiffAt.comp z (σ.contDiff_wallSide 2).contDiffAt

theorem contDiffAt_dist_vertexOne {z : ℂ} (h : z ≠ σ.vertexOne) :
    ContDiffAt ℝ ∞ (fun u => ‖u - σ.vertexOne‖) z :=
  (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h)

theorem contDiffAt_angleCornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz2 : z ∈ σ.domTwo) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.angleCornerOne a b β β') z := by
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b ‖u - σ.vertexOne‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (σ.contDiffAt_dist_vertexOne (σ.ne_vertexOne_of_mem_domOne hz1))
  have hs := σ.contDiffAt_lensSwitch β β' z
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul (σ.contDiffAt_psiOne hψ))).add
    (hτ.mul ((hs.mul (σ.contDiffAt_angleOneAtOne hz1 hpos1)).add
      ((contDiffAt_const.sub hs).mul (σ.contDiffAt_angleTwoAtOne hz2 hpos2))))

theorem contDiffAt_cornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz2 : z ∈ σ.domTwo) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.cornerOne a b β β') z := by
  have hd := σ.contDiffAt_dist_vertexOne (σ.ne_vertexOne_of_mem_domOne hz1)
  have hS : ContDiffAt ℝ ∞ (fun u => innerRadial σ.p₁ a b σ.radOne ‖u - σ.vertexOne‖) z := by
    have hc : ContDiff ℝ ∞ (innerRadial σ.p₁ a b σ.radOne) := by
      unfold innerRadial
      exact (((contDiff_const.sub (contDiff_coneStep a b)).mul (contDiff_id.pow _)).div_const
        _).add ((contDiff_coneStep a b).mul (contDiff_const.add (contDiff_const.mul
          (contDiff_id.sub contDiff_const))))
    exact hc.contDiffAt.comp z hd
  have hΘ := σ.contDiffAt_angleCornerOne a b β β' hz1 hz2 hψ hpos1 hpos2
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))


theorem one_le_p₁ : 1 ≤ σ.p₁ := le_trans (by norm_num) σ.two_le_p₁

theorem one_le_p₂ : 1 ≤ σ.p₂ := le_trans (by norm_num) σ.two_le_p₂

theorem one_le_p₃ : 1 ≤ σ.p₃ := le_trans (by norm_num) σ.two_le_p₃

theorem hasDerivAt_norm_ray (z c : ℂ) :
    HasDerivAt (fun t : ℝ => ‖z + t * (z - c) - c‖) ‖z - c‖ 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 + t) * ‖z - c‖) ‖z - c‖ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖z - c‖
  refine hl.congr_of_eventuallyEq ?_
  have hI : Set.Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hI] with t ht
  have ht' : 0 < 1 + t := by linarith [show -1 < t from ht]
  rw [show z + (t : ℂ) * (z - c) - c = ((1 + t : ℝ) : ℂ) * (z - c) by push_cast; ring, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']

theorem hasDerivAt_comp_ray {Θ : ℂ → ℝ} {z N : ℂ} (hΘ : DifferentiableAt ℝ Θ z) :
    HasDerivAt (fun t : ℝ => Θ (z + t * N)) (fderiv ℝ Θ z N) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * N) N 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const N).const_add z
  have hF' : HasFDerivAt Θ (fderiv ℝ Θ z) (z + ((0 : ℝ) : ℂ) * N) := by
    rw [ofReal_zero, zero_mul, add_zero]
    exact hΘ.hasFDerivAt
  exact hF'.comp_hasDerivAt 0 hl

theorem cross_mul_I (N : ℂ) : N.re * (N * I).im - (N * I).re * N.im = ‖N‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, normSq_apply]
  simp only [mul_im, mul_re, I_re, I_im]
  ring

theorem det_pos_of_polar {D S S' A b n : ℝ} (hn : 0 < n)
    (h : D * n = S * S' * A * b) (hpos : 0 < S * S' * A * b) : 0 < D :=
  (mul_pos_iff_of_pos_right hn).1 (h ▸ hpos)

theorem hasDerivAt_lensSwitch_circOne (β β' : ℝ) (z : ℂ) :
    HasDerivAt (fun t => σ.lensSwitch β β' (circ σ.vertexOne z t))
      (deriv (coneStep β β') (σ.wallSide 2 z) * ((σ.rotTwo z).re - Real.sin σ.θ₃)) 0 := by
  have hW := σ.hasDerivAt_wallSide_two_curve (hasDerivAt_circ σ.vertexOne z)
  rw [σ.wall_deriv_one_two z] at hW
  have h := (hasDerivAt_coneStep β β' (σ.wallSide 2 (circ σ.vertexOne z 0))).comp (0 : ℝ) hW
  rw [circ_zero] at h
  exact h

theorem lensSwitch_deriv_nonpos {β β' : ℝ} (hβ : β < β') {x y : ℝ}
    (h : y ≤ 0 ∨ β' < x ∨ x < β) : deriv (coneStep β β') x * y ≤ 0 := by
  rcases h with h | h | h
  · exact mul_nonpos_of_nonneg_of_nonpos (deriv_coneStep_nonneg hβ x) h
  · rw [deriv_coneStep_eq_zero_of_lt hβ h, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hβ h, zero_mul]

theorem lensSwitch_deriv_nonneg {β β' : ℝ} (hβ : β < β') {x y : ℝ}
    (h : 0 ≤ y ∨ β' < x ∨ x < β) : 0 ≤ deriv (coneStep β β') x * y := by
  rcases h with h | h | h
  · exact mul_nonneg (deriv_coneStep_nonneg hβ x) h
  · rw [deriv_coneStep_eq_zero_of_lt hβ h, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hβ h, zero_mul]

theorem exists_hasDerivAt_angleCornerOne_circ {a b β β' : ℝ} (hβ : β < β')
    {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2))
    (hord : σ.angleOneAtOne z ≤ σ.angleTwoAtOne z)
    (hlam : (σ.rotTwo z).re - Real.sin σ.θ₃ ≤ 0 ∨ β' < σ.wallSide 2 z ∨ σ.wallSide 2 z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => σ.angleCornerOne a b β β' (circ σ.vertexOne z t)) D 0 := by
  have hz0 := σ.ne_vertexOne_of_mem_domOne hz1
  have hd : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 hz0)
  obtain ⟨d₁, hd₁, h₁⟩ := σ.exists_hasDerivAt_angleOneAtOne hz1 hpos1 hψ
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_angleTwoAtOne hz2 hpos2
  have hψd := σ.hasDerivAt_psiOne_circ hψ
  have hsw := σ.hasDerivAt_lensSwitch_circOne β β' z
  have hsw' := lensSwitch_deriv_nonpos hβ hlam
  set τ₀ := coneStep a b ‖z - σ.vertexOne‖ with hτ₀
  set sw' := deriv (coneStep β β') (σ.wallSide 2 z) * ((σ.rotTwo z).re - Real.sin σ.θ₃)
  have hΘγ : HasDerivAt (fun t => σ.angleCornerOne a b β β' (circ σ.vertexOne z t))
      ((1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * σ.angleOneAtOne z + σ.lensSwitch β β' z * d₁) +
        ((0 - sw') * σ.angleTwoAtOne z + (1 - σ.lensSwitch β β' z) * d₂))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₁ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((hsw.mul h₁).add
        (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul h₂)))
    have e : (fun t => σ.angleCornerOne a b β β' (circ σ.vertexOne z t)) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₁ : ℝ) * σ.psiOne (circ σ.vertexOne z t)) +
        (fun _ => τ₀) * ((fun t => σ.lensSwitch β β' (circ σ.vertexOne z t)) *
          (fun t => σ.angleOneAtOne (circ σ.vertexOne z t)) +
          ((fun _ => (1 : ℝ)) - fun t => σ.lensSwitch β β' (circ σ.vertexOne z t)) *
          (fun t => σ.angleTwoAtOne (circ σ.vertexOne z t))) := by
      funext t
      simp only [angleCornerOne, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, norm_circ_sub, hτ₀]
    rw [e]
    convert h using 1
    simp only [circ_zero, Pi.sub_apply, zero_mul, zero_add]
  have hpR : (0 : ℝ) < σ.p₁ := by exact_mod_cast σ.one_le_p₁
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.lensSwitch β β' z := coneStep_nonneg _ _ _
  have hs1 : σ.lensSwitch β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * σ.angleOneAtOne z +
      σ.lensSwitch β β' z * d₁) + ((0 - sw') * σ.angleTwoAtOne z +
        (1 - σ.lensSwitch β β' z) * d₂)) := by
    have hb : 0 < σ.lensSwitch β β' z * d₁ + (1 - σ.lensSwitch β β' z) * d₂ := by
      have := convex_comb_pos hs0 hs1 hd₂ hd₁
      linarith
    have hx : 0 ≤ sw' * (σ.angleOneAtOne z - σ.angleTwoAtOne z) :=
      mul_nonneg_of_nonpos_of_nonpos hsw' (by linarith)
    have hin : 0 < (sw' * σ.angleOneAtOne z + σ.lensSwitch β β' z * d₁) +
        ((0 - sw') * σ.angleTwoAtOne z + (1 - σ.lensSwitch β β' z) * d₂) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₁ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_cornerOne_pos {a b β β' : ℝ} (hab : a < b) (hb : b ≤ 1) (hβ : β < β')
    {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2))
    (hord : σ.angleOneAtOne z ≤ σ.angleTwoAtOne z)
    (hlam : (σ.rotTwo z).re - Real.sin σ.θ₃ ≤ 0 ∨ β' < σ.wallSide 2 z ∨ σ.wallSide 2 z < β) :
    0 < (fderiv ℝ (σ.cornerOne a b β β') z).det := by
  have hz0 := σ.ne_vertexOne_of_mem_domOne hz1
  have hd : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 hz0)
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_innerRadial σ.one_le_p₁ hab hb σ.radOne_lt_one hd
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleCornerOne_circ (a := a) (b := b) hβ hz1 hz2
    hψ hpos1 hpos2 hord hlam
  have hρ : DifferentiableAt ℝ (fun u => ‖u - σ.vertexOne‖) z :=
    (σ.contDiffAt_dist_vertexOne hz0).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.angleCornerOne a b β β') z :=
    (σ.contDiffAt_angleCornerOne a b β β' hz1 hz2 hψ hpos1 hpos2).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖circ σ.vertexOne z t - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    Eventually.of_forall fun t => norm_circ_sub _ _ _
  have key := det_fderiv_polar (c := ((3 / 2 : ℝ) : ℂ))
    (S := innerRadial σ.p₁ a b σ.radOne) (ρ := fun u => ‖u - σ.vertexOne‖)
    (Θ := σ.angleCornerOne a b β β') (N := z - σ.vertexOne) hSd hρ hΘd
    (hasDerivAt_circ σ.vertexOne z) (circ_zero _ _) hργ hΘγ (hasDerivAt_norm_ray z σ.vertexOne)
    (hasDerivAt_comp_ray hΘd)
  rw [cross_mul_I] at key
  have hS0 := innerRadial_pos (p := σ.p₁) (a := a) (b := b) σ.radOne_lt_one hd
  exact det_pos_of_polar (by positivity) key (by positivity)


theorem conj_polar (c S Θ : ℝ) :
    conj ((c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)) =
      (c : ℂ) + (S : ℂ) * exp (((-Θ : ℝ) : ℂ) * I) := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 3
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem exp_two_pi_sub (Θ : ℝ) :
    exp (((2 * Real.pi - Θ : ℝ) : ℂ) * I) = exp (((-Θ : ℝ) : ℂ) * I) := by
  rw [show ((2 * Real.pi - Θ : ℝ) : ℂ) * I = ((-Θ : ℝ) : ℂ) * I + 2 * Real.pi * I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem polar_pow {w : ℂ} (h : 0 < ‖w‖ + w.re) (p : ℕ) :
    w ^ p = ((‖w‖ ^ p : ℝ) : ℂ) * exp ((((p : ℝ) * discAngle w : ℝ) : ℂ) * I) := by
  conv_lhs => rw [halfArg_polar_self (ne_zero_of_norm_add_re_pos h) h]
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem cornerOne_eq_apexOne {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a) {z : ℂ}
    (hd : ‖z - σ.vertexOne‖ ≤ a) (hψ : z = σ.vertexOne ∨ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    σ.cornerOne a b β β' z = σ.apexOne z := by
  have hτ : coneStep a b ‖z - σ.vertexOne‖ = 0 := coneStep_eq_zero hab hd
  rcases hψ with h | h
  · subst h
    have hp := σ.one_le_p₁
    simp only [cornerOne, innerRadial, apexOne, sub_self, norm_zero, rotOne_vertexOne]
    rw [coneStep_eq_zero hab ha]
    simp [zero_pow (by omega : σ.p₁ ≠ 0)]
  · rw [cornerOne, angleCornerOne, innerRadial, hτ, apexOne, polar_pow h, norm_rotOne, psiOne]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

theorem cornerOne_eq_bridgeOne {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hd : b ≤ ‖z - σ.vertexOne‖) (hs : β' ≤ σ.wallSide 2 z) :
    σ.cornerOne a b β β' z = σ.bridgeOne z := by
  rw [σ.bridgeOne_eq_polar_one hz1 hpos1, cornerOne, angleCornerOne, innerRadial,
    coneStep_eq_one hab hd, lensSwitch, coneStep_eq_one hβ hs, modOne_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, zero_div]

theorem cornerOne_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ σ.domTwo) (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2))
    (hd : b ≤ ‖z - σ.vertexOne‖) (hs : σ.wallSide 2 z ≤ β) :
    σ.cornerOne a b β β' z = σ.bridgeTwo z := by
  rw [σ.bridgeTwo_eq_polar_one hz2 hpos2, cornerOne, angleCornerOne, innerRadial,
    coneStep_eq_one hab hd, lensSwitch, coneStep_eq_zero hβ hs, modOne_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add, sub_zero, zero_div]

theorem cornerOne_refl_one (a b β β' : ℝ) {z : ℂ}
    (h : coneStep a b ‖z - σ.vertexOne‖ = 0 ∨
      (σ.lensSwitch β β' z = 1 ∧ σ.lensSwitch β β' (σ.refl 1 z) = 1)) :
    σ.cornerOne a b β β' (σ.refl 1 z) = conj (σ.cornerOne a b β β' z) := by
  have hn : ‖σ.refl 1 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 1 z _ σ.wallSide_one_vertexOne
  have hΘ : σ.angleCornerOne a b β β' (σ.refl 1 z) = -σ.angleCornerOne a b β β' z := by
    rw [angleCornerOne, angleCornerOne, hn, psiOne_refl_one, angleOneAtOne_refl_one]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [cornerOne, cornerOne, hn, hΘ, conj_polar]

theorem cornerOne_refl_two (a b β β' : ℝ) {z : ℂ} (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - σ.psiOne z) (h2 : 2 * σ.θ₁ - σ.psiOne z < Real.pi)
    (h : coneStep a b ‖z - σ.vertexOne‖ = 0 ∨
      (σ.lensSwitch β β' z = 0 ∧ σ.lensSwitch β β' (σ.refl 2 z) = 0)) :
    σ.cornerOne a b β β' (σ.refl 2 z) = conj (σ.cornerOne a b β β' z) := by
  have hn : ‖σ.refl 2 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexOne
  have hp : (σ.p₁ : ℝ) * σ.θ₁ = Real.pi := by rw [mul_comm]; exact σ.θ₁_mul
  have hΘ : σ.angleCornerOne a b β β' (σ.refl 2 z) =
      2 * Real.pi - σ.angleCornerOne a b β β' z := by
    rw [angleCornerOne, angleCornerOne, hn, σ.psiOne_refl_two hψ h1 h2, angleTwoAtOne_refl_two]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b ‖z - σ.vertexOne‖) * hp
  rw [cornerOne, cornerOne, hn, hΘ, exp_two_pi_sub, conj_polar]


def angleCornerTwo (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖z - σ.vertexTwo‖) * (σ.p₂ * σ.psiTwo z) +
    coneStep a b ‖z - σ.vertexTwo‖ * ((1 - σ.lensSwitch β β' z) * σ.angleTwoAtTwo z +
      σ.lensSwitch β β' z * σ.angleZeroAtTwo z)

def cornerTwo (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((-(3 / 2) : ℝ) : ℂ) + (innerRadial σ.p₂ a b σ.radTwo ‖z - σ.vertexTwo‖ : ℂ) *
    exp ((σ.angleCornerTwo a b β β' z : ℂ) * I)

theorem modTwo_eq (z : ℂ) : σ.modTwo z = 3 / 2 + profileSlope * (‖z - σ.vertexTwo‖ - σ.radTwo) :=
  rfl

theorem contDiffAt_dist_vertexTwo {z : ℂ} (h : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ (fun u => ‖u - σ.vertexTwo‖) z :=
  (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h)

theorem contDiff_innerRadial (p : ℕ) (a b r₀ : ℝ) : ContDiff ℝ ∞ (innerRadial p a b r₀) := by
  unfold innerRadial
  exact (((contDiff_const.sub (contDiff_coneStep a b)).mul (contDiff_id.pow _)).div_const
    _).add ((contDiff_coneStep a b).mul (contDiff_const.add (contDiff_const.mul
      (contDiff_id.sub contDiff_const))))

theorem contDiffAt_angleCornerTwo (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ σ.domTwo)
    (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.angleCornerTwo a b β β') z := by
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b ‖u - σ.vertexTwo‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (σ.contDiffAt_dist_vertexTwo (σ.ne_vertexTwo_of_mem_domTwo hz2))
  have hs := σ.contDiffAt_lensSwitch β β' z
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul (σ.contDiffAt_psiTwo hψ))).add
    (hτ.mul (((contDiffAt_const.sub hs).mul (σ.contDiffAt_angleTwoAtTwo hz2 hpos2)).add
      (hs.mul (σ.contDiffAt_angleZeroAtTwo hz0 hpos0))))

theorem contDiffAt_cornerTwo (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ σ.domTwo)
    (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.cornerTwo a b β β') z := by
  have hd := σ.contDiffAt_dist_vertexTwo (σ.ne_vertexTwo_of_mem_domTwo hz2)
  have hS := (contDiff_innerRadial σ.p₂ a b σ.radTwo).contDiffAt.comp z hd
  have hΘ := σ.contDiffAt_angleCornerTwo a b β β' hz2 hz0 hψ hpos2 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem hasDerivAt_lensSwitch_circTwo (β β' : ℝ) (z : ℂ) :
    HasDerivAt (fun t => σ.lensSwitch β β' (circ σ.vertexTwo z t))
      (deriv (coneStep β β') (σ.wallSide 2 z) * (σ.rotTwo z).re) 0 := by
  have hW := σ.hasDerivAt_wallSide_two_curve (hasDerivAt_circ σ.vertexTwo z)
  rw [σ.wall_deriv_two_two z] at hW
  have h := (hasDerivAt_coneStep β β' (σ.wallSide 2 (circ σ.vertexTwo z 0))).comp (0 : ℝ) hW
  rw [circ_zero] at h
  exact h

theorem exists_hasDerivAt_angleCornerTwo_circ {a b β β' : ℝ} (hβ : β < β')
    {z : ℂ} (hz2 : z ∈ σ.domTwo) (hz0 : z ∈ σ.domZero)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2))
    (hord : σ.angleTwoAtTwo z ≤ σ.angleZeroAtTwo z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < σ.wallSide 2 z ∨ σ.wallSide 2 z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => σ.angleCornerTwo a b β β' (circ σ.vertexTwo z t)) D 0 := by
  have hz0' := σ.ne_vertexTwo_of_mem_domTwo hz2
  have hd : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 hz0')
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_angleTwoAtTwo hz2 hpos2 hψ
  obtain ⟨d₀, hd₀, h₀⟩ := σ.exists_hasDerivAt_angleZeroAtTwo hz0 hpos0
  have hψd := σ.hasDerivAt_psiTwo_circ hψ
  have hsw := σ.hasDerivAt_lensSwitch_circTwo β β' z
  have hsw' := lensSwitch_deriv_nonneg hβ hlam
  set τ₀ := coneStep a b ‖z - σ.vertexTwo‖ with hτ₀
  set sw' := deriv (coneStep β β') (σ.wallSide 2 z) * (σ.rotTwo z).re
  have hΘγ : HasDerivAt (fun t => σ.angleCornerTwo a b β β' (circ σ.vertexTwo z t))
      ((1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * σ.angleTwoAtTwo z +
        (1 - σ.lensSwitch β β' z) * d₂) + (sw' * σ.angleZeroAtTwo z +
          σ.lensSwitch β β' z * d₀))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₂ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul
        h₂).add (hsw.mul h₀)))
    have e : (fun t => σ.angleCornerTwo a b β β' (circ σ.vertexTwo z t)) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₂ : ℝ) * σ.psiTwo (circ σ.vertexTwo z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) -
          fun t => σ.lensSwitch β β' (circ σ.vertexTwo z t)) *
          (fun t => σ.angleTwoAtTwo (circ σ.vertexTwo z t)) +
          (fun t => σ.lensSwitch β β' (circ σ.vertexTwo z t)) *
          (fun t => σ.angleZeroAtTwo (circ σ.vertexTwo z t))) := by
      funext t
      simp only [angleCornerTwo, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, norm_circ_sub, hτ₀]
    rw [e]
    convert h using 1
    simp only [circ_zero, Pi.sub_apply, zero_mul, zero_add]
  have hpR : (0 : ℝ) < σ.p₂ := by exact_mod_cast σ.one_le_p₂
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.lensSwitch β β' z := coneStep_nonneg _ _ _
  have hs1 : σ.lensSwitch β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * σ.angleTwoAtTwo z +
      (1 - σ.lensSwitch β β' z) * d₂) + (sw' * σ.angleZeroAtTwo z +
        σ.lensSwitch β β' z * d₀)) := by
    have hb : 0 < (1 - σ.lensSwitch β β' z) * d₂ + σ.lensSwitch β β' z * d₀ := by
      have := convex_comb_pos hs0 hs1 hd₂ hd₀
      linarith
    have hx : 0 ≤ sw' * (σ.angleZeroAtTwo z - σ.angleTwoAtTwo z) :=
      mul_nonneg hsw' (by linarith)
    have hin : 0 < ((0 - sw') * σ.angleTwoAtTwo z + (1 - σ.lensSwitch β β' z) * d₂) +
        (sw' * σ.angleZeroAtTwo z + σ.lensSwitch β β' z * d₀) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₂ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_cornerTwo_pos {a b β β' : ℝ} (hab : a < b) (hb : b ≤ 1) (hβ : β < β')
    {z : ℂ} (hz2 : z ∈ σ.domTwo) (hz0 : z ∈ σ.domZero)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2))
    (hord : σ.angleTwoAtTwo z ≤ σ.angleZeroAtTwo z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < σ.wallSide 2 z ∨ σ.wallSide 2 z < β) :
    0 < (fderiv ℝ (σ.cornerTwo a b β β') z).det := by
  have hz0' := σ.ne_vertexTwo_of_mem_domTwo hz2
  have hd : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 hz0')
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_innerRadial σ.one_le_p₂ hab hb σ.radTwo_lt_one hd
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleCornerTwo_circ (a := a) (b := b) hβ hz2 hz0
    hψ hpos2 hpos0 hord hlam
  have hρ : DifferentiableAt ℝ (fun u => ‖u - σ.vertexTwo‖) z :=
    (σ.contDiffAt_dist_vertexTwo hz0').differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.angleCornerTwo a b β β') z :=
    (σ.contDiffAt_angleCornerTwo a b β β' hz2 hz0 hψ hpos2 hpos0).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖circ σ.vertexTwo z t - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    Eventually.of_forall fun t => norm_circ_sub _ _ _
  have key := det_fderiv_polar (c := ((-(3 / 2) : ℝ) : ℂ))
    (S := innerRadial σ.p₂ a b σ.radTwo) (ρ := fun u => ‖u - σ.vertexTwo‖)
    (Θ := σ.angleCornerTwo a b β β') (N := z - σ.vertexTwo) hSd hρ hΘd
    (hasDerivAt_circ σ.vertexTwo z) (circ_zero _ _) hργ hΘγ (hasDerivAt_norm_ray z σ.vertexTwo)
    (hasDerivAt_comp_ray hΘd)
  rw [cross_mul_I] at key
  have hS0 := innerRadial_pos (p := σ.p₂) (a := a) (b := b) σ.radTwo_lt_one hd
  exact det_pos_of_polar (by positivity) key (by positivity)

theorem cornerTwo_eq_apexTwo {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a) {z : ℂ}
    (hd : ‖z - σ.vertexTwo‖ ≤ a) (hψ : z = σ.vertexTwo ∨ 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    σ.cornerTwo a b β β' z = σ.apexTwo z := by
  have hτ : coneStep a b ‖z - σ.vertexTwo‖ = 0 := coneStep_eq_zero hab hd
  rcases hψ with h | h
  · subst h
    have hp := σ.one_le_p₂
    simp only [cornerTwo, innerRadial, apexTwo, sub_self, norm_zero, rotTwo_vertexTwo]
    rw [coneStep_eq_zero hab ha]
    simp [zero_pow (by omega : σ.p₂ ≠ 0)]
  · rw [cornerTwo, angleCornerTwo, innerRadial, hτ, apexTwo, polar_pow h, norm_rotTwo, psiTwo]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

theorem cornerTwo_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ σ.domTwo) (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hd : b ≤ ‖z - σ.vertexTwo‖) (hs : σ.wallSide 2 z ≤ β) :
    σ.cornerTwo a b β β' z = σ.bridgeTwo z := by
  rw [σ.bridgeTwo_eq_polar_two hz2 hpos2, cornerTwo, angleCornerTwo, innerRadial,
    coneStep_eq_one hab hd, lensSwitch, coneStep_eq_zero hβ hs, modTwo_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, sub_zero, zero_div]

theorem cornerTwo_eq_bridgeZero {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz0 : z ∈ σ.domZero) (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2))
    (hd : b ≤ ‖z - σ.vertexTwo‖) (hs : β' ≤ σ.wallSide 2 z) :
    σ.cornerTwo a b β β' z = σ.bridgeZero z := by
  rw [σ.bridgeZero_eq_polar_two hz0 hpos0, cornerTwo, angleCornerTwo, innerRadial,
    coneStep_eq_one hab hd, lensSwitch, coneStep_eq_one hβ hs, modTwo_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add, zero_div]

theorem cornerTwo_refl_two (a b β β' : ℝ) {z : ℂ}
    (h : coneStep a b ‖z - σ.vertexTwo‖ = 0 ∨
      (σ.lensSwitch β β' z = 0 ∧ σ.lensSwitch β β' (σ.refl 2 z) = 0)) :
    σ.cornerTwo a b β β' (σ.refl 2 z) = conj (σ.cornerTwo a b β β' z) := by
  have hn : ‖σ.refl 2 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexTwo
  have hΘ : σ.angleCornerTwo a b β β' (σ.refl 2 z) = -σ.angleCornerTwo a b β β' z := by
    rw [angleCornerTwo, angleCornerTwo, hn, psiTwo_refl_two, angleTwoAtTwo_refl_two]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [cornerTwo, cornerTwo, hn, hΘ, conj_polar]

theorem cornerTwo_refl_zero (a b β β' : ℝ) {z : ℂ} (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - σ.psiTwo z) (h2 : 2 * σ.θ₂ - σ.psiTwo z < Real.pi)
    (h : coneStep a b ‖z - σ.vertexTwo‖ = 0 ∨
      (σ.lensSwitch β β' z = 1 ∧ σ.lensSwitch β β' (σ.refl 0 z) = 1)) :
    σ.cornerTwo a b β β' (σ.refl 0 z) = conj (σ.cornerTwo a b β β' z) := by
  have hn : ‖σ.refl 0 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 0 z _ σ.wallSide_zero_vertexTwo
  have hp : (σ.p₂ : ℝ) * σ.θ₂ = Real.pi := by rw [mul_comm]; exact σ.θ₂_mul
  have hΘ : σ.angleCornerTwo a b β β' (σ.refl 0 z) =
      2 * Real.pi - σ.angleCornerTwo a b β β' z := by
    rw [angleCornerTwo, angleCornerTwo, hn, σ.psiTwo_refl_zero hψ h1 h2, angleZeroAtTwo_refl_zero]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b ‖z - σ.vertexTwo‖) * hp
  rw [cornerTwo, cornerTwo, hn, hΘ, exp_two_pi_sub, conj_polar]


def blendThree (w δ : ℝ) (z : ℂ) : ℝ :=
  w * (2 * discAngle z / σ.θ₃ - 1) + w / δ * (σ.canon 1 z - σ.canon 0 z)

def nuThree (w δ : ℝ) (z : ℂ) : ℝ := coneStep (-w) w (σ.blendThree w δ z)

def angleCornerThree (a b w δ : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖z‖) * (Real.pi - σ.p₃ * discAngle z) +
    coneStep a b ‖z‖ * ((1 - σ.nuThree w δ z) * σ.angleZeroAtThree z +
      σ.nuThree w δ z * σ.angleOneAtThree z)

def cornerThree (a b w δ : ℝ) (z : ℂ) : ℂ :=
  ((0 : ℝ) : ℂ) + (outerRadial σ.p₃ a b σ.radThree ‖z‖ : ℂ) *
    exp ((σ.angleCornerThree a b w δ z : ℂ) * I)

theorem modThree_eq (z : ℂ) : σ.modThree z = 3 - profileSlope * (‖z‖ - σ.radThree) := rfl

theorem contDiffAt_blendThree (w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : ContDiffAt ℝ ∞ (σ.blendThree w δ) z :=
  (contDiffAt_const.mul (((contDiffAt_const.mul (contDiffAt_psiThree hψ)).div_const _).sub
    contDiffAt_const)).add (contDiffAt_const.mul ((σ.contDiffAt_canon_one h2).sub
      (σ.contDiffAt_canon_zero h1)))

theorem contDiffAt_nuThree (w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : ContDiffAt ℝ ∞ (σ.nuThree w δ) z :=
  (contDiff_coneStep (-w) w).contDiffAt.comp z (σ.contDiffAt_blendThree w δ hψ h1 h2)

theorem contDiffAt_angleCornerThree (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re) :
    ContDiffAt ℝ ∞ (σ.angleCornerThree a b w δ) z := by
  have hτ : ContDiffAt ℝ ∞ (fun u : ℂ => coneStep a b ‖u‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (contDiffAt_norm ℝ (σ.ne_zero_of_mem_domOne hz1))
  have hν := σ.contDiffAt_nuThree w δ hψ (σ.ne_vertexOne_of_mem_domOne hz1)
    (σ.ne_vertexTwo_of_mem_domZero hz0)
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.sub (contDiffAt_const.mul
    (contDiffAt_psiThree hψ)))).add (hτ.mul (((contDiffAt_const.sub hν).mul
      (σ.contDiffAt_angleZeroAtThree hz0 hpos0)).add (hν.mul
        (σ.contDiffAt_angleOneAtThree hz1 hpos1))))

theorem contDiff_outerRadial (p : ℕ) (a b r₀ : ℝ) : ContDiff ℝ ∞ (outerRadial p a b r₀) := by
  unfold outerRadial
  exact ((contDiff_const.sub (contDiff_coneStep a b)).mul (contDiff_const.sub
    ((contDiff_id.pow _).div_const _))).add ((contDiff_coneStep a b).mul (contDiff_const.sub
      (contDiff_const.mul (contDiff_id.sub contDiff_const))))

theorem contDiffAt_cornerThree (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re) :
    ContDiffAt ℝ ∞ (σ.cornerThree a b w δ) z := by
  have hS := (contDiff_outerRadial σ.p₃ a b σ.radThree).contDiffAt.comp z
    (contDiffAt_norm ℝ (σ.ne_zero_of_mem_domOne hz1))
  have hΘ := σ.contDiffAt_angleCornerThree a b w δ hz1 hz0 hψ hpos1 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem hasDerivAt_canon_one_circThree {z : ℂ} (h : z ≠ σ.vertexTwo) :
    HasDerivAt (fun t => σ.canon 1 (circ 0 z t))
      (Real.sin σ.θ₁ * σ.wallSide 0 z / ‖z - σ.vertexTwo‖) 0 := by
  have hn := hasDerivAt_norm_circ_sub 0 z σ.vertexTwo h
  rw [sub_zero, σ.inner_circThree_two z] at hn
  exact hn.sub_const σ.radTwo

theorem hasDerivAt_canon_zero_circThree {z : ℂ} (h : z ≠ σ.vertexOne) :
    HasDerivAt (fun t => σ.canon 0 (circ 0 z t))
      (-(Real.sin σ.θ₂ * σ.wallSide 1 z) / ‖z - σ.vertexOne‖) 0 := by
  have hn := hasDerivAt_norm_circ_sub 0 z σ.vertexOne h
  rw [sub_zero, σ.inner_circThree_one z] at hn
  exact hn.sub_const σ.radOne

theorem exists_hasDerivAt_nuThree {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hψ : 0 < ‖z‖ + z.re) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.blendThree w δ z ∨
      σ.blendThree w δ z < -w) :
    ∃ ν' : ℝ, 0 ≤ ν' ∧ HasDerivAt (fun t => σ.nuThree w δ (circ 0 z t)) ν' 0 := by
  have hψd := hasDerivAt_psiThree_circ hψ
  have hc1 := σ.hasDerivAt_canon_one_circThree h2
  have hc0 := σ.hasDerivAt_canon_zero_circThree h1
  have hB : HasDerivAt (fun t => σ.blendThree w δ (circ 0 z t))
      (w * (2 * 1 / σ.θ₃) + w / δ * (Real.sin σ.θ₁ * σ.wallSide 0 z / ‖z - σ.vertexTwo‖ -
        -(Real.sin σ.θ₂ * σ.wallSide 1 z) / ‖z - σ.vertexOne‖)) 0 := by
    have h := ((((hψd.const_mul 2).div_const σ.θ₃).sub_const 1).const_mul w).add
      ((hc1.sub hc0).const_mul (w / δ))
    exact h
  have hN := (hasDerivAt_coneStep (-w) w (σ.blendThree w δ (circ 0 z 0))).comp (0 : ℝ) hB
  rw [circ_zero] at hN
  refine ⟨_, ?_, hN⟩
  have hwlt : -w < w := by linarith
  rcases hside with ⟨h0', h1'⟩ | h | h
  · apply mul_nonneg (deriv_coneStep_nonneg hwlt _)
    have hn2 : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have hn1 : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have := σ.θ₃_pos
    have := σ.sin_θ₁_pos
    have := σ.sin_θ₂_pos
    have e : Real.sin σ.θ₁ * σ.wallSide 0 z / ‖z - σ.vertexTwo‖ -
        -(Real.sin σ.θ₂ * σ.wallSide 1 z) / ‖z - σ.vertexOne‖ =
        Real.sin σ.θ₁ * σ.wallSide 0 z / ‖z - σ.vertexTwo‖ +
          Real.sin σ.θ₂ * σ.wallSide 1 z / ‖z - σ.vertexOne‖ := by ring
    rw [e]
    positivity
  · rw [deriv_coneStep_eq_zero_of_lt hwlt h, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hwlt h, zero_mul]

theorem exists_hasDerivAt_angleCornerThree_circ {a b w δ : ℝ} (hw : 0 < w)
    (hδ : 0 < δ) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re)
    (hord : σ.angleOneAtThree z ≤ σ.angleZeroAtThree z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.blendThree w δ z ∨
      σ.blendThree w δ z < -w) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t => σ.angleCornerThree a b w δ (circ 0 z t)) D 0 := by
  have hz0' := σ.ne_zero_of_mem_domOne hz1
  have h1 := σ.ne_vertexOne_of_mem_domOne hz1
  have h2 := σ.ne_vertexTwo_of_mem_domZero hz0
  have hd : 0 < ‖z‖ := norm_pos_iff.2 hz0'
  obtain ⟨d₀, hd₀, h₀⟩ := σ.exists_hasDerivAt_angleZeroAtThree hz0 hpos0
  obtain ⟨d₁, hd₁, h₁⟩ := σ.exists_hasDerivAt_angleOneAtThree hz1 hpos1
  obtain ⟨ν', hν', hν⟩ := σ.exists_hasDerivAt_nuThree hw hδ hψ h1 h2 hside
  have hψd := hasDerivAt_psiThree_circ hψ
  set τ₀ := coneStep a b ‖z‖ with hτ₀
  have hΘγ : HasDerivAt (fun t => σ.angleCornerThree a b w δ (circ 0 z t))
      ((1 - τ₀) * (0 - σ.p₃ * 1) + τ₀ * (((0 - ν') * σ.angleZeroAtThree z +
        (1 - σ.nuThree w δ z) * d₀) + (ν' * σ.angleOneAtThree z + σ.nuThree w δ z * d₁))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul ((hasDerivAt_const (0 : ℝ) Real.pi).sub
      (hψd.const_mul (σ.p₃ : ℝ)))).add ((hasDerivAt_const (0 : ℝ) τ₀).mul
        ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul h₀).add (hν.mul h₁)))
    have hn : ∀ t, ‖circ 0 z t‖ = ‖z‖ := by
      intro t
      have := norm_circ_sub 0 z t
      rwa [sub_zero, sub_zero] at this
    have e : (fun t => σ.angleCornerThree a b w δ (circ 0 z t)) =
        (fun _ => 1 - τ₀) * ((fun _ => Real.pi) -
          fun t => (σ.p₃ : ℝ) * discAngle (circ 0 z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) - fun t => σ.nuThree w δ (circ 0 z t)) *
          (fun t => σ.angleZeroAtThree (circ 0 z t)) +
          (fun t => σ.nuThree w δ (circ 0 z t)) * (fun t => σ.angleOneAtThree (circ 0 z t))) := by
      funext t
      simp only [angleCornerThree, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hn, hτ₀]
    rw [e]
    convert h using 1
    simp only [circ_zero, Pi.sub_apply, zero_mul, zero_add]
  have hpR : (0 : ℝ) < σ.p₃ := by exact_mod_cast σ.one_le_p₃
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.nuThree w δ z := coneStep_nonneg _ _ _
  have hs1 : σ.nuThree w δ z ≤ 1 := coneStep_le_one _ _ _
  have hD : (1 - τ₀) * (0 - σ.p₃ * 1) + τ₀ * (((0 - ν') * σ.angleZeroAtThree z +
      (1 - σ.nuThree w δ z) * d₀) + (ν' * σ.angleOneAtThree z + σ.nuThree w δ z * d₁)) < 0 := by
    have hb : 0 < (1 - σ.nuThree w δ z) * -d₀ + σ.nuThree w δ z * -d₁ :=
      convex_comb_pos hs0 hs1 (by linarith) (by linarith)
    have hx : ν' * (σ.angleOneAtThree z - σ.angleZeroAtThree z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hν' (by linarith)
    have hin : 0 < -(((0 - ν') * σ.angleZeroAtThree z + (1 - σ.nuThree w δ z) * d₀) +
        (ν' * σ.angleOneAtThree z + σ.nuThree w δ z * d₁)) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₃ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_cornerThree_pos {a b w δ : ℝ} (hab : a < b) (hb : b ≤ 1 / 5) (hw : 0 < w)
    (hδ : 0 < δ) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz0 : z ∈ σ.domZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re)
    (hord : σ.angleOneAtThree z ≤ σ.angleZeroAtThree z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.blendThree w δ z ∨
      σ.blendThree w δ z < -w) :
    0 < (fderiv ℝ (σ.cornerThree a b w δ) z).det := by
  have hz0' := σ.ne_zero_of_mem_domOne hz1
  have h1 := σ.ne_vertexOne_of_mem_domOne hz1
  have h2 := σ.ne_vertexTwo_of_mem_domZero hz0
  have hd : 0 < ‖z‖ := norm_pos_iff.2 hz0'
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_outerRadial σ.one_le_p₃ hab hb σ.radThree_lt_one hd
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleCornerThree_circ (a := a) (b := b) hw hδ hz1 hz0
    hψ hpos1 hpos0 hord hside
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z :=
    (contDiffAt_norm ℝ hz0' : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.angleCornerThree a b w δ) z :=
    (σ.contDiffAt_angleCornerThree a b w δ hz1 hz0 hψ hpos1 hpos0).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖circ 0 z t‖ = ‖z‖ := Eventually.of_forall fun t => by
    have := norm_circ_sub 0 z t
    rwa [sub_zero, sub_zero] at this
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * z‖) ‖z‖ 0 := by
    have h := hasDerivAt_norm_ray z 0
    simp only [sub_zero] at h
    exact h
  have hγ := hasDerivAt_circ 0 z
  rw [sub_zero] at hγ
  have key := det_fderiv_polar (c := ((0 : ℝ) : ℂ))
    (S := outerRadial σ.p₃ a b σ.radThree) (ρ := fun u : ℂ => ‖u‖)
    (Θ := σ.angleCornerThree a b w δ) (N := z) hSd hρ hΘd hγ (circ_zero _ _) hργ hΘγ hρN
    (hasDerivAt_comp_ray hΘd)
  rw [cross_mul_I] at key
  have hS0 := outerRadial_pos (p := σ.p₃) hab hb σ.radThree_pos.le hd.le hz1.2.2
  have hpos : 0 < outerRadial σ.p₃ a b σ.radThree ‖z‖ * S' * D * ‖z‖ := by
    have := mul_pos_of_neg_of_neg hS' hD
    rw [show outerRadial σ.p₃ a b σ.radThree ‖z‖ * S' * D * ‖z‖ =
      outerRadial σ.p₃ a b σ.radThree ‖z‖ * (S' * D) * ‖z‖ by ring]
    positivity
  exact det_pos_of_polar (by positivity) key hpos

theorem conj_div_norm_eq_exp {z : ℂ} (h : 0 < ‖z‖ + z.re) :
    conj z / ‖z‖ = exp (((-discAngle z : ℝ) : ℂ) * I) := by
  have hz := ne_zero_of_norm_add_re_pos h
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : conj z = (‖z‖ : ℂ) * exp (((-discAngle z : ℝ) : ℂ) * I) := by
    conv_lhs => rw [halfArg_polar_self hz h]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hc, mul_div_cancel_left₀ _ hn]

theorem cornerThree_eq_outerGerm {a b w δ : ℝ} (hab : a < b) {z : ℂ} (hd : ‖z‖ ≤ a)
    (hψ : 0 < ‖z‖ + z.re) : σ.cornerThree a b w δ z = compactOuterGerm σ.p₃ z := by
  rw [cornerThree, angleCornerThree, outerRadial, coneStep_eq_zero hab hd, compactOuterGerm,
    conj_div_norm_eq_exp hψ, ← Complex.exp_nat_mul]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rw [show ((Real.pi - σ.p₃ * discAngle z : ℝ) : ℂ) * I =
      Real.pi * I + (σ.p₃ : ℂ) * (((-discAngle z : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast
  ring

theorem cornerThree_eq_bridgeZero {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz0 : z ∈ σ.domZero) (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re)
    (hd : b ≤ ‖z‖) (hν : σ.blendThree w δ z ≤ -w) :
    σ.cornerThree a b w δ z = σ.bridgeZero z := by
  rw [σ.bridgeZero_eq_polar_three hz0 hpos0, cornerThree, angleCornerThree, outerRadial,
    coneStep_eq_one hab hd, nuThree, coneStep_eq_zero (by linarith) hν, modThree_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, sub_zero]

theorem cornerThree_eq_bridgeOne {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hd : b ≤ ‖z‖) (hν : w ≤ σ.blendThree w δ z) :
    σ.cornerThree a b w δ z = σ.bridgeOne z := by
  rw [σ.bridgeOne_eq_polar_three hz1 hpos1, cornerThree, angleCornerThree, outerRadial,
    coneStep_eq_one hab hd, nuThree, coneStep_eq_one (by linarith) hν, modThree_eq]
  simp only [sub_self, zero_mul, one_mul, zero_add]

theorem cornerThree_refl_zero (a b w δ : ℝ) {z : ℂ}
    (h : coneStep a b ‖z‖ = 0 ∨ (σ.nuThree w δ z = 0 ∧ σ.nuThree w δ (σ.refl 0 z) = 0)) :
    σ.cornerThree a b w δ (σ.refl 0 z) = conj (σ.cornerThree a b w δ z) := by
  have hn : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z
  have hΘ : σ.angleCornerThree a b w δ (σ.refl 0 z) =
      2 * Real.pi - σ.angleCornerThree a b w δ z := by
    rw [angleCornerThree, angleCornerThree, hn, psiThree_refl_zero, angleZeroAtThree_refl_zero]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [cornerThree, cornerThree, hn, hΘ, exp_two_pi_sub, conj_polar]

theorem cornerThree_refl_one (a b w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi)
    (h : coneStep a b ‖z‖ = 0 ∨ (σ.nuThree w δ z = 1 ∧ σ.nuThree w δ (σ.refl 1 z) = 1)) :
    σ.cornerThree a b w δ (σ.refl 1 z) = conj (σ.cornerThree a b w δ z) := by
  have hn : ‖σ.refl 1 z‖ = ‖z‖ := by
    have := σ.norm_refl_sub 1 z 0 σ.wallSide_one_zero
    rwa [sub_zero, sub_zero] at this
  have hp : (σ.p₃ : ℝ) * σ.θ₃ = Real.pi := by rw [mul_comm]; exact σ.θ₃_mul
  have hΘ : σ.angleCornerThree a b w δ (σ.refl 1 z) = -σ.angleCornerThree a b w δ z := by
    rw [angleCornerThree, angleCornerThree, hn, σ.psiThree_refl_one hψ h1 h2,
      angleOneAtThree_refl_one]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination (-2) * hp
    · rw [h3, h4]
      linear_combination (-2) * (1 - coneStep a b ‖z‖) * hp
  rw [cornerThree, cornerThree, hn, hΘ, conj_polar]

end EuclidShape

end GC.Seifert
