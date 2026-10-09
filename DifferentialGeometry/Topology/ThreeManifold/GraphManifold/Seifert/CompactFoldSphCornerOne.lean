import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphRadial

/-!
# The corner of the spherical compact fold at `v₁`

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The corner at `v₁` is the polar map about `+3/2`
`sphCornerOne = 3/2 + S(ϖ₁) e^{iΘ₁}` with `ϖ₁ = ‖rotOne‖`, the radial profile
`S = sphInnerRadial p₁ a b τ₁` and the angle `Θ₁ = (1 - τ) p₁ ψ₁ + τ (s · sphAngleOneAtOne +
(1 - s) · sphAngleTwoAtOne)`, where `τ = coneStep a b ϖ₁`, `ψ₁ = sphPsiOne` and
`s = sphLensSwitch β β' = coneStep β β' (Im rotTwo)` switches from the bridge of wall 2 (`s = 0`
within `β` of wall 2) to the bridge of wall 1 (`s = 1` beyond `β'`).

Along the circle about `v₁` the coordinate `rotTwo` moves on the circle about `t₁₂` in its own disc
coordinate (`eventually_rotTwo_sphCirc_one`), so the side coordinate `Im rotTwo` has derivative
`Re ((ζ - t₁₂)(1 + t₁₂ ζ))/(1 + t₁₂²)`, `ζ = rotTwo z` (`hasDerivAt_sphSideTwo_sphCircOne`). With
the order of the two bridge angles and this sign where the switch moves, the angle `Θ₁` is strictly
increasing along the circle, and A4's polar formula gives a positive Jacobian off `v₁`
(`det_fderiv_sphCornerOne_pos`). Near `v₁` the corner is the apex model `3/2 + rotOne^{p₁}/2`
(`sphCornerOne_eq_apex`); where `τ = 1` and the switch is saturated it is a bridge
(`sphCornerOne_eq_bridgeOne`, `sphCornerOne_eq_bridgeTwo`); it satisfies the wall identities where
the weights are constant (`sphCornerOne_refl_one`, `sphCornerOne_refl_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem sphRayDir_eq {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    sphRayDir a z = (z - a) * (1 + conj a * z) / (1 + conj a * a) := by
  have ha := one_add_conj_mul_self_ne_sph a
  rw [sphRayDir, one_sub_conj_mul_sphMoeb h, sphMoeb]
  field_simp

namespace CompactShape

variable {σ : CompactShape}

def sphLensSwitch (σ : CompactShape) (β β' : ℝ) (z : ℂ) : ℝ := coneStep β β' (σ.sphSideTwo z)

def sphAngleCornerOne (σ : CompactShape) (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖σ.rotOne z‖) * (σ.p₁ * σ.sphPsiOne z) +
    coneStep a b ‖σ.rotOne z‖ * (σ.sphLensSwitch β β' z * σ.sphAngleOneAtOne z +
      (1 - σ.sphLensSwitch β β' z) * σ.sphAngleTwoAtOne z)

def sphCornerOne (σ : CompactShape) (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) + (sphInnerRadial σ.p₁ a b (σ.sphTau 0) ‖σ.rotOne z‖ : ℂ) *
    exp ((σ.sphAngleCornerOne a b β β' z : ℂ) * I)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem eventually_rotTwo_sphCirc_one {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), σ.rotTwo (sphCirc σ.vertexOne z t) =
      sphCirc σ.sphTOneTwo (σ.rotTwo z) t := by
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have hγc := continuousAt_sphCirc hv1
  have hRc : ContinuousAt (fun t => σ.rotTwo (sphCirc σ.vertexOne z t)) 0 := by
    have h' : ContinuousAt σ.rotTwo (sphCirc σ.vertexOne z 0) := by
      rw [sphCirc_zero hv1]
      exact (contDiffAt_rotTwo_sph hs hv2).continuousAt
    exact h'.comp hγc
  have hζ : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0 := by
    have hc := one_add_conj_sphMoeb_ne (a := σ.vertexTwo) (b := σ.vertexOne) hv2'
      (by rw [conj_vertexTwo_sph]; exact one_add_vertexTwo_mul_vertexOne_ne_sph hs) hv1
    rwa [conj_sphMoeb_vertexTwo_vertexOne_mul hs] at hc
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),
      1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo (sphCirc σ.vertexOne z t) ≠ 0 := by
    have hc : ContinuousAt (fun t => 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo (sphCirc σ.vertexOne z t))
        0 := continuousAt_const.add (continuousAt_const.mul hRc)
    have h0 : (fun t => 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo (sphCirc σ.vertexOne z t)) 0 ≠ 0 := by
      simp only [sphCirc_zero hv1]
      exact hζ
    exact hc.eventually_ne h0
  filter_upwards [eventually_rotOne_sphCirc hs hv1, eventually_ne_sphCirc (b := σ.vertexOne)
    hv1 hv1, eventually_ne_sphCirc (b := σ.vertexTwo) hv1 hv2', hne] with t ht e1 e2 e3
  have k1 := rotOne_eq_rotTwo_sph hs e1 e2
  have k0 := rotOne_eq_rotTwo_sph hs hv1 hv2'
  rw [ht, k0] at k1
  have hm : sphMoeb σ.sphTOneTwo (σ.rotTwo (sphCirc σ.vertexOne z t)) =
      sphMoeb σ.sphTOneTwo (σ.rotTwo z) * exp ((t : ℂ) * I) := by
    have hu : exp ((σ.θ₁ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have k2 : exp ((σ.θ₁ : ℂ) * I) * sphMoeb σ.sphTOneTwo (σ.rotTwo (sphCirc σ.vertexOne z t)) =
        exp ((σ.θ₁ : ℂ) * I) * (sphMoeb σ.sphTOneTwo (σ.rotTwo z) * exp ((t : ℂ) * I)) := by
      linear_combination k1
    exact mul_left_cancel₀ hu k2
  change _ = sphMoebInv (σ.sphTOneTwo : ℂ)
    (sphMoeb (σ.sphTOneTwo : ℂ) (σ.rotTwo z) * exp ((t : ℂ) * I))
  rw [← hm, sphMoebInv_sphMoeb]
  rwa [Complex.conj_ofReal]

theorem hasDerivAt_sphSideTwo_sphCircOne {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hv2 : 1 + σ.vertexTwo * z ≠ 0) (hζ : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0) :
    HasDerivAt (fun t => σ.sphSideTwo (sphCirc σ.vertexOne z t))
      (((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re /
        (1 + σ.sphTOneTwo ^ 2)) 0 := by
  have hζ' : 1 + conj (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0 := by rwa [Complex.conj_ofReal]
  have hd := hasDerivAt_im_curve_sph (hasDerivAt_sphCirc hζ')
  rw [sphCirc_deriv_eq, sphRayDir_eq hζ', Complex.conj_ofReal] at hd
  have e : ((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z) /
      (1 + σ.sphTOneTwo * σ.sphTOneTwo) * I).im =
      ((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re /
        (1 + σ.sphTOneTwo ^ 2) := by
    have e2 : ((1 : ℂ) + (σ.sphTOneTwo : ℂ) * σ.sphTOneTwo) = ((1 + σ.sphTOneTwo ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2, Complex.mul_I_im, Complex.div_ofReal_re]
  rw [e] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_rotTwo_sphCirc_one hs hv1 hv2] with t ht
  rw [sphSideTwo, ht]


theorem one_add_conj_vertexOne_refl_two_ne_sph {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) : 1 + conj σ.vertexOne * σ.refl 2 z ≠ 0 := by
  set a := sphMoeb σ.vertexTwo σ.vertexOne with ha_def
  set u := exp (-(2 * (σ.θ₂ : ℂ) * I)) with hu_def
  have hv : 1 + conj σ.vertexTwo * σ.vertexOne ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_vertexOne_ne_sph hs
  have hz1 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact ((mem_reflChart_two_iff_sph hs).1 hz).1
  have hr1 : 1 + conj σ.vertexTwo * σ.refl 2 z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_refl_two_sph hs hz
  have ha : a = u * conj a := by
    rw [ha_def, sphMoeb_vertexTwo_vertexOne hs, hu_def, map_neg, map_mul,
      Complex.conj_ofReal, conj_exp_neg_sph, exp_neg_two_mul_eq_sph]
    have := exp_mul_exp_neg_sph σ.θ₂
    linear_combination (exp (-((σ.θ₂ : ℂ) * I)) * σ.sphTOneTwo) * this
  have hω : sphMoeb σ.vertexTwo (σ.refl 2 z) = u * conj (sphMoeb σ.vertexTwo z) := by
    rw [sphMoeb_refl_two hs hz, reflTwoAux_sph hs]
  have hca : conj a * u = a := by
    conv_rhs => rw [ha]
    ring
  have hA : ∀ w, 1 + conj σ.vertexTwo * w ≠ 0 →
      (1 + conj a * sphMoeb σ.vertexTwo w = 0 ↔ 1 + conj σ.vertexOne * w = 0) := by
    intro w hw
    rw [ha_def, one_add_conj_sphMoeb_mul hw hv]
    have hvv := one_add_conj_mul_self_ne_sph σ.vertexTwo
    have hv' := one_add_mul_conj_ne_sph hv
    constructor
    · intro h
      rcases div_eq_zero_iff.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hvv
        · exact h
      · exact absurd h (mul_ne_zero hv' hw)
    · intro h
      simp [h]
  intro h
  have h' := (hA _ hr1).2 h
  rw [hω, ← mul_assoc, hca] at h'
  have h'' : 1 + conj a * sphMoeb σ.vertexTwo z = 0 := by
    have := congrArg conj h'
    rw [map_add, map_one, map_mul, Complex.conj_conj, map_zero] at this
    exact this
  exact h1 ((hA z hz1).1 h'')

theorem rotOne_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) :
    σ.rotOne (σ.refl 2 z) = exp (2 * (σ.θ₁ : ℂ) * I) * conj (σ.rotOne z) := by
  have h2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact ((mem_reflChart_two_iff_sph hs).1 hz).1
  have h1' := one_add_conj_vertexOne_refl_two_ne_sph hs hz h1
  have h2' : 1 + conj σ.vertexTwo * σ.refl 2 z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_refl_two_sph hs hz
  rw [rotOne_eq_rotTwo_sph hs h1' h2', rotOne_eq_rotTwo_sph hs h1 h2, rotTwo_refl_two_sph hs hz,
    ← Complex.conj_ofReal σ.sphTOneTwo, sphMoeb_conj, Complex.conj_ofReal, map_neg, map_mul,
    conj_exp_ofReal_mul_I_sph, exp_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₁
  linear_combination (exp ((σ.θ₁ : ℂ) * I) * conj (sphMoeb σ.sphTOneTwo (σ.rotTwo z))) * this

theorem contDiffAt_sphLensSwitch (β β' : ℝ) {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContDiffAt ℝ ∞ (σ.sphLensSwitch β β') z :=
  (contDiff_coneStep β β').contDiffAt.comp z (contDiffAt_sphSideTwo hs hv2)

theorem contDiffAt_norm_rotOne {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hne : σ.rotOne z ≠ 0) : ContDiffAt ℝ ∞ (fun u => ‖σ.rotOne u‖) z :=
  (contDiffAt_rotOne_sph hs hv1).norm ℝ hne

theorem rotOne_ne_zero_of_domOne {z : ℂ} (hz : z ∈ σ.sphDomOne) : σ.rotOne z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_rotOne_sph hs, norm_ne_zero_iff]
  exact sphMoeb_vertexOne_ne_of_domOne hs hz

theorem contDiffAt_sphAngleCornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz2 : z ∈ σ.sphDomTwo) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.sphAngleCornerOne a b β β') z := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz2.2.1
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b ‖σ.rotOne u‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (contDiffAt_norm_rotOne hs hv1 (rotOne_ne_zero_of_domOne hs hz1))
  have hsw := contDiffAt_sphLensSwitch hs β β' hz2.1
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul
    (contDiffAt_sphPsiOne hs hv1 hψ))).add (hτ.mul ((hsw.mul
      (contDiffAt_sphAngleOneAtOne hs hz1 hpos1)).add ((contDiffAt_const.sub hsw).mul
        (contDiffAt_sphAngleTwoAtOne hs hz2 hpos2))))

omit hs in
theorem contDiff_sphInnerRadial_at (p : ℕ) (a b : ℝ) {τ x : ℝ} (h : 1 + x * τ ≠ 0) :
    ContDiffAt ℝ ∞ (sphInnerRadial p a b τ) x := by
  unfold sphInnerRadial
  exact (((contDiffAt_const.sub (contDiff_coneStep a b).contDiffAt).mul
    (contDiffAt_id.pow p)).div_const _).add ((contDiff_coneStep a b).contDiffAt.mul
      (contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_sphCanonF h))))

theorem contDiffAt_sphCornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz2 : z ∈ σ.sphDomTwo) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.sphCornerOne a b β β') z := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz2.2.1
  have hd := contDiffAt_norm_rotOne hs hv1 (rotOne_ne_zero_of_domOne hs hz1)
  have hS : ContDiffAt ℝ ∞ (fun u => sphInnerRadial σ.p₁ a b (σ.sphTau 0) ‖σ.rotOne u‖) z := by
    have hpos : 1 + ‖σ.rotOne z‖ * σ.sphTau 0 ≠ 0 := by
      have := mul_nonneg (norm_nonneg (σ.rotOne z)) (sphTau_pos hs 0).le
      linarith
    exact (contDiff_sphInnerRadial_at σ.p₁ a b hpos).comp z hd
  have hΘ := contDiffAt_sphAngleCornerOne hs a b β β' hz1 hz2 hψ hpos1 hpos2
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem exists_hasDerivAt_sphAngleCornerOne_circ {a b β β' : ℝ} (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ σ.sphDomOne) (hz2 : z ∈ σ.sphDomTwo)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2))
    (hord : σ.sphAngleOneAtOne z ≤ σ.sphAngleTwoAtOne z)
    (hlam : ((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re ≤ 0 ∨
      β' < σ.sphSideTwo z ∨ σ.sphSideTwo z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => σ.sphAngleCornerOne a b β β' (sphCirc σ.vertexOne z t)) D 0 := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz2.2.1
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := hz2.1
  have hζ : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0 := one_add_real_mul_ne_sph hz2.2.2.2.1
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_sphAngleOneAtOne hs hz1 hpos1
  obtain ⟨d₂, hd₂, h₂⟩ := exists_hasDerivAt_sphAngleTwoAtOne hs hz2 hpos2
  have hψd := hasDerivAt_sphPsiOne_sphCirc hs hv1 hψ
  have hY := hasDerivAt_sphSideTwo_sphCircOne hs hv1 hv2 hζ
  have hsw : HasDerivAt (fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t))
      (deriv (coneStep β β') (σ.sphSideTwo z) *
        (((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re /
          (1 + σ.sphTOneTwo ^ 2))) 0 := by
    have h := (hasDerivAt_coneStep β β' (σ.sphSideTwo (sphCirc σ.vertexOne z 0))).comp
      (0 : ℝ) hY
    rw [sphCirc_zero hv1] at h
    exact h
  have hsw' : deriv (coneStep β β') (σ.sphSideTwo z) *
      (((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re /
        (1 + σ.sphTOneTwo ^ 2)) ≤ 0 := by
    apply EuclidShape.lensSwitch_deriv_nonpos hβ
    rcases hlam with h | h | h
    · left
      exact div_nonpos_of_nonpos_of_nonneg h (by positivity)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  set τ₀ := coneStep a b ‖σ.rotOne z‖ with hτ₀
  set sw' := deriv (coneStep β β') (σ.sphSideTwo z) *
    (((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re / (1 + σ.sphTOneTwo ^ 2))
  have hΘγ : HasDerivAt (fun t => σ.sphAngleCornerOne a b β β' (sphCirc σ.vertexOne z t))
      ((1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * σ.sphAngleOneAtOne z + σ.sphLensSwitch β β' z * d₁) +
        ((0 - sw') * σ.sphAngleTwoAtOne z + (1 - σ.sphLensSwitch β β' z) * d₂))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₁ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((hsw.mul h₁).add
        (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul h₂)))
    have e : (fun t => (1 - τ₀) * (σ.p₁ * σ.sphPsiOne (sphCirc σ.vertexOne z t)) +
        τ₀ * (σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t) *
          σ.sphAngleOneAtOne (sphCirc σ.vertexOne z t) +
          (1 - σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t)) *
          σ.sphAngleTwoAtOne (sphCirc σ.vertexOne z t))) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₁ : ℝ) * σ.sphPsiOne (sphCirc σ.vertexOne z t)) +
        (fun _ => τ₀) * ((fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t)) *
          (fun t => σ.sphAngleOneAtOne (sphCirc σ.vertexOne z t)) +
          ((fun _ => (1 : ℝ)) - fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t)) *
          (fun t => σ.sphAngleTwoAtOne (sphCirc σ.vertexOne z t))) := by
      funext t
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    have h' : HasDerivAt (fun t => (1 - τ₀) * (σ.p₁ * σ.sphPsiOne (sphCirc σ.vertexOne z t)) +
        τ₀ * (σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t) *
          σ.sphAngleOneAtOne (sphCirc σ.vertexOne z t) +
          (1 - σ.sphLensSwitch β β' (sphCirc σ.vertexOne z t)) *
          σ.sphAngleTwoAtOne (sphCirc σ.vertexOne z t)))
        ((1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * σ.sphAngleOneAtOne z +
          σ.sphLensSwitch β β' z * d₁) + ((0 - sw') * σ.sphAngleTwoAtOne z +
            (1 - σ.sphLensSwitch β β' z) * d₂))) 0 := by
      rw [e]
      convert h using 1
      simp only [sphCirc_zero hv1, Pi.sub_apply, zero_mul, zero_add]
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [eventually_rotOne_sphCirc hs hv1] with t ht
    rw [sphAngleCornerOne, ht, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hpR : (0 : ℝ) < σ.p₁ := by exact_mod_cast le_trans (by norm_num) σ.two_le_p₁
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.sphLensSwitch β β' z := coneStep_nonneg _ _ _
  have hs1 : σ.sphLensSwitch β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * σ.sphAngleOneAtOne z +
      σ.sphLensSwitch β β' z * d₁) + ((0 - sw') * σ.sphAngleTwoAtOne z +
        (1 - σ.sphLensSwitch β β' z) * d₂)) := by
    have hb : 0 < σ.sphLensSwitch β β' z * d₁ + (1 - σ.sphLensSwitch β β' z) * d₂ := by
      have := convex_comb_pos hs0 hs1 hd₂ hd₁
      linarith
    have hx : 0 ≤ sw' * (σ.sphAngleOneAtOne z - σ.sphAngleTwoAtOne z) :=
      mul_nonneg_of_nonpos_of_nonpos hsw' (by linarith)
    have hin : 0 < (sw' * σ.sphAngleOneAtOne z + σ.sphLensSwitch β β' z * d₁) +
        ((0 - sw') * σ.sphAngleTwoAtOne z + (1 - σ.sphLensSwitch β β' z) * d₂) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₁ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_sphCornerOne_pos {a b β β' : ℝ} (hab : a < b) (hb : b ≤ 1) (hβ : β < β')
    {z : ℂ} (hz1 : z ∈ σ.sphDomOne) (hz2 : z ∈ σ.sphDomTwo)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2))
    (hord : σ.sphAngleOneAtOne z ≤ σ.sphAngleTwoAtOne z)
    (hlam : ((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re ≤ 0 ∨
      β' < σ.sphSideTwo z ∨ σ.sphSideTwo z < β) :
    0 < (fderiv ℝ (σ.sphCornerOne a b β β') z).det := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz2.2.1
  have hne := rotOne_ne_zero_of_domOne hs hz1
  have hne' := sphMoeb_vertexOne_ne_of_domOne hs hz1
  have hϖ : 0 < ‖σ.rotOne z‖ := norm_pos_iff.2 hne
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_sphInnerRadial (p := σ.p₁)
    (le_trans (by norm_num) σ.two_le_p₁) hab hb (sphTau_pos hs 0).le (sphTau_lt_one hs 0) hϖ
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleCornerOne_circ hs (a := a) (b := b) hβ hz1 hz2
    hψ hpos1 hpos2 hord hlam
  have hρ : DifferentiableAt ℝ (fun u => ‖σ.rotOne u‖) z :=
    (contDiffAt_norm_rotOne hs hv1 hne).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.sphAngleCornerOne a b β β') z :=
    (contDiffAt_sphAngleCornerOne hs a b β β' hz1 hz2 hψ hpos1 hpos2).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖σ.rotOne (sphCirc σ.vertexOne z t)‖ = ‖σ.rotOne z‖ := by
    filter_upwards [eventually_rotOne_sphCirc hs hv1] with t ht
    rw [ht, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hγ : HasDerivAt (sphCirc σ.vertexOne z) (sphRayDir σ.vertexOne z * I) 0 := by
    have := hasDerivAt_sphCirc hv1
    rwa [sphCirc_deriv_eq] at this
  have hρN : HasDerivAt (fun t : ℝ => ‖σ.rotOne (z + t * sphRayDir σ.vertexOne z)‖)
      ‖sphMoeb σ.vertexOne z‖ 0 := by
    have h := hasDerivAt_norm_sphMoeb_ray hv1 hne'
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => norm_rotOne_sph hs _)
  have key := det_fderiv_polar (c := ((3 / 2 : ℝ) : ℂ))
    (S := sphInnerRadial σ.p₁ a b (σ.sphTau 0)) (ρ := fun u => ‖σ.rotOne u‖)
    (Θ := σ.sphAngleCornerOne a b β β') (N := sphRayDir σ.vertexOne z) hSd hρ hΘd hγ
    (sphCirc_zero hv1) hργ hΘγ hρN (EuclidShape.hasDerivAt_comp_ray hΘd)
  rw [EuclidShape.cross_mul_I] at key
  have hN : sphRayDir σ.vertexOne z ≠ 0 := by
    intro h0
    have := sphRayDir_mul (a := σ.vertexOne) hv1
    rw [h0, mul_zero] at this
    exact hne' this.symm
  have hS0 := sphInnerRadial_pos (p := σ.p₁) (a := a) (b := b) (sphTau_pos hs 0).le
    (sphTau_lt_one hs 0) hϖ
  have hm := norm_pos_iff.2 hne'
  exact EuclidShape.det_pos_of_polar (by positivity) key (by positivity)

omit hs in
theorem sphCornerOne_eq_apex {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a) {z : ℂ}
    (hd : ‖σ.rotOne z‖ ≤ a) (hψ : σ.rotOne z = 0 ∨ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    σ.sphCornerOne a b β β' z = 3 / 2 + σ.rotOne z ^ σ.p₁ / 2 := by
  have hτ : coneStep a b ‖σ.rotOne z‖ = 0 := coneStep_eq_zero hab hd
  have hp : σ.p₁ ≠ 0 := by have := σ.two_le_p₁; omega
  rcases hψ with h | h
  · simp only [sphCornerOne, sphInnerRadial, h, norm_zero]
    rw [coneStep_eq_zero hab ha]
    simp [zero_pow hp]
  · rw [sphCornerOne, sphAngleCornerOne, sphInnerRadial, hτ, EuclidShape.polar_pow h, sphPsiOne]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

theorem sphCornerOne_eq_bridgeOne {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ σ.sphDomOne) (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hd : b ≤ ‖σ.rotOne z‖) (hsw : β' ≤ σ.sphSideTwo z) :
    σ.sphCornerOne a b β β' z = σ.sphBridgeOne z := by
  have hm : σ.sphModOne z = 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖σ.rotOne z‖ := by
    rw [sphModOne, sphCanon_zero_eq_F hs, norm_rotOne_sph hs]
  rw [sphBridgeOne_eq_polar_one hs hz1 hpos1, sphCornerOne, sphAngleCornerOne, sphInnerRadial,
    coneStep_eq_one hab hd, sphLensSwitch, coneStep_eq_one hβ hsw, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, zero_div]

theorem sphCornerOne_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ σ.sphDomTwo) (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2))
    (hd : b ≤ ‖σ.rotOne z‖) (hsw : σ.sphSideTwo z ≤ β) :
    σ.sphCornerOne a b β β' z = σ.sphBridgeTwo z := by
  have hm : σ.sphModOne z = 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖σ.rotOne z‖ := by
    rw [sphModOne, sphCanon_zero_eq_F hs, norm_rotOne_sph hs]
  rw [sphBridgeTwo_eq_polar_one hs hz2 hpos2, sphCornerOne, sphAngleCornerOne, sphInnerRadial,
    coneStep_eq_one hab hd, sphLensSwitch, coneStep_eq_zero hβ hsw, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add, sub_zero, zero_div]

theorem sphCornerOne_refl_one (a b β β' : ℝ) {z : ℂ}
    (h : coneStep a b ‖σ.rotOne z‖ = 0 ∨
      (σ.sphLensSwitch β β' z = 1 ∧ σ.sphLensSwitch β β' (σ.refl 1 z) = 1)) :
    σ.sphCornerOne a b β β' (σ.refl 1 z) = conj (σ.sphCornerOne a b β β' z) := by
  have hn : ‖σ.rotOne (σ.refl 1 z)‖ = ‖σ.rotOne z‖ := by
    rw [rotOne_refl_one_sph hs, Complex.norm_conj]
  have hΘ : σ.sphAngleCornerOne a b β β' (σ.refl 1 z) = -σ.sphAngleCornerOne a b β β' z := by
    rw [sphAngleCornerOne, sphAngleCornerOne, hn, sphPsiOne_refl_one hs,
      sphAngleOneAtOne_refl_one hs]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [sphCornerOne, sphCornerOne, hn, hΘ, EuclidShape.conj_polar]

theorem sphPsiOne_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - σ.sphPsiOne z) (h2 : 2 * σ.θ₁ - σ.sphPsiOne z < Real.pi) :
    σ.sphPsiOne (σ.refl 2 z) = 2 * σ.θ₁ - σ.sphPsiOne z := by
  rw [sphPsiOne, rotOne_refl_two_sph hs hz hv1, EuclidShape.two_mul_ofReal_mul_I]
  exact EuclidShape.discAngle_exp_mul_conj hψ h1 h2

theorem sphCornerOne_refl_two (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - σ.sphPsiOne z) (h2 : 2 * σ.θ₁ - σ.sphPsiOne z < Real.pi)
    (h : coneStep a b ‖σ.rotOne z‖ = 0 ∨
      (σ.sphLensSwitch β β' z = 0 ∧ σ.sphLensSwitch β β' (σ.refl 2 z) = 0)) :
    σ.sphCornerOne a b β β' (σ.refl 2 z) = conj (σ.sphCornerOne a b β β' z) := by
  have hn : ‖σ.rotOne (σ.refl 2 z)‖ = ‖σ.rotOne z‖ := by
    rw [rotOne_refl_two_sph hs hz hv1, norm_mul, Complex.norm_conj, exp_two_mul_eq_sph, norm_mul,
      norm_exp_mul_I_sph', one_mul, one_mul]
  have hp : (σ.p₁ : ℝ) * σ.θ₁ = Real.pi := by rw [mul_comm]; exact σ.θ₁_mul_sph
  have hΘ : σ.sphAngleCornerOne a b β β' (σ.refl 2 z) =
      2 * Real.pi - σ.sphAngleCornerOne a b β β' z := by
    rw [sphAngleCornerOne, sphAngleCornerOne, hn, sphPsiOne_refl_two hs hz hv1 hψ h1 h2,
      sphAngleTwoAtOne_refl_two hs hz hv1]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b ‖σ.rotOne z‖) * hp
  rw [sphCornerOne, sphCornerOne, hn, hΘ, EuclidShape.exp_two_pi_sub, EuclidShape.conj_polar]

end Spherical

end CompactShape

end GC.Seifert
