import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCornerOne

/-!
# The corner of the spherical compact fold at `v₂`

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The corner at `v₂` is the polar map about `-3/2`
`sphCornerTwo = -3/2 + S(ϖ₂) e^{iΘ₂}` with `ϖ₂ = ‖rotTwo‖`, `S = sphInnerRadial p₂ a b τ₂` and
`Θ₂ = (1 - τ) p₂ ψ₂ + τ ((1 - s) · sphAngleTwoAtTwo + s · sphAngleZeroAtTwo)`, `ψ₂ = sphPsiTwo`,
with the same lens switch `s` as at `v₁` (the bridge of wall 2 within `β` of wall 2, the bridge of
wall 0 beyond `β'`). Along the circle about `v₂` the side coordinate `Im rotTwo` has derivative
`Re rotTwo`, so where the switch moves and `Re rotTwo ≥ 0` the angle is strictly increasing and the
Jacobian is positive off `v₂` (`det_fderiv_sphCornerTwo_pos`). Near `v₂` the corner is the apex
model `-3/2 + rotTwo^{p₂}/2` (`sphCornerTwo_eq_apex`); where the weights saturate it is a bridge
(`sphCornerTwo_eq_bridgeTwo`, `sphCornerTwo_eq_bridgeZero`), and it satisfies the wall identities
(`sphCornerTwo_refl_two`, `sphCornerTwo_refl_zero`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

def sphAngleCornerTwo (σ : CompactShape) (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖σ.rotTwo z‖) * (σ.p₂ * σ.sphPsiTwo z) +
    coneStep a b ‖σ.rotTwo z‖ * ((1 - σ.sphLensSwitch β β' z) * σ.sphAngleTwoAtTwo z +
      σ.sphLensSwitch β β' z * σ.sphAngleZeroAtTwo z)

def sphCornerTwo (σ : CompactShape) (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((-(3 / 2) : ℝ) : ℂ) + (sphInnerRadial σ.p₂ a b (σ.sphTau 1) ‖σ.rotTwo z‖ : ℂ) *
    exp ((σ.sphAngleCornerTwo a b β β' z : ℂ) * I)

omit σ in
theorem sphCornerTwo_eq_apex {σ : CompactShape} {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a)
    {z : ℂ} (hd : ‖σ.rotTwo z‖ ≤ a)
    (hψ : σ.rotTwo z = 0 ∨ 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    σ.sphCornerTwo a b β β' z = -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 := by
  have hτ : coneStep a b ‖σ.rotTwo z‖ = 0 := coneStep_eq_zero hab hd
  have hp : σ.p₂ ≠ 0 := by have := σ.two_le_p₂; omega
  rcases hψ with h | h
  · simp only [sphCornerTwo, sphInnerRadial, h, norm_zero]
    rw [coneStep_eq_zero hab ha]
    simp [zero_pow hp]
  · rw [sphCornerTwo, sphAngleCornerTwo, sphInnerRadial, hτ, EuclidShape.polar_pow h, sphPsiTwo]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

section Spherical

variable (hs : σ.curv = .spherical)
include hs

omit hs in
theorem rotTwo_ne_zero_of_domTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) : σ.rotTwo z ≠ 0 :=
  ne_zero_of_pos_norm_add_re_sph hz.2.2.1

theorem contDiffAt_norm_rotTwo {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0)
    (hne : σ.rotTwo z ≠ 0) : ContDiffAt ℝ ∞ (fun u => ‖σ.rotTwo u‖) z :=
  (contDiffAt_rotTwo_sph hs hv2).norm ℝ hne

theorem contDiffAt_sphAngleCornerTwo (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ σ.sphDomTwo)
    (hz0 : z ∈ σ.sphDomZero)
    (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.sphAngleCornerTwo a b β β') z := by
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := hz2.1
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b ‖σ.rotTwo u‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (contDiffAt_norm_rotTwo hs hv2 (rotTwo_ne_zero_of_domTwo hz2))
  have hsw := contDiffAt_sphLensSwitch hs β β' hv2
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul
    (contDiffAt_sphPsiTwo hs hv2 hz2.2.2.1))).add (hτ.mul (((contDiffAt_const.sub hsw).mul
      (contDiffAt_sphAngleTwoAtTwo hs hz2 hpos2)).add (hsw.mul
        (contDiffAt_sphAngleZeroAtTwo hs hz0 hpos0))))

theorem exists_hasDerivAt_sphAngleCornerTwo_circ {a b β β' : ℝ} (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ σ.sphDomTwo) (hz0 : z ∈ σ.sphDomZero)
    (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2))
    (hord : σ.sphAngleTwoAtTwo z ≤ σ.sphAngleZeroAtTwo z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < σ.sphSideTwo z ∨ σ.sphSideTwo z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => σ.sphAngleCornerTwo a b β β' (sphCirc σ.vertexTwo z t)) D 0 := by
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := hz2.1
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  obtain ⟨d₂, hd₂, h₂⟩ := exists_hasDerivAt_sphAngleTwoAtTwo hs hz2 hpos2
  obtain ⟨d₀, hd₀, h₀⟩ := exists_hasDerivAt_sphAngleZeroAtTwo hs hz0 hpos0
  have hψd := hasDerivAt_sphPsiTwo_sphCirc hs hv2 hz2.2.2.1
  have hY := hasDerivAt_sphSideTwo_sphCirc hs hv2
  have hsw : HasDerivAt (fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t))
      (deriv (coneStep β β') (σ.sphSideTwo z) * (σ.rotTwo z).re) 0 := by
    have h := (hasDerivAt_coneStep β β' (σ.sphSideTwo (sphCirc σ.vertexTwo z 0))).comp
      (0 : ℝ) hY
    rw [sphCirc_zero hv2'] at h
    exact h
  have hsw' : 0 ≤ deriv (coneStep β β') (σ.sphSideTwo z) * (σ.rotTwo z).re :=
    EuclidShape.lensSwitch_deriv_nonneg hβ hlam
  set τ₀ := coneStep a b ‖σ.rotTwo z‖ with hτ₀
  set sw' := deriv (coneStep β β') (σ.sphSideTwo z) * (σ.rotTwo z).re
  have hΘγ : HasDerivAt (fun t => σ.sphAngleCornerTwo a b β β' (sphCirc σ.vertexTwo z t))
      ((1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * σ.sphAngleTwoAtTwo z +
        (1 - σ.sphLensSwitch β β' z) * d₂) + (sw' * σ.sphAngleZeroAtTwo z +
          σ.sphLensSwitch β β' z * d₀))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₂ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul
        h₂).add (hsw.mul h₀)))
    have e : (fun t => (1 - τ₀) * (σ.p₂ * σ.sphPsiTwo (sphCirc σ.vertexTwo z t)) +
        τ₀ * ((1 - σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t)) *
          σ.sphAngleTwoAtTwo (sphCirc σ.vertexTwo z t) +
          σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t) *
          σ.sphAngleZeroAtTwo (sphCirc σ.vertexTwo z t))) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₂ : ℝ) * σ.sphPsiTwo (sphCirc σ.vertexTwo z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) -
          fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t)) *
          (fun t => σ.sphAngleTwoAtTwo (sphCirc σ.vertexTwo z t)) +
          (fun t => σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t)) *
          (fun t => σ.sphAngleZeroAtTwo (sphCirc σ.vertexTwo z t))) := by
      funext t
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    have h' : HasDerivAt (fun t => (1 - τ₀) * (σ.p₂ * σ.sphPsiTwo (sphCirc σ.vertexTwo z t)) +
        τ₀ * ((1 - σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t)) *
          σ.sphAngleTwoAtTwo (sphCirc σ.vertexTwo z t) +
          σ.sphLensSwitch β β' (sphCirc σ.vertexTwo z t) *
          σ.sphAngleZeroAtTwo (sphCirc σ.vertexTwo z t)))
        ((1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * σ.sphAngleTwoAtTwo z +
          (1 - σ.sphLensSwitch β β' z) * d₂) + (sw' * σ.sphAngleZeroAtTwo z +
            σ.sphLensSwitch β β' z * d₀))) 0 := by
      rw [e]
      convert h using 1
      simp only [sphCirc_zero hv2', Pi.sub_apply, zero_mul, zero_add]
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [eventually_rotTwo_sphCirc hs hv2] with t ht
    rw [sphAngleCornerTwo, ht, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hpR : (0 : ℝ) < σ.p₂ := by exact_mod_cast le_trans (by norm_num) σ.two_le_p₂
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.sphLensSwitch β β' z := coneStep_nonneg _ _ _
  have hs1 : σ.sphLensSwitch β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * σ.sphAngleTwoAtTwo z +
      (1 - σ.sphLensSwitch β β' z) * d₂) + (sw' * σ.sphAngleZeroAtTwo z +
        σ.sphLensSwitch β β' z * d₀)) := by
    have hb : 0 < (1 - σ.sphLensSwitch β β' z) * d₂ + σ.sphLensSwitch β β' z * d₀ :=
      convex_comb_pos hs0 hs1 hd₂ hd₀
    have hx : 0 ≤ sw' * (σ.sphAngleZeroAtTwo z - σ.sphAngleTwoAtTwo z) :=
      mul_nonneg hsw' (by linarith)
    have hin : 0 < ((0 - sw') * σ.sphAngleTwoAtTwo z + (1 - σ.sphLensSwitch β β' z) * d₂) +
        (sw' * σ.sphAngleZeroAtTwo z + σ.sphLensSwitch β β' z * d₀) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₂ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_sphCornerTwo_pos {a b β β' : ℝ} (hab : a < b) (hb : b ≤ 1) (hβ : β < β')
    {z : ℂ} (hz2 : z ∈ σ.sphDomTwo) (hz0 : z ∈ σ.sphDomZero)
    (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2))
    (hord : σ.sphAngleTwoAtTwo z ≤ σ.sphAngleZeroAtTwo z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < σ.sphSideTwo z ∨ σ.sphSideTwo z < β) :
    0 < (fderiv ℝ (σ.sphCornerTwo a b β β') z).det := by
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := hz2.1
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have hne := rotTwo_ne_zero_of_domTwo hz2
  have hne' : sphMoeb σ.vertexTwo z ≠ 0 := sphMoeb_vertexTwo_ne_of_domTwo hs hz2
  have hϖ : 0 < ‖σ.rotTwo z‖ := norm_pos_iff.2 hne
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_sphInnerRadial (p := σ.p₂)
    (le_trans (by norm_num) σ.two_le_p₂) hab hb (sphTau_pos hs 1).le (sphTau_lt_one hs 1) hϖ
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleCornerTwo_circ hs (a := a) (b := b) hβ hz2 hz0
    hpos2 hpos0 hord hlam
  have hρ : DifferentiableAt ℝ (fun u => ‖σ.rotTwo u‖) z :=
    (contDiffAt_norm_rotTwo hs hv2 hne).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.sphAngleCornerTwo a b β β') z :=
    (contDiffAt_sphAngleCornerTwo hs a b β β' hz2 hz0 hpos2 hpos0).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖σ.rotTwo (sphCirc σ.vertexTwo z t)‖ = ‖σ.rotTwo z‖ := by
    filter_upwards [eventually_rotTwo_sphCirc hs hv2] with t ht
    rw [ht, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hγ : HasDerivAt (sphCirc σ.vertexTwo z) (sphRayDir σ.vertexTwo z * I) 0 := by
    have := hasDerivAt_sphCirc hv2'
    rwa [sphCirc_deriv_eq] at this
  have hρN : HasDerivAt (fun t : ℝ => ‖σ.rotTwo (z + t * sphRayDir σ.vertexTwo z)‖)
      ‖sphMoeb σ.vertexTwo z‖ 0 := by
    have h := hasDerivAt_norm_sphMoeb_ray hv2' hne'
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => norm_rotTwo_sph hs _)
  have key := det_fderiv_polar (c := ((-(3 / 2) : ℝ) : ℂ))
    (S := sphInnerRadial σ.p₂ a b (σ.sphTau 1)) (ρ := fun u => ‖σ.rotTwo u‖)
    (Θ := σ.sphAngleCornerTwo a b β β') (N := sphRayDir σ.vertexTwo z) hSd hρ hΘd hγ
    (sphCirc_zero hv2') hργ hΘγ hρN (EuclidShape.hasDerivAt_comp_ray hΘd)
  rw [EuclidShape.cross_mul_I] at key
  have hN : sphRayDir σ.vertexTwo z ≠ 0 := by
    intro h0
    have := sphRayDir_mul (a := σ.vertexTwo) hv2'
    rw [h0, mul_zero] at this
    exact hne' this.symm
  have hS0 := sphInnerRadial_pos (p := σ.p₂) (a := a) (b := b) (sphTau_pos hs 1).le
    (sphTau_lt_one hs 1) hϖ
  have hm := norm_pos_iff.2 hne'
  exact EuclidShape.det_pos_of_polar (by positivity) key (by positivity)

theorem sphCornerTwo_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ σ.sphDomTwo) (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hd : b ≤ ‖σ.rotTwo z‖) (hsw : σ.sphSideTwo z ≤ β) :
    σ.sphCornerTwo a b β β' z = σ.sphBridgeTwo z := by
  have hm : σ.sphModTwo z = 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 1) ‖σ.rotTwo z‖ := by
    rw [sphModTwo, sphCanon_one_eq_F hs, norm_rotTwo_sph hs]
  rw [sphBridgeTwo_eq_polar_two hs hz2 hpos2, sphCornerTwo, sphAngleCornerTwo, sphInnerRadial,
    coneStep_eq_one hab hd, sphLensSwitch, coneStep_eq_zero hβ hsw, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero, zero_div]

theorem sphCornerTwo_eq_bridgeZero {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz0 : z ∈ σ.sphDomZero) (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2))
    (hd : b ≤ ‖σ.rotTwo z‖) (hsw : β' ≤ σ.sphSideTwo z) :
    σ.sphCornerTwo a b β β' z = σ.sphBridgeZero z := by
  have hm : σ.sphModTwo z = 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 1) ‖σ.rotTwo z‖ := by
    rw [sphModTwo, sphCanon_one_eq_F hs, norm_rotTwo_sph hs]
  rw [sphBridgeZero_eq_polar_two hs hz0 hpos0, sphCornerTwo, sphAngleCornerTwo, sphInnerRadial,
    coneStep_eq_one hab hd, sphLensSwitch, coneStep_eq_one hβ hsw, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add, zero_div]

theorem sphCornerTwo_refl_two (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h : coneStep a b ‖σ.rotTwo z‖ = 0 ∨
      (σ.sphLensSwitch β β' z = 0 ∧ σ.sphLensSwitch β β' (σ.refl 2 z) = 0)) :
    σ.sphCornerTwo a b β β' (σ.refl 2 z) = conj (σ.sphCornerTwo a b β β' z) := by
  have hn : ‖σ.rotTwo (σ.refl 2 z)‖ = ‖σ.rotTwo z‖ := by
    rw [rotTwo_refl_two_sph hs hz, Complex.norm_conj]
  have hΘ : σ.sphAngleCornerTwo a b β β' (σ.refl 2 z) = -σ.sphAngleCornerTwo a b β β' z := by
    rw [sphAngleCornerTwo, sphAngleCornerTwo, hn, sphPsiTwo_refl_two hs hz,
      sphAngleTwoAtTwo_refl_two hs hz hv1]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [sphCornerTwo, sphCornerTwo, hn, hΘ, EuclidShape.conj_polar]

theorem sphCornerTwo_refl_zero (a b β β' : ℝ) {z : ℂ}
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - σ.sphPsiTwo z) (h2 : 2 * σ.θ₂ - σ.sphPsiTwo z < Real.pi)
    (h : coneStep a b ‖σ.rotTwo z‖ = 0 ∨
      (σ.sphLensSwitch β β' z = 1 ∧ σ.sphLensSwitch β β' (σ.refl 0 z) = 1)) :
    σ.sphCornerTwo a b β β' (σ.refl 0 z) = conj (σ.sphCornerTwo a b β β' z) := by
  have hn : ‖σ.rotTwo (σ.refl 0 z)‖ = ‖σ.rotTwo z‖ := by
    rw [rotTwo_refl_zero_sph hs, norm_mul, Complex.norm_conj, exp_two_mul_eq_sph, norm_mul,
      norm_exp_mul_I_sph', one_mul, one_mul]
  have hp : (σ.p₂ : ℝ) * σ.θ₂ = Real.pi := by rw [mul_comm]; exact σ.θ₂_mul_sph
  have hΘ : σ.sphAngleCornerTwo a b β β' (σ.refl 0 z) =
      2 * Real.pi - σ.sphAngleCornerTwo a b β β' z := by
    rw [sphAngleCornerTwo, sphAngleCornerTwo, hn, sphPsiTwo_refl_zero hs hψ h1 h2,
      sphAngleZeroAtTwo_refl_zero hs]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b ‖σ.rotTwo z‖) * hp
  rw [sphCornerTwo, sphCornerTwo, hn, hΘ, EuclidShape.exp_two_pi_sub, EuclidShape.conj_polar]

end Spherical

end CompactShape

end GC.Seifert
