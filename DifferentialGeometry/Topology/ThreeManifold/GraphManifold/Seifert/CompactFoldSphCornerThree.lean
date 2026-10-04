import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCornerTwo

/-!
# The outer corner of the spherical compact fold at `v₃ = 0`

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The corner at `v₃ = 0` is the polar map about `0`
`sphCornerThree = S(‖z‖) e^{iΘ₃}` with the decreasing profile `S = sphOuterRadial p₃ a b τ₃` and
`Θ₃ = (1 - τ)(π - p₃ ψ₃) + τ ((1 - ν) · sphAngleZeroAtThree + ν · sphAngleOneAtThree)`,
`ψ₃ = arg z`, with the outer weight `ν = coneStep (-w) w B`,
`B = w (2ψ₃/θ₃ - 1) + (w/δ)(T₂ - T₁)` (`T₁, T₂` the profiles of `v₁, v₂`). Along the circles
about `0` the blend `B` increases where both side functions of the walls through `0` are
nonnegative (`exists_hasDerivAt_sphNuThree`), so `Θ₃` strictly decreases, and with the decreasing
profile the Jacobian is positive (`det_fderiv_sphCornerThree_pos`). Near `0` the corner is the
outer germ `compactOuterGerm p₃` (`sphCornerThree_eq_outerGerm`); where the weights saturate it
is a bridge (`sphCornerThree_eq_bridgeZero`, `sphCornerThree_eq_bridgeOne`), and it satisfies the
wall identities (`sphCornerThree_refl_zero`, `sphCornerThree_refl_one`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

def sphBlendThree (σ : CompactShape) (w δ : ℝ) (z : ℂ) : ℝ :=
  w * (2 * discAngle z / σ.θ₃ - 1) + w / δ * (σ.sphCanon 1 z - σ.sphCanon 0 z)

def sphNuThree (σ : CompactShape) (w δ : ℝ) (z : ℂ) : ℝ := coneStep (-w) w (σ.sphBlendThree w δ z)

def sphAngleCornerThree (σ : CompactShape) (a b w δ : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖z‖) * (Real.pi - σ.p₃ * discAngle z) +
    coneStep a b ‖z‖ * ((1 - σ.sphNuThree w δ z) * σ.sphAngleZeroAtThree z +
      σ.sphNuThree w δ z * σ.sphAngleOneAtThree z)

def sphCornerThree (σ : CompactShape) (a b w δ : ℝ) (z : ℂ) : ℂ :=
  ((0 : ℝ) : ℂ) + (sphOuterRadial σ.p₃ a b (σ.sphTau 2) ‖z‖ : ℂ) *
    exp ((σ.sphAngleCornerThree a b w δ z : ℂ) * I)

theorem sphCornerThree_eq_outerGerm {a b w δ : ℝ} (hab : a < b) {z : ℂ} (hd : ‖z‖ ≤ a)
    (hψ : 0 < ‖z‖ + z.re) : σ.sphCornerThree a b w δ z = compactOuterGerm σ.p₃ z := by
  rw [sphCornerThree, sphAngleCornerThree, sphOuterRadial, coneStep_eq_zero hab hd,
    compactOuterGerm, EuclidShape.conj_div_norm_eq_exp hψ, ← Complex.exp_nat_mul]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rw [show ((Real.pi - σ.p₃ * discAngle z : ℝ) : ℂ) * I =
      Real.pi * I + (σ.p₃ : ℂ) * (((-discAngle z : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast
  ring

theorem contDiff_sphOuterRadial_at (p : ℕ) (a b : ℝ) {τ x : ℝ} (h : 1 + x * τ ≠ 0) :
    ContDiffAt ℝ ∞ (sphOuterRadial p a b τ) x := by
  unfold sphOuterRadial
  exact ((contDiffAt_const.sub (contDiff_coneStep a b).contDiffAt).mul (contDiffAt_const.sub
    ((contDiffAt_id.pow p).div_const _))).add ((contDiff_coneStep a b).contDiffAt.mul
      (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_sphCanonF h))))

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem contDiffAt_sphBlendThree (w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0) (hne1 : sphMoeb σ.vertexOne z ≠ 0)
    (hv2 : 1 + conj σ.vertexTwo * z ≠ 0) (hne2 : sphMoeb σ.vertexTwo z ≠ 0) :
    ContDiffAt ℝ ∞ (σ.sphBlendThree w δ) z :=
  (contDiffAt_const.mul (((contDiffAt_const.mul (EuclidShape.contDiffAt_psiThree hψ)).div_const
    _).sub contDiffAt_const)).add (contDiffAt_const.mul ((contDiffAt_sphCanon_one hs hv2 hne2).sub
      (contDiffAt_sphCanon_zero hs hv1 hne1)))

theorem exists_hasDerivAt_sphNuThree {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hψ : 0 < ‖z‖ + z.re) (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hne1 : sphMoeb σ.vertexOne z ≠ 0) (hv2 : 1 + conj σ.vertexTwo * z ≠ 0)
    (hne2 : sphMoeb σ.vertexTwo z ≠ 0)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.sphBlendThree w δ z ∨
      σ.sphBlendThree w δ z < -w) :
    ∃ ν' : ℝ, 0 ≤ ν' ∧ HasDerivAt (fun t => σ.sphNuThree w δ (sphCirc 0 z t)) ν' 0 := by
  have hψd := hasDerivAt_sphPsiThree_sphCirc hψ
  obtain ⟨K₂, hK₂, hd₂⟩ := exists_hasDerivAt_canonF_sphCirc (a := 0) (b := σ.vertexTwo) (z := z)
    (sphTau_pos hs 1).le (by simp) (by simp) hv2 hne2
  obtain ⟨K₁, hK₁, hd₁⟩ := exists_hasDerivAt_canonF_sphCirc (a := 0) (b := σ.vertexOne) (z := z)
    (sphTau_pos hs 0).le (by simp) (by simp) hv1 hne1
  have hc : HasDerivAt (fun t => σ.sphCanon 1 (sphCirc 0 z t) - σ.sphCanon 0 (sphCirc 0 z t))
      (σ.sphTTwoThree * σ.wallSide 0 z * K₂ + σ.sphTOneThree * σ.wallSide 1 z * K₁) 0 := by
    have e : (fun t => σ.sphCanon 1 (sphCirc 0 z t) - σ.sphCanon 0 (sphCirc 0 z t)) =
        fun t => sphCanonF (σ.sphTau 1) ‖sphMoeb σ.vertexTwo (sphCirc 0 z t)‖ -
          sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne (sphCirc 0 z t)‖ := by
      funext t
      rw [sphCanon_one_eq_F hs, sphCanon_zero_eq_F hs]
    rw [e]
    refine (hd₂.sub hd₁).congr_deriv ?_
    rw [sphMoeb_zero, sphMoeb_zero, sphMoeb_zero, im_conj_vertexTwo_mul, im_conj_vertexOne_mul]
    ring
  have hB : HasDerivAt (fun t => σ.sphBlendThree w δ (sphCirc 0 z t))
      (w * (2 * 1 / σ.θ₃) + w / δ * (σ.sphTTwoThree * σ.wallSide 0 z * K₂ +
        σ.sphTOneThree * σ.wallSide 1 z * K₁)) 0 :=
    ((((hψd.const_mul 2).div_const σ.θ₃).sub_const 1).const_mul w).add (hc.const_mul (w / δ))
  have hN := (hasDerivAt_coneStep (-w) w (σ.sphBlendThree w δ (sphCirc 0 z 0))).comp (0 : ℝ) hB
  rw [sphCirc_zero (by simp)] at hN
  refine ⟨_, ?_, hN⟩
  have hwlt : -w < w := by linarith
  rcases hside with ⟨h0', h1'⟩ | h | h
  · apply mul_nonneg (deriv_coneStep_nonneg hwlt _)
    have := σ.θ₃_pos_sph
    have := tTwoThree_pos_sph hs
    have := tOneThree_pos_sph hs
    positivity
  · rw [deriv_coneStep_eq_zero_of_lt hwlt h, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hwlt h, zero_mul]

theorem contDiffAt_sphAngleCornerThree (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz0 : z ∈ σ.sphDomZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re) :
    ContDiffAt ℝ ∞ (σ.sphAngleCornerThree a b w δ) z := by
  have hτ : ContDiffAt ℝ ∞ (fun u : ℂ => coneStep a b ‖u‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z (contDiffAt_norm ℝ (ne_zero_of_domOne hz1))
  have hν : ContDiffAt ℝ ∞ (σ.sphNuThree w δ) z :=
    (contDiff_coneStep (-w) w).contDiffAt.comp z (contDiffAt_sphBlendThree hs w δ hψ
      (one_add_conj_vertexOne_ne_of_domOne hz1) (sphMoeb_vertexOne_ne_of_domOne hs hz1)
      (one_add_vertexTwo_ne_of_domZero hz0) (sphMoeb_vertexTwo_ne_of_domZero hz0))
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.sub (contDiffAt_const.mul
    (EuclidShape.contDiffAt_psiThree hψ)))).add (hτ.mul (((contDiffAt_const.sub hν).mul
      (contDiffAt_sphAngleZeroAtThree hs hz0 hpos0)).add (hν.mul
        (contDiffAt_sphAngleOneAtThree hs hz1 hpos1))))

theorem exists_hasDerivAt_sphAngleCornerThree_circ {a b w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ)
    {z : ℂ} (hz1 : z ∈ σ.sphDomOne) (hz0 : z ∈ σ.sphDomZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re)
    (hord : σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.sphBlendThree w δ z ∨
      σ.sphBlendThree w δ z < -w) :
    ∃ D : ℝ, D < 0 ∧
      HasDerivAt (fun t => σ.sphAngleCornerThree a b w δ (sphCirc 0 z t)) D 0 := by
  obtain ⟨d₀, hd₀, h₀⟩ := exists_hasDerivAt_sphAngleZeroAtThree hs hz0 hpos0
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_sphAngleOneAtThree hs hz1 hpos1
  obtain ⟨ν', hν', hν⟩ := exists_hasDerivAt_sphNuThree hs hw hδ hψ
    (one_add_conj_vertexOne_ne_of_domOne hz1) (sphMoeb_vertexOne_ne_of_domOne hs hz1)
    (one_add_vertexTwo_ne_of_domZero hz0) (sphMoeb_vertexTwo_ne_of_domZero hz0) hside
  have hψd := hasDerivAt_sphPsiThree_sphCirc hψ
  set τ₀ := coneStep a b ‖z‖ with hτ₀
  have hΘγ : HasDerivAt (fun t => σ.sphAngleCornerThree a b w δ (sphCirc 0 z t))
      ((1 - τ₀) * (0 - σ.p₃ * 1) + τ₀ * (((0 - ν') * σ.sphAngleZeroAtThree z +
        (1 - σ.sphNuThree w δ z) * d₀) + (ν' * σ.sphAngleOneAtThree z +
          σ.sphNuThree w δ z * d₁))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul ((hasDerivAt_const (0 : ℝ) Real.pi).sub
      (hψd.const_mul (σ.p₃ : ℝ)))).add ((hasDerivAt_const (0 : ℝ) τ₀).mul
        ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul h₀).add (hν.mul h₁)))
    have hn : ∀ t, ‖sphCirc 0 z t‖ = ‖z‖ := by
      intro t
      rw [sphCirc_center_zero, norm_mul_exp_I_sph]
    have e : (fun t => σ.sphAngleCornerThree a b w δ (sphCirc 0 z t)) =
        (fun _ => 1 - τ₀) * ((fun _ => Real.pi) -
          fun t => (σ.p₃ : ℝ) * discAngle (sphCirc 0 z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) - fun t => σ.sphNuThree w δ (sphCirc 0 z t)) *
          (fun t => σ.sphAngleZeroAtThree (sphCirc 0 z t)) +
          (fun t => σ.sphNuThree w δ (sphCirc 0 z t)) *
          (fun t => σ.sphAngleOneAtThree (sphCirc 0 z t))) := by
      funext t
      simp only [sphAngleCornerThree, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hn, hτ₀]
    rw [e]
    convert h using 1
    simp only [sphCirc_zero (show (1 : ℂ) + conj 0 * z ≠ 0 by simp), Pi.sub_apply, zero_mul,
      zero_add]
  have hpR : (0 : ℝ) < σ.p₃ := by exact_mod_cast le_trans (by norm_num) σ.two_le_p₃
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ σ.sphNuThree w δ z := coneStep_nonneg _ _ _
  have hs1 : σ.sphNuThree w δ z ≤ 1 := coneStep_le_one _ _ _
  have hD : (1 - τ₀) * (0 - σ.p₃ * 1) + τ₀ * (((0 - ν') * σ.sphAngleZeroAtThree z +
      (1 - σ.sphNuThree w δ z) * d₀) + (ν' * σ.sphAngleOneAtThree z +
        σ.sphNuThree w δ z * d₁)) < 0 := by
    have hb : 0 < (1 - σ.sphNuThree w δ z) * -d₀ + σ.sphNuThree w δ z * -d₁ :=
      convex_comb_pos hs0 hs1 (by linarith) (by linarith)
    have hx : ν' * (σ.sphAngleOneAtThree z - σ.sphAngleZeroAtThree z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hν' (by linarith)
    have hin : 0 < -(((0 - ν') * σ.sphAngleZeroAtThree z + (1 - σ.sphNuThree w δ z) * d₀) +
        (ν' * σ.sphAngleOneAtThree z + σ.sphNuThree w δ z * d₁)) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₃ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_sphCornerThree_pos {a b w δ : ℝ} (hab : a < b) (hb : b ≤ 1 / 5)
    (hw : 0 < w) (hδ : 0 < δ) {z : ℂ} (hz1 : z ∈ σ.sphDomOne) (hz0 : z ∈ σ.sphDomZero)
    (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re)
    (hord : σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < σ.sphBlendThree w δ z ∨
      σ.sphBlendThree w δ z < -w) :
    0 < (fderiv ℝ (σ.sphCornerThree a b w δ) z).det := by
  have hz0' := ne_zero_of_domOne hz1
  have hd : 0 < ‖z‖ := norm_pos_iff.2 hz0'
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_sphOuterRadial (p := σ.p₃)
    (le_trans (by norm_num) σ.two_le_p₃) hab hb (sphTau_pos hs 2).le (sphTau_lt_one hs 2) hd
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleCornerThree_circ hs (a := a) (b := b) hw hδ
    hz1 hz0 hψ hpos1 hpos0 hord hside
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z :=
    (contDiffAt_norm ℝ hz0' : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (σ.sphAngleCornerThree a b w δ) z :=
    (contDiffAt_sphAngleCornerThree hs a b w δ hz1 hz0 hψ hpos1 hpos0).differentiableAt
      (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖sphCirc 0 z t‖ = ‖z‖ := Eventually.of_forall fun t => by
    rw [sphCirc_center_zero, norm_mul_exp_I_sph]
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * z‖) ‖z‖ 0 := by
    have h := EuclidShape.hasDerivAt_norm_ray z 0
    simp only [sub_zero] at h
    exact h
  have key := det_fderiv_polar (c := ((0 : ℝ) : ℂ))
    (S := sphOuterRadial σ.p₃ a b (σ.sphTau 2)) (ρ := fun u : ℂ => ‖u‖)
    (Θ := σ.sphAngleCornerThree a b w δ) (N := z) hSd hρ hΘd
    (hasDerivAt_sphCirc_center_zero z) (sphCirc_zero (by simp)) hργ hΘγ hρN
    (EuclidShape.hasDerivAt_comp_ray hΘd)
  rw [EuclidShape.cross_mul_I] at key
  have hS0 := sphOuterRadial_pos (p := σ.p₃) hab hb (sphTau_pos hs 2).le hd.le
    (by linarith [hz1.2.2.2.2.1, norm_exp_neg_mul_sph (σ := σ) z])
  have hpos : 0 < sphOuterRadial σ.p₃ a b (σ.sphTau 2) ‖z‖ * S' * D * ‖z‖ := by
    have := mul_pos_of_neg_of_neg hS' hD
    rw [show sphOuterRadial σ.p₃ a b (σ.sphTau 2) ‖z‖ * S' * D * ‖z‖ =
      sphOuterRadial σ.p₃ a b (σ.sphTau 2) ‖z‖ * (S' * D) * ‖z‖ by ring]
    positivity
  exact EuclidShape.det_pos_of_polar (by positivity) key hpos

theorem sphCornerThree_eq_bridgeZero {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz0 : z ∈ σ.sphDomZero) (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re)
    (hd : b ≤ ‖z‖) (hν : σ.sphBlendThree w δ z ≤ -w) :
    σ.sphCornerThree a b w δ z = σ.sphBridgeZero z := by
  have hm : σ.sphModThree z = 3 - compactProfileSlope * sphCanonF (σ.sphTau 2) ‖z‖ := by
    rw [sphModThree, sphCanon_two_eq_F, sphMoeb_zero]
  rw [sphBridgeZero_eq_polar_three hs hz0 hpos0, sphCornerThree, sphAngleCornerThree,
    sphOuterRadial, coneStep_eq_one hab hd, sphNuThree, coneStep_eq_zero (by linarith) hν, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, sub_zero]

theorem sphCornerThree_eq_bridgeOne {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz1 : z ∈ σ.sphDomOne) (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hd : b ≤ ‖z‖) (hν : w ≤ σ.sphBlendThree w δ z) :
    σ.sphCornerThree a b w δ z = σ.sphBridgeOne z := by
  have hm : σ.sphModThree z = 3 - compactProfileSlope * sphCanonF (σ.sphTau 2) ‖z‖ := by
    rw [sphModThree, sphCanon_two_eq_F, sphMoeb_zero]
  rw [sphBridgeOne_eq_polar_three hs hz1 hpos1, sphCornerThree, sphAngleCornerThree,
    sphOuterRadial, coneStep_eq_one hab hd, sphNuThree, coneStep_eq_one (by linarith) hν, hm]
  simp only [sub_self, zero_mul, one_mul, zero_add]

theorem sphCornerThree_refl_zero (a b w δ : ℝ) {z : ℂ}
    (h : coneStep a b ‖z‖ = 0 ∨
      (σ.sphNuThree w δ z = 0 ∧ σ.sphNuThree w δ (σ.refl 0 z) = 0)) :
    σ.sphCornerThree a b w δ (σ.refl 0 z) = conj (σ.sphCornerThree a b w δ z) := by
  have hn : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z
  have hΘ : σ.sphAngleCornerThree a b w δ (σ.refl 0 z) =
      2 * Real.pi - σ.sphAngleCornerThree a b w δ z := by
    rw [sphAngleCornerThree, sphAngleCornerThree, hn, sphPsiThree_refl_zero,
      sphAngleZeroAtThree_refl_zero hs]
    rcases h with h | ⟨h1, h2⟩
    · rw [h]
      ring
    · rw [h1, h2]
      ring
  rw [sphCornerThree, sphCornerThree, hn, hΘ, EuclidShape.exp_two_pi_sub, EuclidShape.conj_polar]

theorem sphCornerThree_refl_one (a b w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi)
    (h : coneStep a b ‖z‖ = 0 ∨
      (σ.sphNuThree w δ z = 1 ∧ σ.sphNuThree w δ (σ.refl 1 z) = 1)) :
    σ.sphCornerThree a b w δ (σ.refl 1 z) = conj (σ.sphCornerThree a b w δ z) := by
  have hn : ‖σ.refl 1 z‖ = ‖z‖ := norm_refl_one_sph z
  have hp : (σ.p₃ : ℝ) * σ.θ₃ = Real.pi := by rw [mul_comm]; exact σ.θ₃_mul_sph
  have hΘ : σ.sphAngleCornerThree a b w δ (σ.refl 1 z) = -σ.sphAngleCornerThree a b w δ z := by
    rw [sphAngleCornerThree, sphAngleCornerThree, hn, sphPsiThree_refl_one hψ h1 h2,
      sphAngleOneAtThree_refl_one hs]
    rcases h with h | ⟨h3, h4⟩
    · rw [h]
      linear_combination (-2) * hp
    · rw [h3, h4]
      linear_combination (-2) * (1 - coneStep a b ‖z‖) * hp
  rw [sphCornerThree, sphCornerThree, hn, hΘ, EuclidShape.conj_polar]

end Spherical

end CompactShape

end GC.Seifert
