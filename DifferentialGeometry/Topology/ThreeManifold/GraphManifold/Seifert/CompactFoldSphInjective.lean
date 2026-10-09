import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphValid
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidInjective

/-!
# Injectivity of the spherical compact fold before the core replacement

Lane CF-S3i, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5; the flat model is `CompactFoldEuclidInjective`).
The map `sphPreFold` is injective on the whole triangle minus `v₃ = 0` (`injOn_sphPreFold`); the
core is not used. With `cⱼ = sphCornerRad j = τⱼ ⊖ d` (so `sphCanonF τⱼ cⱼ = -d`) and
`κ = compactProfileSlope`, the triangle splits into four regions:
* `sphRegionOne = {‖rotOne‖ < c₁}`: `sphPreFold = sphFoldCornerOne`, `‖E - 3/2‖` is the inner
  radial profile of `‖rotOne‖`, below `3/2 - κd`;
* `sphRegionTwo = {‖rotTwo‖ < c₂}`: likewise `‖E + 3/2‖ < 3/2 - κd`;
* `sphRegionLens = {‖rotOne‖ ≥ c₁, ‖rotTwo‖ ≥ c₂, Im rotTwo < β}`: `sphPreFold = sphBridgeTwo`,
  `‖E ∓ 3/2‖ ≥ 3/2 - κd` and `‖E‖ < 3/2`;
* `sphRegionThree` (the rest, minus `0`): `sphPreFold = sphFoldCornerThree`, `‖E‖ > 13/5` and
  `‖E ∓ 3/2‖ ≥ 3/2 - κd` (the angle lies between the two bridge angles at `v₃`).
So the images are pairwise disjoint. Inside a region the modulus fixes the distance to the vertex
(the radial profiles are strictly monotone) and the angle in `[0, π]` is strictly monotone along the
arc `sphCirc` of that distance: at `v₁`, `v₂` the arc of radius `< τⱼ` lies in the triangle (an
intermediate value argument, since wall points of `T` are at distance `≥ τⱼ`), at `v₃` every
validity condition holds on the whole open sector arc (`sphValidSector_sphInj`). On the lens the
two distances and `Im rotTwo ≥ 0` fix the point.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

/-! ### Real profiles -/

theorem sphCanonF_lt_sphInj {τ x y : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x < y) :
    sphCanonF τ x < sphCanonF τ y := by
  have hx' : 0 < 1 + x * τ := by positivity
  have hy' : 0 < 1 + y * τ := by positivity
  unfold sphCanonF
  rw [div_lt_div_iff₀ hx' hy']
  nlinarith [mul_pos (sub_pos.2 hxy) (by positivity : (0 : ℝ) < 1 + τ ^ 2)]

theorem sphCanonF_le_sphInj {τ x y : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    sphCanonF τ x ≤ sphCanonF τ y := by
  rcases hxy.eq_or_lt with h | h
  · rw [h]
  · exact (sphCanonF_lt_sphInj hτ hx (hx.trans h.le) h).le

theorem sphCanonF_inj_sphInj {τ x y : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : sphCanonF τ x = sphCanonF τ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (sphCanonF_lt_sphInj hτ hx hy hxy).ne
  · exact hxy
  · exact absurd h (sphCanonF_lt_sphInj hτ hy hx hxy).ne'

theorem sphCanonF_shrink_sphInj {τ d : ℝ} (hτ : 0 ≤ τ) (hd : 0 ≤ d) :
    sphCanonF τ ((τ - d) / (1 + τ * d)) = -d := by
  have h1 : 0 < 1 + τ * d := by positivity
  have h2 : 0 < 1 + τ ^ 2 := by positivity
  have e1 : (τ - d) / (1 + τ * d) - τ = -d * (1 + τ ^ 2) / (1 + τ * d) := by
    field_simp
    ring
  have e2 : 1 + (τ - d) / (1 + τ * d) * τ = (1 + τ ^ 2) / (1 + τ * d) := by
    field_simp
    ring
  unfold sphCanonF
  rw [e1, e2]
  field_simp

theorem strictMonoOn_sphInnerRadial_sphInj {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (hab : a < b)
    (hb : b ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    StrictMonoOn (sphInnerRadial p a b τ) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : (0 : ℝ) ≤ x := hx
    exact (CompactShape.contDiff_sphInnerRadial_at p a b (by positivity : 1 + x * τ ≠ 0)
      ).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hx
    obtain ⟨S', hS', h⟩ := exists_hasDerivAt_sphInnerRadial hp hab hb hτ0 hτ1 hx
    rw [h.deriv]
    exact hS'

theorem strictAntiOn_sphOuterRadial_sphInj {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    StrictAntiOn (sphOuterRadial p a b τ) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : (0 : ℝ) ≤ x := hx
    exact (CompactShape.contDiff_sphOuterRadial_at p a b (by positivity : 1 + x * τ ≠ 0)
      ).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hx
    obtain ⟨S', hS', h⟩ := exists_hasDerivAt_sphOuterRadial hp hab hb hτ0 hτ1 hx
    rw [h.deriv]
    exact hS'

theorem sphInnerRadial_zero_sphInj {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    sphInnerRadial p a b τ 0 = 0 := by
  rw [sphInnerRadial, coneStep_eq_zero hab ha, zero_pow (by omega)]
  ring

theorem sphInnerRadial_of_ge_sphInj {p : ℕ} {a b τ x : ℝ} (hab : a < b) (hx : b ≤ x) :
    sphInnerRadial p a b τ x = 3 / 2 + compactProfileSlope * sphCanonF τ x := by
  rw [sphInnerRadial, coneStep_eq_one hab hx]
  ring

theorem sphOuterRadial_of_ge_sphInj {p : ℕ} {a b τ x : ℝ} (hab : a < b) (hx : b ≤ x) :
    sphOuterRadial p a b τ x = 3 - compactProfileSlope * sphCanonF τ x := by
  rw [sphOuterRadial, coneStep_eq_one hab hx]
  ring

/-! ### Arcs of the rotation coordinates -/

def sphInjArc (a u : ℂ) (ρ φ : ℝ) : ℂ := sphMoebInv a (u * ((ρ : ℂ) * exp ((φ : ℂ) * I)))

theorem sphInjArc_ne {a u : ℂ} (ha : ‖a‖ ≤ 1) (hu : ‖u‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (φ : ℝ) : 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  have hn := congrArg norm h0
  rw [norm_one, norm_mul, norm_mul, norm_mul, Complex.norm_conj, hu,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] at hn
  nlinarith [norm_nonneg a]

theorem sphMoeb_sphInjArc {a u : ℂ} {ρ φ : ℝ}
    (h : 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0) :
    sphMoeb a (sphInjArc a u ρ φ) = u * ((ρ : ℂ) * exp ((φ : ℂ) * I)) :=
  sphMoeb_sphMoebInv h

theorem one_add_conj_mul_sphInjArc {a u : ℂ} {ρ φ : ℝ}
    (h : 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0) :
    1 + conj a * sphInjArc a u ρ φ ≠ 0 := by
  rw [sphInjArc, one_add_conj_mul_sphMoebInv h]
  exact div_ne_zero (one_add_conj_mul_self_ne_sph a) h

theorem sphCirc_sphInjArc {a u : ℂ} {ρ φ : ℝ}
    (h : 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0) (t : ℝ) :
    sphCirc a (sphInjArc a u ρ φ) t = sphInjArc a u ρ (φ + t) := by
  rw [sphCirc, sphMoeb_sphInjArc h, sphInjArc]
  congr 1
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem continuous_sphInjArc {a u : ℂ} {ρ : ℝ}
    (hne : ∀ φ : ℝ, 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0) :
    Continuous (fun φ : ℝ => sphInjArc a u ρ φ) := by
  unfold sphInjArc sphMoebInv
  exact Continuous.div (by fun_prop) (by fun_prop) hne

theorem strictMonoOn_sphInjArc {a u : ℂ} {ρ : ℝ} {Θ : ℂ → ℝ} {lo hi : ℝ}
    (hne : ∀ φ : ℝ, 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0)
    (hcont : ∀ φ ∈ Icc lo hi, ContinuousAt Θ (sphInjArc a u ρ φ))
    (hder : ∀ φ ∈ Ioo lo hi, ∃ D, 0 < D ∧
      HasDerivAt (fun t => Θ (sphCirc a (sphInjArc a u ρ φ) t)) D 0) :
    StrictMonoOn (fun φ => Θ (sphInjArc a u ρ φ)) (Icc lo hi) := by
  have hγ := continuous_sphInjArc hne
  refine strictMonoOn_of_deriv_pos (convex_Icc lo hi)
    (fun φ hφ => ((hcont φ hφ).comp (f := fun φ : ℝ => sphInjArc a u ρ φ)
      hγ.continuousAt).continuousWithinAt) (fun φ hφ => ?_)
  rw [interior_Icc] at hφ
  obtain ⟨D, hD, h⟩ := hder φ hφ
  simp only [sphCirc_sphInjArc (hne φ)] at h
  rw [(hasDerivAt_of_shift' h).deriv]
  exact hD

theorem strictAntiOn_sphInjArc {a u : ℂ} {ρ : ℝ} {Θ : ℂ → ℝ} {lo hi : ℝ}
    (hne : ∀ φ : ℝ, 1 - conj a * (u * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0)
    (hcont : ∀ φ ∈ Icc lo hi, ContinuousAt Θ (sphInjArc a u ρ φ))
    (hder : ∀ φ ∈ Ioo lo hi, ∃ D, D < 0 ∧
      HasDerivAt (fun t => Θ (sphCirc a (sphInjArc a u ρ φ) t)) D 0) :
    StrictAntiOn (fun φ => Θ (sphInjArc a u ρ φ)) (Icc lo hi) := by
  have hγ := continuous_sphInjArc hne
  refine strictAntiOn_of_deriv_neg (convex_Icc lo hi)
    (fun φ hφ => ((hcont φ hφ).comp (f := fun φ : ℝ => sphInjArc a u ρ φ)
      hγ.continuousAt).continuousWithinAt) (fun φ hφ => ?_)
  rw [interior_Icc] at hφ
  obtain ⟨D, hD, h⟩ := hder φ hφ
  simp only [sphCirc_sphInjArc (hne φ)] at h
  rw [(hasDerivAt_of_shift' h).deriv]
  exact hD


theorem sphInjArc_zero_one (r φ : ℝ) : sphInjArc 0 1 r φ = (r : ℂ) * exp ((φ : ℂ) * I) := by
  simp [sphInjArc, sphMoebInv]

theorem sphInjArc_zero_one_ne (r φ : ℝ) :
    1 - conj (0 : ℂ) * (1 * ((r : ℂ) * exp ((φ : ℂ) * I))) ≠ 0 := by
  simp

theorem norm_ofReal_mul_exp_sphInj {ρ : ℝ} (hρ : 0 ≤ ρ) (φ : ℝ) :
    ‖(ρ : ℂ) * exp ((φ : ℂ) * I)‖ = ρ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρ]

theorem im_ofReal_mul_exp_sphInj (ρ φ : ℝ) : ((ρ : ℂ) * exp ((φ : ℂ) * I)).im = ρ * Real.sin φ := by
  rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem im_exp_conj_ofReal_mul_exp_sphInj (θ ρ φ : ℝ) :
    (exp ((θ : ℂ) * I) * conj ((ρ : ℂ) * exp ((φ : ℂ) * I))).im = ρ * Real.sin (θ - φ) := by
  rw [CompactShape.im_exp_mul_conj_sph, re_ofReal_mul, im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.sin_sub]
  ring

theorem sin_nonneg_sphInj {θ φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    0 ≤ Real.sin φ ∧ 0 ≤ Real.sin (θ - φ) := by
  have hpi := Real.pi_pos
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith),
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)⟩

theorem nonneg_of_mul_pos_right_sphInj {W P Q : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (h : W * P = Q) :
    0 ≤ W := by
  by_contra hW
  have := mul_neg_of_neg_of_pos (not_le.1 hW) hP
  linarith

namespace CompactShape

variable {σ : CompactShape}

def sphInjArcOne (σ : CompactShape) (ρ φ : ℝ) : ℂ :=
  sphInjArc σ.vertexOne (-exp ((σ.θ₃ : ℂ) * I)) ρ φ

def sphInjArcTwo (σ : CompactShape) (ρ φ : ℝ) : ℂ :=
  sphInjArc σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I))) ρ φ

def sphRegionOne (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ ‖σ.rotOne z‖ < σ.sphCornerRad 0}

def sphRegionTwo (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ ‖σ.rotTwo z‖ < σ.sphCornerRad 1}

def sphRegionLens (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖ ∧ σ.sphCornerRad 1 ≤ ‖σ.rotTwo z‖ ∧
    σ.sphSideTwo z < σ.sphLensWidth}

def sphRegionThree (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖ ∧
    σ.sphCornerRad 1 ≤ ‖σ.rotTwo z‖ ∧ σ.sphLensWidth ≤ σ.sphSideTwo z}

theorem sphCanon_eq_F_sphInj (j : Fin 3) (z : ℂ) :
    σ.sphCanon j z = sphCanonF (σ.sphTau j) (σ.sphDist j z) := rfl

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem norm_vertexOne_le_sphInj : ‖σ.vertexOne‖ ≤ 1 := by
  rw [norm_vertexOne_sph hs]
  exact tOneThree_le_one_sph hs

theorem norm_vertexTwo_le_sphInj : ‖σ.vertexTwo‖ ≤ 1 := by
  rw [norm_vertexTwo_sph hs]
  exact tTwoThree_le_one_sph hs

theorem sphCornerShrink_pos_sphInj : 0 < σ.sphCornerShrink := (sphParams hs).1

theorem kappa_shrink_sphInj :
    0 < compactProfileSlope * σ.sphCornerShrink ∧
      compactProfileSlope * σ.sphCornerShrink < 3 / 2 := by
  have hd := sphCornerShrink_pos_sphInj hs
  have h1 := sphScale_le_tau hs 0
  have h2 := sphTau_lt_one hs 0
  unfold compactProfileSlope
  unfold sphCornerShrink at hd ⊢
  constructor <;> linarith

theorem sphCanonF_cornerRad_sphInj (j : Fin 3) :
    sphCanonF (σ.sphTau j) (σ.sphCornerRad j) = -σ.sphCornerShrink :=
  sphCanonF_shrink_sphInj (sphTau_pos hs j).le (sphCornerShrink_pos_sphInj hs).le

theorem sphCanon_ge_of_cornerRad_sphInj (j : Fin 3) {z : ℂ}
    (h : σ.sphCornerRad j ≤ σ.sphDist j z) : -σ.sphCornerShrink ≤ σ.sphCanon j z := by
  rw [← sphCanonF_cornerRad_sphInj hs j, sphCanon_eq_F_sphInj]
  exact sphCanonF_le_sphInj (sphTau_pos hs j).le
    (by linarith [(sphCornerRad_bounds hs j).1, sphTau_pos hs j]) h

theorem sphModOne_ge_sphInj {z : ℂ} (h : σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖) :
    3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ σ.sphModOne z := by
  have := sphCanon_ge_of_cornerRad_sphInj hs 0 (z := z) h
  unfold sphModOne compactProfileSlope at *
  linarith

theorem sphModTwo_ge_sphInj {z : ℂ} (h : σ.sphCornerRad 1 ≤ ‖σ.rotTwo z‖) :
    3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ σ.sphModTwo z := by
  have := sphCanon_ge_of_cornerRad_sphInj hs 1 (z := z) h
  unfold sphModTwo compactProfileSlope at *
  linarith

theorem tau_zero_lt_tOneThree_sphInj : σ.sphTau 0 < σ.sphTOneThree := by
  have e := sphTau_oplus_onethree hs
  have t0 := sphTau_pos hs 0
  have t2 := sphTau_pos hs 2
  have hm := sphTau_mul_lt_one hs 0 2
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 1 - σ.sphTau 0 * σ.sphTau 2),
    mul_pos (mul_pos t0 t0) t2]

theorem tau_zero_lt_tOneTwo_sphInj : σ.sphTau 0 < σ.sphTOneTwo := by
  have e := sphTau_oplus_onetwo hs
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have hm := sphTau_mul_lt_one hs 0 1
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 1 - σ.sphTau 0 * σ.sphTau 1),
    mul_pos (mul_pos t0 t0) t1]

theorem tau_one_lt_tOneTwo_sphInj : σ.sphTau 1 < σ.sphTOneTwo := by
  have e := sphTau_oplus_onetwo hs
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have hm := sphTau_mul_lt_one hs 0 1
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 1 - σ.sphTau 0 * σ.sphTau 1),
    mul_pos (mul_pos t1 t1) t0]

theorem tau_one_lt_tTwoThree_sphInj : σ.sphTau 1 < σ.sphTTwoThree := by
  have e := sphTau_oplus_twothree hs
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have hm := sphTau_mul_lt_one hs 1 2
  by_contra h
  push Not at h
  nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 1 - σ.sphTau 1 * σ.sphTau 2),
    mul_pos (mul_pos t1 t1) t2]

/-! ### Sectors -/

theorem sphPsiOne_mem_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne) :
    0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧ 0 ≤ σ.sphPsiOne z ∧ σ.sphPsiOne z ≤ σ.θ₁ := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hψ := pos_norm_add_re_sph (rotOne_ne_zero_sph hs hv1 h1) (re_rotOne_nonneg_sph hs hz)
  obtain ⟨a, b⟩ := sector_one_sph hs hz
  rw [im_exp_mul_conj_eq_neg_sph] at b
  obtain ⟨c, d, -⟩ := discAngle_sector σ.θ₁_pos_sph σ.θ₁_le_sph hψ a b
  exact ⟨hψ, c, d⟩

theorem sphPsiTwo_mem_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo) :
    0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧ 0 ≤ σ.sphPsiTwo z ∧ σ.sphPsiTwo z ≤ σ.θ₂ := by
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hψ := pos_norm_add_re_sph (rotTwo_ne_zero_sph hs hv2 h2) (re_rotTwo_nonneg_sph hs hz)
  obtain ⟨a, b⟩ := sector_two_sph hs hz
  rw [im_exp_mul_conj_eq_neg_sph] at b
  obtain ⟨c, d, -⟩ := discAngle_sector σ.θ₂_pos_sph σ.θ₂_le_sph hψ a b
  exact ⟨hψ, c, d⟩

theorem discAngle_mem_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 < ‖z‖ + z.re ∧ 0 ≤ discAngle z ∧ discAngle z ≤ σ.θ₃ := by
  have hψ := pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz)
  obtain ⟨a, b, -⟩ := (mem_triangle_iff_sph hs).1 hz
  rw [wallSide_one_eq_neg_im_sph] at b
  obtain ⟨c, d, -⟩ := discAngle_sector σ.θ₃_pos_sph σ.θ₃_le_sph hψ a b
  exact ⟨hψ, c, d⟩

/-! ### The arcs about `v₁` and `v₂` -/

theorem sphInjArcOne_ne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    1 - conj σ.vertexOne * (-exp ((σ.θ₃ : ℂ) * I) * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0 :=
  sphInjArc_ne (norm_vertexOne_le_sphInj hs) (by rw [norm_neg, Complex.norm_exp_ofReal_mul_I])
    hρ0 hρ1 φ

theorem sphInjArcTwo_ne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ((ρ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0 :=
  sphInjArc_ne (norm_vertexTwo_le_sphInj hs) (by
    rw [norm_neg, exp_neg_ofReal_mul_I_sph, Complex.norm_exp_ofReal_mul_I]) hρ0 hρ1 φ

theorem rotOne_sphInjArcOne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    σ.rotOne (σ.sphInjArcOne ρ φ) = (ρ : ℂ) * exp ((φ : ℂ) * I) := by
  rw [rotOne_eq_mul_sph hs, sphInjArcOne, sphMoeb_sphInjArc (sphInjArcOne_ne hs hρ0 hρ1 φ)]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination ((ρ : ℂ) * exp ((φ : ℂ) * I)) * this

theorem rotTwo_sphInjArcTwo {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    σ.rotTwo (σ.sphInjArcTwo ρ φ) = (ρ : ℂ) * exp ((φ : ℂ) * I) := by
  rw [rotTwo_eq_mul_sph hs, sphInjArcTwo, sphMoeb_sphInjArc (sphInjArcTwo_ne hs hρ0 hρ1 φ)]
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination ((ρ : ℂ) * exp ((φ : ℂ) * I)) * this

theorem one_add_sphInjArcOne_ne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    1 + conj σ.vertexOne * σ.sphInjArcOne ρ φ ≠ 0 :=
  one_add_conj_mul_sphInjArc (sphInjArcOne_ne hs hρ0 hρ1 φ)

theorem one_add_sphInjArcTwo_ne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    1 + σ.vertexTwo * σ.sphInjArcTwo ρ φ ≠ 0 := by
  have := one_add_conj_mul_sphInjArc (sphInjArcTwo_ne hs hρ0 hρ1 φ)
  rwa [conj_vertexTwo_sph] at this

theorem eq_sphInjArcOne {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    z = σ.sphInjArcOne ‖σ.rotOne z‖ (σ.sphPsiOne z) := by
  have hp := halfArg_polar_self (ne_zero_of_pos_norm_add_re_sph hψ) hψ
  rw [sphInjArcOne, sphInjArc, sphPsiOne, ← hp, neg_mul, ← sphMoeb_vertexOne_eq_rotOne hs,
    sphMoebInv_sphMoeb hv1]

theorem eq_sphInjArcTwo {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    z = σ.sphInjArcTwo ‖σ.rotTwo z‖ (σ.sphPsiTwo z) := by
  have hp := halfArg_polar_self (ne_zero_of_pos_norm_add_re_sph hψ) hψ
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have e : -exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z = sphMoeb σ.vertexTwo z := by
    rw [rotTwo_eq_mul_sph hs]
    have := exp_mul_exp_neg_sph σ.θ₂
    linear_combination (sphMoeb σ.vertexTwo z) * this
  rw [sphInjArcTwo, sphInjArc, sphPsiTwo, ← hp, e, sphMoebInv_sphMoeb hv2']

end Spherical

end CompactShape

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

/-! ### The arcs lie in the triangle, and the corner angles are monotone along them -/

theorem sphInjArcOne_walls {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ σ.θ₁) :
    0 ≤ σ.wallSide 1 (σ.sphInjArcOne ρ φ) ∧ 0 ≤ σ.wallSide 2 (σ.sphInjArcOne ρ φ) := by
  have hr := rotOne_sphInjArcOne hs hρ0 hρ1 φ
  have hv1 := one_add_sphInjArcOne_ne hs hρ0 hρ1 φ
  obtain ⟨s1, s2⟩ := sin_nonneg_sphInj hφ0 hφ1 σ.θ₁_le_sph
  constructor
  · have e := wallSide_one_eq_rotOne_sph hs (σ.sphInjArcOne ρ φ)
    rw [hr, im_ofReal_mul_exp_sphInj] at e
    exact nonneg_of_mul_pos_right_sphInj (by positivity)
      (mul_nonneg (mul_nonneg hρ0 s1) (Complex.normSq_nonneg _)) e
  · by_cases h2 : 1 + σ.vertexTwo * σ.sphInjArcOne ρ φ = 0
    · rw [wallSide_two_eq_sph hs, h2, Complex.normSq_zero, mul_zero]
    · have h2' : 1 + conj σ.vertexTwo * σ.sphInjArcOne ρ φ ≠ 0 := by rwa [conj_vertexTwo_sph]
      have e := wallSide_two_eq_rotOne_sph hs hv1 h2'
      rw [hr, im_exp_conj_ofReal_mul_exp_sphInj] at e
      have ht : 0 < 1 + σ.sphTOneTwo ^ 2 := by positivity
      have hY : 0 ≤ (σ.rotTwo (σ.sphInjArcOne ρ φ)).im := by
        have h3 := mul_nonneg (mul_nonneg hρ0 s2)
          (Complex.normSq_nonneg (1 + σ.sphTOneTwo * σ.rotTwo (σ.sphInjArcOne ρ φ)))
        rw [e] at h3
        exact (mul_nonneg_iff_of_pos_left ht).1 h3
      rw [wallSide_two_eq_sph hs]
      exact mul_nonneg hY (Complex.normSq_nonneg _)

theorem sphInjArcTwo_walls {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ σ.θ₂) :
    0 ≤ σ.wallSide 0 (σ.sphInjArcTwo ρ φ) ∧ 0 ≤ σ.wallSide 2 (σ.sphInjArcTwo ρ φ) := by
  have hr := rotTwo_sphInjArcTwo hs hρ0 hρ1 φ
  obtain ⟨s1, s2⟩ := sin_nonneg_sphInj hφ0 hφ1 σ.θ₂_le_sph
  constructor
  · have e := wallSide_zero_eq_rotTwo_sph hs (σ.sphInjArcTwo ρ φ)
    rw [hr, im_exp_conj_ofReal_mul_exp_sphInj] at e
    exact nonneg_of_mul_pos_right_sphInj (by positivity)
      (mul_nonneg (mul_nonneg hρ0 s2) (Complex.normSq_nonneg _)) e
  · rw [wallSide_two_eq_sph hs, hr, im_ofReal_mul_exp_sphInj]
    exact mul_nonneg (mul_nonneg hρ0 s1) (Complex.normSq_nonneg _)

theorem sphInjArcOne_mem {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (hτ : ‖σ.rotOne z‖ < σ.sphTau 0) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ σ.θ₁) :
    σ.sphInjArcOne ‖σ.rotOne z‖ φ ∈ σ.triangle := by
  have hρ0 : 0 ≤ ‖σ.rotOne z‖ := norm_nonneg _
  have hρ1 : ‖σ.rotOne z‖ < 1 := hτ.trans (sphTau_lt_one hs 0)
  have hmem : ∀ s ∈ Icc 0 σ.θ₁, 0 ≤ σ.wallSide 0 (σ.sphInjArcOne ‖σ.rotOne z‖ s) →
      σ.sphInjArcOne ‖σ.rotOne z‖ s ∈ σ.triangle := fun s hs' h0 =>
    (mem_triangle_iff_sph hs).2 ⟨h0, sphInjArcOne_walls hs hρ0 hρ1 hs'.1 hs'.2⟩
  refine hmem φ ⟨hφ0, hφ1⟩ ?_
  by_contra hneg
  push Not at hneg
  obtain ⟨hψ, p0, p1⟩ := sphPsiOne_mem_sphInj hs hz h1
  have hz' := eq_sphInjArcOne hs (one_add_conj_vertexOne_ne_sph hs hz) hψ
  have hf : Continuous fun s : ℝ => (σ.sphInjArcOne ‖σ.rotOne z‖ s).im :=
    continuous_im.comp (continuous_sphInjArc (sphInjArcOne_ne hs hρ0 hρ1))
  have hfz : (σ.sphInjArcOne ‖σ.rotOne z‖ (σ.sphPsiOne z)).im = z.im := by rw [← hz']
  have h0mem : (0 : ℝ) ∈ uIcc (σ.sphInjArcOne ‖σ.rotOne z‖ (σ.sphPsiOne z)).im
      (σ.sphInjArcOne ‖σ.rotOne z‖ φ).im := by
    rw [hfz, mem_uIcc]
    exact Or.inr ⟨hneg.le, im_nonneg_of_mem_sph hs hz⟩
  obtain ⟨s, hsI, hs0⟩ := intermediate_value_uIcc hf.continuousOn h0mem
  have hsI' : s ∈ Icc 0 σ.θ₁ := uIcc_subset_Icc ⟨p0, p1⟩ ⟨hφ0, hφ1⟩ hsI
  have hT := hmem s hsI' (le_of_eq hs0.symm)
  have hle := tauZero_le_of_wallZero_sph hs hT hs0
  rw [rotOne_sphInjArcOne hs hρ0 hρ1, norm_ofReal_mul_exp_sphInj hρ0] at hle
  linarith

theorem sphInjArcTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo)
    (hτ : ‖σ.rotTwo z‖ < σ.sphTau 1) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ σ.θ₂) :
    σ.sphInjArcTwo ‖σ.rotTwo z‖ φ ∈ σ.triangle := by
  have hρ0 : 0 ≤ ‖σ.rotTwo z‖ := norm_nonneg _
  have hρ1 : ‖σ.rotTwo z‖ < 1 := hτ.trans (sphTau_lt_one hs 1)
  have hmem : ∀ s ∈ Icc 0 σ.θ₂, 0 ≤ σ.wallSide 1 (σ.sphInjArcTwo ‖σ.rotTwo z‖ s) →
      σ.sphInjArcTwo ‖σ.rotTwo z‖ s ∈ σ.triangle := fun s hs' h1 =>
    (mem_triangle_iff_sph hs).2 ⟨(sphInjArcTwo_walls hs hρ0 hρ1 hs'.1 hs'.2).1, h1,
      (sphInjArcTwo_walls hs hρ0 hρ1 hs'.1 hs'.2).2⟩
  refine hmem φ ⟨hφ0, hφ1⟩ ?_
  by_contra hneg
  push Not at hneg
  obtain ⟨hψ, p0, p1⟩ := sphPsiTwo_mem_sphInj hs hz h2
  have hz' := eq_sphInjArcTwo hs (one_add_vertexTwo_ne_sph hs hz) hψ
  have hf : Continuous fun s : ℝ => σ.wallSide 1 (σ.sphInjArcTwo ‖σ.rotTwo z‖ s) :=
    (continuous_wallSide_sph hs 1).comp (continuous_sphInjArc (sphInjArcTwo_ne hs hρ0 hρ1))
  have hfz : σ.wallSide 1 (σ.sphInjArcTwo ‖σ.rotTwo z‖ (σ.sphPsiTwo z)) = σ.wallSide 1 z := by
    rw [← hz']
  have h0mem : (0 : ℝ) ∈ uIcc (σ.wallSide 1 (σ.sphInjArcTwo ‖σ.rotTwo z‖ (σ.sphPsiTwo z)))
      (σ.wallSide 1 (σ.sphInjArcTwo ‖σ.rotTwo z‖ φ)) := by
    rw [hfz, mem_uIcc]
    exact Or.inr ⟨hneg.le, ((mem_triangle_iff_sph hs).1 hz).2.1⟩
  obtain ⟨s, hsI, hs0⟩ := intermediate_value_uIcc hf.continuousOn h0mem
  have hsI' : s ∈ Icc 0 σ.θ₂ := uIcc_subset_Icc ⟨p0, p1⟩ ⟨hφ0, hφ1⟩ hsI
  have hT := hmem s hsI' (le_of_eq hs0.symm)
  have hle := tauOne_le_of_wallOne_sph hs hT hs0
  rw [rotTwo_sphInjArcTwo hs hρ0 hρ1, norm_ofReal_mul_exp_sphInj hρ0] at hle
  linarith

theorem sphLam_sphInj {u : ℂ} (hu : u ∈ σ.triangle) :
    ((σ.rotTwo u - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo u)).re ≤ 0 := by
  have hq := re_sphMoeb_nonpos_of_mem hs hu
  have ht : 0 < σ.sphTOneTwo := tOneTwo_pos_sph hs
  have hX : 0 ≤ (σ.rotTwo u).re := re_rotTwo_nonneg_sph hs hu
  have hden : 0 < 1 + σ.sphTOneTwo * (σ.rotTwo u).re := by positivity
  have hN := one_add_real_mul_ne_sph hden
  have hNpos : 0 < Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo u) := Complex.normSq_pos.2 hN
  have key : (sphMoeb σ.sphTOneTwo (σ.rotTwo u)).re *
      Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo u) =
      ((σ.rotTwo u).re - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * (σ.rotTwo u).re) +
        σ.sphTOneTwo * (σ.rotTwo u).im ^ 2 := by
    rw [sphMoeb, Complex.conj_ofReal, Complex.div_re, ← add_div, div_mul_cancel₀ _ hNpos.ne']
    simp only [sub_re, sub_im, add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re,
      ofReal_im]
    ring
  have e : ((σ.rotTwo u - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo u)).re =
      ((σ.rotTwo u).re - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * (σ.rotTwo u).re) -
        σ.sphTOneTwo * (σ.rotTwo u).im ^ 2 := by
    simp only [sub_re, sub_im, add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re,
      ofReal_im]
    ring
  rw [e]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hq hNpos.le,
    mul_nonneg ht.le (sq_nonneg (σ.rotTwo u).im)]

theorem sphValidOne_sphInj {u : ℂ} (hu : u ∈ σ.triangle) (h0 : u ≠ 0) (h1 : u ≠ σ.vertexOne)
    (h2 : u ≠ σ.vertexTwo) (hd : ‖σ.rotOne u‖ ≤ σ.sphTau 0) :
    u ∈ σ.sphDomOne ∧ u ∈ σ.sphDomTwo ∧ 0 < ‖σ.rotOne u‖ + (σ.rotOne u).re ∧
      0 < σ.sphModOne u + ((σ.sphBridgeOne u).re - 3 / 2) ∧
      0 < σ.sphModOne u - ((σ.sphBridgeTwo u).re - 3 / 2) ∧
      σ.sphAngleOneAtOne u ≤ σ.sphAngleTwoAtOne u ∧
      ((σ.rotTwo u - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo u)).re ≤ 0 := by
  have d1 := mem_sphDomOne hs hu h0 h1
  have d2 := mem_sphDomTwo hs hu h1 h2
  have r1 := three_halves_lt_re_sphBridgeOne hs hu hd
  have r2 := (re_sphBridgeTwo_mem_sph hs hu).2
  have hM := sphModOne_pos hs u
  have hp1 : 0 < σ.sphModOne u + ((σ.sphBridgeOne u).re - 3 / 2) := by linarith
  have hp2 : 0 < σ.sphModOne u - ((σ.sphBridgeTwo u).re - 3 / 2) := by linarith
  exact ⟨d1, d2, (sphPsiOne_mem_sphInj hs hu h1).1, hp1, hp2,
    sphAngleOneAtOne_le_sphAngleTwoAtOne hs d1 d2 hp1 hp2 ((mem_triangle_iff_sph hs).1 hu).2.1
      (sector_two_sph hs hu).1 (by linarith), sphLam_sphInj hs hu⟩

theorem sphValidTwo_sphInj {u : ℂ} (hu : u ∈ σ.triangle) (h0 : u ≠ 0) (h1 : u ≠ σ.vertexOne)
    (h2 : u ≠ σ.vertexTwo) (hd : ‖σ.rotTwo u‖ ≤ σ.sphTau 1) :
    u ∈ σ.sphDomTwo ∧ u ∈ σ.sphDomZero ∧
      0 < σ.sphModTwo u + ((σ.sphBridgeTwo u).re + 3 / 2) ∧
      0 < σ.sphModTwo u - ((σ.sphBridgeZero u).re + 3 / 2) ∧
      σ.sphAngleTwoAtTwo u ≤ σ.sphAngleZeroAtTwo u ∧ 0 ≤ (σ.rotTwo u).re := by
  have d2 := mem_sphDomTwo hs hu h1 h2
  have d0 := mem_sphDomZero hs hu h0 h2
  have r2 := (re_sphBridgeTwo_mem_sph hs hu).1
  have r0 := re_sphBridgeZero_lt_sph hs hu hd
  have hM := sphModTwo_pos hs u
  have hp2 : 0 < σ.sphModTwo u + ((σ.sphBridgeTwo u).re + 3 / 2) := by linarith
  have hp0 : 0 < σ.sphModTwo u - ((σ.sphBridgeZero u).re + 3 / 2) := by linarith
  exact ⟨d2, d0, hp2, hp0,
    sphAngleTwoAtTwo_le_sphAngleZeroAtTwo hs d2 d0 hp2 hp0 (sector_two_sph hs hu).1
      ((mem_triangle_iff_sph hs).1 hu).1 (by linarith), re_rotTwo_nonneg_sph hs hu⟩

theorem sphInjArcOne_facts {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (hτ : ‖σ.rotOne z‖ < σ.sphTau 0) {φ : ℝ} (hφ : φ ∈ Icc 0 σ.θ₁) :
    σ.sphInjArcOne ‖σ.rotOne z‖ φ ∈ σ.triangle ∧ σ.sphInjArcOne ‖σ.rotOne z‖ φ ≠ 0 ∧
      σ.sphInjArcOne ‖σ.rotOne z‖ φ ≠ σ.vertexOne ∧
      σ.sphInjArcOne ‖σ.rotOne z‖ φ ≠ σ.vertexTwo ∧
      ‖σ.rotOne (σ.sphInjArcOne ‖σ.rotOne z‖ φ)‖ = ‖σ.rotOne z‖ := by
  have hρ0 : 0 ≤ ‖σ.rotOne z‖ := norm_nonneg _
  have hρpos : 0 < ‖σ.rotOne z‖ :=
    norm_pos_iff.2 (rotOne_ne_zero_sph hs (one_add_conj_vertexOne_ne_sph hs hz) h1)
  have hρ1 : ‖σ.rotOne z‖ < 1 := hτ.trans (sphTau_lt_one hs 0)
  have hn : ‖σ.rotOne (σ.sphInjArcOne ‖σ.rotOne z‖ φ)‖ = ‖σ.rotOne z‖ := by
    rw [rotOne_sphInjArcOne hs hρ0 hρ1, norm_ofReal_mul_exp_sphInj hρ0]
  refine ⟨sphInjArcOne_mem hs hz h1 hτ hφ.1 hφ.2, fun h => ?_, fun h => ?_, fun h => ?_, hn⟩
  · rw [h, norm_rotOne_zero_sph hs] at hn
    linarith [tau_zero_lt_tOneThree_sphInj hs]
  · rw [h, rotOne_vertexOne_sph hs, norm_zero] at hn
    linarith
  · rw [h, norm_rotOne_vertexTwo_sph hs] at hn
    linarith [tau_zero_lt_tOneTwo_sphInj hs]

theorem sphInjArcTwo_facts {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo)
    (hτ : ‖σ.rotTwo z‖ < σ.sphTau 1) {φ : ℝ} (hφ : φ ∈ Icc 0 σ.θ₂) :
    σ.sphInjArcTwo ‖σ.rotTwo z‖ φ ∈ σ.triangle ∧ σ.sphInjArcTwo ‖σ.rotTwo z‖ φ ≠ 0 ∧
      σ.sphInjArcTwo ‖σ.rotTwo z‖ φ ≠ σ.vertexOne ∧
      σ.sphInjArcTwo ‖σ.rotTwo z‖ φ ≠ σ.vertexTwo ∧
      ‖σ.rotTwo (σ.sphInjArcTwo ‖σ.rotTwo z‖ φ)‖ = ‖σ.rotTwo z‖ := by
  have hρ0 : 0 ≤ ‖σ.rotTwo z‖ := norm_nonneg _
  have hρpos : 0 < ‖σ.rotTwo z‖ :=
    norm_pos_iff.2 (rotTwo_ne_zero_sph hs (one_add_vertexTwo_ne_sph hs hz) h2)
  have hρ1 : ‖σ.rotTwo z‖ < 1 := hτ.trans (sphTau_lt_one hs 1)
  have hn : ‖σ.rotTwo (σ.sphInjArcTwo ‖σ.rotTwo z‖ φ)‖ = ‖σ.rotTwo z‖ := by
    rw [rotTwo_sphInjArcTwo hs hρ0 hρ1, norm_ofReal_mul_exp_sphInj hρ0]
  refine ⟨sphInjArcTwo_mem hs hz h2 hτ hφ.1 hφ.2, fun h => ?_, fun h => ?_, fun h => ?_, hn⟩
  · rw [h, norm_rotTwo_zero_sph hs] at hn
    linarith [tau_one_lt_tTwoThree_sphInj hs]
  · rw [h, norm_rotTwo_vertexOne_sph hs] at hn
    linarith [tau_one_lt_tOneTwo_sphInj hs]
  · rw [h, rotTwo_vertexTwo_sph hs, norm_zero] at hn
    linarith

theorem strictMonoOn_sphInjArcOne {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (hτ : ‖σ.rotOne z‖ < σ.sphTau 0) :
    StrictMonoOn (fun φ => σ.sphAngleCornerOne σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth
      σ.sphSwitchTop (σ.sphInjArcOne ‖σ.rotOne z‖ φ)) (Icc 0 σ.θ₁) := by
  have hρ0 : 0 ≤ ‖σ.rotOne z‖ := norm_nonneg _
  have hρ1 : ‖σ.rotOne z‖ < 1 := hτ.trans (sphTau_lt_one hs 0)
  have hβ : σ.sphLensWidth < σ.sphSwitchTop := (sphParams hs).2.2.1
  have hval := fun φ (hφ : φ ∈ Icc 0 σ.θ₁) => by
    obtain ⟨hT, u0, u1, u2, hn⟩ := sphInjArcOne_facts hs hz h1 hτ hφ
    exact sphValidOne_sphInj hs hT u0 u1 u2 (by rw [hn]; exact hτ.le)
  refine strictMonoOn_sphInjArc (sphInjArcOne_ne hs hρ0 hρ1) (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨d1, d2, hψ, hp1, hp2, -, -⟩ := hval φ hφ
    exact (contDiffAt_sphAngleCornerOne hs _ _ _ _ d1 d2 hψ hp1 hp2).continuousAt
  · obtain ⟨d1, d2, hψ, hp1, hp2, hord, hlam⟩ := hval φ (Ioo_subset_Icc_self hφ)
    exact exists_hasDerivAt_sphAngleCornerOne_circ hs hβ d1 d2 hψ hp1 hp2 hord (Or.inl hlam)

theorem strictMonoOn_sphInjArcTwo {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo)
    (hτ : ‖σ.rotTwo z‖ < σ.sphTau 1) :
    StrictMonoOn (fun φ => σ.sphAngleCornerTwo σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth
      σ.sphSwitchTop (σ.sphInjArcTwo ‖σ.rotTwo z‖ φ)) (Icc 0 σ.θ₂) := by
  have hρ0 : 0 ≤ ‖σ.rotTwo z‖ := norm_nonneg _
  have hρ1 : ‖σ.rotTwo z‖ < 1 := hτ.trans (sphTau_lt_one hs 1)
  have hβ : σ.sphLensWidth < σ.sphSwitchTop := (sphParams hs).2.2.1
  have hval := fun φ (hφ : φ ∈ Icc 0 σ.θ₂) => by
    obtain ⟨hT, u0, u1, u2, hn⟩ := sphInjArcTwo_facts hs hz h2 hτ hφ
    exact sphValidTwo_sphInj hs hT u0 u1 u2 (by rw [hn]; exact hτ.le)
  refine strictMonoOn_sphInjArc (sphInjArcTwo_ne hs hρ0 hρ1) (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨d2, d0, hp2, hp0, -, -⟩ := hval φ hφ
    exact (contDiffAt_sphAngleCornerTwo hs _ _ _ _ d2 d0 hp2 hp0).continuousAt
  · obtain ⟨d2, d0, hp2, hp0, hord, hX⟩ := hval φ (Ioo_subset_Icc_self hφ)
    exact exists_hasDerivAt_sphAngleCornerTwo_circ hs hβ d2 d0 hp2 hp0 hord (Or.inl hX)

end Spherical

end CompactShape

theorem mul_mem_angle_sphInj {p : ℕ} {θ ψ : ℝ} (hθ : θ * p = Real.pi) (h0 : 0 ≤ ψ)
    (h1 : ψ ≤ θ) : 0 ≤ (p : ℝ) * ψ ∧ (p : ℝ) * ψ ≤ Real.pi := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  refine ⟨mul_nonneg hp h0, ?_⟩
  rw [← hθ, mul_comm θ]
  exact mul_le_mul_of_nonneg_left h1 hp

theorem sub_mul_mem_angle_sphInj {p : ℕ} {θ ψ : ℝ} (hθ : θ * p = Real.pi) (h0 : 0 ≤ ψ)
    (h1 : ψ ≤ θ) : 0 ≤ Real.pi - (p : ℝ) * ψ ∧ Real.pi - (p : ℝ) * ψ ≤ Real.pi := by
  obtain ⟨a, b⟩ := mul_mem_angle_sphInj hθ h0 h1
  constructor <;> linarith

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

/-! ### The four regions and the formula of `sphPreFold` on each -/

theorem sphBlendEnd_le_cornerRad_sphInj :
    σ.sphBlendEnd ≤ σ.sphCornerRad 0 ∧ σ.sphBlendEnd ≤ σ.sphCornerRad 1 := by
  have c0 := (sphCornerRad_bounds hs 0).1
  have c1 := (sphCornerRad_bounds hs 1).1
  have m0 : σ.sphInnerScale ≤ σ.sphTau 0 := min_le_left _ _
  have m1 : σ.sphInnerScale ≤ σ.sphTau 1 := min_le_right _ _
  unfold sphBlendEnd
  constructor <;> linarith

omit hs in
theorem mem_sphRegions {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    z ∈ σ.sphRegionOne ∨ z ∈ σ.sphRegionTwo ∨ z ∈ σ.sphRegionLens ∨ z ∈ σ.sphRegionThree := by
  by_cases c1 : ‖σ.rotOne z‖ < σ.sphCornerRad 0
  · exact Or.inl ⟨hz, c1⟩
  by_cases c2 : ‖σ.rotTwo z‖ < σ.sphCornerRad 1
  · exact Or.inr (Or.inl ⟨hz, c2⟩)
  rw [not_lt] at c1 c2
  by_cases l : σ.sphSideTwo z < σ.sphLensWidth
  · exact Or.inr (Or.inr (Or.inl ⟨hz, c1, c2, l⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, h0, c1, c2, not_lt.1 l⟩))

theorem facts_sphRegionOne {z : ℂ} (hz : z ∈ σ.sphRegionOne) :
    z ≠ 0 ∧ z ≠ σ.vertexTwo ∧ ‖σ.rotOne z‖ < σ.sphTau 0 := by
  obtain ⟨f2, f3⟩ := sphDist_gt_of_cornerOne hs hz.1 hz.2.le
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  refine ⟨fun h => ?_, fun h => ?_, hz.2.trans (sphLayout_ineqs hs).2.2.2.2.1⟩
  · rw [h, norm_zero] at f3
    linarith
  · rw [h, rotTwo_vertexTwo_sph hs, norm_zero] at f2
    linarith

theorem facts_sphRegionTwo {z : ℂ} (hz : z ∈ σ.sphRegionTwo) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ ‖σ.rotTwo z‖ < σ.sphTau 1 := by
  obtain ⟨f1, f3⟩ := sphDist_gt_of_cornerTwo hs hz.1 hz.2.le
  have t0 := sphTau_pos hs 0
  have t2 := sphTau_pos hs 2
  refine ⟨fun h => ?_, fun h => ?_, hz.2.trans (sphLayout_ineqs hs).2.2.2.2.2.1⟩
  · rw [h, norm_zero] at f3
    linarith
  · rw [h, rotOne_vertexOne_sph hs, norm_zero] at f1
    linarith

theorem ne_vertices_of_far_sphInj {z : ℂ} (c1 : σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖)
    (c2 : σ.sphCornerRad 1 ≤ ‖σ.rotTwo z‖) : z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  have b0 := (sphCornerRad_bounds hs 0).1
  have b1 := (sphCornerRad_bounds hs 1).1
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  constructor <;> intro h
  · rw [h, rotOne_vertexOne_sph hs, norm_zero] at c1
    linarith
  · rw [h, rotTwo_vertexTwo_sph hs, norm_zero] at c2
    linarith

theorem sphPreFold_regionOne {z : ℂ} (hz : z ∈ σ.sphRegionOne) :
    σ.sphPreFold z = σ.sphFoldCornerOne z := by
  obtain ⟨hT, hr⟩ := hz
  obtain ⟨f2, f3⟩ := sphDist_gt_of_cornerOne hs hT hr.le
  obtain ⟨-, -, -, p4, p5, p6, -, -, -, -, -⟩ := sphParams hs
  obtain ⟨l1, l2, -, -, -, l6, -, -, -⟩ := sphLayout_ineqs hs
  have t2 := sphTau_pos hs 2
  have hg2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hg3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 (by unfold sphOuterGermRadius; linarith)
  rcases lt_or_ge ‖σ.rotOne z‖ σ.sphGermRadius with h1 | h1
  · simp only [sphPreFold, h1, ↓reduceIte, sphFoldCornerOne, sphApexOne]
    refine (sphCornerOne_eq_apex (by linarith) (by linarith) (by linarith) ?_).symm
    by_cases hv : z = σ.vertexOne
    · left
      rw [hv]
      exact rotOne_vertexOne_sph hs
    · exact Or.inr (sphPsiOne_mem_sphInj hs hT hv).1
  · simp only [sphPreFold, not_lt.2 h1, hg2, hg3, hr, ↓reduceIte]

theorem sphPreFold_regionTwo {z : ℂ} (hz : z ∈ σ.sphRegionTwo) :
    σ.sphPreFold z = σ.sphFoldCornerTwo z := by
  obtain ⟨hT, hr⟩ := hz
  obtain ⟨f1, f3⟩ := sphDist_gt_of_cornerTwo hs hT hr.le
  obtain ⟨-, -, -, p4, p5, p6, -, -, -, -, -⟩ := sphParams hs
  obtain ⟨l1, l2, -, -, l5, -, -, -, -⟩ := sphLayout_ineqs hs
  have t2 := sphTau_pos hs 2
  have hg1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphCornerRad 0 := not_lt.2 (by linarith)
  have hg3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 (by unfold sphOuterGermRadius; linarith)
  rcases lt_or_ge ‖σ.rotTwo z‖ σ.sphGermRadius with h2 | h2
  · simp only [sphPreFold, hg1, h2, ↓reduceIte, sphFoldCornerTwo, sphApexTwo]
    refine (sphCornerTwo_eq_apex (by linarith) (by linarith) (by linarith) ?_).symm
    by_cases hv : z = σ.vertexTwo
    · left
      rw [hv]
      exact rotTwo_vertexTwo_sph hs
    · exact Or.inr (sphPsiTwo_mem_sphInj hs hT hv).1
  · simp only [sphPreFold, hg1, not_lt.2 h2, hg3, hc1, hr, ↓reduceIte]

theorem sphPreFold_regionLens {z : ℂ} (hz : z ∈ σ.sphRegionLens) :
    σ.sphPreFold z = σ.sphBridgeTwo z := by
  obtain ⟨hT, c1, c2, l⟩ := hz
  obtain ⟨-, -, hββ, -, -, -, -, -, -, -, -⟩ := sphParams hs
  obtain ⟨l1, l2, -, -, -, -, -, -, -⟩ := sphLayout_ineqs hs
  have hY : 0 ≤ σ.sphSideTwo z := (sector_two_sph hs hT).1
  have hn := sph_norm_gt_of_lens hs hT (by linarith) c1
  have t2 := sphTau_pos hs 2
  have hg1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hg2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hg3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 (by unfold sphOuterGermRadius; linarith)
  have hl : |σ.sphSideTwo z| < σ.sphLensWidth := by rwa [abs_of_nonneg hY]
  simp only [sphPreFold, hg1, hg2, hg3, not_lt.2 c1, not_lt.2 c2, hl, ↓reduceIte]

theorem sphPreFold_regionThree {z : ℂ} (hz : z ∈ σ.sphRegionThree) :
    σ.sphPreFold z = σ.sphFoldCornerThree z := by
  obtain ⟨hT, h0, c1, c2, l⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, q0, q1, q2, -⟩ := sphParams hs
  obtain ⟨l1, l2, -, -, -, -, -, -, -⟩ := sphLayout_ineqs hs
  have hY : 0 ≤ σ.sphSideTwo z := (sector_two_sph hs hT).1
  have hg1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hg2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hl : ¬ |σ.sphSideTwo z| < σ.sphLensWidth := not_lt.2 (by rwa [abs_of_nonneg hY])
  by_cases h3 : ‖z‖ < σ.sphOuterGermRadius
  · simp only [sphPreFold, hg1, hg2, h3, ↓reduceIte, sphFoldCornerThree]
    exact (sphCornerThree_eq_outerGerm (by linarith) (by linarith)
      (discAngle_mem_sphInj hs hT h0).1).symm
  · simp only [sphPreFold, hg1, hg2, h3, not_lt.2 c1, not_lt.2 c2, hl, ↓reduceIte]

/-! ### Radial profiles of the fold -/

theorem strictMono_sphInnerOne :
    StrictMonoOn (sphInnerRadial σ.p₁ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 0)) (Ici 0) :=
  strictMonoOn_sphInnerRadial_sphInj (by have := σ.two_le_p₁; omega) (sphParams hs).2.2.2.2.2.1
    (sphParams hs).2.2.2.2.2.2.1 (sphTau_pos hs 0).le (sphTau_lt_one hs 0)

theorem strictMono_sphInnerTwo :
    StrictMonoOn (sphInnerRadial σ.p₂ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 1)) (Ici 0) :=
  strictMonoOn_sphInnerRadial_sphInj (by have := σ.two_le_p₂; omega) (sphParams hs).2.2.2.2.2.1
    (sphParams hs).2.2.2.2.2.2.1 (sphTau_pos hs 1).le (sphTau_lt_one hs 1)

theorem strictAnti_sphOuter :
    StrictAntiOn (sphOuterRadial σ.p₃ σ.sphOuterBlendStart σ.sphOuterBlendEnd (σ.sphTau 2))
      (Ici 0) :=
  strictAntiOn_sphOuterRadial_sphInj (by have := σ.two_le_p₃; omega)
    (sphParams hs).2.2.2.2.2.2.2.2.2.1 (sphParams hs).2.2.2.2.2.2.2.2.2.2
    (sphTau_pos hs 2).le (sphTau_lt_one hs 2)

theorem sphBlendStart_nonneg_sphInj : 0 ≤ σ.sphBlendStart := by
  have := (sphParams hs).2.2.2.1
  have := (sphParams hs).2.2.2.2.1
  linarith

theorem sphInnerOne_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ sphInnerRadial σ.p₁ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 0) d := by
  have := (strictMono_sphInnerOne hs).monotoneOn (Set.mem_Ici.2 le_rfl) hd hd
  rwa [sphInnerRadial_zero_sphInj (by have := σ.two_le_p₁; omega)
    (sphBlendStart_nonneg_sphInj hs) (sphParams hs).2.2.2.2.2.1] at this

theorem sphInnerTwo_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ sphInnerRadial σ.p₂ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 1) d := by
  have := (strictMono_sphInnerTwo hs).monotoneOn (Set.mem_Ici.2 le_rfl) hd hd
  rwa [sphInnerRadial_zero_sphInj (by have := σ.two_le_p₂; omega)
    (sphBlendStart_nonneg_sphInj hs) (sphParams hs).2.2.2.2.2.1] at this

theorem sphInnerOne_lt {d : ℝ} (hd0 : 0 ≤ d) (hd : d < σ.sphCornerRad 0) :
    sphInnerRadial σ.p₁ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 0) d <
      3 / 2 - compactProfileSlope * σ.sphCornerShrink := by
  have hc := (sphBlendEnd_le_cornerRad_sphInj hs).1
  have h := strictMono_sphInnerOne hs hd0 (show (0 : ℝ) ≤ σ.sphCornerRad 0 by linarith) hd
  rw [sphInnerRadial_of_ge_sphInj (sphParams hs).2.2.2.2.2.1 hc,
    sphCanonF_cornerRad_sphInj hs 0] at h
  linarith

theorem sphInnerTwo_lt {d : ℝ} (hd0 : 0 ≤ d) (hd : d < σ.sphCornerRad 1) :
    sphInnerRadial σ.p₂ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 1) d <
      3 / 2 - compactProfileSlope * σ.sphCornerShrink := by
  have hc := (sphBlendEnd_le_cornerRad_sphInj hs).2
  have h := strictMono_sphInnerTwo hs hd0 (show (0 : ℝ) ≤ σ.sphCornerRad 1 by linarith) hd
  rw [sphInnerRadial_of_ge_sphInj (sphParams hs).2.2.2.2.2.1 hc,
    sphCanonF_cornerRad_sphInj hs 1] at h
  linarith

theorem sphOuter_ge_three_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h : ‖z‖ < σ.sphOuterBlendEnd) :
    3 ≤ sphOuterRadial σ.p₃ σ.sphOuterBlendStart σ.sphOuterBlendEnd (σ.sphTau 2) ‖z‖ := by
  have t2 := sphTau_pos hs 2
  have hd1 : ‖z‖ ≤ 1 := norm_le_one_of_mem_sph hs hz
  have hA : ‖z‖ ^ σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg _) hd1
  have hlt : ‖z‖ ≤ σ.sphTau 2 := by unfold sphOuterBlendEnd at h; linarith
  have hC : sphCanonF (σ.sphTau 2) ‖z‖ ≤ 0 := by
    unfold sphCanonF
    have : 0 < 1 + ‖z‖ * σ.sphTau 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le
  have hτ0 := coneStep_nonneg σ.sphOuterBlendStart σ.sphOuterBlendEnd ‖z‖
  have hτ1 := coneStep_le_one σ.sphOuterBlendStart σ.sphOuterBlendEnd ‖z‖
  unfold sphOuterRadial compactProfileSlope
  nlinarith [mul_nonneg hτ0 (by linarith : (0 : ℝ) ≤ -(2 / 5 * sphCanonF (σ.sphTau 2) ‖z‖)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - coneStep σ.sphOuterBlendStart σ.sphOuterBlendEnd ‖z‖)
      (by linarith : (0 : ℝ) ≤ 7 / 2 - ‖z‖ ^ σ.p₃ / 2 - 3)]

theorem sphOuter_gt_sphInj {z : ℂ} (hz : z ∈ σ.triangle) :
    13 / 5 < sphOuterRadial σ.p₃ σ.sphOuterBlendStart σ.sphOuterBlendEnd (σ.sphTau 2) ‖z‖ := by
  rcases lt_or_ge ‖z‖ σ.sphOuterBlendEnd with h | h
  · linarith [sphOuter_ge_three_sphInj hs hz h]
  · rw [sphOuterRadial_of_ge_sphInj (sphParams hs).2.2.2.2.2.2.2.2.2.1 h]
    exact (sphModThree_mem hs hz).1

/-! ### The images of the regions -/

theorem norm_sphPreFold_regionOne {z : ℂ} (hz : z ∈ σ.sphRegionOne) :
    ‖σ.sphPreFold z - 3 / 2‖ =
      sphInnerRadial σ.p₁ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 0) ‖σ.rotOne z‖ := by
  rw [sphPreFold_regionOne hs hz, sphFoldCornerOne, sphCornerOne, EuclidShape.three_halves_cast]
  exact norm_real_add_polar _ _ _ (sphInnerOne_nonneg hs (norm_nonneg _))

theorem norm_sphPreFold_regionTwo {z : ℂ} (hz : z ∈ σ.sphRegionTwo) :
    ‖σ.sphPreFold z + 3 / 2‖ =
      sphInnerRadial σ.p₂ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 1) ‖σ.rotTwo z‖ := by
  rw [sphPreFold_regionTwo hs hz, sphFoldCornerTwo, sphCornerTwo,
    show ∀ u : ℂ, u + 3 / 2 = u - ((-(3 / 2) : ℝ) : ℂ) by intro u; push_cast; ring]
  exact norm_real_add_polar _ _ _ (sphInnerTwo_nonneg hs (norm_nonneg _))

theorem image_sphRegionOne {z : ℂ} (hz : z ∈ σ.sphRegionOne) :
    ‖σ.sphPreFold z - 3 / 2‖ < 3 / 2 - compactProfileSlope * σ.sphCornerShrink := by
  rw [norm_sphPreFold_regionOne hs hz]
  exact sphInnerOne_lt hs (norm_nonneg _) hz.2

theorem image_sphRegionTwo {z : ℂ} (hz : z ∈ σ.sphRegionTwo) :
    ‖σ.sphPreFold z + 3 / 2‖ < 3 / 2 - compactProfileSlope * σ.sphCornerShrink := by
  rw [norm_sphPreFold_regionTwo hs hz]
  exact sphInnerTwo_lt hs (norm_nonneg _) hz.2

theorem image_sphRegionLens {z : ℂ} (hz : z ∈ σ.sphRegionLens) :
    3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ ‖σ.sphPreFold z - 3 / 2‖ ∧
      3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ ‖σ.sphPreFold z + 3 / 2‖ ∧
        ‖σ.sphPreFold z‖ < 3 / 2 := by
  have e := sphPreFold_regionLens hs hz
  obtain ⟨hT, c1, c2, -⟩ := hz
  obtain ⟨h1, h2⟩ := ne_vertices_of_far_sphInj hs c1 c2
  obtain ⟨e1, e2⟩ := norm_sphBridgeTwo hs (mem_sphDomTwo hs hT h1 h2)
  rw [e, e1, e2]
  exact ⟨sphModOne_ge_sphInj hs c1, sphModTwo_ge_sphInj hs c2, norm_sphBridgeTwo_lt hs hT h1 h2⟩

theorem norm_sphPreFold_regionThree {z : ℂ} (hz : z ∈ σ.sphRegionThree) :
    ‖σ.sphPreFold z‖ =
      sphOuterRadial σ.p₃ σ.sphOuterBlendStart σ.sphOuterBlendEnd (σ.sphTau 2) ‖z‖ := by
  have hS := (sphOuter_gt_sphInj hs hz.1).le
  rw [sphPreFold_regionThree hs hz, sphFoldCornerThree, sphCornerThree, ofReal_zero, zero_add,
    norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

theorem im_sphBridgeOne_nonneg_sphInj {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.sphBridgeOne z).im := by
  rw [sphBridgeOne, twoCircle_im]
  have := Real.sqrt_nonneg (σ.sphCofBridgeOne z)
  have := ((mem_triangle_iff_sph hs).1 hz).2.1
  positivity

theorem im_sphBridgeZero_nonneg_sphInj {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.sphBridgeZero z).im := by
  rw [sphBridgeZero, twoCircle_im]
  have := Real.sqrt_nonneg (σ.sphCofBridgeZero z)
  have := ((mem_triangle_iff_sph hs).1 hz).1
  positivity

theorem im_sphBridgeTwo_nonneg_sphInj {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.sphBridgeTwo z).im := by
  rw [sphBridgeTwo, twoCircle_im]
  have := Real.sqrt_nonneg (σ.sphCofBridgeTwo z)
  have : 0 ≤ σ.sphSideTwo z := (sector_two_sph hs hz).1
  positivity

theorem sphValidThree_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) :
    z ∈ σ.sphDomOne ∧ z ∈ σ.sphDomZero ∧ 0 < ‖z‖ + z.re ∧
      0 < σ.sphModThree z + (σ.sphBridgeOne z).re ∧
      0 < σ.sphModThree z - (σ.sphBridgeZero z).re ∧
      0 ≤ σ.sphAngleOneAtThree z ∧ σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z ∧
      σ.sphAngleZeroAtThree z ≤ Real.pi := by
  have d1 := mem_sphDomOne hs hz h0 h1
  have d0 := mem_sphDomZero hs hz h0 h2
  have hM := (sphModThree_mem hs hz).1
  have r1 := re_sphBridgeOne_pos hs hz
  have r0 := re_sphBridgeZero_neg hs hz
  have hp1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re := by linarith
  have hp0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re := by linarith
  obtain ⟨w0, w1, -⟩ := (mem_triangle_iff_sph hs).1 hz
  exact ⟨d1, d0, (discAngle_mem_sphInj hs hz h0).1, hp1, hp0,
    (EuclidShape.halfArg_mem_Ico hp1 (im_sphBridgeOne_nonneg_sphInj hs hz)).1,
    sphAngleOneAtThree_le_sphAngleZeroAtThree hs d1 d0 hp1 hp0 w1 w0 (by linarith),
    (EuclidShape.negHalfArg_mem_Ioc hp0 (im_sphBridgeZero_nonneg_sphInj hs hz)).2⟩

theorem sphPreFold_regionThree_far {z : ℂ} (hz : z ∈ σ.sphRegionThree)
    (h : σ.sphOuterBlendEnd ≤ ‖z‖) :
    σ.sphPreFold z = (σ.sphModThree z : ℂ) * exp ((((1 - σ.sphNuThree 1 σ.sphCornerShrink z) *
      σ.sphAngleZeroAtThree z + σ.sphNuThree 1 σ.sphCornerShrink z * σ.sphAngleOneAtThree z :
        ℝ) : ℂ) * I) := by
  have hab := (sphParams hs).2.2.2.2.2.2.2.2.2.1
  rw [sphPreFold_regionThree hs hz, sphFoldCornerThree, sphCornerThree, sphAngleCornerThree,
    sphOuterRadial_of_ge_sphInj hab h, coneStep_eq_one hab h]
  simp only [ofReal_zero, zero_add, sub_self, zero_mul, one_mul]
  rfl

theorem image_sphRegionThree {z : ℂ} (hz : z ∈ σ.sphRegionThree) :
    13 / 5 < ‖σ.sphPreFold z‖ ∧
      3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ ‖σ.sphPreFold z - 3 / 2‖ ∧
      3 / 2 - compactProfileSlope * σ.sphCornerShrink ≤ ‖σ.sphPreFold z + 3 / 2‖ := by
  have hn := norm_sphPreFold_regionThree hs hz
  have hg := sphOuter_gt_sphInj hs hz.1
  obtain ⟨hk0, hk⟩ := kappa_shrink_sphInj hs
  refine ⟨hn ▸ hg, ?_⟩
  have hz' := hz
  obtain ⟨hT, h0, c1, c2, -⟩ := hz
  obtain ⟨h1, h2⟩ := ne_vertices_of_far_sphInj hs c1 c2
  rcases lt_or_ge ‖z‖ σ.sphOuterBlendEnd with h | h
  · have h3 := sphOuter_ge_three_sphInj hs hT h
    have a := norm_sub_norm_le (σ.sphPreFold z) (3 / 2)
    have b := norm_sub_norm_le (σ.sphPreFold z) (-(3 / 2))
    rw [sub_neg_eq_add] at b
    have n32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [EuclidShape.three_halves_cast, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [norm_neg, n32] at b
    rw [n32] at a
    constructor <;> linarith
  · obtain ⟨d1, d0, -, hp1, hp0, a0, a10, a1π⟩ := sphValidThree_sphInj hs hT h0 h1 h2
    have hM := (sphModThree_mem hs hT).1
    set ν := σ.sphNuThree 1 σ.sphCornerShrink z with hν
    have hν0 : 0 ≤ ν := coneStep_nonneg _ _ _
    have hν1 : ν ≤ 1 := coneStep_le_one _ _ _
    set Θ := (1 - ν) * σ.sphAngleZeroAtThree z + ν * σ.sphAngleOneAtThree z with hΘ
    have hΘ1 : σ.sphAngleOneAtThree z ≤ Θ := by nlinarith
    have hΘ0 : Θ ≤ σ.sphAngleZeroAtThree z := by nlinarith
    have hC := sphPreFold_regionThree_far hs hz' h
    rw [← hΘ] at hC
    have hB1 := sphBridgeOne_eq_polar_three hs d1 hp1
    have hB0 := sphBridgeZero_eq_polar_three hs d0 hp0
    rw [ofReal_zero, zero_add] at hB1 hB0
    have q1 := normSq_polar_sub_real (σ.sphModThree z) (3 / 2) Θ
    have q0 := normSq_polar_sub_real (σ.sphModThree z) (-(3 / 2)) Θ
    have r1 := normSq_polar_sub_real (σ.sphModThree z) (3 / 2) (σ.sphAngleOneAtThree z)
    have r0 := normSq_polar_sub_real (σ.sphModThree z) (-(3 / 2)) (σ.sphAngleZeroAtThree z)
    rw [← hB1, ← EuclidShape.three_halves_cast, (norm_sphBridgeOne hs d1).2] at r1
    rw [← hB0, show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add,
      (norm_sphBridgeZero hs d0).2] at r0
    rw [← hC, ← EuclidShape.three_halves_cast] at q1
    rw [← hC, show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at q0
    have cA := Real.cos_le_cos_of_nonneg_of_le_pi a0 (by linarith) hΘ1
    have cB := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) a1π hΘ0
    have m1 := sphModOne_ge_sphInj hs c1
    have m2 := sphModTwo_ge_sphInj hs c2
    constructor
    · nlinarith [norm_nonneg (σ.sphPreFold z - 3 / 2)]
    · nlinarith [norm_nonneg (σ.sphPreFold z + 3 / 2)]

end Spherical

end CompactShape

theorem eq_of_norm_sphMoeb_sphInj {t : ℝ} (ht : 0 < t) {ζ ξ : ℂ} (h1 : 0 < 1 + t * ζ.re)
    (h2 : 0 < 1 + t * ξ.re) (hn : ‖ξ‖ = ‖ζ‖) (hm : ‖sphMoeb t ξ‖ = ‖sphMoeb t ζ‖)
    (hy : 0 ≤ ζ.im) (hy' : 0 ≤ ξ.im) : ξ = ζ := by
  have e1 := sq_norm_sphMoeb_real t ζ h1
  have e2 := sq_norm_sphMoeb_real t ξ h2
  rw [hm] at e2
  have q1 := CompactShape.sq_norm_eq_sph ζ
  have q2 := CompactShape.sq_norm_eq_sph ξ
  rw [hn] at q2
  have key : (ξ.re - ζ.re) * (2 * t * (‖sphMoeb t ζ‖ ^ 2 + 1)) = 0 := by
    linear_combination e2 - e1 + (1 - ‖sphMoeb t ζ‖ ^ 2 * t ^ 2) * (q1 - q2)
  have hpos : 0 < 2 * t * (‖sphMoeb t ζ‖ ^ 2 + 1) := by positivity
  have hX : ξ.re = ζ.re := by
    rcases mul_eq_zero.1 key with h | h
    · linarith
    · linarith
  have hY : ξ.im = ζ.im := by
    have hsq : ξ.im ^ 2 = ζ.im ^ 2 := by
      rw [hX] at q2
      linarith
    exact (pow_left_inj₀ hy' hy two_ne_zero).1 hsq
  exact Complex.ext hX hY

theorem mem_sphPairDom_sphInj {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {ζ : ℂ} (hX : 0 ≤ ζ.re)
    (hY : ζ.im ≠ 0) (hn : ‖ζ‖ ≤ 1) : ζ ∈ sphPairDom t := by
  have h0 : ζ ≠ 0 := fun h => hY (by rw [h, zero_im])
  have hne : ζ ≠ (t : ℂ) := fun h => hY (by rw [h, ofReal_im])
  obtain ⟨c1, c2, c3, c4⟩ := pair_conditions_sph ht ht1 hX h0 hne (fun h => absurd h hY)
  refine ⟨c1, c2, c3, c4, by linarith, ?_⟩
  have := CompactShape.norm_sphMoeb_le_one (a := (t : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]; exact ht1) hn
    (by rw [Complex.conj_ofReal, re_ofReal_mul]; positivity)
  linarith

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

/-! ### Injectivity on each region -/

theorem rotTwo_inj_sphInj {z w : ℂ} (hz : 1 + σ.vertexTwo * z ≠ 0) (hw : 1 + σ.vertexTwo * w ≠ 0)
    (h : σ.rotTwo z = σ.rotTwo w) : z = w := by
  have hz' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have hw' : 1 + conj σ.vertexTwo * w ≠ 0 := by rwa [conj_vertexTwo_sph]
  have e : ∀ u, sphMoeb σ.vertexTwo u = -exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo u := fun u => by
    rw [rotTwo_eq_mul_sph hs]
    have := exp_mul_exp_neg_sph σ.θ₂
    linear_combination (-(sphMoeb σ.vertexTwo u)) * this
  calc z = sphMoebInv σ.vertexTwo (sphMoeb σ.vertexTwo z) := (sphMoebInv_sphMoeb hz').symm
    _ = sphMoebInv σ.vertexTwo (sphMoeb σ.vertexTwo w) := by rw [e z, e w, h]
    _ = w := sphMoebInv_sphMoeb hw'

theorem injOn_sphRegionLens : InjOn σ.sphPreFold σ.sphRegionLens := by
  intro z hz w hw h
  rw [sphPreFold_regionLens hs hz, sphPreFold_regionLens hs hw] at h
  obtain ⟨hT, c1, c2, -⟩ := hz
  obtain ⟨hT', c1', c2', -⟩ := hw
  obtain ⟨z1, z2⟩ := ne_vertices_of_far_sphInj hs c1 c2
  obtain ⟨w1, w2⟩ := ne_vertices_of_far_sphInj hs c1' c2'
  obtain ⟨e1, e2⟩ := norm_sphBridgeTwo hs (mem_sphDomTwo hs hT z1 z2)
  obtain ⟨e1', e2'⟩ := norm_sphBridgeTwo hs (mem_sphDomTwo hs hT' w1 w2)
  rw [h, e1'] at e1
  rw [h, e2'] at e2
  have d1 : ‖σ.rotOne w‖ = ‖σ.rotOne z‖ := by
    have : σ.sphCanon 0 w = σ.sphCanon 0 z := by
      unfold sphModOne compactProfileSlope at e1
      linarith
    exact sphCanonF_inj_sphInj (sphTau_pos hs 0).le (norm_nonneg _) (norm_nonneg _) this
  have d2 : ‖σ.rotTwo w‖ = ‖σ.rotTwo z‖ := by
    have : σ.sphCanon 1 w = σ.sphCanon 1 z := by
      unfold sphModTwo compactProfileSlope at e2
      linarith
    exact sphCanonF_inj_sphInj (sphTau_pos hs 1).le (norm_nonneg _) (norm_nonneg _) this
  have hv2 := one_add_vertexTwo_ne_sph hs hT
  have hv2' := one_add_vertexTwo_ne_sph hs hT'
  have hc2 : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have hc2' : 1 + conj σ.vertexTwo * w ≠ 0 := by rwa [conj_vertexTwo_sph]
  have m := norm_rotOne_eq_sphMoeb_rotTwo hs (one_add_conj_vertexOne_ne_sph hs hT) hc2
  have m' := norm_rotOne_eq_sphMoeb_rotTwo hs (one_add_conj_vertexOne_ne_sph hs hT') hc2'
  have ht := tOneTwo_pos_sph hs
  have x := re_rotTwo_nonneg_sph hs hT
  have x' := re_rotTwo_nonneg_sph hs hT'
  have hR : σ.rotTwo w = σ.rotTwo z := eq_of_norm_sphMoeb_sphInj ht (by positivity)
    (by positivity) d2 (by rw [← m', ← m, d1]) (sector_two_sph hs hT).1 (sector_two_sph hs hT').1
  exact (rotTwo_inj_sphInj hs hv2' hv2 hR).symm

theorem sphAngleCornerOne_mem_sphInj {u : ℂ} (hu : u ∈ σ.triangle) (h0 : u ≠ 0)
    (h1 : u ≠ σ.vertexOne) (h2 : u ≠ σ.vertexTwo) (hd : ‖σ.rotOne u‖ ≤ σ.sphTau 0) :
    0 ≤ σ.sphAngleCornerOne σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop u ∧
      σ.sphAngleCornerOne σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop u ≤
        Real.pi := by
  obtain ⟨-, -, -, hp1, hp2, -, -⟩ := sphValidOne_sphInj hs hu h0 h1 h2 hd
  have a1 := EuclidShape.halfArg_mem_Ico hp1 (im_sphBridgeOne_nonneg_sphInj hs hu)
  have a2 := EuclidShape.negHalfArg_mem_Ioc hp2 (im_sphBridgeTwo_nonneg_sphInj hs hu)
  obtain ⟨-, ψ0, ψ1⟩ := sphPsiOne_mem_sphInj hs hu h1
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    (mul_mem_angle_sphInj σ.θ₁_mul_sph ψ0 ψ1)
    (EuclidShape.convex_angle' (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
      ⟨a1.1, a1.2.le⟩ ⟨a2.1.le, a2.2⟩)

theorem sphAngleCornerTwo_mem_sphInj {u : ℂ} (hu : u ∈ σ.triangle) (h0 : u ≠ 0)
    (h1 : u ≠ σ.vertexOne) (h2 : u ≠ σ.vertexTwo) (hd : ‖σ.rotTwo u‖ ≤ σ.sphTau 1) :
    0 ≤ σ.sphAngleCornerTwo σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop u ∧
      σ.sphAngleCornerTwo σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop u ≤
        Real.pi := by
  obtain ⟨-, -, hp2, hp0, -, -⟩ := sphValidTwo_sphInj hs hu h0 h1 h2 hd
  have a2 := EuclidShape.halfArg_mem_Ico hp2 (im_sphBridgeTwo_nonneg_sphInj hs hu)
  have a0 := EuclidShape.negHalfArg_mem_Ioc hp0 (im_sphBridgeZero_nonneg_sphInj hs hu)
  have a2' : 0 ≤ σ.sphAngleTwoAtTwo u ∧ σ.sphAngleTwoAtTwo u < Real.pi := a2
  have a0' : 0 < σ.sphAngleZeroAtTwo u ∧ σ.sphAngleZeroAtTwo u ≤ Real.pi := a0
  obtain ⟨-, ψ0, ψ1⟩ := sphPsiTwo_mem_sphInj hs hu h2
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    (mul_mem_angle_sphInj σ.θ₂_mul_sph ψ0 ψ1)
    (convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
      ⟨a2'.1, a2'.2.le⟩ ⟨a0'.1.le, a0'.2⟩)

theorem injOn_sphRegionOne : InjOn σ.sphPreFold σ.sphRegionOne := by
  intro z hz w hw h
  have nz := norm_sphPreFold_regionOne hs hz
  have nw := norm_sphPreFold_regionOne hs hw
  rw [h, nw] at nz
  have hd : ‖σ.rotOne w‖ = ‖σ.rotOne z‖ :=
    (strictMono_sphInnerOne hs).injOn (norm_nonneg _) (norm_nonneg _) nz
  obtain ⟨z0, z2, hτ⟩ := facts_sphRegionOne hs hz
  obtain ⟨w0, w2, hτ'⟩ := facts_sphRegionOne hs hw
  rw [sphPreFold_regionOne hs hz, sphPreFold_regionOne hs hw, sphFoldCornerOne,
    sphCornerOne, sphCornerOne, hd] at h
  obtain ⟨hT, hr⟩ := hz
  obtain ⟨hT', hr'⟩ := hw
  have hv1 := one_add_conj_vertexOne_ne_sph hs hT
  have hv1' := one_add_conj_vertexOne_ne_sph hs hT'
  by_cases hz1 : z = σ.vertexOne
  · have h0 : ‖σ.rotOne w‖ = 0 := by rw [hd, hz1, rotOne_vertexOne_sph hs, norm_zero]
    have hw1 : w = σ.vertexOne := by
      by_contra hne
      exact rotOne_ne_zero_sph hs hv1' hne (norm_eq_zero.1 h0)
    rw [hz1, hw1]
  · have hw1 : w ≠ σ.vertexOne := fun hw1 => by
      have h0 : ‖σ.rotOne z‖ = 0 := by rw [← hd, hw1, rotOne_vertexOne_sph hs, norm_zero]
      exact rotOne_ne_zero_sph hs hv1 hz1 (norm_eq_zero.1 h0)
    have hpos : 0 < ‖σ.rotOne z‖ := norm_pos_iff.2 (rotOne_ne_zero_sph hs hv1 hz1)
    have hS : (sphInnerRadial σ.p₁ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 0)
        ‖σ.rotOne z‖ : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (sphInnerRadial_pos (sphTau_pos hs 0).le (sphTau_lt_one hs 0) hpos).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
      (sphAngleCornerOne_mem_sphInj hs hT z0 hz1 z2 hτ.le)
      (sphAngleCornerOne_mem_sphInj hs hT' w0 hw1 w2 hτ'.le)
    obtain ⟨hψz, p0, p1⟩ := sphPsiOne_mem_sphInj hs hT hz1
    obtain ⟨hψw, q0, q1⟩ := sphPsiOne_mem_sphInj hs hT' hw1
    have pz := eq_sphInjArcOne hs hv1 hψz
    have pw := eq_sphInjArcOne hs hv1' hψw
    rw [hd] at pw
    have he : σ.sphPsiOne z = σ.sphPsiOne w := (strictMonoOn_sphInjArcOne hs hT hz1 hτ).injOn
      ⟨p0, p1⟩ ⟨q0, q1⟩ (by
        rw [← pz, ← pw]
        exact hΘ)
    calc z = σ.sphInjArcOne ‖σ.rotOne z‖ (σ.sphPsiOne z) := pz
      _ = σ.sphInjArcOne ‖σ.rotOne z‖ (σ.sphPsiOne w) := by rw [he]
      _ = w := pw.symm

theorem injOn_sphRegionTwo : InjOn σ.sphPreFold σ.sphRegionTwo := by
  intro z hz w hw h
  have nz := norm_sphPreFold_regionTwo hs hz
  have nw := norm_sphPreFold_regionTwo hs hw
  rw [h, nw] at nz
  have hd : ‖σ.rotTwo w‖ = ‖σ.rotTwo z‖ :=
    (strictMono_sphInnerTwo hs).injOn (norm_nonneg _) (norm_nonneg _) nz
  obtain ⟨z0, z1, hτ⟩ := facts_sphRegionTwo hs hz
  obtain ⟨w0, w1, hτ'⟩ := facts_sphRegionTwo hs hw
  rw [sphPreFold_regionTwo hs hz, sphPreFold_regionTwo hs hw, sphFoldCornerTwo,
    sphCornerTwo, sphCornerTwo, hd] at h
  obtain ⟨hT, hr⟩ := hz
  obtain ⟨hT', hr'⟩ := hw
  have hv2 := one_add_vertexTwo_ne_sph hs hT
  have hv2' := one_add_vertexTwo_ne_sph hs hT'
  by_cases hz2 : z = σ.vertexTwo
  · have h0 : ‖σ.rotTwo w‖ = 0 := by rw [hd, hz2, rotTwo_vertexTwo_sph hs, norm_zero]
    have hw2 : w = σ.vertexTwo := by
      by_contra hne
      exact rotTwo_ne_zero_sph hs hv2' hne (norm_eq_zero.1 h0)
    rw [hz2, hw2]
  · have hw2 : w ≠ σ.vertexTwo := fun hw2 => by
      have h0 : ‖σ.rotTwo z‖ = 0 := by rw [← hd, hw2, rotTwo_vertexTwo_sph hs, norm_zero]
      exact rotTwo_ne_zero_sph hs hv2 hz2 (norm_eq_zero.1 h0)
    have hpos : 0 < ‖σ.rotTwo z‖ := norm_pos_iff.2 (rotTwo_ne_zero_sph hs hv2 hz2)
    have hS : (sphInnerRadial σ.p₂ σ.sphBlendStart σ.sphBlendEnd (σ.sphTau 1)
        ‖σ.rotTwo z‖ : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (sphInnerRadial_pos (sphTau_pos hs 1).le (sphTau_lt_one hs 1) hpos).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
      (sphAngleCornerTwo_mem_sphInj hs hT z0 z1 hz2 hτ.le)
      (sphAngleCornerTwo_mem_sphInj hs hT' w0 w1 hw2 hτ'.le)
    obtain ⟨hψz, p0, p1⟩ := sphPsiTwo_mem_sphInj hs hT hz2
    obtain ⟨hψw, q0, q1⟩ := sphPsiTwo_mem_sphInj hs hT' hw2
    have pz := eq_sphInjArcTwo hs hv2 hψz
    have pw := eq_sphInjArcTwo hs hv2' hψw
    rw [hd] at pw
    have he : σ.sphPsiTwo z = σ.sphPsiTwo w := (strictMonoOn_sphInjArcTwo hs hT hz2 hτ).injOn
      ⟨p0, p1⟩ ⟨q0, q1⟩ (by
        rw [← pz, ← pw]
        exact hΘ)
    calc z = σ.sphInjArcTwo ‖σ.rotTwo z‖ (σ.sphPsiTwo z) := pz
      _ = σ.sphInjArcTwo ‖σ.rotTwo z‖ (σ.sphPsiTwo w) := by rw [he]
      _ = w := pw.symm

/-! ### The corner at `v₃`: validity on the whole open sector arc -/

theorem sphValidSector_sphInj {z : ℂ} (hn : ‖z‖ ≤ 1) (hw0 : 0 < σ.wallSide 0 z)
    (hw1 : 0 < σ.wallSide 1 z) :
    z ∈ σ.sphDomOne ∧ z ∈ σ.sphDomZero ∧ 0 < ‖z‖ + z.re ∧
      0 < σ.sphModThree z + (σ.sphBridgeOne z).re ∧
      0 < σ.sphModThree z - (σ.sphBridgeZero z).re ∧
      σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z := by
  have hθ0 := σ.θ₃_pos_sph
  have hθ1 := σ.θ₃_le_sph
  have hY : 0 < z.im := hw0
  have hX : 0 ≤ z.re := re_nonneg_of_sector_sph hθ0 hθ1 hY.le hw1.le
  have hY1 : (exp (-((σ.θ₃ : ℂ) * I)) * z).im < 0 := by
    have := wallSide_one_eq_neg_im_sph (σ := σ) z
    linarith
  have hX1 : 0 ≤ (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
    have := re_nonneg_of_sector_sph hθ0 hθ1 (w := conj (exp (-((σ.θ₃ : ℂ) * I)) * z))
      (by rw [conj_im]; linarith) (by
        rw [Complex.conj_conj, ← mul_assoc, exp_mul_exp_neg_sph, one_mul]
        exact hY.le)
    rwa [conj_re] at this
  have d0 : z ∈ σ.sphDomZero :=
    mem_sphPairDom_sphInj (tTwoThree_pos_sph hs) (tTwoThree_le_one_sph hs) hX hY.ne' hn
  have d1 : z ∈ σ.sphDomOne :=
    mem_sphPairDom_sphInj (tOneThree_pos_sph hs) (tOneThree_le_one_sph hs) hX1 hY1.ne
      (by rw [norm_exp_neg_mul_sph]; exact hn)
  have hz0 : z ≠ 0 := fun h => by
    rw [h, zero_im] at hY
    exact lt_irrefl 0 hY
  have hψ : 0 < ‖z‖ + z.re := pos_norm_add_re_sph hz0 hX
  have c2 : σ.sphCanon 2 z < 1 := sphCanon_lt_one hs hn
  have c0 := (sphCanon_bounds_one hs d1).1
  have c1 := (sphCanon_bounds_zero hs d0).1
  have m1 := sphModOne_pos hs z
  have m2 := sphModTwo_pos hs z
  have hA : 13 / 5 < σ.sphModThree z := by
    unfold sphModThree compactProfileSlope
    linarith
  have hB1 : σ.sphModOne z < 23 / 10 := by
    unfold sphModOne compactProfileSlope
    linarith
  have hB2 : σ.sphModTwo z < 23 / 10 := by
    unfold sphModTwo compactProfileSlope
    linarith
  have r1 : 0 < (σ.sphBridgeOne z).re := by
    rw [sphBridgeOne, twoCircle_re]
    have : 0 < σ.sphModThree z ^ 2 - σ.sphModOne z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
    have h2 : (0 : ℝ) < 2 * (3 / 2 - 0) := by norm_num
    have := div_pos this h2
    linarith
  have r0 : (σ.sphBridgeZero z).re < 0 := by
    rw [sphBridgeZero, twoCircle_re]
    have : 0 < σ.sphModThree z ^ 2 - σ.sphModTwo z ^ 2 + (-(3 / 2) - 0) ^ 2 := by nlinarith
    have h2 : 2 * (-(3 / 2) - 0 : ℝ) < 0 := by norm_num
    have := div_neg_of_pos_of_neg this h2
    linarith
  have hp1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re := by linarith
  have hp0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re := by linarith
  exact ⟨d1, d0, hψ, hp1, hp0,
    sphAngleOneAtThree_le_sphAngleZeroAtThree hs d1 d0 hp1 hp0 hw1.le hw0.le (by linarith)⟩

omit hs in
theorem sphArcThree_facts_sphInj {r φ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hφ0 : 0 < φ)
    (hφ1 : φ < σ.θ₃) :
    ‖sphInjArc 0 1 r φ‖ ≤ 1 ∧ 0 < σ.wallSide 0 (sphInjArc 0 1 r φ) ∧
      0 < σ.wallSide 1 (sphInjArc 0 1 r φ) := by
  have hpi := Real.pi_pos
  have hθ := σ.θ₃_le_sph
  rw [sphInjArc_zero_one]
  refine ⟨by rw [norm_ofReal_mul_exp_sphInj hr0.le]; exact hr1, ?_, ?_⟩
  · change 0 < ((r : ℂ) * exp ((φ : ℂ) * I)).im
    rw [im_ofReal_mul_exp_sphInj]
    exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith))
  · change 0 < (exp ((σ.θ₃ : ℂ) * I) * conj ((r : ℂ) * exp ((φ : ℂ) * I))).im
    rw [im_exp_conj_ofReal_mul_exp_sphInj]
    exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem sphAngleThree_lt_sphInj {r ψ ψ' : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (h0 : 0 ≤ ψ)
    (hψ : ψ < ψ') (h1 : ψ' ≤ σ.θ₃)
    (hc : ContinuousAt (σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1
      σ.sphCornerShrink) (sphInjArc 0 1 r ψ))
    (hc' : ContinuousAt (σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1
      σ.sphCornerShrink) (sphInjArc 0 1 r ψ')) :
    σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1 σ.sphCornerShrink
        (sphInjArc 0 1 r ψ') <
      σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1 σ.sphCornerShrink
        (sphInjArc 0 1 r ψ) := by
  have hδ := sphCornerShrink_pos_sphInj hs
  have hanti : StrictAntiOn (fun φ => σ.sphAngleCornerThree σ.sphOuterBlendStart
      σ.sphOuterBlendEnd 1 σ.sphCornerShrink (sphInjArc 0 1 r φ)) (Icc ψ ψ') := by
    refine strictAntiOn_sphInjArc (sphInjArc_zero_one_ne r) (fun φ hφ => ?_) (fun φ hφ => ?_)
    · rcases eq_or_lt_of_le hφ.1 with e | e
      · rw [← e]
        exact hc
      rcases eq_or_lt_of_le hφ.2 with e' | e'
      · rw [e']
        exact hc'
      obtain ⟨hn, w0, w1⟩ := sphArcThree_facts_sphInj (σ := σ) (φ := φ) hr0 hr1 (by linarith)
        (by linarith)
      obtain ⟨d1, d0, hψ0, hp1, hp0, -⟩ := sphValidSector_sphInj hs hn w0 w1
      exact (contDiffAt_sphAngleCornerThree hs _ _ _ _ d1 d0 hψ0 hp1 hp0).continuousAt
    · obtain ⟨hn, w0, w1⟩ := sphArcThree_facts_sphInj (σ := σ) (φ := φ) hr0 hr1 (by linarith [hφ.1])
        (by linarith [hφ.2])
      obtain ⟨d1, d0, hψ0, hp1, hp0, hord⟩ := sphValidSector_sphInj hs hn w0 w1
      exact exists_hasDerivAt_sphAngleCornerThree_circ hs one_pos hδ d1 d0 hψ0 hp1 hp0 hord
        (Or.inl ⟨w0.le, w1.le⟩)
  exact hanti ⟨le_rfl, hψ.le⟩ ⟨hψ.le, le_rfl⟩ hψ

theorem sphAngleCornerThree_mem_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1 σ.sphCornerShrink z ∧
      σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1 σ.sphCornerShrink z ≤
        Real.pi := by
  obtain ⟨-, -, -, -, -, a0, a10, a1π⟩ := sphValidThree_sphInj hs hz h0 h1 h2
  obtain ⟨-, ψ0, ψ1⟩ := discAngle_mem_sphInj hs hz h0
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    (sub_mul_mem_angle_sphInj σ.θ₃_mul_sph ψ0 ψ1)
    (convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) ⟨by linarith, a1π⟩
      ⟨a0, by linarith⟩)

theorem continuousAt_sphAngleCornerThree_sphInj {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ContinuousAt (σ.sphAngleCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1
      σ.sphCornerShrink) z := by
  obtain ⟨d1, d0, hψ, hp1, hp0, -⟩ := sphValidThree_sphInj hs hz h0 h1 h2
  exact (contDiffAt_sphAngleCornerThree hs _ _ _ _ d1 d0 hψ hp1 hp0).continuousAt

theorem injOn_sphRegionThree : InjOn σ.sphPreFold σ.sphRegionThree := by
  intro z hz w hw h
  have nz := norm_sphPreFold_regionThree hs hz
  have nw := norm_sphPreFold_regionThree hs hw
  rw [h, nw] at nz
  have hr : ‖w‖ = ‖z‖ := (strictAnti_sphOuter hs).injOn (norm_nonneg _) (norm_nonneg _) nz
  have hS : (sphOuterRadial σ.p₃ σ.sphOuterBlendStart σ.sphOuterBlendEnd (σ.sphTau 2) ‖z‖ :
      ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith [sphOuter_gt_sphInj hs hz.1])
  rw [sphPreFold_regionThree hs hz, sphPreFold_regionThree hs hw, sphFoldCornerThree,
    sphCornerThree, sphCornerThree, hr] at h
  obtain ⟨hT, h0, c1, c2, -⟩ := hz
  obtain ⟨hT', h0', c1', c2', -⟩ := hw
  obtain ⟨h1, h2⟩ := ne_vertices_of_far_sphInj hs c1 c2
  obtain ⟨h1', h2'⟩ := ne_vertices_of_far_sphInj hs c1' c2'
  have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
    (sphAngleCornerThree_mem_sphInj hs hT h0 h1 h2)
    (sphAngleCornerThree_mem_sphInj hs hT' h0' h1' h2')
  obtain ⟨hψz, ψz0, ψz1⟩ := discAngle_mem_sphInj hs hT h0
  obtain ⟨hψw, ψw0, ψw1⟩ := discAngle_mem_sphInj hs hT' h0'
  have pz : z = sphInjArc 0 1 ‖z‖ (discAngle z) := by
    rw [sphInjArc_zero_one]
    exact halfArg_polar_self h0 hψz
  have pw : w = sphInjArc 0 1 ‖w‖ (discAngle w) := by
    rw [sphInjArc_zero_one]
    exact halfArg_polar_self h0' hψw
  rw [hr] at pw
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  have hr1 := norm_le_one_of_mem_sph hs hT
  have cz := continuousAt_sphAngleCornerThree_sphInj hs hT h0 h1 h2
  have cw := continuousAt_sphAngleCornerThree_sphInj hs hT' h0' h1' h2'
  rw [pz] at cz
  rw [pw] at cw
  rcases lt_trichotomy (discAngle z) (discAngle w) with hlt | heq | hgt
  · exfalso
    have := sphAngleThree_lt_sphInj hs hr0 hr1 ψz0 hlt ψw1 cz cw
    rw [← pz, ← pw] at this
    linarith
  · calc z = sphInjArc 0 1 ‖z‖ (discAngle z) := pz
      _ = sphInjArc 0 1 ‖z‖ (discAngle w) := by rw [heq]
      _ = w := pw.symm
  · exfalso
    have := sphAngleThree_lt_sphInj hs hr0 hr1 ψw0 hgt ψz1 cw cz
    rw [← pz, ← pw] at this
    linarith

/-! ### Injectivity on the triangle minus `v₃` -/

theorem injOn_sphPreFold : InjOn σ.sphPreFold (σ.triangle \ {0}) := by
  intro z hz w hw h
  obtain ⟨hk, hk'⟩ := kappa_shrink_sphInj hs
  have t := EuclidShape.three_le_norm_sub_add (σ.sphPreFold w)
  rcases mem_sphRegions hz.1 hz.2 with a | a | a | a <;>
    rcases mem_sphRegions hw.1 hw.2 with b | b | b | b
  · exact injOn_sphRegionOne hs a b h
  · have := image_sphRegionOne hs a
    rw [h] at this
    linarith [image_sphRegionTwo hs b]
  · have := image_sphRegionOne hs a
    rw [h] at this
    linarith [image_sphRegionLens hs b]
  · have := image_sphRegionOne hs a
    rw [h] at this
    linarith [image_sphRegionThree hs b]
  · have := image_sphRegionTwo hs a
    rw [h] at this
    linarith [image_sphRegionOne hs b]
  · exact injOn_sphRegionTwo hs a b h
  · have := image_sphRegionTwo hs a
    rw [h] at this
    linarith [image_sphRegionLens hs b]
  · have := image_sphRegionTwo hs a
    rw [h] at this
    linarith [image_sphRegionThree hs b]
  · have := image_sphRegionLens hs a
    rw [h] at this
    linarith [image_sphRegionOne hs b]
  · have := image_sphRegionLens hs a
    rw [h] at this
    linarith [image_sphRegionTwo hs b]
  · exact injOn_sphRegionLens hs a b h
  · have := image_sphRegionLens hs a
    rw [h] at this
    linarith [image_sphRegionThree hs b]
  · have := image_sphRegionThree hs a
    rw [h] at this
    linarith [image_sphRegionOne hs b]
  · have := image_sphRegionThree hs a
    rw [h] at this
    linarith [image_sphRegionTwo hs b]
  · have := image_sphRegionThree hs a
    rw [h] at this
    linarith [image_sphRegionLens hs b]
  · exact injOn_sphRegionThree hs a b h

end Spherical

end CompactShape
end GC.Seifert
