import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeAngles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeAssembly

/-!
# The corner at the first cone vertex of the two-cone fold

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5, for the
shapes `(p₁, p₂, ⊤)`). The corner `cornerConeC` at `v₁` is `cornerCone` of `SF/ConeFoldConeCorner`
with the wall-2 bridge `bridgeTwo` of the cusp replaced by the two-cone bridge `bridgeTwoC`:
`-3/2 + S e^{iΘ}` with the same radial profile `S = coneRadial` and angle
`Θ = (1 - τ)(π - pφ) + τ((1 - λ) Θ₁' + λ Θ₂'')`, `Θ₂'' = angleTwoConeC`. It is the apex model
for `η₁ ≤ a`, the wall-1 bridge for `η₁ ≥ b, φ ≤ φa` and `bridgeTwoC` for `η₁ ≥ b, φ ≥ φb`
(`cornerConeC_eq_apex`, `cornerConeC_eq_bridgeOne`, `cornerConeC_eq_bridgeTwoC`); its Jacobian is
nonzero off `v₁` on the triangle (`det_fderiv_cornerConeC_ne_zero`, from the angular monotonicity
of `SF/ConeFoldTwoConeAngles` and `angleTwoConeC_le_angleOneCone`), and it is equivariant for the
reflections in walls 1 and 2 (`cornerConeC_refl_one`, `cornerConeC_refl_two`).

The disc coordinates at the two cones are related by the Möbius identity
`e^{iθ₂} ω₂ (1 - t ω') = t - ω'` (`discTwo_moebius`), which shows that the triangle minus both
vertices lies in the domain `domTwoC` of the two-cone bridge (`mem_domTwoC_of_mem_triangle`): on
the circle wall `ω'` is real and `e^{iθ₂} ω₂ = (t - ω')/(1 - t ω')` is positive away from `v₂`
because `Im ω₂ < 0` there.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

/-! ### The Möbius identity and the domain of the two-cone bridge -/

theorem conj_exp_mul_I (θ : ℝ) : conj (exp ((θ : ℂ) * I)) = (exp ((θ : ℂ) * I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp

theorem vertex_ratio :
    conj σ.vertexTwo - σ.vertexOne =
      exp ((σ.θ₁ : ℂ) * I) * exp ((σ.θ₂ : ℂ) * I) * (σ.vertexTwo - conj σ.vertexOne) := by
  set E := exp ((σ.θ₁ : ℂ) * I) with hE
  set F := exp ((σ.θ₂ : ℂ) * I) with hF
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hF0 : F ≠ 0 := Complex.exp_ne_zero _
  have h2 : exp (((Real.pi - σ.θ₂ : ℝ) : ℂ) * I) = -F⁻¹ := by
    rw [hF, ← Complex.exp_neg, show ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I =
      Real.pi * I + -((σ.θ₂ : ℂ) * I) by push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [vertexTwo_eq, vertexOne_eq, h2, map_add, map_add, Complex.conj_ofReal, map_div₀, map_div₀,
    map_neg, map_inv₀, map_ofNat, conj_exp_mul_I, conj_exp_mul_I, ← hE, ← hF, inv_inv]
  field_simp
  ring

theorem discTwo_moebius (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    σ.discTwo z * exp ((σ.θ₂ : ℂ) * I) * (1 - σ.tCone * σ.rotOne z) = σ.tCone - σ.rotOne z := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have h := coneDisc_sub_coneDisc hv1 hv2 hz
  set E := exp ((σ.θ₁ : ℂ) * I) with hE
  set F := exp ((σ.θ₂ : ℂ) * I) with hF
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hd : σ.vertexTwo - conj σ.vertexOne ≠ 0 := sub_conj_ne_zero hv1 hv2
  have hu : (conj σ.vertexTwo - σ.vertexOne) / (σ.vertexTwo - conj σ.vertexOne) = E * F := by
    rw [div_eq_iff hd, σ.vertex_ratio]
  have hω : coneDisc σ.vertexOne z = E * σ.rotOne z := by
    rw [rotOne, discOne, show -((σ.θ₁ : ℂ) * I) = ((-σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring,
      exp_neg_mul_I_eq_conj, ← hE, conj_exp_mul_I, ← hE]
    field_simp
  have hv : coneDisc σ.vertexOne σ.vertexTwo = (σ.tCone : ℂ) * E :=
    σ.coneDisc_vertexOne_vertexTwo hθ
  have hcv : conj (coneDisc σ.vertexOne σ.vertexTwo) = (σ.tCone : ℂ) * E⁻¹ := by
    rw [hv, map_mul, Complex.conj_ofReal, hE, conj_exp_mul_I]
  rw [hu, hω, hcv, hv] at h
  have key : E * (σ.rotOne z - σ.tCone) =
      E * (-(σ.discTwo z * F * (1 - σ.tCone * σ.rotOne z))) := by
    rw [discTwo]
    field_simp
    field_simp at h
    linear_combination h
  have := mul_left_cancel₀ hE0 key
  linear_combination this

theorem wallSide_two_eq_zero_of_wallTwo {z : ℂ} (hz : 0 < z.im) (h : σ.wallTwo z = 0) :
    σ.wallSide 2 z = 0 := by
  have h1 := σ.im_rot_coneDisc_vertexOne_mul z
  have hs := σ.sin_θ₁_pos
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have h2 : (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z).im = 0 := by
    have := h
    rw [wallTwo, neg_eq_zero] at this
    exact this
  rw [h2, zero_mul] at h1
  have : Real.sin σ.θ₁ * σ.wallSide 2 z = 0 := by linarith
  rcases mul_eq_zero.1 this with h3 | h3
  · linarith
  · exact h3

theorem eq_vertexTwo_of_walls {z : ℂ} (hz : 0 < z.im) (h0 : z.re = 0) (h2 : σ.wallSide 2 z = 0) :
    z = σ.vertexTwo := by
  simp only [wallSide] at h2
  rw [h0] at h2
  have hc : σ.centre = Real.cos σ.θ₂ / 4 := rfl
  have hs := Real.sin_sq_add_cos_sq σ.θ₂
  have hsn := σ.sin_θ₂_nonneg
  have hy : z.im = Real.sin σ.θ₂ / 4 := by
    have hsq : z.im ^ 2 = (Real.sin σ.θ₂ / 4) ^ 2 := by rw [hc] at h2; nlinarith
    exact (pow_left_inj₀ hz.le (by positivity) two_ne_zero).1 hsq
  exact Complex.ext (by rw [h0, vertexTwo_re]) (by rw [hy, vertexTwo_im])

theorem mem_domTwoC_of_mem_triangle (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.triangle)
    (hzv1 : z ≠ σ.vertexOne) (hzv2 : z ≠ σ.vertexTwo) : z ∈ σ.domTwoC := by
  have hd2 := σ.mem_domTwo_of_mem_triangle hz hzv1
  refine ⟨hz.1, hd2.2, ?_⟩
  by_cases hw : σ.wallTwo z = 0
  · have hv2 := σ.vertexTwo_im_pos hθ
    have hY : (σ.rotOne z).im = 0 := by rw [σ.rotOne_im, hw, neg_zero]
    have hm := σ.discTwo_moebius hθ hz.1
    have hd := σ.one_sub_t_rot_pos hθ hz.1
    set X := (σ.rotOne z).re with hX
    have hrot : σ.rotOne z = (X : ℂ) := Complex.ext (by simp [hX]) (by simp [hY])
    rw [hrot] at hm
    set s := (σ.tCone - X) / (1 - σ.tCone * X) with hs
    have hω : σ.discTwo z * exp ((σ.θ₂ : ℂ) * I) = (s : ℂ) := by
      rw [hs]
      push_cast
      rw [eq_div_iff (by exact_mod_cast hd.ne')]
      exact hm
    have hF1 : exp ((σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hω2 : σ.discTwo z = (s : ℂ) * exp (-((σ.θ₂ : ℂ) * I)) := by
      rw [← hω, mul_assoc, hF1, mul_one]
    have hnorm : ‖σ.discTwo z‖ = |s| := by
      rw [hω2, norm_mul, show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hw2 := σ.wallSide_two_eq_zero_of_wallTwo hz.1 hw
    have hx : 0 < z.re := by
      rcases (show 0 ≤ z.re from hz.2 0).lt_or_eq with h | h
      · exact h
      · exact absurd (σ.eq_vertexTwo_of_walls hz.1 h.symm hw2) hzv2
    have himω : (σ.discTwo z).im < 0 := by
      have h1 := σ.im_coneDisc_vertexTwo_mul z
      have hN := normSq_sub_conj_pos hv2 hz.1
      have : (coneDisc σ.vertexTwo z).im * normSq (z - conj σ.vertexTwo) < 0 := by
        rw [h1]
        have : 0 < 2 * σ.vertexTwo.im * σ.wallSide 0 z := by
          simp only [wallSide]
          positivity
        linarith
      exact neg_of_mul_neg_left this hN.le
    have hspos : 0 < s := by
      rw [hω2, show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg] at himω
      have hs2 : 0 < Real.sin σ.θ₂ :=
        Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
      nlinarith
    rw [hnorm, abs_of_pos hspos]
    change 0 < s + (σ.tCone - X) / (1 - σ.tCone * X)
    rw [← hs]
    linarith
  · exact σ.mu_add_pos_of_im_ne hθ hz.1 hw

/-! ### The corner map -/

def angleConeBlendC (φa φb : ℝ) (z : ℂ) : ℝ :=
  (1 - σ.coneLambda φa φb z) * σ.angleOneCone z + σ.coneLambda φa φb z * σ.angleTwoConeC z

def angleConeC (p : ℕ) (a b φa φb : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b (σ.etaOne z)) * (Real.pi - p * discAngle (σ.discOne z)) +
    coneStep a b (σ.etaOne z) * σ.angleConeBlendC φa φb z

def cornerConeC (p : ℕ) (a b φa φb : ℝ) (z : ℂ) : ℂ :=
  -(3 / 2 : ℂ) + ((coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) : ℝ) : ℂ) *
    exp ((σ.angleConeC p a b φa φb z : ℂ) * I)

theorem contDiffAt_angleConeC (hθ : 0 < σ.θ₂) (p : ℕ) (a b φa φb : ℝ) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ (σ.angleConeC p a b φa φb) z := by
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b (σ.etaOne u)) z :=
    (contDiff_coneStep a b).contDiffAt.comp z (σ.contDiffAt_etaOne hz1)
  have hφ := σ.contDiffAt_discAngle hz1
  have hl : ContDiffAt ℝ ∞ (σ.coneLambda φa φb) z :=
    (contDiff_coneStep φa φb).contDiffAt.comp z hφ
  have hB : ContDiffAt ℝ ∞ (σ.angleConeBlendC φa φb) z :=
    ((contDiffAt_const.sub hl).mul (σ.contDiffAt_angleOneCone hz1)).add
      (hl.mul (σ.contDiffAt_angleTwoConeC hθ hz2))
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.sub (contDiffAt_const.mul hφ))).add
    (hτ.mul hB)

theorem contDiffAt_cornerConeC (hθ : 0 < σ.θ₂) (p : ℕ) (a b φa φb : ℝ) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ (σ.cornerConeC p a b φa φb) z := by
  have hS : ContDiffAt ℝ ∞ (fun u => coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne u)) z :=
    (σ.contDiffAt_coneRadial p a b (σ.etaOne_pos hz1.1)).comp z (σ.contDiffAt_etaOne hz1)
  have h1 : ContDiffAt ℝ ∞
      (fun u => ((coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne u) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hS
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleConeC p a b φa φb u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
        (σ.contDiffAt_angleConeC hθ p a b φa φb hz1 hz2)).mul contDiffAt_const)
  exact contDiffAt_const.add (h1.mul h2)

theorem cornerConeC_eq_cornerCone_of_le {p : ℕ} {a b φa φb : ℝ} {z : ℂ}
    (hη : σ.etaOne z ≤ a) (hab : a < b) :
    σ.cornerConeC p a b φa φb z = σ.cornerCone p a b φa φb z := by
  rw [cornerConeC, cornerCone, angleConeC, angleCone, coneStep_eq_zero hab hη]
  simp

theorem cornerConeC_eq_apex {p : ℕ} (hp : 1 ≤ p) {a b φa φb : ℝ} (hab : a < b) {z : ℂ}
    (hz : 0 < z.im) (hpos : z = σ.vertexOne ∨ z ∈ σ.domOne) (hη : σ.etaOne z ≤ a) :
    σ.cornerConeC p a b φa φb z = -(3 / 2) - conj (σ.discOne z) ^ p / 2 := by
  rw [σ.cornerConeC_eq_cornerCone_of_le hη hab]
  exact σ.cornerCone_eq_apex hp hab hz hpos hη

theorem cornerConeC_eq_bridgeOne (p : ℕ) {a b φa φb : ℝ} (hab : a < b) (hφ : φa < φb) {z : ℂ}
    (hz : z ∈ σ.domOne) (hη : b ≤ σ.etaOne z) (hl : discAngle (σ.discOne z) ≤ φa) :
    σ.cornerConeC p a b φa φb z = σ.bridgeOne z := by
  rw [← σ.cornerCone_eq_bridgeOne p hab hφ hz hη hl, cornerConeC, cornerCone, angleConeC,
    angleCone, angleConeBlendC, angleConeBlend, coneLambda, coneStep_eq_zero hφ hl]
  simp

theorem cornerConeC_eq_bridgeTwoC (hθ : 0 < σ.θ₂) (p : ℕ) {a b φa φb : ℝ} (hab : a < b)
    (hφ : φa < φb) {z : ℂ} (hz : z ∈ σ.domTwoC) (hη : b ≤ σ.etaOne z)
    (hl : φb ≤ discAngle (σ.discOne z)) :
    σ.cornerConeC p a b φa φb z = σ.bridgeTwoC z := by
  have hK := σ.constK_pos
  have hG : 0 < coneProfile σ.constK (σ.etaOne z) := by
    have := half_le_coneProfile hK (σ.etaOne z); linarith
  have hsq : ((σ.bridgeTwoC z).re + 3 / 2) ^ 2 + (σ.bridgeTwoC z).im ^ 2 =
      coneProfile σ.constK (σ.etaOne z) ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeTwoC_add hθ hz)
    simpa using this
  have hpos := σ.bridgeTwoC_cone_pos hθ hz
  rw [sub_neg_eq_add] at hpos
  have hp := halfArg_polar hG hpos hsq
  rw [cornerConeC, angleConeC, angleConeBlendC, coneLambda, coneRadial, coneStep_eq_one hab hη,
    coneStep_eq_one hφ hl]
  simp only [sub_self, zero_mul, one_mul, zero_add, zero_div]
  rw [angleTwoConeC, ← hp]
  apply Complex.ext <;> simp

theorem exists_hasDerivAt_angleConeC (hθ : 0 < σ.θ₂) {p : ℕ} (hp : 1 ≤ p) (a b : ℝ)
    {φa φb : ℝ} (hφ : φa < φb) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwoC)
    (hord : σ.angleTwoConeC z ≤ σ.angleOneCone z) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t : ℝ =>
      σ.angleConeC p a b φa φb (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) D 0 := by
  have hv := σ.vertexOne_im_pos
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz1.1
  obtain ⟨d₁, hd₁, h₁⟩ := σ.exists_hasDerivAt_angleOneCone hz1
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_angleTwoConeC hθ hz2
  have hφd := σ.hasDerivAt_discAngle_circle hz1
  set τ₀ := coneStep a b (σ.etaOne z) with hτ₀
  have hlam := (hasDerivAt_coneStep φa φb (discAngle (σ.discOne
    (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0)))).comp (0 : ℝ) hφd
  have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul ((hasDerivAt_const (0 : ℝ) Real.pi).sub
    (hφd.const_mul (p : ℝ)))).add ((hasDerivAt_const (0 : ℝ) τ₀).mul
      ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hlam).mul h₁).add (hlam.mul h₂)))
  have e : (fun t : ℝ =>
      σ.angleConeC p a b φa φb (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) =
      ((fun _ => 1 - τ₀) * ((fun _ => Real.pi) - fun t => (p : ℝ) *
        discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)))) +
      (fun _ => τ₀) * ((((fun _ => (1 : ℝ)) - coneStep φa φb ∘ fun t =>
        discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))) *
          fun t => σ.angleOneCone (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) +
        (coneStep φa φb ∘ fun t =>
          discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))) *
          fun t => σ.angleTwoConeC (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) := by
    funext t
    simp only [angleConeC, angleConeBlendC, coneLambda, σ.etaOne_circleCurve hz1.1 t,
      Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hτ₀]
  rw [e]
  refine ⟨_, ?_, h⟩
  simp only [h0, Function.comp_apply, Pi.sub_apply, mul_one, zero_sub]
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg a b (σ.etaOne z)
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one a b (σ.etaOne z)
  have hl0 := coneStep_nonneg φa φb (discAngle (σ.discOne z))
  have hl1 := coneStep_le_one φa φb (discAngle (σ.discOne z))
  have hl' := deriv_coneStep_nonneg hφ (discAngle (σ.discOne z))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hbr : (1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
      coneStep φa φb (discAngle (σ.discOne z)) * d₂ < 0 := by
    have := convex_comb_pos hl0 hl1 (neg_pos.2 hd₁) (neg_pos.2 hd₂)
    linarith
  have hlo : deriv (coneStep φa φb) (discAngle (σ.discOne z)) *
      (σ.angleTwoConeC z - σ.angleOneCone z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hl' (by linarith)
  have key : τ₀ * ((1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
      coneStep φa φb (discAngle (σ.discOne z)) * d₂ +
      deriv (coneStep φa φb) (discAngle (σ.discOne z)) *
        (σ.angleTwoConeC z - σ.angleOneCone z)) + (1 - τ₀) * -(p : ℝ) < 0 := by
    rcases eq_or_lt_of_le hτ0 with h' | h'
    · rw [← h']
      linarith
    · have : τ₀ * ((1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
          coneStep φa φb (discAngle (σ.discOne z)) * d₂ + deriv (coneStep φa φb)
            (discAngle (σ.discOne z)) * (σ.angleTwoConeC z - σ.angleOneCone z)) < 0 :=
        mul_neg_of_pos_of_neg h' (by linarith)
      have : (1 - τ₀) * -(p : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
  linarith [key]

theorem det_fderiv_cornerConeC_ne_zero (hθ : 0 < σ.θ₂) {p : ℕ} (hp : 1 ≤ p) {a b φa φb : ℝ}
    (hab : a < b) (hφ : φa < φb) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwoC)
    (hord : σ.angleTwoConeC z ≤ σ.angleOneCone z) :
    (fderiv ℝ (σ.cornerConeC p a b φa φb) z).det ≠ 0 := by
  have hK := σ.constK_pos
  have hv := σ.vertexOne_im_pos
  have hzv := σ.vertexOne_ne_of_domOne hz1
  have hηgt := coneHeight_gt hv hz1.1 hzv
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_coneRadial hp hab hv hK hηgt
  obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleConeC hθ hp a b hφ hz1 hz2 hord
  have hρd : DifferentiableAt ℝ σ.etaOne z := (σ.contDiffAt_etaOne hz1).differentiableAt (by simp)
  have hΘd := (σ.contDiffAt_angleConeC hθ p a b φa φb hz1 hz2).differentiableAt (by simp)
  have hγ := σ.hasDerivAt_circle_velocity hz1.1
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz1.1
  have hργ : ∀ᶠ t : ℝ in 𝓝 0,
      σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) = σ.etaOne z :=
    Eventually.of_forall fun t => σ.etaOne_circleCurve hz1.1 t
  set Wv := (z - σ.vertexOne) * (normSq (z - conj σ.vertexOne) : ℂ) -
    (z - conj σ.vertexOne) * (normSq (z - σ.vertexOne) : ℂ) with hWv
  have hWne : Wv ≠ 0 := radial_vector_ne hv hz1.1 hzv
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Wv) Wv 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Wv).const_add z
  have hρN0 := hasDerivAt_coneHeight_curve hv hl (by simpa using hz1.1) (by simpa using hzv)
  simp only [ofReal_zero, zero_mul, add_zero] at hρN0
  have hN := normSq_sub_conj_pos hv hz1.1
  have hr1 := norm_coneDisc_lt_one hv hz1.1
  have hr0 : 0 < ‖coneDisc σ.vertexOne z‖ := norm_pos_iff.2 (coneDisc_ne_zero hv hz1.1 hzv)
  have hbracket : 2 * ((z - σ.vertexOne).re * Wv.re + (z - σ.vertexOne).im * Wv.im) *
      normSq (z - conj σ.vertexOne) - normSq (z - σ.vertexOne) *
        (2 * ((z - conj σ.vertexOne).re * Wv.re + (z - conj σ.vertexOne).im * Wv.im)) =
      2 * normSq Wv := by
    have e1 : Wv.re = (z - σ.vertexOne).re * normSq (z - conj σ.vertexOne) -
        (z - conj σ.vertexOne).re * normSq (z - σ.vertexOne) := by
      simp [hWv]
    have e2 : Wv.im = (z - σ.vertexOne).im * normSq (z - conj σ.vertexOne) -
        (z - conj σ.vertexOne).im * normSq (z - σ.vertexOne) := by
      simp [hWv]
    rw [normSq_apply Wv, e1, e2]
    ring
  set bN := σ.vertexOne.im / ((1 - ‖coneDisc σ.vertexOne z‖) ^ 2 * ‖coneDisc σ.vertexOne z‖) *
    ((2 * ((z - σ.vertexOne).re * Wv.re + (z - σ.vertexOne).im * Wv.im) *
      normSq (z - conj σ.vertexOne) - normSq (z - σ.vertexOne) *
        (2 * ((z - conj σ.vertexOne).re * Wv.re + (z - conj σ.vertexOne).im * Wv.im))) /
      normSq (z - conj σ.vertexOne) ^ 2) with hbN
  have hbpos : 0 < bN := by
    rw [hbN, hbracket]
    have : 0 < normSq Wv := normSq_pos.2 hWne
    have : 0 < 1 - ‖coneDisc σ.vertexOne z‖ := by linarith
    positivity
  have hρN : HasDerivAt (fun t : ℝ => σ.etaOne (z + t * Wv)) bN 0 := hρN0
  have hΘN : HasDerivAt (fun t : ℝ => σ.angleConeC p a b φa φb (z + t * Wv))
      (fderiv ℝ (σ.angleConeC p a b φa φb) z Wv) 0 := by
    have hF' : HasFDerivAt (σ.angleConeC p a b φa φb) (fderiv ℝ (σ.angleConeC p a b φa φb) z)
        (z + ((0 : ℝ) : ℂ) * Wv) := by
      rw [ofReal_zero, zero_mul, add_zero]
      exact hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := -(3 / 2 : ℂ))
    (S := coneRadial p a b σ.vertexOne.im σ.constK) (ρ := σ.etaOne)
    (Θ := σ.angleConeC p a b φa φb) hSd hρd hΘd hγ h0 hργ hDd hρN hΘN
  have hfun : (fun u => -(3 / 2 : ℂ) + ((coneRadial p a b σ.vertexOne.im σ.constK
      (σ.etaOne u) : ℝ) : ℂ) * exp ((σ.angleConeC p a b φa φb u : ℂ) * I)) =
      σ.cornerConeC p a b φa φb := rfl
  rw [hfun] at hdet
  intro h0'
  rw [h0', zero_mul] at hdet
  have hS0 : 0 < coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) := by
    have hτ0 := coneStep_nonneg a b (σ.etaOne z)
    have hτ1 := coneStep_le_one a b (σ.etaOne z)
    have hη' : σ.vertexOne.im < σ.etaOne z := hηgt
    have hϖ : 0 < (σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im) :=
      div_pos (by linarith) (by linarith)
    have hG : 0 < coneProfile σ.constK (σ.etaOne z) := by
      have := half_le_coneProfile hK (σ.etaOne z); linarith
    have := convex_comb_pos hτ0 hτ1 (by positivity : 0 <
      ((σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im)) ^ p / 2) hG
    simpa [coneRadial, mul_div_assoc] using this
  have : coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) * S' * D * bN < 0 := by
    have h1 : 0 < coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) * S' := by positivity
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 hD) hbpos
  linarith

theorem bridgeTwoC_im_nonneg (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC)
    (hw : 0 ≤ σ.wallTwo z) : 0 ≤ (σ.bridgeTwoC z).im := by
  rcases eq_or_lt_of_le hw with h | h
  · have : (σ.bridgeTwoC z).im = 0 := by
      simp [bridgeTwoC, innerBridge, ← h]
    rw [this]
  · exact (σ.bridgeTwoC_im_pos hθ hz h).le

theorem angleTwoConeC_le_angleOneCone (hθ : 0 < σ.θ₂) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz2 : z ∈ σ.domTwoC) (hw1 : 0 ≤ σ.wallOne z) (hw2 : 0 ≤ σ.wallTwo z) :
    σ.angleTwoConeC z ≤ σ.angleOneCone z := by
  have hK := σ.constK_pos
  set G := coneProfile σ.constK (σ.etaOne z)
  have hG : 0 < G := by have := half_le_coneProfile hK (σ.etaOne z); linarith
  have h1 : ((σ.bridgeOne z).re + 3 / 2) ^ 2 + (σ.bridgeOne z).im ^ 2 = G ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeOne_add hz1)
    simpa using this
  have h2 : ((σ.bridgeTwoC z).re + 3 / 2) ^ 2 + (σ.bridgeTwoC z).im ^ 2 = G ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeTwoC_add hθ hz2)
    simpa using this
  have hp1 := σ.bridgeOne_cone_pos hz1
  rw [sub_neg_eq_add] at hp1
  have hp2 := σ.bridgeTwoC_cone_pos hθ hz2
  rw [sub_neg_eq_add] at hp2
  have hI1 : 0 ≤ (σ.bridgeOne z).im := by
    rcases eq_or_lt_of_le hw1 with h | h
    · have : (σ.bridgeOne z).im = 0 := by
        simp [bridgeOne, outerBridge, ← h]
      rw [this]
    · exact (σ.bridgeOne_im_pos hz1 h).le
  have hI2 := σ.bridgeTwoC_im_nonneg hθ hz2 hw2
  have hΘ1 : 0 ≤ σ.angleOneCone z := le_of_lt negHalfArg_mem.1
  have hΘ2π : σ.angleTwoConeC z ≤ Real.pi := by
    unfold angleTwoConeC halfArg
    have := Real.arctan_lt_pi_div_two ((σ.bridgeTwoC z).im /
      (coneProfile σ.constK (σ.etaOne z) + ((σ.bridgeTwoC z).re + 3 / 2)))
    linarith
  have hc1 := negHalfArg_cos hG hp1 h1
  have hc2 := halfArg_cos hG hp2 h2
  have hR : (σ.bridgeOne z).re < (σ.bridgeTwoC z).re := by
    have n1 := sq_add_sq_eq_of_norm (σ.norm_bridgeOne hz1)
    have n2 : (σ.bridgeTwoC z).re ^ 2 + (σ.bridgeTwoC z).im ^ 2 < 4 := by
      have := sq_add_sq_eq_of_norm (u := σ.bridgeTwoC z) rfl
      have := σ.norm_bridgeTwoC_lt_two hθ hz2
      nlinarith [norm_nonneg (σ.bridgeTwoC z)]
    have hR2 : 2 < 3 / 2 + coneProfile σ.constK z.im := by
      have := half_lt_coneProfile hK hz1.1.ne'
      linarith
    nlinarith
  by_contra hc
  have hlt : σ.angleOneCone z < σ.angleTwoConeC z := not_le.1 hc
  have := Real.cos_le_cos_of_nonneg_of_le_pi hΘ1 hΘ2π hlt.le
  rw [angleOneCone, angleTwoConeC, hc1, hc2] at this
  have : (σ.bridgeTwoC z).re + 3 / 2 ≤ (σ.bridgeOne z).re + 3 / 2 := by
    rwa [div_le_div_iff_of_pos_right hG] at this
  linarith

/-! ### Wall equivariance -/

theorem angleTwoConeC_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.angleTwoConeC (σ.refl 2 z) = -σ.angleTwoConeC z := by
  rw [angleTwoConeC, angleTwoConeC, σ.bridgeTwoC_refl_two hz, σ.etaOne_refl_two hz, conj_re,
    conj_im, halfArg_neg]

theorem angleConeC_refl_one (p : ℕ) {a b φa φb : ℝ} (hφ : φa < φb) (z : ℂ)
    (hl : |discAngle (σ.discOne z)| ≤ φa) :
    σ.angleConeC p a b φa φb (σ.refl 1 z) = 2 * Real.pi - σ.angleConeC p a b φa φb z := by
  have h1 : discAngle (σ.discOne z) ≤ φa := le_trans (le_abs_self _) hl
  have h2 : -discAngle (σ.discOne z) ≤ φa := le_trans (neg_le_abs _) hl
  rw [angleConeC, angleConeC, angleConeBlendC, angleConeBlendC, coneLambda, coneLambda,
    σ.etaOne_refl_one, σ.discAngle_discOne_refl_one, coneStep_eq_zero hφ h1,
    coneStep_eq_zero hφ h2, σ.angleOneCone_refl_one]
  ring

theorem cornerConeC_refl_one (p : ℕ) {a b φa φb : ℝ} (hφ : φa < φb) (z : ℂ)
    (hl : |discAngle (σ.discOne z)| ≤ φa) :
    σ.cornerConeC p a b φa φb (σ.refl 1 z) = conj (σ.cornerConeC p a b φa φb z) := by
  rw [cornerConeC, cornerConeC, σ.angleConeC_refl_one p hφ z hl, σ.etaOne_refl_one, map_add,
    map_mul, Complex.conj_ofReal, exp_two_pi_sub_mul_I]
  simp [map_neg, map_div₀, map_ofNat]

theorem angleConeC_refl_two {p : ℕ} (hp : σ.θ₁ * p = Real.pi) {a b φa φb : ℝ}
    (hφ : φa < φb) (hb0 : 0 < φb) {z : ℂ} (hz : z ∈ σ.domOne)
    (hl : φb ≤ discAngle (σ.discOne z)) (hl' : φb ≤ 2 * σ.θ₁ - discAngle (σ.discOne z)) :
    σ.angleConeC p a b φa φb (σ.refl 2 z) = -σ.angleConeC p a b φa φb z := by
  have hθ1 := σ.θ₁_le
  have hφ0 : 2 * σ.θ₁ - Real.pi < discAngle (σ.discOne z) := by linarith
  have hr := σ.discAngle_discOne_refl_two hz hφ0
  rw [angleConeC, angleConeC, angleConeBlendC, angleConeBlendC, coneLambda, coneLambda,
    σ.etaOne_refl_two hz.1, hr, coneStep_eq_one hφ hl, coneStep_eq_one hφ hl',
    σ.angleTwoConeC_refl_two hz.1]
  have e : (p : ℝ) * (2 * σ.θ₁ - discAngle (σ.discOne z)) =
      2 * Real.pi - p * discAngle (σ.discOne z) := by
    rw [← hp]
    ring
  rw [e]
  ring

theorem cornerConeC_refl_two {p : ℕ} (hp : σ.θ₁ * p = Real.pi) {a b φa φb : ℝ}
    (hφ : φa < φb) (hb0 : 0 < φb) {z : ℂ} (hz : z ∈ σ.domOne)
    (hl : φb ≤ discAngle (σ.discOne z)) (hl' : φb ≤ 2 * σ.θ₁ - discAngle (σ.discOne z)) :
    σ.cornerConeC p a b φa φb (σ.refl 2 z) = conj (σ.cornerConeC p a b φa φb z) := by
  rw [cornerConeC, cornerConeC, σ.angleConeC_refl_two hp hφ hb0 hz hl hl', σ.etaOne_refl_two hz.1,
    map_add, map_mul, Complex.conj_ofReal, ← exp_neg_mul_I_eq_conj]
  simp [map_neg, map_div₀, map_ofNat]

end ConeShape

end GC.Seifert
