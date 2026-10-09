import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldFermi

/-!
# Separation of the cone discs and the blend of the outer corner

Lane A4, layout (errata after review 15 to the design
`docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`). The virtual heights of the two
vertices of the circle wall satisfy `η₁ η₂ ≥ K` on the whole upper half-plane
(`constK_le_coneHeight_mul`, `constK_le_coneHeight_mul_cuspZero`), the hyperbolic triangle
inequality `d(z, v₁) + d(z, v₂) ≥ d(v₁, v₂)` (horocyclic for the cusp), proved from the height
identities of the Fermi chart: `x₂ = η₂/√K ≥ Im ζ` and then `1/x₂` lies between the roots of the
quadratic of `x₁ = η₁/√K` (`le_mul_of_height_identities`).

Consequently the closed cone discs `η₂ ≤ √K/λ` and `η₁ ≤ √K/λ` (`λ = 21/20`) are separated by the
ratio `η₁/η₂ ≥ λ²` resp. `≤ λ⁻²`, uniformly in the shape. The blend function of the outer corner
`blendFn z = 2x/W - 1 + 42 (η₂ - η₁)/(η₂ + η₁)` replaces the vertical strip of the design: it is
`≤ -1` on the closed disc at `v₂` (for `x ≤ W`) and near wall 0 where `η₂ ≤ η₁`, `≥ 1` on the closed
disc at `v₁` (for `x ≥ 0`) and near wall 1 where `η₁ ≤ η₂` (`blendFn_le_of_etaTwo_le`,
`one_le_blendFn_of_etaOne_le`, `blendFn_lt_of_wallZero`, `blendFn_gt_of_wallOne`); it increases
along horizontal lines in the strip `0 ≤ x ≤ W` because `η₂` increases and `η₁` decreases there,
so a smooth step of it is an admissible weight for the corner at `∞` (no separation in `x` needed).
-/

set_option autoImplicit false

noncomputable section

open Complex

namespace GC.Seifert

theorem le_mul_of_height_identities {s K e₁ e₂ Y N t₁ t₂ : ℝ} (hs : 0 < s) (hsK : s ^ 2 = K)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hY : 0 < Y) (hN : Y ^ 2 ≤ N) (ht₁ : 0 ≤ t₁)
    (htt : t₁ * t₂ < 1) (hg₁ : t₁ * K ≤ e₁ ^ 2) (hg₂ : t₂ * K ≤ e₂ ^ 2)
    (I1 : s * e₁ * (1 + t₁ * N) = Y * (e₁ ^ 2 + t₁ * K))
    (I2 : s * e₂ * (N + t₂) = Y * (e₂ ^ 2 + t₂ * K)) : K ≤ e₁ * e₂ := by
  subst hsK
  have step1 : s * Y ≤ e₂ := by
    by_contra hc
    have hlt : e₂ < s * Y := not_le.1 hc
    have key : e₂ * (s ^ 2 * Y * (Y ^ 2 - N)) =
        Y * (s * Y - e₂) * (e₂ * s * Y - t₂ * s ^ 2) := by
      linear_combination (-(s * Y)) * I2
    have h1 : e₂ * (s ^ 2 * Y * (Y ^ 2 - N)) ≤ 0 := by
      have : Y ^ 2 - N ≤ 0 := by linarith
      have : 0 ≤ e₂ * (s ^ 2 * Y) := by positivity
      nlinarith
    have h2 : 0 < e₂ * s * Y - t₂ * s ^ 2 := by nlinarith
    have h3 : 0 < Y * (s * Y - e₂) * (e₂ * s * Y - t₂ * s ^ 2) := by
      have : 0 < s * Y - e₂ := by linarith
      positivity
    linarith
  have hG : Y * s ^ 4 - s ^ 3 * (1 + t₁ * N) * e₂ + t₁ * s ^ 2 * Y * e₂ ^ 2 =
      s ^ 3 * (1 - t₁ * t₂) * (Y * s - e₂) := by
    linear_combination (-(s ^ 2 * t₁)) * I2
  have hGle : Y * s ^ 4 - s ^ 3 * (1 + t₁ * N) * e₂ + t₁ * s ^ 2 * Y * e₂ ^ 2 ≤ 0 := by
    rw [hG]
    have h0 : 0 < 1 - t₁ * t₂ := by linarith
    have : 0 ≤ s ^ 3 * (1 - t₁ * t₂) := by positivity
    nlinarith
  by_contra hc
  have hlt : e₁ * e₂ < s ^ 2 := not_le.1 hc
  have key2 : e₁ * (Y * s ^ 4 - s ^ 3 * (1 + t₁ * N) * e₂ + t₁ * s ^ 2 * Y * e₂ ^ 2) =
      Y * (s ^ 2 - e₁ * e₂) * (e₁ * s ^ 2 - t₁ * s ^ 2 * e₂) := by
    linear_combination (-(e₂ * s ^ 2)) * I1
  have h4 : 0 < e₁ * s ^ 2 - t₁ * s ^ 2 * e₂ := by
    have hs2 : 0 < s ^ 2 := by positivity
    rcases ht₁.lt_or_eq with ht | ht
    · have h5 : t₁ * (e₁ * e₂) < t₁ * s ^ 2 := mul_lt_mul_of_pos_left hlt ht
      have h6 : t₁ * e₂ < e₁ := by nlinarith
      nlinarith
    · rw [← ht]
      nlinarith
  have h5 : 0 < Y * (s ^ 2 - e₁ * e₂) * (e₁ * s ^ 2 - t₁ * s ^ 2 * e₂) := by
    have : 0 < s ^ 2 - e₁ * e₂ := by linarith
    positivity
  have h6 : e₁ * (Y * s ^ 4 - s ^ 3 * (1 + t₁ * N) * e₂ + t₁ * s ^ 2 * Y * e₂ ^ 2) ≤ 0 := by
    nlinarith
  linarith

namespace ConeShape

variable (σ : ConeShape)

def etaTwo (z : ℂ) : ℝ := if σ.θ₂ = 0 then cuspZeroHeight z else coneHeight σ.vertexTwo z

def blendFn (z : ℂ) : ℝ :=
  2 * z.re / σ.width - 1 +
    42 * (σ.etaTwo z - coneHeight σ.vertexOne z) / (σ.etaTwo z + coneHeight σ.vertexOne z)

theorem vertexTwo_im_pos (hθ : 0 < σ.θ₂) : 0 < σ.vertexTwo.im := by
  rw [vertexTwo_im]
  have := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  positivity

theorem tOne_mul_tTwo_lt_one : σ.tOne * σ.tTwo < 1 := by
  have h1 := σ.one_add_cos_θ₁_pos
  have h2 := σ.one_add_cos_θ₂_pos
  have hs := σ.cos_add_cos_pos
  rw [tOne, tTwo, div_mul_div_comm, div_lt_one (by positivity)]
  nlinarith

theorem im_sq_le_normSq (ζ : ℂ) : ζ.im ^ 2 ≤ normSq ζ := by
  rw [normSq_apply]
  nlinarith [sq_nonneg ζ.re]

theorem etaTwo_pos {z : ℂ} (hz : 0 < z.im) : 0 < σ.etaTwo z := by
  unfold etaTwo
  split_ifs with h
  · have : 0 < normSq z := normSq_pos.2 (fun h0 => by rw [h0] at hz; simp at hz)
    unfold cuspZeroHeight
    positivity
  · exact coneHeight_pos (σ.vertexTwo_im_pos (lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm h))) hz

theorem constK_le_coneHeight_mul (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    σ.constK ≤ coneHeight σ.vertexOne z * coneHeight σ.vertexTwo z := by
  have hv₂ := σ.vertexTwo_im_pos hθ
  have hg₁ : σ.tOne * σ.constK ≤ coneHeight σ.vertexOne z ^ 2 := by
    rw [← σ.vertexOne_im_sq]
    have := coneHeight_ge σ.vertexOne_im_pos hz
    nlinarith [σ.vertexOne_im_pos]
  have hg₂ : σ.tTwo * σ.constK ≤ coneHeight σ.vertexTwo z ^ 2 := by
    rw [← σ.vertexTwo_im_sq]
    have := coneHeight_ge hv₂ hz
    nlinarith
  have I1 := σ.sqrt_constK_mul_coneHeight_one hz
  have I2 := σ.sqrt_constK_mul_coneHeight_two hθ hz
  rw [σ.vertexOne_im_sq] at I1
  rw [σ.vertexTwo_im_sq] at I2
  exact le_mul_of_height_identities σ.sqrt_constK_pos (Real.sq_sqrt σ.constK_pos.le)
    (coneHeight_pos σ.vertexOne_im_pos hz) (coneHeight_pos hv₂ hz) (σ.fermiChart_im_pos hz)
    (im_sq_le_normSq _) σ.tOne_pos.le σ.tOne_mul_tTwo_lt_one hg₁ hg₂ I1 I2

theorem constK_le_coneHeight_mul_cuspZero (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    σ.constK ≤ coneHeight σ.vertexOne z * cuspZeroHeight z := by
  have h0 : 0 < cuspZeroHeight z := by
    have := σ.etaTwo_pos hz
    simpa [etaTwo, hθ] using this
  have hg₁ : σ.tOne * σ.constK ≤ coneHeight σ.vertexOne z ^ 2 := by
    rw [← σ.vertexOne_im_sq]
    have := coneHeight_ge σ.vertexOne_im_pos hz
    nlinarith [σ.vertexOne_im_pos]
  have I1 := σ.sqrt_constK_mul_coneHeight_one hz
  rw [σ.vertexOne_im_sq] at I1
  have I2' := σ.sqrt_constK_mul_normSq_fermiChart hθ hz
  have I2 : Real.sqrt σ.constK * cuspZeroHeight z * (normSq (σ.fermiChart z) + 0) =
      (σ.fermiChart z).im * (cuspZeroHeight z ^ 2 + 0 * σ.constK) := by
    linear_combination cuspZeroHeight z * I2'
  exact le_mul_of_height_identities σ.sqrt_constK_pos (Real.sq_sqrt σ.constK_pos.le)
    (coneHeight_pos σ.vertexOne_im_pos hz) h0 (σ.fermiChart_im_pos hz)
    (im_sq_le_normSq _) σ.tOne_pos.le (by simp) hg₁ (by rw [zero_mul]; positivity) I1 I2

theorem constK_le_coneHeight_mul_etaTwo {z : ℂ} (hz : 0 < z.im) :
    σ.constK ≤ coneHeight σ.vertexOne z * σ.etaTwo z := by
  unfold etaTwo
  split_ifs with h
  · exact σ.constK_le_coneHeight_mul_cuspZero h hz
  · exact σ.constK_le_coneHeight_mul (lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm h)) hz

theorem ratio_le_of_etaTwo_le {z : ℂ} (hz : 0 < z.im)
    (h : σ.etaTwo z ≤ Real.sqrt σ.constK / (21 / 20)) :
    441 / 400 * σ.etaTwo z ≤ coneHeight σ.vertexOne z := by
  have hK := σ.constK_le_coneHeight_mul_etaTwo hz
  have h2 := σ.etaTwo_pos hz
  have hs := σ.sqrt_constK_pos
  have hss : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  have h' : 21 / 20 * σ.etaTwo z ≤ Real.sqrt σ.constK := by
    rw [le_div_iff₀ (by norm_num)] at h
    linarith
  have : (21 / 20 * σ.etaTwo z) ^ 2 ≤ σ.constK := by
    rw [← hss]
    exact pow_le_pow_left₀ (by positivity) h' 2
  nlinarith

theorem ratio_le_of_etaOne_le {z : ℂ} (hz : 0 < z.im)
    (h : coneHeight σ.vertexOne z ≤ Real.sqrt σ.constK / (21 / 20)) :
    441 / 400 * coneHeight σ.vertexOne z ≤ σ.etaTwo z := by
  have hK := σ.constK_le_coneHeight_mul_etaTwo hz
  have h1 := coneHeight_pos σ.vertexOne_im_pos hz
  have hs := σ.sqrt_constK_pos
  have hss : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  have h' : 21 / 20 * coneHeight σ.vertexOne z ≤ Real.sqrt σ.constK := by
    rw [le_div_iff₀ (by norm_num)] at h
    linarith
  have : (21 / 20 * coneHeight σ.vertexOne z) ^ 2 ≤ σ.constK := by
    rw [← hss]
    exact pow_le_pow_left₀ (by positivity) h' 2
  nlinarith

theorem blendFn_le_of_etaTwo_le {z : ℂ} (hz : 0 < z.im) (hx : z.re ≤ σ.width)
    (h : σ.etaTwo z ≤ Real.sqrt σ.constK / (21 / 20)) : σ.blendFn z ≤ -1 := by
  have hr := σ.ratio_le_of_etaTwo_le hz h
  have h1 := coneHeight_pos σ.vertexOne_im_pos hz
  have h2 := σ.etaTwo_pos hz
  have hW := σ.width_pos
  have hxW : 2 * z.re / σ.width ≤ 2 := by
    rw [div_le_iff₀ hW]
    linarith
  have hg : 42 * (σ.etaTwo z - coneHeight σ.vertexOne z) /
      (σ.etaTwo z + coneHeight σ.vertexOne z) ≤ -2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  unfold blendFn
  linarith

theorem one_le_blendFn_of_etaOne_le {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re)
    (h : coneHeight σ.vertexOne z ≤ Real.sqrt σ.constK / (21 / 20)) : 1 ≤ σ.blendFn z := by
  have hr := σ.ratio_le_of_etaOne_le hz h
  have h1 := coneHeight_pos σ.vertexOne_im_pos hz
  have h2 := σ.etaTwo_pos hz
  have hW := σ.width_pos
  have hxW : 0 ≤ 2 * z.re / σ.width := by positivity
  have hg : 2 ≤ 42 * (σ.etaTwo z - coneHeight σ.vertexOne z) /
      (σ.etaTwo z + coneHeight σ.vertexOne z) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold blendFn
  linarith

theorem blendFn_le_of_wallZero {z : ℂ} (hz : 0 < z.im) (hx : z.re ≤ 0)
    (h : σ.etaTwo z ≤ coneHeight σ.vertexOne z) : σ.blendFn z ≤ -1 := by
  have h1 := coneHeight_pos σ.vertexOne_im_pos hz
  have h2 := σ.etaTwo_pos hz
  have hW := σ.width_pos
  have hxW : 2 * z.re / σ.width ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hW.le
  have hg : 42 * (σ.etaTwo z - coneHeight σ.vertexOne z) /
      (σ.etaTwo z + coneHeight σ.vertexOne z) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  unfold blendFn
  linarith

theorem one_le_blendFn_of_wallOne {z : ℂ} (hz : 0 < z.im) (hx : σ.width ≤ z.re)
    (h : coneHeight σ.vertexOne z ≤ σ.etaTwo z) : 1 ≤ σ.blendFn z := by
  have h1 := coneHeight_pos σ.vertexOne_im_pos hz
  have h2 := σ.etaTwo_pos hz
  have hW := σ.width_pos
  have hxW : 2 ≤ 2 * z.re / σ.width := by
    rw [le_div_iff₀ hW]
    linarith
  have hg : 0 ≤ 42 * (σ.etaTwo z - coneHeight σ.vertexOne z) /
      (σ.etaTwo z + coneHeight σ.vertexOne z) := by
    apply div_nonneg <;> linarith
  unfold blendFn
  linarith

end ConeShape

end GC.Seifert
