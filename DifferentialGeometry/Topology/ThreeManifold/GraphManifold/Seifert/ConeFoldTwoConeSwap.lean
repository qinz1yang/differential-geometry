import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeCorner

/-!
# The swap of the two cones

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §2, two-cone
shapes). For a shape with a second cone (`θ₂ > 0`) the swapped shape `σ.swap hθ` has the angles
`(θ₂, θ₁)`; it has the same width `W` and the same constant `K`, and the anti-holomorphic
isometry `swapPt z = W - z̄` carries the triangle of `σ` onto that of the swap, exchanging the
vertices (`swap_vertexOne`, `swap_vertexTwo`), the walls `0 ↔ 1` and fixing the circle wall
(`swap_wallSide_zero/one/two`, `swap_refl_zero/one/two`). Disc coordinates are conjugated
(`coneDisc_swapPt`), so the virtual heights are exchanged (`swap_etaOne`, `swap_etaTwoC`), and
under the target mirror `u ↦ -ū` the wall-1 bridge of the swap is the wall-0 bridge of `σ`
(`swap_bridgeOne`), and on the triangle the two-cone wall-2 bridges correspond
(`swap_bridgeTwoC`, from equal moduli and the common sign of the wall functions). Maps of the
form `-conj ∘ g ∘ swapPt` have the regularity and the Jacobian of `g` (`contDiffAt_mirror`,
`det_fderiv_mirror`): this is how the corner at `v₂` is obtained from the corner at `v₁` of the
swap.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem outerBridge_neg_b (K y η w q : ℝ) :
    outerBridge K (-(3 / 2)) y η w q = -conj (outerBridge K (3 / 2) y η w q) := by
  have hq : outerCofactor K (-(3 / 2)) y η q = outerCofactor K (3 / 2) y η q := by
    simp [outerCofactor, abs_neg]
  apply Complex.ext
  · simp only [outerBridge, hq, twoCircle_re, neg_re, conj_re]
    ring
  · simp [outerBridge, hq, twoCircle_im, abs_neg]

theorem twoCircle_congr_im {a b A B w P w' P' : ℝ}
    (h : w * Real.sqrt P = w' * Real.sqrt P') :
    twoCircle a b A B w P = twoCircle a b A B w' P' := by
  unfold twoCircle
  rw [h]

theorem twoCircle_neg_ab (a b A B w P : ℝ) :
    twoCircle (-a) (-b) A B w P = -conj (twoCircle a b A B w P) := by
  apply Complex.ext
  · simp only [twoCircle_re, neg_re, conj_re]
    by_cases hb : b - a = 0
    · have : -b - -a = 0 := by linarith
      rw [hb, this]
      simp
    · have : -b - -a ≠ 0 := by intro h; apply hb; linarith
      field_simp
      ring
  · simp only [twoCircle_im, neg_im, conj_im, neg_neg]
    rw [show -b - -a = -(b - a) by ring, abs_neg]

namespace ConeShape

variable (σ : ConeShape)

def swap (hθ : 0 < σ.θ₂) : ConeShape where
  θ₁ := σ.θ₂
  θ₂ := σ.θ₁
  θ₁_pos := hθ
  θ₁_le := σ.θ₂_le
  θ₂_nonneg := σ.θ₁_pos.le
  θ₂_le := σ.θ₁_le
  sum_lt := by linarith [σ.sum_lt]

def swapPt (z : ℂ) : ℂ := (σ.width : ℂ) - conj z

section Swap

variable (hθ : 0 < σ.θ₂)

@[simp] theorem swap_θ₁ : (σ.swap hθ).θ₁ = σ.θ₂ := rfl

@[simp] theorem swap_θ₂ : (σ.swap hθ).θ₂ = σ.θ₁ := rfl

theorem swap_swap : (σ.swap hθ).swap σ.θ₁_pos = σ := by
  cases σ
  rfl

theorem swap_width : (σ.swap hθ).width = σ.width := by
  unfold width
  simp only [swap_θ₁, swap_θ₂]
  ring

theorem swap_centre : (σ.swap hθ).centre = σ.width - σ.centre := by
  unfold centre width
  simp only [swap_θ₂]
  ring

theorem swap_constK : (σ.swap hθ).constK = σ.constK := by
  unfold constK
  simp only [swap_θ₁, swap_θ₂]
  ring

theorem swap_swapPt_eq : (σ.swap hθ).swapPt = σ.swapPt := by
  funext z
  rw [swapPt, swapPt, σ.swap_width hθ]

@[simp] theorem swapPt_re (z : ℂ) : (σ.swapPt z).re = σ.width - z.re := by simp [swapPt]

@[simp] theorem swapPt_im (z : ℂ) : (σ.swapPt z).im = z.im := by simp [swapPt]

theorem swapPt_swapPt (z : ℂ) : σ.swapPt (σ.swapPt z) = z := by
  apply Complex.ext <;> simp

theorem swap_vertexOne : (σ.swap hθ).vertexOne = σ.swapPt σ.vertexTwo := by
  apply Complex.ext
  · rw [vertexOne_re, swapPt_re, vertexTwo_re, sub_zero, σ.swap_width hθ]
  · rw [vertexOne_im, swapPt_im, vertexTwo_im, swap_θ₁]

theorem swap_vertexTwo : (σ.swap hθ).vertexTwo = σ.swapPt σ.vertexOne := by
  apply Complex.ext
  · rw [vertexTwo_re, swapPt_re, vertexOne_re, sub_self]
  · rw [vertexTwo_im, swapPt_im, vertexOne_im, swap_θ₂]

theorem swap_wallSide_zero (z : ℂ) : (σ.swap hθ).wallSide 0 (σ.swapPt z) = σ.wallSide 1 z := by
  simp [wallSide]

theorem swap_wallSide_one (z : ℂ) : (σ.swap hθ).wallSide 1 (σ.swapPt z) = σ.wallSide 0 z := by
  simp only [wallSide, swapPt_re, σ.swap_width hθ]
  ring

theorem swap_wallSide_two (z : ℂ) : (σ.swap hθ).wallSide 2 (σ.swapPt z) = σ.wallSide 2 z := by
  simp only [wallSide, swapPt_re, swapPt_im, σ.swap_centre hθ]
  ring

theorem swapPt_mem_triangle {z : ℂ} : σ.swapPt z ∈ (σ.swap hθ).triangle ↔ z ∈ σ.triangle := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨by simpa using h0, fun i => ?_⟩
    fin_cases i
    · have := h 1; rwa [σ.swap_wallSide_one hθ] at this
    · have := h 0; rwa [σ.swap_wallSide_zero hθ] at this
    · have := h 2; rwa [σ.swap_wallSide_two hθ] at this
  · rintro ⟨h0, h⟩
    refine ⟨by simpa using h0, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ (σ.swap hθ).wallSide 0 (σ.swapPt z)
      rw [σ.swap_wallSide_zero hθ]; exact h 1
    · change 0 ≤ (σ.swap hθ).wallSide 1 (σ.swapPt z)
      rw [σ.swap_wallSide_one hθ]; exact h 0
    · change 0 ≤ (σ.swap hθ).wallSide 2 (σ.swapPt z)
      rw [σ.swap_wallSide_two hθ]; exact h 2

theorem swap_refl_one (z : ℂ) : (σ.swap hθ).refl 1 (σ.swapPt z) = σ.swapPt (σ.refl 0 z) := by
  simp only [refl, swapPt, σ.swap_width hθ, map_sub, map_neg, Complex.conj_conj,
    Complex.conj_ofReal]
  ring

theorem swap_refl_zero (z : ℂ) : (σ.swap hθ).refl 0 (σ.swapPt z) = σ.swapPt (σ.refl 1 z) := by
  simp only [refl, swapPt, map_sub, Complex.conj_conj, Complex.conj_ofReal, map_mul, map_ofNat]
  ring

theorem swap_refl_two {z : ℂ} (hz : 0 < z.im) :
    (σ.swap hθ).refl 2 (σ.swapPt z) = σ.swapPt (σ.refl 2 z) := by
  have h1 : (z : ℂ) - σ.centre ≠ 0 := σ.centre_ne hz
  have h2 : conj z - σ.centre ≠ 0 := σ.conj_centre_ne hz
  simp only [refl, swapPt, σ.swap_centre hθ, map_sub, map_add, map_div₀, Complex.conj_conj,
    Complex.conj_ofReal, map_one, map_ofNat]
  have h3 : (σ.width : ℂ) - z - ((σ.width : ℂ) - σ.centre) ≠ 0 := by
    intro h; apply h1; linear_combination -h
  push_cast
  field_simp
  ring

theorem coneDisc_swapPt (a z : ℂ) :
    coneDisc (σ.swapPt a) (σ.swapPt z) = conj (coneDisc a z) := by
  simp only [coneDisc, swapPt, map_div₀, map_sub, Complex.conj_conj, Complex.conj_ofReal]
  conv_lhs => rw [← neg_div_neg_eq]
  congr 1 <;> ring

theorem swap_discOne (z : ℂ) : (σ.swap hθ).discOne (σ.swapPt z) = conj (σ.discTwo z) := by
  rw [discOne, σ.swap_vertexOne hθ, coneDisc_swapPt, discTwo]

theorem swap_discTwo (z : ℂ) : (σ.swap hθ).discTwo (σ.swapPt z) = conj (σ.discOne z) := by
  rw [discTwo, σ.swap_vertexTwo hθ, coneDisc_swapPt, discOne]

theorem swap_etaOne (z : ℂ) : (σ.swap hθ).etaOne (σ.swapPt z) = σ.etaTwoC z := by
  simp only [etaOne, etaTwoC, coneHeight]
  rw [← discOne, σ.swap_discOne hθ, Complex.norm_conj, discTwo, σ.swap_vertexOne hθ, swapPt_im]

theorem swap_etaTwoC (z : ℂ) : (σ.swap hθ).etaTwoC (σ.swapPt z) = σ.etaOne z := by
  simp only [etaOne, etaTwoC, coneHeight]
  rw [← discTwo, σ.swap_discTwo hθ, Complex.norm_conj, discOne, σ.swap_vertexTwo hθ, swapPt_im]

theorem swap_wallOne (z : ℂ) : (σ.swap hθ).wallOne (σ.swapPt z) = σ.wallZeroC z := by
  rw [wallOne, σ.swap_discOne hθ, conj_im, wallZeroC]

theorem swap_cofOne (z : ℂ) : (σ.swap hθ).cofOne (σ.swapPt z) = σ.cofZeroC z := by
  simp only [cofOne, cofZeroC, σ.swap_discOne hθ, Complex.norm_conj, conj_re, conj_im, neg_sq]
  rw [σ.swap_vertexOne hθ, swapPt_im]

theorem swap_bridgeOne (z : ℂ) :
    (σ.swap hθ).bridgeOne (σ.swapPt z) = -conj (σ.bridgeZeroC z) := by
  rw [bridgeOne, bridgeZeroC, σ.swap_constK hθ, swapPt_im, σ.swap_etaOne hθ, σ.swap_wallOne hθ,
    σ.swap_cofOne hθ, ← outerBridge_neg_b]

theorem swap_bridgeZeroC (z : ℂ) :
    (σ.swap hθ).bridgeZeroC (σ.swapPt z) = -conj (σ.bridgeOne z) := by
  have h := ((σ.swap hθ).swap_bridgeOne σ.θ₁_pos (σ.swapPt z))
  rw [σ.swap_swap hθ, σ.swap_swapPt_eq hθ, σ.swapPt_swapPt] at h
  rw [h, map_neg, Complex.conj_conj, neg_neg]

theorem swap_sinhN (z : ℂ) : (σ.swap hθ).sinhN (σ.swapPt z) = σ.sinhN z := by
  rw [sinhN, sinhN, σ.swap_wallSide_two hθ, swapPt_im]

theorem swap_tCone : (σ.swap hθ).tCone = σ.tCone := by
  unfold tCone
  simp only [swap_θ₁, swap_θ₂]
  rw [add_comm, ← Real.cos_neg ((σ.θ₂ - σ.θ₁) / 2)]
  congr 2
  ring

theorem swap_foldH : (σ.swap hθ).foldH = σ.foldH := by
  rw [foldH, foldH, σ.swap_constK hθ]

theorem swap_vertexOne_im : (σ.swap hθ).vertexOne.im = σ.vertexTwo.im := rfl

theorem swap_vertexTwo_im : (σ.swap hθ).vertexTwo.im = σ.vertexOne.im := rfl

theorem swap_discAngle (z : ℂ) :
    discAngle ((σ.swap hθ).discOne (σ.swapPt z)) = -discAngle (σ.discTwo z) := by
  rw [σ.swap_discOne hθ, discAngle_conj]

theorem wallTwo_mul_normSq (z : ℂ) :
    σ.wallTwo z * normSq (z - conj σ.vertexOne) = Real.sin σ.θ₁ * σ.wallSide 2 z := by
  have h := σ.im_rot_coneDisc_vertexOne_mul z
  rw [wallTwo, discOne, neg_mul, h, neg_neg]

theorem swap_wallTwo_mul (z : ℂ) :
    (σ.swap hθ).wallTwo (σ.swapPt z) * normSq (σ.swapPt z - conj (σ.swap hθ).vertexOne) =
      Real.sin σ.θ₂ * σ.wallSide 2 z := by
  rw [(σ.swap hθ).wallTwo_mul_normSq, σ.swap_wallSide_two hθ, swap_θ₁]

theorem swap_mem_domTwoC_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) (hzv1 : z ≠ σ.vertexOne)
    (hzv2 : z ≠ σ.vertexTwo) : σ.swapPt z ∈ (σ.swap hθ).domTwoC := by
  refine (σ.swap hθ).mem_domTwoC_of_mem_triangle σ.θ₁_pos ((σ.swapPt_mem_triangle hθ).2 hz)
    (fun h => hzv2 ?_) (fun h => hzv1 ?_)
  · rw [σ.swap_vertexOne hθ] at h
    rw [← σ.swapPt_swapPt z, h, σ.swapPt_swapPt]
  · rw [σ.swap_vertexTwo hθ] at h
    rw [← σ.swapPt_swapPt z, h, σ.swapPt_swapPt]

theorem innerCofactor_eq (K η₂ η₁ q : ℝ) :
    innerCofactor K η₂ η₁ q = (coneProfile K η₂ + coneProfile K η₁ + 3) *
      (9 - (coneProfile K η₂ - coneProfile K η₁) ^ 2) *
        (2 * (η₁ * η₂ + K) / ((η₂ ^ 2 + K) * (η₁ ^ 2 + K))) * q := by
  unfold innerCofactor
  ring

theorem swap_bridgeTwoC {z : ℂ} (hz : z ∈ σ.domTwoC) (hz' : σ.swapPt z ∈ (σ.swap hθ).domTwoC) :
    (σ.swap hθ).bridgeTwoC (σ.swapPt z) = -conj (σ.bridgeTwoC z) := by
  have hK := σ.constK_pos
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hη₁ := σ.etaOne_pos hz.1
  have hη₂ := σ.etaTwoC_pos hθ hz.1
  have hq := σ.cofTwoC_pos hθ hz
  have hq' := (σ.swap hθ).cofTwoC_pos σ.θ₁_pos hz'
  have hd := σ.etaOne_mul_etaTwoC_sub hθ hz
  have hd' := (σ.swap hθ).etaOne_mul_etaTwoC_sub σ.θ₁_pos hz'
  rw [σ.swap_etaOne hθ, σ.swap_etaTwoC hθ, σ.swap_constK hθ] at hd'
  set w := σ.wallTwo z
  set w' := (σ.swap hθ).wallTwo (σ.swapPt z)
  set q := σ.cofTwoC z
  set q' := (σ.swap hθ).cofTwoC (σ.swapPt z)
  have hww : w ^ 2 * q = w' ^ 2 * q' := by linarith
  set N := normSq (z - conj σ.vertexOne)
  set N' := normSq (σ.swapPt z - conj (σ.swap hθ).vertexOne)
  have hN : 0 < N := normSq_sub_conj_pos hv1 hz.1
  have hN' : 0 < N' := normSq_sub_conj_pos (σ.swap hθ).vertexOne_im_pos hz'.1
  have hs1 := σ.sin_θ₁_pos
  have hs2 : 0 < Real.sin σ.θ₂ :=
    Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  have hw : w = Real.sin σ.θ₁ / N * σ.wallSide 2 z := by
    rw [div_mul_eq_mul_div, eq_div_iff hN.ne', ← σ.wallTwo_mul_normSq]
  have hw' : w' = Real.sin σ.θ₂ / N' * σ.wallSide 2 z := by
    rw [div_mul_eq_mul_div, eq_div_iff hN'.ne', ← σ.swap_wallTwo_mul hθ]
  set a := Real.sin σ.θ₁ / N
  set b := Real.sin σ.θ₂ / N'
  have ha : 0 < a := div_pos hs1 hN
  have hb : 0 < b := div_pos hs2 hN'
  have key : w * Real.sqrt q = w' * Real.sqrt q' := by
    rw [hw, hw']
    by_cases hs : σ.wallSide 2 z = 0
    · rw [hs]; ring
    · have h2 : a ^ 2 * q = b ^ 2 * q' := by
        rw [hw, hw'] at hww
        have : (σ.wallSide 2 z) ^ 2 ≠ 0 := pow_ne_zero 2 hs
        have e : (σ.wallSide 2 z) ^ 2 * (a ^ 2 * q) = (σ.wallSide 2 z) ^ 2 * (b ^ 2 * q') := by
          linear_combination hww
        exact mul_left_cancel₀ this e
      have h3 : a * Real.sqrt q = b * Real.sqrt q' := by
        rw [← Real.sqrt_sq ha.le, ← Real.sqrt_sq hb.le, ← Real.sqrt_mul (sq_nonneg _),
          ← Real.sqrt_mul (sq_nonneg _), h2]
      calc a * σ.wallSide 2 z * Real.sqrt q = (a * Real.sqrt q) * σ.wallSide 2 z := by ring
        _ = (b * Real.sqrt q') * σ.wallSide 2 z := by rw [h3]
        _ = b * σ.wallSide 2 z * Real.sqrt q' := by ring
  rw [bridgeTwoC, bridgeTwoC, σ.swap_etaOne hθ, σ.swap_etaTwoC hθ, σ.swap_constK hθ, innerBridge,
    innerBridge, ← twoCircle_neg_ab]
  conv_rhs => rw [twoCircle_swap, neg_neg]
  set C := (coneProfile σ.constK (σ.etaTwoC z) + coneProfile σ.constK (σ.etaOne z) + 3) *
    (9 - (coneProfile σ.constK (σ.etaTwoC z) - coneProfile σ.constK (σ.etaOne z)) ^ 2) *
      (2 * (σ.etaOne z * σ.etaTwoC z + σ.constK) /
        ((σ.etaTwoC z ^ 2 + σ.constK) * (σ.etaOne z ^ 2 + σ.constK))) with hC
  have hC' : (coneProfile σ.constK (σ.etaOne z) + coneProfile σ.constK (σ.etaTwoC z) + 3) *
      (9 - (coneProfile σ.constK (σ.etaOne z) - coneProfile σ.constK (σ.etaTwoC z)) ^ 2) *
      (2 * (σ.etaTwoC z * σ.etaOne z + σ.constK) /
        ((σ.etaOne z ^ 2 + σ.constK) * (σ.etaTwoC z ^ 2 + σ.constK))) = C := by
    rw [hC]; ring
  have hC0 : 0 ≤ C := by
    have h1 := innerCofactor_pos hK hη₂ hη₁ hq
    rw [innerCofactor_eq, ← hC] at h1
    nlinarith [h1]
  apply twoCircle_congr_im
  rw [innerCofactor_eq, innerCofactor_eq, hC', ← hC, Real.sqrt_mul hC0, Real.sqrt_mul hC0]
  linear_combination (Real.sqrt C) * key.symm

/-! ### Mirrored maps -/

theorem contDiffAt_mirror {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℝ ∞ g (σ.swapPt z)) :
    ContDiffAt ℝ ∞ (fun w => -conj (g (σ.swapPt w))) z := by
  have hs : ContDiffAt ℝ ∞ σ.swapPt z :=
    (contDiffAt_const.sub (conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt)
  exact (-(conjCLE : ℂ →L[ℝ] ℂ)).contDiff.contDiffAt.comp z (hg.comp z hs)

theorem det_neg_conj_comp (A : ℂ →L[ℝ] ℂ) :
    ((-(conjCLE : ℂ →L[ℝ] ℂ)).comp (A.comp (-(conjCLE : ℂ →L[ℝ] ℂ)))).det = A.det := by
  simp only [ContinuousLinearMap.det]
  change LinearMap.det (((-(conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ∘ₗ
    ((A : ℂ →ₗ[ℝ] ℂ) ∘ₗ ((-(conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))) = _
  rw [LinearMap.det_comp, LinearMap.det_comp, det_neg_conj_clm]
  ring

theorem det_fderiv_mirror {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (σ.swapPt z)) :
    (fderiv ℝ (fun w => -conj (g (σ.swapPt w))) z).det = (fderiv ℝ g (σ.swapPt z)).det := by
  have hs : HasFDerivAt σ.swapPt (-(conjCLE : ℂ →L[ℝ] ℂ)) z :=
    ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := z)).const_sub (σ.width : ℂ)
  have h1 : HasFDerivAt (fun w => g (σ.swapPt w)) ((fderiv ℝ g (σ.swapPt z)).comp
      (-(conjCLE : ℂ →L[ℝ] ℂ))) z := hg.hasFDerivAt.comp z hs
  have h2 : HasFDerivAt (fun w => -conj (g (σ.swapPt w)))
      ((-(conjCLE : ℂ →L[ℝ] ℂ)).comp ((fderiv ℝ g (σ.swapPt z)).comp
        (-(conjCLE : ℂ →L[ℝ] ℂ)))) z :=
    (-(conjCLE : ℂ →L[ℝ] ℂ)).hasFDerivAt.comp z h1
  rw [h2.fderiv, det_neg_conj_comp]

theorem continuous_swapPt : Continuous σ.swapPt :=
  continuous_const.sub continuous_conj

end Swap

end ConeShape

end GC.Seifert
