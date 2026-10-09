import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeAssembly

/-!
# Image and injectivity of the two-cone fold on the triangle

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §6, "separation
is structural", two-cone shapes). On the triangle `T` every branch of `foldE₂` has an explicit
image region (`foldE₂_cases`):
* on `R₂`: `‖E - 3/2‖ < G(h)`; on `R₁`: `‖E + 3/2‖ < G(h)`;
* on the lens: `‖E ∓ 3/2‖ ≥ G(h)` and `‖E‖ < 2`;
* elsewhere: `‖E‖ = outerProfile y > 2` and `‖E ∓ 3/2‖ ≥ G(h)` (`foldE₂_image_inf`: below `Y₁` the
  angle lies between those of `bridgeZeroC` and `bridgeOne`, above `Y₁` the outer profile exceeds
  `3/2 + G(Y₁)`).
Since `G(h) < 3/2` the regions are pairwise disjoint, and each branch is injective: the corners at
the vertices by `coneRegion_injective` (and its swap `regionTwoC_injective`), `bridgeTwoC` because
its two moduli fix `η₁, η₂` and hence the Fermi chart point on the side `Re ζ ≤ 0`
(`bridgeTwoC_injective`, from `√K η₁ η₂ (1 - t₁ t₂) = Y [η₂(η₁² + y₁²) - t₁ η₁ (η₂² + y₂²)]`), and
`cornerInfC` because the modulus fixes the height and the angle increases along horizontal lines
(`cornerInfC_injective`). Hence `foldE₂` is injective on `T` (`foldE₂_injOn`) with values in
`{‖u‖ < 3, Im u ≥ 0}` (`foldE₂_mem_target`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

section Inj

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include hθ in
theorem mem_domZeroC_of_re_ne {w : ℂ} (hw : 0 < w.im) (hx : w.re ≠ 0) : w ∈ σ.domZeroC := by
  refine (σ.swapPt_mem_domOne_iff hθ).1 ((σ.swap hθ).mem_domOne_of_re_ne (by simpa using hw) ?_)
  rw [swapPt_re, σ.swap_width hθ]
  intro h
  exact hx (by linarith)

include hθ in
theorem mem_domZeroC_of_im_gt {w : ℂ} (hw : σ.vertexTwo.im < w.im) : w ∈ σ.domZeroC :=
  (σ.swapPt_mem_domOne_iff hθ).1 ((σ.swap hθ).mem_domOne_of_im_gt (by
    rw [swapPt_im, σ.swap_vertexOne_im]; exact hw))

include hθ in
theorem re_pos_of_im_le {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexTwo)
    (hy : z.im ≤ σ.vertexTwo.im) : 0 < z.re := by
  have h := (σ.swap hθ).re_lt_width_of_im_le ((σ.swapPt_mem_triangle hθ).2 hz)
    ((σ.swapPt_ne_vertexOne_iff hθ).2 hzv) (by rw [swapPt_im, σ.swap_vertexOne_im]; exact hy)
  rw [swapPt_re, σ.swap_width hθ] at h
  linarith

theorem ne_vertexTwo_of_domZeroC {w : ℂ} (hw : w ∈ σ.domZeroC) : w ≠ σ.vertexTwo := by
  rintro rfl
  have := hw.2
  rw [discTwo, coneDisc_self, norm_zero, zero_re, add_zero] at this
  exact lt_irrefl _ this

include hθ h₁ h₂ in
theorem ne_vertexTwo_of_foldH_le {z : ℂ} (h : σ.foldH ≤ σ.etaTwoC z) : z ≠ σ.vertexTwo := by
  rintro rfl
  have h0 : σ.etaTwoC σ.vertexTwo = σ.vertexTwo.im := by
    simp [etaTwoC, coneHeight, coneDisc_self]
  have := σ.vertexTwo_im_lt_foldH hθ h₁ h₂
  linarith

include hθ h₁ h₂ in
theorem foldE₂_image_inf {p q : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.foldH ≤ σ.etaTwoC z) (h1 : σ.foldH ≤ σ.etaOne z) (hL : 1 / 10 ≤ |σ.sinhN z|) :
    ‖σ.foldE₂ hθ p q z‖ = outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z + 3 / 2‖ ∧
        0 ≤ (σ.foldE₂ hθ p q z).im := by
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le h1)
  have hzv2 := σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ h2
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz0 := σ.mem_domZeroC_of_mem_triangle hθ hz hzv2
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  have hx := σ.re_nonneg_of_triangle hz
  have hw := σ.wallOne_nonneg_of_mem_triangle hz
  obtain ⟨hα0, hαA, hAΘ, hΘπ⟩ := σ.angleInfC_mem hθ hz1 hz0 hx hw (σ.blendWeight_nonneg z)
    (σ.blendWeight_le_one z)
  set R := outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im with hR
  set A := σ.angleInfC σ.blendWeight z with hAdef
  have hR2 : 2 < R := two_lt_outerProfile hK σ.sqrt_constK_le_half
    (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1
  have hE : σ.foldE₂ hθ p q z = (R : ℂ) * exp ((A : ℂ) * I) := by
    rw [σ.foldE₂_of_inf hθ h2 h1 hL]
    rfl
  have hGh := σ.coneProfile_foldH_lt
  have hnorm : ‖σ.foldE₂ hθ p q z‖ = R := by rw [hE, norm_ofReal_mul_exp _ _ (by linarith)]
  have him : 0 ≤ (σ.foldE₂ hθ p q z).im := by
    rw [hE]
    exact im_ofReal_mul_exp_nonneg (by linarith) (le_trans hα0 hαA) (le_trans hAΘ hΘπ)
  refine ⟨hnorm, ?_, ?_, him⟩
  · rw [hE]
    rcases le_or_gt z.im σ.foldY₁ with hy | hy
    · have hRy : R = 3 / 2 + coneProfile σ.constK z.im := outerProfile_of_le σ.foldY₁_lt_foldY₂ hy
      have hcos : Real.cos A ≤ Real.cos (σ.angleZeroInfC z) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hα0 (le_trans hAΘ hΘπ) hαA
      have hb := σ.norm_bridgeZeroC_sub hθ hz0
      rw [σ.bridgeZeroC_polar hθ hz0, ← hRy] at hb
      have e1 := normSq_polar_sub R (3 / 2) A
      have e2 := normSq_polar_sub R (3 / 2) (σ.angleZeroInfC z)
      push_cast at e1 e2
      rw [hb] at e2
      have hRc : R * Real.cos A ≤ R * Real.cos (σ.angleZeroInfC z) :=
        mul_le_mul_of_nonneg_left hcos (by linarith)
      have hGη : coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (σ.etaTwoC z) :=
        (coneProfile_le_iff hK hH.le (by linarith)).2 h2
      have hsq : coneProfile σ.constK (σ.etaTwoC z) ^ 2 ≤
          ‖(R : ℂ) * exp ((A : ℂ) * I) - 3 / 2‖ ^ 2 := by
        rw [e1]; nlinarith
      have hG0 : 0 ≤ coneProfile σ.constK (σ.etaTwoC z) := by
        linarith [half_le_coneProfile hK (σ.etaTwoC z)]
      have h3 := (sq_le_sq₀ hG0 (norm_nonneg _)).1 hsq
      linarith
    · have hmono := outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt (show σ.foldY₁ ∈ Set.Ioi 0 from σ.foldY₁_pos)
        (show z.im ∈ Set.Ioi 0 from hz.1) hy
      rw [outerProfile_of_le σ.foldY₁_lt_foldY₂ le_rfl] at hmono
      have hGY : coneProfile σ.constK σ.foldH < coneProfile σ.constK σ.foldY₁ :=
        (coneProfile_lt_iff hK hH.le σ.foldY₁_pos.le).2 σ.foldH_lt_foldY₁
      have h3 := norm_sub_norm_le ((R : ℂ) * exp ((A : ℂ) * I)) (3 / 2)
      rw [norm_ofReal_mul_exp _ _ (by linarith)] at h3
      norm_num at h3
      linarith
  · rw [hE]
    rcases le_or_gt z.im σ.foldY₁ with hy | hy
    · have hRy : R = 3 / 2 + coneProfile σ.constK z.im := outerProfile_of_le σ.foldY₁_lt_foldY₂ hy
      have hcos : Real.cos (σ.angleOneInf z) ≤ Real.cos A :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_trans hα0 hαA) hΘπ hAΘ
      have hb := σ.norm_bridgeOne_add hz1
      rw [σ.bridgeOne_polar hz1, ← hRy] at hb
      have e1 := normSq_polar_sub R (-(3 / 2)) A
      have e2 := normSq_polar_sub R (-(3 / 2)) (σ.angleOneInf z)
      rw [show (R : ℂ) * exp ((A : ℂ) * I) - ((-(3 / 2) : ℝ) : ℂ) =
        (R : ℂ) * exp ((A : ℂ) * I) + 3 / 2 by push_cast; ring] at e1
      rw [show (R : ℂ) * exp ((σ.angleOneInf z : ℂ) * I) - ((-(3 / 2) : ℝ) : ℂ) =
        (R : ℂ) * exp ((σ.angleOneInf z : ℂ) * I) + 3 / 2 by push_cast; ring, hb] at e2
      have hRc : R * Real.cos (σ.angleOneInf z) ≤ R * Real.cos A :=
        mul_le_mul_of_nonneg_left hcos (by linarith)
      have hGη : coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (σ.etaOne z) :=
        (coneProfile_le_iff hK hH.le (by linarith)).2 h1
      have hsq : coneProfile σ.constK (σ.etaOne z) ^ 2 ≤
          ‖(R : ℂ) * exp ((A : ℂ) * I) + 3 / 2‖ ^ 2 := by
        rw [e1]; nlinarith
      have hG0 : 0 ≤ coneProfile σ.constK (σ.etaOne z) := by
        linarith [half_le_coneProfile hK (σ.etaOne z)]
      have h3 := (sq_le_sq₀ hG0 (norm_nonneg _)).1 hsq
      linarith
    · have hmono := outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt (show σ.foldY₁ ∈ Set.Ioi 0 from σ.foldY₁_pos)
        (show z.im ∈ Set.Ioi 0 from hz.1) hy
      rw [outerProfile_of_le σ.foldY₁_lt_foldY₂ le_rfl] at hmono
      have hGY : coneProfile σ.constK σ.foldH < coneProfile σ.constK σ.foldY₁ :=
        (coneProfile_lt_iff hK hH.le σ.foldY₁_pos.le).2 σ.foldH_lt_foldY₁
      have h3 := norm_sub_norm_le ((R : ℂ) * exp ((A : ℂ) * I)) (-(3 / 2))
      rw [norm_ofReal_mul_exp _ _ (by linarith), sub_neg_eq_add] at h3
      norm_num at h3
      linarith

include hθ in
theorem bridgeTwoC_injective {z z' : ℂ} (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle)
    (hd : z ∈ σ.domTwoC) (hd' : z' ∈ σ.domTwoC) (heq : σ.bridgeTwoC z = σ.bridgeTwoC z') :
    z = z' := by
  have hK := σ.constK_pos
  have hη₂ : σ.etaTwoC z = σ.etaTwoC z' := by
    have e1 := σ.norm_bridgeTwoC_sub hθ hd
    have e2 := σ.norm_bridgeTwoC_sub hθ hd'
    rw [heq, e2] at e1
    exact (strictMonoOn_coneProfile hK).injOn (σ.etaTwoC_pos hθ hz.1).le
      (σ.etaTwoC_pos hθ hz'.1).le e1.symm
  have hη₁ : σ.etaOne z = σ.etaOne z' := by
    have e1 := σ.norm_bridgeTwoC_add hθ hd
    have e2 := σ.norm_bridgeTwoC_add hθ hd'
    rw [heq, e2] at e1
    exact (strictMonoOn_coneProfile hK).injOn (σ.etaOne_pos hz.1).le (σ.etaOne_pos hz'.1).le
      e1.symm
  have key : ∀ w : ℂ, 0 < w.im → (σ.fermiChart w).im *
      (σ.etaTwoC w * (σ.etaOne w ^ 2 + σ.vertexOne.im ^ 2) -
        σ.tOne * σ.etaOne w * (σ.etaTwoC w ^ 2 + σ.vertexTwo.im ^ 2)) =
        Real.sqrt σ.constK * σ.etaOne w * σ.etaTwoC w * (1 - σ.tOne * σ.tTwo) := by
    intro w hw
    have I1 := σ.sqrt_constK_mul_coneHeight_one hw
    have I2 := σ.sqrt_constK_mul_coneHeight_two hθ hw
    change Real.sqrt σ.constK * σ.etaOne w * (1 + σ.tOne * normSq (σ.fermiChart w)) =
      (σ.fermiChart w).im * (σ.etaOne w ^ 2 + σ.vertexOne.im ^ 2) at I1
    change Real.sqrt σ.constK * σ.etaTwoC w * (normSq (σ.fermiChart w) + σ.tTwo) =
      (σ.fermiChart w).im * (σ.etaTwoC w ^ 2 + σ.vertexTwo.im ^ 2) at I2
    linear_combination -(σ.etaTwoC w) * I1 + σ.tOne * σ.etaOne w * I2
  have k1 := key z hz.1
  have k2 := key z' hz'.1
  rw [← hη₂, ← hη₁] at k2
  set c := σ.etaTwoC z * (σ.etaOne z ^ 2 + σ.vertexOne.im ^ 2) -
    σ.tOne * σ.etaOne z * (σ.etaTwoC z ^ 2 + σ.vertexTwo.im ^ 2)
  have htt := σ.tOne_mul_tTwo_lt_one
  have hpos : 0 < Real.sqrt σ.constK * σ.etaOne z * σ.etaTwoC z * (1 - σ.tOne * σ.tTwo) := by
    have := σ.sqrt_constK_pos
    have := σ.etaOne_pos hz.1
    have := σ.etaTwoC_pos hθ hz.1
    have : 0 < 1 - σ.tOne * σ.tTwo := by linarith
    positivity
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k1
    linarith
  have hY : (σ.fermiChart z).im = (σ.fermiChart z').im :=
    mul_right_cancel₀ hc (k1.trans k2.symm)
  have hN : normSq (σ.fermiChart z) = normSq (σ.fermiChart z') := by
    have I2 := σ.sqrt_constK_mul_coneHeight_two hθ hz.1
    have I2' := σ.sqrt_constK_mul_coneHeight_two hθ hz'.1
    change Real.sqrt σ.constK * σ.etaTwoC z * (normSq (σ.fermiChart z) + σ.tTwo) =
      (σ.fermiChart z).im * (σ.etaTwoC z ^ 2 + σ.vertexTwo.im ^ 2) at I2
    change Real.sqrt σ.constK * σ.etaTwoC z' * (normSq (σ.fermiChart z') + σ.tTwo) =
      (σ.fermiChart z').im * (σ.etaTwoC z' ^ 2 + σ.vertexTwo.im ^ 2) at I2'
    rw [← hη₂, ← hY] at I2'
    have hs0 : Real.sqrt σ.constK * σ.etaTwoC z ≠ 0 :=
      (mul_pos σ.sqrt_constK_pos (σ.etaTwoC_pos hθ hz.1)).ne'
    have := mul_left_cancel₀ hs0 (I2.trans I2'.symm)
    linarith
  have hX : (σ.fermiChart z).re ≤ 0 := by
    rw [σ.fermiChart_re]
    have := σ.normSq_sub_rightFoot_pos hz.1
    have := hz.2 2
    have := σ.chartScale_pos
    have : 0 ≤ σ.chartScale * σ.wallSide 2 z / normSq (z - σ.rightFoot) := by positivity
    linarith
  have hX' : (σ.fermiChart z').re ≤ 0 := by
    rw [σ.fermiChart_re]
    have := σ.normSq_sub_rightFoot_pos hz'.1
    have := hz'.2 2
    have := σ.chartScale_pos
    have : 0 ≤ σ.chartScale * σ.wallSide 2 z' / normSq (z' - σ.rightFoot) := by positivity
    linarith
  have hX2 : (σ.fermiChart z).re ^ 2 = (σ.fermiChart z').re ^ 2 := by
    rw [normSq_apply, normSq_apply, hY] at hN
    nlinarith
  have hXe : (σ.fermiChart z).re = (σ.fermiChart z').re := by
    have hm : ((σ.fermiChart z).re - (σ.fermiChart z').re) *
        ((σ.fermiChart z).re + (σ.fermiChart z').re) = 0 := by linear_combination hX2
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  exact σ.fermiChart_injOn hz.1 hz'.1 (Complex.ext hXe hY)

include hθ in
theorem cornerInfC_injective {z z' : ℂ} (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle)
    (hzv : z ≠ σ.vertexOne) (hzv' : z' ≠ σ.vertexOne) (hzw : z ≠ σ.vertexTwo)
    (hzw' : z' ≠ σ.vertexTwo)
    (heq : σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z =
      σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z') : z = z' := by
  have hK := σ.constK_pos
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz1' := σ.mem_domOne_of_mem_triangle hz' hzv'
  have hz0 := σ.mem_domZeroC_of_mem_triangle hθ hz hzw
  have hz0' := σ.mem_domZeroC_of_mem_triangle hθ hz' hzw'
  have hRpos : ∀ w : ℂ, 0 < w.im → 0 < outerProfile σ.constK σ.foldY₁ σ.foldY₂ w.im := fun w hw =>
    lt_trans (by norm_num) (two_lt_outerProfile hK σ.sqrt_constK_le_half
      (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hw)
  have hy : z.im = z'.im := by
    have e1 : ‖σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z‖ =
        outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im := by
      rw [cornerInfC, norm_ofReal_mul_exp _ _ (hRpos z hz.1).le]
    have e2 : ‖σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z'‖ =
        outerProfile σ.constK σ.foldY₁ σ.foldY₂ z'.im := by
      rw [cornerInfC, norm_ofReal_mul_exp _ _ (hRpos z' hz'.1).le]
    rw [heq, e2] at e1
    exact (outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
      σ.foldY₂_lt_sqrt).injOn hz.1 hz'.1 e1.symm
  have hA := σ.angleInfC_mem hθ (ν := σ.blendWeight) hz1 hz0 (σ.re_nonneg_of_triangle hz)
    (σ.wallOne_nonneg_of_mem_triangle hz) (σ.blendWeight_nonneg z) (σ.blendWeight_le_one z)
  have hA' := σ.angleInfC_mem hθ (ν := σ.blendWeight) hz1' hz0' (σ.re_nonneg_of_triangle hz')
    (σ.wallOne_nonneg_of_mem_triangle hz') (σ.blendWeight_nonneg z') (σ.blendWeight_le_one z')
  have hexp : exp ((σ.angleInfC σ.blendWeight z : ℂ) * I) =
      exp ((σ.angleInfC σ.blendWeight z' : ℂ) * I) := by
    have h3 := heq
    rw [cornerInfC, cornerInfC, hy] at h3
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (hRpos z' hz'.1).ne') h3
  have hAA := eq_of_exp_eq_of_mem hexp ⟨le_trans hA.1 hA.2.1, le_trans hA.2.2.1 hA.2.2.2⟩
    ⟨le_trans hA'.1 hA'.2.1, le_trans hA'.2.2.1 hA'.2.2.2⟩
  set t := z'.re - z.re with ht
  have hz't : z' = z + (t : ℂ) := by
    apply Complex.ext
    · simp [ht]
    · simp [hy]
  have hder : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D, 0 < D ∧
      HasDerivAt (fun u : ℝ => σ.angleInfC σ.blendWeight (z + (u : ℂ))) D s := by
    intro s hs
    have hm := mem_Icc_minmax hs
    set w := z + (s : ℂ) with hwdef
    have hwim : w.im = z.im := by simp [hwdef]
    have hwre : w.re = z.re + s := by simp [hwdef]
    have hx0 : 0 ≤ w.re := by
      rw [hwre]; linarith [le_min (σ.re_nonneg_of_triangle hz) (σ.re_nonneg_of_triangle hz')]
    have hxW : w.re ≤ σ.width := by
      rw [hwre]; linarith [max_le (σ.re_le_width_of_mem_triangle hz)
        (σ.re_le_width_of_mem_triangle hz')]
    have hw1 : w ∈ σ.domOne := by
      rcases lt_or_ge σ.vertexOne.im z.im with hgt | hle
      · exact σ.mem_domOne_of_im_gt (by rw [hwim]; exact hgt)
      · have h1 := σ.re_lt_width_of_im_le hz hzv hle
        have h2 := σ.re_lt_width_of_im_le hz' hzv' (by rw [← hy]; exact hle)
        refine σ.mem_domOne_of_re_ne (by rw [hwim]; exact hz.1) (ne_of_lt ?_)
        rw [hwre]
        linarith [max_lt h1 h2]
    have hw0 : w ∈ σ.domZeroC := by
      rcases lt_or_ge σ.vertexTwo.im z.im with hgt | hle
      · exact σ.mem_domZeroC_of_im_gt hθ (by rw [hwim]; exact hgt)
      · have h1 := σ.re_pos_of_im_le hθ hz hzw hle
        have h2 := σ.re_pos_of_im_le hθ hz' hzw' (by rw [← hy]; exact hle)
        refine σ.mem_domZeroC_of_re_ne hθ (by rw [hwim]; exact hz.1) (ne_of_gt ?_)
        rw [hwre]
        linarith [lt_min h1 h2]
    have hwv := σ.vertexOne_ne_of_domOne hw1
    have hwv2 := σ.ne_vertexTwo_of_domZeroC hw0
    obtain ⟨d, hd, hdd⟩ := σ.exists_hasDerivAt_blendWeight hw1.1 hwv (fun _ => hwv2) hx0 hxW
    obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleInfC hθ hw1 hw0 hdd hd
      (σ.blendWeight_nonneg w) (σ.blendWeight_le_one w)
    refine ⟨D, hD, hasDerivAt_of_shift ?_⟩
    refine hDd.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp only [hwdef]
    push_cast
    ring_nf
  have ht0 : t = 0 := by
    refine eq_zero_of_strictMonoOn hder ?_
    simp only [ofReal_zero, add_zero, ← hz't]
    exact hAA
  rw [hz't, ht0, ofReal_zero, add_zero]

include hθ h₁ h₂ in
theorem foldE₂_cases {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpθ : σ.θ₁ * p = Real.pi)
    (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ} (hz : z ∈ σ.triangle) :
    (σ.etaTwoC z < σ.foldH ∧ ‖σ.foldE₂ hθ p q z - 3 / 2‖ < coneProfile σ.constK σ.foldH ∧
      0 ≤ (σ.foldE₂ hθ p q z).im) ∨
    (σ.foldH ≤ σ.etaTwoC z ∧ σ.etaOne z < σ.foldH ∧
      ‖σ.foldE₂ hθ p q z + 3 / 2‖ < coneProfile σ.constK σ.foldH ∧
        0 ≤ (σ.foldE₂ hθ p q z).im) ∨
    (σ.foldH ≤ σ.etaTwoC z ∧ σ.foldH ≤ σ.etaOne z ∧ |σ.sinhN z| < 1 / 10 ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z + 3 / 2‖ ∧
        ‖σ.foldE₂ hθ p q z‖ < 2 ∧ 0 ≤ (σ.foldE₂ hθ p q z).im) ∨
    (σ.foldH ≤ σ.etaTwoC z ∧ σ.foldH ≤ σ.etaOne z ∧ 1 / 10 ≤ |σ.sinhN z| ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE₂ hθ p q z + 3 / 2‖ ∧
        2 < ‖σ.foldE₂ hθ p q z‖ ∧ ‖σ.foldE₂ hθ p q z‖ < 3 ∧ 0 ≤ (σ.foldE₂ hθ p q z).im) := by
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  rcases lt_or_ge (σ.etaTwoC z) σ.foldH with h2 | h2
  · obtain ⟨-, hlt, him⟩ := σ.regionTwoC_image hθ h₁ h₂ hq hqθ hz h2
    rw [← σ.foldE₂_of_two hθ (p := p) h2] at hlt him
    exact Or.inl ⟨h2, hlt, him⟩
  rcases lt_or_ge (σ.etaOne z) σ.foldH with h1 | h1
  · obtain ⟨-, hlt, him⟩ := σ.coneRegion_image hθ h₁ h₂ hp hpθ hz h1
    rw [← σ.foldE₂_of_one hθ (q := q) h2 h1] at hlt him
    exact Or.inr (Or.inl ⟨h2, h1, hlt, him⟩)
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le h1)
  have hzv2 := σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ h2
  rcases lt_or_ge |σ.sinhN z| (1 / 10) with hL | hL
  · have hd := σ.mem_domTwoC_of_mem_triangle hθ hz hzv hzv2
    rw [σ.foldE₂_of_lens hθ h2 h1 hL]
    refine Or.inr (Or.inr (Or.inl ⟨h2, h1, hL, ?_, ?_, σ.norm_bridgeTwoC_lt_two hθ hd,
      σ.bridgeTwoC_im_nonneg hθ hd (σ.wallTwo_nonneg_of_mem_triangle hz)⟩))
    · rw [σ.norm_bridgeTwoC_sub hθ hd]
      exact (coneProfile_le_iff hK hH.le (σ.etaTwoC_pos hθ hz.1).le).2 h2
    · rw [σ.norm_bridgeTwoC_add hθ hd]
      exact (coneProfile_le_iff hK hH.le (σ.etaOne_pos hz.1).le).2 h1
  · obtain ⟨e, g1, g2, him⟩ := σ.foldE₂_image_inf hθ h₁ h₂ (p := p) (q := q) hz h2 h1 hL
    have h3 : 2 < ‖σ.foldE₂ hθ p q z‖ := by
      rw [e]
      exact two_lt_outerProfile hK σ.sqrt_constK_le_half
        (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1
    have h4 : ‖σ.foldE₂ hθ p q z‖ < 3 := by
      rw [e]
      exact outerProfile_lt_three hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt hz.1
    exact Or.inr (Or.inr (Or.inr ⟨h2, h1, hL, g1, g2, h3, h4, him⟩))

include hθ h₁ h₂ in
theorem foldE₂_injOn {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpθ : σ.θ₁ * p = Real.pi)
    (hqθ : σ.θ₂ * q = Real.pi) : Set.InjOn (σ.foldE₂ hθ p q) σ.triangle := by
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  intro z hz z' hz' heq
  rcases σ.foldE₂_cases hθ h₁ h₂ hp hq hpθ hqθ hz with hZ | hC | hL | hI <;>
  rcases σ.foldE₂_cases hθ h₁ h₂ hp hq hpθ hqθ hz' with hZ' | hC' | hL' | hI'
  · rw [σ.foldE₂_of_two hθ hZ.1, σ.foldE₂_of_two hθ hZ'.1] at heq
    exact σ.regionTwoC_injective hθ h₁ h₂ hq hqθ hz hz' hZ.1 hZ'.1 heq
  · rw [← heq] at hC'; exact (σ.not_both_small hZ.2.1 hC'.2.2.1).elim
  · rw [← heq] at hL'; linarith [hZ.2.1, hL'.2.2.2.1]
  · rw [← heq] at hI'; linarith [hZ.2.1, hI'.2.2.2.1]
  · rw [heq] at hC; exact (σ.not_both_small hZ'.2.1 hC.2.2.1).elim
  · rw [σ.foldE₂_of_one hθ hC.1 hC.2.1, σ.foldE₂_of_one hθ hC'.1 hC'.2.1] at heq
    exact σ.coneRegion_injective hθ h₁ h₂ hp hpθ hz hz' hC.2.1 hC'.2.1 heq
  · rw [← heq] at hL'; linarith [hC.2.2.1, hL'.2.2.2.2.1]
  · rw [← heq] at hI'; linarith [hC.2.2.1, hI'.2.2.2.2.1]
  · rw [heq] at hL; linarith [hZ'.2.1, hL.2.2.2.1]
  · rw [heq] at hL; linarith [hC'.2.2.1, hL.2.2.2.2.1]
  · have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le hL.2.1)
    have hzv' := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le hL'.2.1)
    have hzw := σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ hL.1
    have hzw' := σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ hL'.1
    rw [σ.foldE₂_of_lens hθ hL.1 hL.2.1 hL.2.2.1,
      σ.foldE₂_of_lens hθ hL'.1 hL'.2.1 hL'.2.2.1] at heq
    exact σ.bridgeTwoC_injective hθ hz hz' (σ.mem_domTwoC_of_mem_triangle hθ hz hzv hzw)
      (σ.mem_domTwoC_of_mem_triangle hθ hz' hzv' hzw') heq
  · rw [← heq] at hI'; linarith [hL.2.2.2.2.2.1, hI'.2.2.2.2.2.1]
  · rw [heq] at hI; linarith [hZ'.2.1, hI.2.2.2.1]
  · rw [heq] at hI; linarith [hC'.2.2.1, hI.2.2.2.2.1]
  · rw [heq] at hI; linarith [hL'.2.2.2.2.2.1, hI.2.2.2.2.2.1]
  · rw [σ.foldE₂_of_inf hθ hI.1 hI.2.1 hI.2.2.1,
      σ.foldE₂_of_inf hθ hI'.1 hI'.2.1 hI'.2.2.1] at heq
    exact σ.cornerInfC_injective hθ hz hz'
      (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le hI.2.1))
      (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le hI'.2.1))
      (σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ hI.1) (σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ hI'.1) heq

include hθ h₁ h₂ in
theorem foldE₂_mem_target {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpθ : σ.θ₁ * p = Real.pi)
    (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ} (hz : z ∈ σ.triangle) :
    ‖σ.foldE₂ hθ p q z‖ < 3 ∧ 0 ≤ (σ.foldE₂ hθ p q z).im := by
  have hG := σ.coneProfile_foldH_lt
  have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  rcases σ.foldE₂_cases hθ h₁ h₂ hp hq hpθ hqθ hz with hZ | hC | hL | hI
  · refine ⟨?_, hZ.2.2⟩
    have := norm_le_norm_add_norm_sub' (σ.foldE₂ hθ p q z) (3 / 2)
    linarith [hZ.2.1]
  · refine ⟨?_, hC.2.2.2⟩
    have := norm_sub_le (σ.foldE₂ hθ p q z + 3 / 2) (3 / 2)
    rw [add_sub_cancel_right] at this
    linarith [hC.2.2.1]
  · exact ⟨by linarith [hL.2.2.2.2.2.1], hL.2.2.2.2.2.2⟩
  · exact ⟨hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2⟩

end Inj

end ConeShape

end GC.Seifert
