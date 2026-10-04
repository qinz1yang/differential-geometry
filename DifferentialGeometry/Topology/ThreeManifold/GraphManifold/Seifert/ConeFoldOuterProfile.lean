import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldHeights

/-!
# Smooth steps and the bent outer profile

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
`coneStep a b` is the smooth monotone step from `0` (below `a`) to `1` (above `b`).
The outer modulus of the corner at the cusp `∞` must equal the bridge modulus `3/2 + G y` up to
a height `Y₁` and stay below `3`; it is `outerProfile K Y₁ Y₂ y = 3/2 + G (outerReparam y)`, where
the reparametrisation equals `y` below `Y₁`, bends on `[Y₁, Y₂]` towards
`outerTarget y = √K - (√K - Y₂)(1 + Y₂)/(1 + y)`, which lies above `y` there and below `√K`
everywhere. So the profile is strictly increasing with positive derivative
(`exists_hasDerivAt_outerProfile`), lies in `(2, 3)` (`two_lt_outerProfile`,
`outerProfile_lt_three`) and is at least `3/2 + G Y₁` above `Y₁`. Since
`K = (1 + cos θ₁)(1 + cos θ₂)/16 ≤ 1/4`, `√K ≤ 1/2` is assumed where needed.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped ContDiff Topology

namespace GC.Seifert

def coneStep (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

section Step

variable {a b : ℝ}

theorem coneStep_eq_zero (hab : a < b) {t : ℝ} (ht : t ≤ a) : coneStep a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith))

theorem coneStep_eq_one (hab : a < b) {t : ℝ} (ht : b ≤ t) : coneStep a b t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem coneStep_nonneg (a b t : ℝ) : 0 ≤ coneStep a b t := Real.smoothTransition.nonneg _

theorem coneStep_le_one (a b t : ℝ) : coneStep a b t ≤ 1 := Real.smoothTransition.le_one _

theorem monotone_coneStep (hab : a < b) : Monotone (coneStep a b) := fun s t hst =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem contDiff_coneStep (a b : ℝ) : ContDiff ℝ ∞ (coneStep a b) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem hasDerivAt_coneStep (a b t : ℝ) :
    HasDerivAt (coneStep a b) (deriv (coneStep a b) t) t :=
  ((contDiff_coneStep a b).differentiable (by simp) t).hasDerivAt

theorem deriv_coneStep_nonneg (hab : a < b) (t : ℝ) : 0 ≤ deriv (coneStep a b) t :=
  (monotone_coneStep hab).deriv_nonneg

theorem deriv_coneStep_eq_zero_of_lt (hab : a < b) {t : ℝ} (ht : b < t) :
    deriv (coneStep a b) t = 0 := by
  have h : coneStep a b =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact coneStep_eq_one hab (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem deriv_coneStep_eq_zero_of_gt (hab : a < b) {t : ℝ} (ht : t < a) :
    deriv (coneStep a b) t = 0 := by
  have h : coneStep a b =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact coneStep_eq_zero hab (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem convex_comb_pos {t p q : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hp : 0 < p) (hq : 0 < q) :
    0 < (1 - t) * p + t * q := by
  rcases lt_or_eq_of_le h1 with h | h
  · have : 0 < (1 - t) * p := mul_pos (by linarith) hp
    nlinarith
  · subst h
    simpa using hq

end Step

def outerTarget (K Y₂ y : ℝ) : ℝ := Real.sqrt K - (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y)

def outerReparam (K Y₁ Y₂ y : ℝ) : ℝ :=
  (1 - coneStep Y₁ Y₂ y) * y + coneStep Y₁ Y₂ y * outerTarget K Y₂ y

def outerProfile (K Y₁ Y₂ y : ℝ) : ℝ := 3 / 2 + coneProfile K (outerReparam K Y₁ Y₂ y)

section Profile

variable {K Y₁ Y₂ : ℝ}

theorem outerTarget_lt (hY₂0 : 0 ≤ Y₂) (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 ≤ y) :
    outerTarget K Y₂ y < Real.sqrt K := by
  unfold outerTarget
  have : 0 < (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y) := by
    have : 0 < Real.sqrt K - Y₂ := by linarith
    have : 0 < 1 + y := by linarith
    positivity
  linarith

theorem outerTarget_pos (hK : Real.sqrt K ≤ 1 / 2) (hY₂0 : 0 < Y₂) (hY₂ : Y₂ < Real.sqrt K)
    {y : ℝ} (hy : 0 ≤ y) : 0 < outerTarget K Y₂ y := by
  unfold outerTarget
  have h1 : (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y) ≤ (Real.sqrt K - Y₂) * (1 + Y₂) := by
    apply div_le_self (by nlinarith) (by linarith)
  have h2 : (Real.sqrt K - Y₂) * (1 + Y₂) < Real.sqrt K := by
    have := mul_pos hY₂0 (show 0 < 1 + Y₂ - Real.sqrt K by linarith)
    nlinarith
  linarith

theorem le_outerTarget (hK : Real.sqrt K ≤ 1 / 2) (hY₂0 : 0 ≤ Y₂) (hY₂ : Y₂ < Real.sqrt K)
    {y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y₂) : y ≤ outerTarget K Y₂ y := by
  unfold outerTarget
  have h3 : (Real.sqrt K - Y₂) * (1 + Y₂) ≤ (Real.sqrt K - y) * (1 + y) := by
    have := mul_nonneg (show 0 ≤ Y₂ - y by linarith)
      (show 0 ≤ 1 + y + Y₂ - Real.sqrt K by linarith)
    nlinarith
  have h4 : (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y) ≤ Real.sqrt K - y := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

theorem hasDerivAt_outerTarget (K Y₂ : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (outerTarget K Y₂) ((Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y) ^ 2) y := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 y := (hasDerivAt_id' y).const_add 1
  have h := ((hasDerivAt_const y ((Real.sqrt K - Y₂) * (1 + Y₂))).div h1
    (by linarith : (1 + y) ≠ 0)).const_sub (Real.sqrt K)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem outerReparam_of_le (hY : Y₁ < Y₂) {y : ℝ} (hy : y ≤ Y₁) : outerReparam K Y₁ Y₂ y = y := by
  rw [outerReparam, coneStep_eq_zero hY hy]
  ring

theorem outerReparam_pos (hK : Real.sqrt K ≤ 1 / 2) (hY₂0 : 0 < Y₂)
    (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 < y) : 0 < outerReparam K Y₁ Y₂ y :=
  convex_comb_pos (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hy
    (outerTarget_pos hK hY₂0 hY₂ hy.le)

theorem outerReparam_lt (hY₁ : 0 ≤ Y₁) (hY : Y₁ < Y₂)
    (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 ≤ y) :
    outerReparam K Y₁ Y₂ y < Real.sqrt K := by
  have ht := outerTarget_lt (by linarith) hY₂ hy
  rcases le_or_gt y Y₂ with h | h
  · have hy' : y < Real.sqrt K := by linarith
    have hc := convex_comb_pos (coneStep_nonneg Y₁ Y₂ y) (coneStep_le_one Y₁ Y₂ y)
      (sub_pos.2 hy') (sub_pos.2 ht)
    unfold outerReparam
    linarith
  · rw [outerReparam, coneStep_eq_one hY h.le]
    linarith

theorem exists_hasDerivAt_outerReparam (hK : Real.sqrt K ≤ 1 / 2) (hY₁ : 0 ≤ Y₁)
    (hY : Y₁ < Y₂) (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 ≤ y) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (outerReparam K Y₁ Y₂) D y := by
  have hτ := hasDerivAt_coneStep Y₁ Y₂ y
  have hτ0 := deriv_coneStep_nonneg hY y
  have ht := hasDerivAt_outerTarget K Y₂ hy
  have hd := (((hasDerivAt_const y (1 : ℝ)).sub hτ).mul (hasDerivAt_id' y)).add (hτ.mul ht)
  refine ⟨_, ?_, hd⟩
  have hY₂0 : 0 ≤ Y₂ := by linarith
  have ht' : 0 < (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y) ^ 2 := by
    apply div_pos _ (by positivity)
    have : 0 < Real.sqrt K - Y₂ := by linarith
    positivity
  have hc := convex_comb_pos (coneStep_nonneg Y₁ Y₂ y) (coneStep_le_one Y₁ Y₂ y)
    (show (0 : ℝ) < 1 by norm_num) ht'
  have hm : 0 ≤ deriv (coneStep Y₁ Y₂) y * (outerTarget K Y₂ y - y) := by
    rcases le_or_gt y Y₂ with h | h
    · exact mul_nonneg hτ0 (by linarith [le_outerTarget hK hY₂0 hY₂ hy h])
    · rw [deriv_coneStep_eq_zero_of_lt hY h, zero_mul]
  simp only [Pi.sub_apply]
  nlinarith

theorem contDiff_outerReparam (K Y₁ Y₂ : ℝ) :
    ContDiffOn ℝ ∞ (outerReparam K Y₁ Y₂) (Set.Ioi (-1)) := by
  have h1 := (contDiff_coneStep Y₁ Y₂).contDiffOn (s := Set.Ioi (-1))
  have h2 : ContDiffOn ℝ ∞ (outerTarget K Y₂) (Set.Ioi (-1)) := by
    unfold outerTarget
    exact contDiffOn_const.sub (contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
      fun y hy => by simp at hy; linarith)
  exact ((contDiffOn_const.sub h1).mul contDiffOn_id).add (h1.mul h2)

theorem outerProfile_of_le (hY : Y₁ < Y₂) {y : ℝ} (hy : y ≤ Y₁) :
    outerProfile K Y₁ Y₂ y = 3 / 2 + coneProfile K y := by
  rw [outerProfile, outerReparam_of_le hY hy]

theorem outerProfile_lt_three (hK0 : 0 < K) (hK : Real.sqrt K ≤ 1 / 2) (hY₁ : 0 ≤ Y₁)
    (hY : Y₁ < Y₂) (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 < y) :
    outerProfile K Y₁ Y₂ y < 3 := by
  have h := outerReparam_lt hY₁ hY hY₂ hy.le
  have hp := outerReparam_pos hK (by linarith) hY₂ (Y₁ := Y₁) hy
  have := (coneProfile_lt_three_halves_iff hK0 hp.le).2 h
  unfold outerProfile
  linarith

theorem two_lt_outerProfile (hK0 : 0 < K) (hK : Real.sqrt K ≤ 1 / 2) (hY₂0 : 0 < Y₂)
    (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 < y) : 2 < outerProfile K Y₁ Y₂ y := by
  have hp := outerReparam_pos hK hY₂0 hY₂ (Y₁ := Y₁) hy
  have := half_lt_coneProfile hK0 hp.ne'
  unfold outerProfile
  linarith

theorem exists_hasDerivAt_outerProfile (hK0 : 0 < K) (hK : Real.sqrt K ≤ 1 / 2)
    (hY₁ : 0 ≤ Y₁) (hY : Y₁ < Y₂) (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : 0 < y) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (outerProfile K Y₁ Y₂) D y := by
  obtain ⟨D, hD, hd⟩ := exists_hasDerivAt_outerReparam hK hY₁ hY hY₂ hy.le
  have hp := outerReparam_pos hK (by linarith) hY₂ (Y₁ := Y₁) hy
  have hG := hasDerivAt_coneProfile hK0 (outerReparam K Y₁ Y₂ y)
  refine ⟨_, ?_, (hG.comp y hd).const_add (3 / 2)⟩
  have : 0 < 4 * K * outerReparam K Y₁ Y₂ y / (outerReparam K Y₁ Y₂ y ^ 2 + K) ^ 2 := by
    positivity
  positivity

theorem outerProfile_mono (hK0 : 0 < K) (hK : Real.sqrt K ≤ 1 / 2) (hY₁ : 0 ≤ Y₁)
    (hY : Y₁ < Y₂) (hY₂ : Y₂ < Real.sqrt K) :
    StrictMonoOn (outerProfile K Y₁ Y₂) (Set.Ioi 0) := by
  have hcont : ContinuousOn (outerProfile K Y₁ Y₂) (Set.Ioi 0) := by
    intro y hy
    obtain ⟨D, -, hd⟩ := exists_hasDerivAt_outerProfile hK0 hK hY₁ hY hY₂ hy
    exact hd.continuousAt.continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont ?_
  intro y hy
  rw [interior_Ioi] at hy
  obtain ⟨D, hD, hd⟩ := exists_hasDerivAt_outerProfile hK0 hK hY₁ hY hY₂ hy
  rw [hd.deriv]
  exact hD

end Profile

end GC.Seifert
