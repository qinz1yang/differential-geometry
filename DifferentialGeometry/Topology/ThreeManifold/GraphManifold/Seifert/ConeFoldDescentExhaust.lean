import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentSurj

/-!
# An exhaustion function of the filled base

The profile `G = coneProfile K`, `G(t) = 1/2 + 2t²/(t² + K)`, has the explicit inverse
`innerInv K ρ = √(K (ρ - 1/2)/(5/2 - ρ))` on `t ≥ 0` (`innerInv_coneProfile`), and the final outer
profile `R∞ = outerProfile K Y₁ Y₂`, which is `3/2 + G(√K - A/(1 + y))` for `y ≥ Y₂`,
`A = (√K - Y₂)(1 + Y₂)`, has the explicit inverse
`outerInv K Y₂ r = A/(√K - innerInv K (r - 3/2)) - 1` there (`outerInv_outerProfile`); both
inverses are smooth and strictly increasing. With the ramp
`rampFn a t = t · step(a, a + 1)(t)` (zero for `t ≤ a`, equal to `t` for `t ≥ a + 1`) the
exhaustion of the filled base `{‖u‖ < 3, ‖u + 3/2‖ > 1/2}` is
`exhaust u = rampFn (log (Y₂ + 1)) (log (outerInv ‖u‖))
  + rampFn (-log (Y₂/2)) (-log (innerInv ‖u + 3/2‖))`,
each term cut off by an `if` where the inverse is not defined. It is smooth on the filled base
(`contDiffOn_exhaust`), invariant under conjugation, nonnegative, equal to `log y` on the outer
cusp (`outerExhaust_outerProfile`) and to `-log η₀` on the inner cusp (`innerExhaust_coneProfile`),
and its sublevel sets stay in `{‖u‖ ≤ R∞(Y_R), ‖u + 3/2‖ ≥ G(η_R)}`
(`le_of_outerExhaust_le`, `le_of_innerExhaust_le`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

namespace GC.Seifert

def innerInv (K ρ : ℝ) : ℝ := Real.sqrt (K * (ρ - 1 / 2) / (5 / 2 - ρ))

def outerInv (K Y₂ r : ℝ) : ℝ :=
  (Real.sqrt K - Y₂) * (1 + Y₂) / (Real.sqrt K - innerInv K (r - 3 / 2)) - 1

def rampFn (a t : ℝ) : ℝ := t * coneStep a (a + 1) t

section Inverses

variable {K : ℝ}

theorem innerInv_coneProfile (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    innerInv K (coneProfile K t) = t := by
  unfold innerInv coneProfile
  have h1 : 0 < t ^ 2 + K := by positivity
  have hK' : K ≠ 0 := hK.ne'
  have e1 : 1 / 2 + 2 * t ^ 2 / (t ^ 2 + K) - 1 / 2 = 2 * t ^ 2 / (t ^ 2 + K) := by ring
  have e2 : 5 / 2 - (1 / 2 + 2 * t ^ 2 / (t ^ 2 + K)) = 2 * K / (t ^ 2 + K) := by
    field_simp
    ring
  have e : K * (1 / 2 + 2 * t ^ 2 / (t ^ 2 + K) - 1 / 2) /
      (5 / 2 - (1 / 2 + 2 * t ^ 2 / (t ^ 2 + K))) = t ^ 2 := by
    rw [e1, e2]
    field_simp
  rw [e, Real.sqrt_sq ht]

theorem innerInv_pos (hK : 0 < K) {ρ : ℝ} (h1 : 1 / 2 < ρ) (h2 : ρ < 5 / 2) : 0 < innerInv K ρ := by
  unfold innerInv
  apply Real.sqrt_pos.2
  apply div_pos (mul_pos hK (by linarith)) (by linarith)

theorem innerInv_lt_innerInv (hK : 0 < K) {ρ ρ' : ℝ} (h1 : 1 / 2 ≤ ρ) (h2 : ρ < ρ')
    (h3 : ρ' < 5 / 2) : innerInv K ρ < innerInv K ρ' := by
  unfold innerInv
  apply Real.sqrt_lt_sqrt
  · apply div_nonneg (mul_nonneg hK.le (by linarith)) (by linarith)
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

theorem innerInv_lt_sqrt (hK : 0 < K) {ρ : ℝ} (h1 : 1 / 2 ≤ ρ) (h2 : ρ < 3 / 2) :
    innerInv K ρ < Real.sqrt K := by
  unfold innerInv
  apply Real.sqrt_lt_sqrt
  · apply div_nonneg (mul_nonneg hK.le (by linarith)) (by linarith)
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith

theorem contDiffAt_innerInv (hK : 0 < K) {ρ : ℝ} (h1 : 1 / 2 < ρ) (h2 : ρ < 5 / 2) :
    ContDiffAt ℝ ∞ (innerInv K) ρ := by
  have hd : (5 / 2 - ρ) ≠ 0 := by linarith
  have h : ContDiffAt ℝ ∞ (fun x : ℝ => K * (x - 1 / 2) / (5 / 2 - x)) ρ :=
    (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const)).div
      (contDiffAt_const.sub contDiffAt_id) hd
  exact h.sqrt (div_pos (mul_pos hK (by linarith)) (by linarith)).ne'

theorem outerInv_lt_outerInv (hK : 0 < K) {Y₂ : ℝ} (hY₂ : Y₂ < Real.sqrt K) (hY₂0 : 0 < Y₂)
    {r r' : ℝ} (h1 : 2 ≤ r) (h2 : r < r') (h3 : r' < 3) : outerInv K Y₂ r < outerInv K Y₂ r' := by
  unfold outerInv
  have hA : 0 < (Real.sqrt K - Y₂) * (1 + Y₂) := mul_pos (by linarith) (by linarith)
  have hi := innerInv_lt_innerInv hK (K := K) (ρ := r - 3 / 2) (ρ' := r' - 3 / 2) (by linarith)
    (by linarith) (by linarith)
  have hs' := innerInv_lt_sqrt hK (ρ := r' - 3 / 2) (by linarith) (by linarith)
  have := div_lt_div_of_pos_left hA (by linarith : 0 < Real.sqrt K - innerInv K (r' - 3 / 2))
    (by linarith : Real.sqrt K - innerInv K (r' - 3 / 2) < Real.sqrt K - innerInv K (r - 3 / 2))
  linarith

theorem contDiffAt_outerInv (hK : 0 < K) (Y₂ : ℝ) {r : ℝ} (h1 : 2 < r) (h2 : r < 3) :
    ContDiffAt ℝ ∞ (outerInv K Y₂) r := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => innerInv K (x - 3 / 2)) r :=
    (contDiffAt_innerInv hK (by linarith) (by linarith)).comp r
      (contDiffAt_id.sub contDiffAt_const)
  have hs := innerInv_lt_sqrt hK (ρ := r - 3 / 2) (by linarith) (by linarith)
  exact (contDiffAt_const.div (contDiffAt_const.sub hi) (by linarith)).sub contDiffAt_const

theorem outerProfile_eq_of_le {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) {y : ℝ} (hy : Y₂ ≤ y) :
    outerProfile K Y₁ Y₂ y = 3 / 2 + coneProfile K (outerTarget K Y₂ y) := by
  unfold outerProfile outerReparam
  rw [coneStep_eq_one hY hy]
  ring_nf

theorem outerTarget_self (Y₂ : ℝ) (hY₂ : 0 < Y₂) : outerTarget K Y₂ Y₂ = Y₂ := by
  unfold outerTarget
  have : (1 + Y₂) ≠ 0 := by linarith
  field_simp
  ring

theorem outerInv_outerProfile (hK0 : 0 < K) (hK : Real.sqrt K ≤ 1 / 2) {Y₁ Y₂ : ℝ}
    (hY₁ : 0 ≤ Y₁) (hY : Y₁ < Y₂) (hY₂ : Y₂ < Real.sqrt K) {y : ℝ} (hy : Y₂ ≤ y) :
    outerInv K Y₂ (outerProfile K Y₁ Y₂ y) = y := by
  have hY₂0 : 0 < Y₂ := by linarith
  have hy0 : 0 ≤ y := by linarith
  rw [outerProfile_eq_of_le hY hy, outerInv,
    show 3 / 2 + coneProfile K (outerTarget K Y₂ y) - 3 / 2 = coneProfile K (outerTarget K Y₂ y)
      by ring, innerInv_coneProfile hK0 (outerTarget_pos hK hY₂0 hY₂ hy0).le]
  unfold outerTarget
  have hA : 0 < (Real.sqrt K - Y₂) * (1 + Y₂) := mul_pos (by linarith) (by linarith)
  have h1 : (1 + y) ≠ 0 := by linarith
  have h2 : Real.sqrt K - Y₂ ≠ 0 := by linarith
  rw [sub_sub_cancel]
  field_simp
  ring

theorem outerProfile_self {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) (hY₂0 : 0 < Y₂) :
    outerProfile K Y₁ Y₂ Y₂ = 3 / 2 + coneProfile K Y₂ := by
  rw [outerProfile_eq_of_le hY le_rfl, outerTarget_self Y₂ hY₂0]

end Inverses

theorem contDiff_rampFn (a : ℝ) : ContDiff ℝ ∞ (rampFn a) :=
  contDiff_id.mul (contDiff_coneStep _ _)

theorem rampFn_of_le {a t : ℝ} (h : t ≤ a) : rampFn a t = 0 := by
  rw [rampFn, coneStep_eq_zero (by linarith) h, mul_zero]

theorem rampFn_of_ge {a t : ℝ} (h : a + 1 ≤ t) : rampFn a t = t := by
  rw [rampFn, coneStep_eq_one (by linarith) h, mul_one]

theorem rampFn_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : 0 ≤ rampFn a t := by
  rcases le_or_gt t a with h | h
  · rw [rampFn_of_le h]
  · exact mul_nonneg (by linarith) (coneStep_nonneg _ _ _)

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData)

theorem constK_pos' : 0 < σ.constK := σ.constK_pos

theorem outerY₂_pos : 0 < D.outerY₂ := by linarith [D.outerY₁_pos, D.outerY₁_lt]

def outerExhaust (r : ℝ) : ℝ :=
  if outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ < r then
    rampFn (Real.log (D.outerY₂ + 1)) (Real.log (outerInv σ.constK D.outerY₂ r))
  else 0

def innerExhaust (ρ : ℝ) : ℝ :=
  if ρ < coneProfile σ.constK D.outerY₂ then
    rampFn (-Real.log (D.outerY₂ / 2)) (-Real.log (innerInv σ.constK ρ))
  else 0

def exhaust (u : ℂ) : ℝ := D.outerExhaust ‖u‖ + D.innerExhaust ‖u + 3 / 2‖

theorem exhaust_conj (u : ℂ) : D.exhaust (conj u) = D.exhaust u := by
  have h : conj u + 3 / 2 = conj (u + 3 / 2) := by
    rw [map_add, map_div₀, map_ofNat, map_ofNat]
  rw [exhaust, exhaust, Complex.norm_conj, h, Complex.norm_conj]

theorem log_outerY₂_nonneg : 0 ≤ Real.log (D.outerY₂ + 1) :=
  Real.log_nonneg (by linarith [D.outerY₂_pos])

theorem neg_log_outerY₂_nonneg : 0 ≤ -Real.log (D.outerY₂ / 2) := by
  have h1 : D.outerY₂ / 2 ≤ 1 := by
    have := D.outerY₂_lt
    have := σ.sqrt_constK_le
    linarith
  have := Real.log_nonpos (by linarith [D.outerY₂_pos]) h1
  linarith

theorem outerExhaust_nonneg (r : ℝ) : 0 ≤ D.outerExhaust r := by
  unfold outerExhaust
  split_ifs
  · exact rampFn_nonneg D.log_outerY₂_nonneg _
  · exact le_rfl

theorem innerExhaust_nonneg (ρ : ℝ) : 0 ≤ D.innerExhaust ρ := by
  unfold innerExhaust
  split_ifs
  · exact rampFn_nonneg D.neg_log_outerY₂_nonneg _
  · exact le_rfl

theorem exhaust_nonneg (u : ℂ) : 0 ≤ D.exhaust u :=
  add_nonneg (D.outerExhaust_nonneg _) (D.innerExhaust_nonneg _)

theorem outerProfile_props {y : ℝ} (hy : 0 < y) :
    2 < outerProfile σ.constK D.outerY₁ D.outerY₂ y ∧
      outerProfile σ.constK D.outerY₁ D.outerY₂ y < 3 :=
  ⟨two_lt_outerProfile σ.constK_pos σ.sqrt_constK_le D.outerY₂_pos D.outerY₂_lt hy,
    outerProfile_lt_three σ.constK_pos σ.sqrt_constK_le D.outerY₁_pos.le D.outerY₁_lt
      D.outerY₂_lt hy⟩

theorem outerProfile_lt_outerProfile {y y' : ℝ} (hy : 0 < y) (h : y < y') :
    outerProfile σ.constK D.outerY₁ D.outerY₂ y < outerProfile σ.constK D.outerY₁ D.outerY₂ y' :=
  outerProfile_mono σ.constK_pos σ.sqrt_constK_le D.outerY₁_pos.le D.outerY₁_lt D.outerY₂_lt
    hy (lt_trans hy h) h

theorem outerInv_outerProfile' {y : ℝ} (hy : D.outerY₂ ≤ y) :
    outerInv σ.constK D.outerY₂ (outerProfile σ.constK D.outerY₁ D.outerY₂ y) = y :=
  outerInv_outerProfile σ.constK_pos σ.sqrt_constK_le D.outerY₁_pos.le D.outerY₁_lt D.outerY₂_lt hy

theorem outerInv_gt_of_lt {y r : ℝ} (hy : D.outerY₂ ≤ y)
    (h : outerProfile σ.constK D.outerY₁ D.outerY₂ y < r) (hr : r < 3) :
    y < outerInv σ.constK D.outerY₂ r := by
  have hy0 : 0 < y := lt_of_lt_of_le D.outerY₂_pos hy
  have h2 := (D.outerProfile_props hy0).1
  have := outerInv_lt_outerInv σ.constK_pos D.outerY₂_lt D.outerY₂_pos h2.le h hr
  rwa [D.outerInv_outerProfile' hy] at this

theorem outerInv_lt_of_lt {y r : ℝ} (hy : D.outerY₂ ≤ y)
    (h0 : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ ≤ r)
    (h : r < outerProfile σ.constK D.outerY₁ D.outerY₂ y) :
    outerInv σ.constK D.outerY₂ r < y := by
  have hy0 : 0 < y := lt_of_lt_of_le D.outerY₂_pos hy
  have h2 := (D.outerProfile_props D.outerY₂_pos).1
  have := outerInv_lt_outerInv σ.constK_pos D.outerY₂_lt D.outerY₂_pos (by linarith) h
    (D.outerProfile_props hy0).2
  rwa [D.outerInv_outerProfile' hy] at this

theorem outerInv_pos_of_lt {r : ℝ} (h : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ < r)
    (hr : r < 3) : 0 < outerInv σ.constK D.outerY₂ r :=
  lt_trans D.outerY₂_pos (D.outerInv_gt_of_lt le_rfl h hr)

theorem outerExhaust_eq_zero {r : ℝ}
    (h : r < outerProfile σ.constK D.outerY₁ D.outerY₂ (D.outerY₂ + 1)) : D.outerExhaust r = 0 := by
  unfold outerExhaust
  split_ifs with h0
  · apply rampFn_of_le
    have hlt := D.outerInv_lt_of_lt (by linarith) h0.le h
    exact (Real.log_lt_log (D.outerInv_pos_of_lt h0
      (lt_trans h (D.outerProfile_props (by linarith [D.outerY₂_pos])).2)) hlt).le
  · rfl

theorem outerExhaust_outerProfile {y : ℝ} (hy : Real.exp (Real.log (D.outerY₂ + 1) + 1) ≤ y) :
    D.outerExhaust (outerProfile σ.constK D.outerY₁ D.outerY₂ y) = Real.log y := by
  have hY : D.outerY₂ + 1 ≤ Real.exp (Real.log (D.outerY₂ + 1) + 1) := by
    rw [Real.exp_add, Real.exp_log (by linarith [D.outerY₂_pos])]
    nlinarith [Real.add_one_le_exp (1 : ℝ), D.outerY₂_pos]
  have hy2 : D.outerY₂ < y := by linarith
  have hy0 : 0 < y := lt_trans D.outerY₂_pos hy2
  unfold outerExhaust
  rw [ite_eq_left (D.outerProfile_lt_outerProfile D.outerY₂_pos hy2),
    D.outerInv_outerProfile' hy2.le]
  apply rampFn_of_ge
  rw [← Real.log_exp (Real.log (D.outerY₂ + 1) + 1)]
  exact Real.log_le_log (Real.exp_pos _) hy

theorem innerExhaust_eq_zero {ρ : ℝ} (h : coneProfile σ.constK (D.outerY₂ / 2) < ρ) :
    D.innerExhaust ρ = 0 := by
  unfold innerExhaust
  split_ifs with h0
  · apply rampFn_of_le
    have hK := σ.constK_pos
    have hY := D.outerY₂_pos
    have h1 := innerInv_lt_innerInv hK (half_le_coneProfile hK _) h
      (lt_trans h0 (coneProfile_lt hK _))
    rw [innerInv_coneProfile hK (by linarith)] at h1
    have := Real.log_lt_log (by linarith) h1
    linarith
  · rfl

theorem innerExhaust_coneProfile {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) :
    D.innerExhaust (coneProfile σ.constK t) = -Real.log t := by
  have hK := σ.constK_pos
  have hY := D.outerY₂_pos
  have hlt : t < D.outerY₂ := by
    have e : Real.exp (-(-Real.log (D.outerY₂ / 2) + 1)) = D.outerY₂ / 2 * Real.exp (-1) := by
      rw [show -(-Real.log (D.outerY₂ / 2) + 1) = Real.log (D.outerY₂ / 2) + -1 by ring,
        Real.exp_add, Real.exp_log (by linarith)]
    have : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at this
    rw [e] at ht
    nlinarith
  unfold innerExhaust
  rw [ite_eq_left (strictMonoOn_coneProfile hK ht0.le hY.le hlt), innerInv_coneProfile hK ht0.le]
  apply rampFn_of_ge
  have := Real.log_le_log ht0 ht
  rw [Real.log_exp] at this
  linarith

theorem le_of_outerExhaust_le {r R : ℝ} (hr : r < 3) (h : D.outerExhaust r ≤ R) :
    r ≤ outerProfile σ.constK D.outerY₁ D.outerY₂
      (max (Real.exp (Real.log (D.outerY₂ + 1) + 1)) (Real.exp R)) := by
  set Y := max (Real.exp (Real.log (D.outerY₂ + 1) + 1)) (Real.exp R)
  have hY1 : D.outerY₂ + 1 ≤ Real.exp (Real.log (D.outerY₂ + 1) + 1) := by
    rw [Real.exp_add, Real.exp_log (by linarith [D.outerY₂_pos])]
    nlinarith [Real.add_one_le_exp (1 : ℝ), D.outerY₂_pos]
  have hYY : D.outerY₂ ≤ Y := by
    have := le_max_left (Real.exp (Real.log (D.outerY₂ + 1) + 1)) (Real.exp R)
    linarith
  by_contra hc
  push Not at hc
  have hY0 : 0 < Y := lt_of_lt_of_le D.outerY₂_pos hYY
  have h0 : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ < r := by
    rcases hYY.lt_or_eq with h' | h'
    · exact lt_trans (D.outerProfile_lt_outerProfile D.outerY₂_pos h') hc
    · have e : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ =
          outerProfile σ.constK D.outerY₁ D.outerY₂ Y :=
        congrArg (outerProfile σ.constK D.outerY₁ D.outerY₂) h'
      rw [e]
      exact hc
  have hgt := D.outerInv_gt_of_lt hYY hc hr
  have hlog : Real.log Y < Real.log (outerInv σ.constK D.outerY₂ r) := Real.log_lt_log hY0 hgt
  have hl1 : Real.log (D.outerY₂ + 1) + 1 ≤ Real.log Y := by
    rw [← Real.log_exp (Real.log (D.outerY₂ + 1) + 1)]
    exact Real.log_le_log (Real.exp_pos _) (le_max_left _ _)
  have hl2 : R ≤ Real.log Y := by
    rw [← Real.log_exp R]
    exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  unfold outerExhaust at h
  rw [ite_eq_left h0, rampFn_of_ge (by linarith)] at h
  linarith

theorem le_of_innerExhaust_le {ρ R : ℝ} (hρ : 1 / 2 < ρ) (h : D.innerExhaust ρ ≤ R) :
    coneProfile σ.constK (min (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) (Real.exp (-R))) ≤
      ρ := by
  set η := min (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) (Real.exp (-R))
  have hK := σ.constK_pos
  have hY := D.outerY₂_pos
  have hη0 : 0 < η := lt_min (Real.exp_pos _) (Real.exp_pos _)
  by_contra hc
  push Not at hc
  have hηY : η < D.outerY₂ := by
    have e : Real.exp (-(-Real.log (D.outerY₂ / 2) + 1)) = D.outerY₂ / 2 * Real.exp (-1) := by
      rw [show -(-Real.log (D.outerY₂ / 2) + 1) = Real.log (D.outerY₂ / 2) + -1 by ring,
        Real.exp_add, Real.exp_log (by linarith)]
    have : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at this
    have := min_le_left (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) (Real.exp (-R))
    nlinarith
  have h0 : ρ < coneProfile σ.constK D.outerY₂ :=
    lt_trans hc (strictMonoOn_coneProfile hK hη0.le hY.le hηY)
  have hlt := innerInv_lt_innerInv hK hρ.le hc (coneProfile_lt hK _)
  rw [innerInv_coneProfile hK hη0.le] at hlt
  have hpos := innerInv_pos hK hρ (lt_trans hc (coneProfile_lt hK _))
  have hlog := Real.log_lt_log hpos hlt
  have hl1 : -Real.log (D.outerY₂ / 2) + 1 ≤ -Real.log η := by
    have := Real.log_le_log hη0 (min_le_left _ _)
    rw [Real.log_exp] at this
    linarith
  have hl2 : R ≤ -Real.log η := by
    have := Real.log_le_log hη0 (min_le_right _ _)
    rw [Real.log_exp] at this
    linarith
  unfold innerExhaust at h
  rw [ite_eq_left h0, rampFn_of_ge (by linarith)] at h
  linarith

theorem contDiffAt_outerExhaust_norm {u : ℂ} (hu : ‖u‖ < 3) :
    ContDiffAt ℝ ∞ (fun w : ℂ => D.outerExhaust ‖w‖) u := by
  have hK := σ.constK_pos
  by_cases h : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ < ‖u‖
  · have h2 : 2 < ‖u‖ := lt_trans (D.outerProfile_props D.outerY₂_pos).1 h
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h2
      linarith
    have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) u := contDiffAt_norm ℝ hu0
    have hev : (fun w : ℂ => D.outerExhaust ‖w‖) =ᶠ[𝓝 u] fun w =>
        rampFn (Real.log (D.outerY₂ + 1)) (Real.log (outerInv σ.constK D.outerY₂ ‖w‖)) := by
      filter_upwards [continuousAt_const.eventually_lt hn.continuousAt h] with w hw
      rw [outerExhaust, ite_eq_left hw]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hi : ContDiffAt ℝ ∞ (outerInv σ.constK D.outerY₂ ∘ fun w : ℂ => ‖w‖) u :=
      (contDiffAt_outerInv hK _ h2 hu).comp u hn
    exact (contDiff_rampFn _).contDiffAt.comp u (hi.log (D.outerInv_pos_of_lt h hu).ne')
  · push Not at h
    have hlt : ‖u‖ < outerProfile σ.constK D.outerY₁ D.outerY₂ (D.outerY₂ + 1) :=
      lt_of_le_of_lt h (D.outerProfile_lt_outerProfile D.outerY₂_pos (by linarith))
    have hev : (fun w : ℂ => D.outerExhaust ‖w‖) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hlt] with w hw
      exact D.outerExhaust_eq_zero hw
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiffAt_innerExhaust_norm {u : ℂ} (hu : 1 / 2 < ‖u + 3 / 2‖) :
    ContDiffAt ℝ ∞ (fun w : ℂ => D.innerExhaust ‖w + 3 / 2‖) u := by
  have hK := σ.constK_pos
  have hY := D.outerY₂_pos
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w + 3 / 2‖) u := by
    have hu0 : u + 3 / 2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hu
      linarith
    exact (contDiffAt_norm ℝ hu0).comp u (contDiffAt_id.add contDiffAt_const)
  by_cases h : ‖u + 3 / 2‖ < coneProfile σ.constK D.outerY₂
  · have hev : (fun w : ℂ => D.innerExhaust ‖w + 3 / 2‖) =ᶠ[𝓝 u] fun w =>
        rampFn (-Real.log (D.outerY₂ / 2)) (-Real.log (innerInv σ.constK ‖w + 3 / 2‖)) := by
      filter_upwards [hn.continuousAt.eventually_lt continuousAt_const h] with w hw
      rw [innerExhaust, ite_eq_left hw]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h5 : ‖u + 3 / 2‖ < 5 / 2 := lt_trans h (coneProfile_lt hK _)
    have hi : ContDiffAt ℝ ∞ (innerInv σ.constK ∘ fun w : ℂ => ‖w + 3 / 2‖) u :=
      (contDiffAt_innerInv hK hu h5).comp u hn
    exact (contDiff_rampFn _).contDiffAt.comp u
      ((hi.log (innerInv_pos hK hu h5).ne').neg)
  · push Not at h
    have hlt : coneProfile σ.constK (D.outerY₂ / 2) < ‖u + 3 / 2‖ :=
      lt_of_lt_of_le (strictMonoOn_coneProfile hK (by positivity : (0 : ℝ) ≤ D.outerY₂ / 2)
        hY.le (by linarith)) h
    have hev : (fun w : ℂ => D.innerExhaust ‖w + 3 / 2‖) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [continuousAt_const.eventually_lt hn.continuousAt hlt] with w hw
      exact D.innerExhaust_eq_zero hw
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiffOn_exhaust : ContDiffOn ℝ ∞ D.exhaust filledBase := fun _ hu =>
  ((D.contDiffAt_outerExhaust_norm hu.1).add
    (D.contDiffAt_innerExhaust_norm hu.2)).contDiffWithinAt

end ConeShape.FoldData

end GC.Seifert
