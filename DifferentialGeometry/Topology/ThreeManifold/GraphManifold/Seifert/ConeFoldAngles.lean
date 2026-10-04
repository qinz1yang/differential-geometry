import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldPolar

/-!
# Angles of a bridge about one of its centres

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
Along a curve on which the radius `A₀` of the first circle of a `twoCircle` bridge is constant,
the bridge point turns about the first centre `a`; its angle, written with `halfArg` (bridge
point near the positive side, `a + A₀`) or `negHalfArg` (near the negative side, `a - A₀`), has
an explicit derivative (`hasDerivAt_halfArg_twoCircle`, `hasDerivAt_negHalfArg_twoCircle`): off the
wall (`w ≠ 0`) it is `2|b - a| B B' / ((b - a) w √P)`, where `B'` is the derivative of the other
radius, so its sign is the sign of `B'/w` — the second-order defect makes `B'` vanish with `w`
and the quotient is the explicit derivative of the other virtual height divided by the wall
function; on the wall it is `± w' √P / (2|b - a| A₀)`. Both are nonzero, which is the exact
monotonicity of design §5 at every point, including the wall. `twoCircle_swap` exchanges the two
centres, so the angle about the second centre is the same lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem twoCircle_swap (a b A B w P : ℝ) : twoCircle a b A B w P = twoCircle b a B A w P := by
  by_cases hab : a = b
  · subst hab
    apply Complex.ext <;> simp
  · have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hd' : a - b ≠ 0 := sub_ne_zero.2 hab
    apply Complex.ext
    · simp only [twoCircle_re]
      field_simp
      ring
    · simp only [twoCircle_im, abs_sub_comm]

theorem sq_add_sq_of_twoCircle {a b A B w P : ℝ} (hab : a ≠ b) (hP : 0 ≤ P)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P) :
    ((twoCircle a b A B w P).re - a) ^ 2 + (twoCircle a b A B w P).im ^ 2 = A ^ 2 := by
  have h := twoCircle_normSq_sub_left hab hP hH
  rw [normSq_apply] at h
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero] at h
  nlinarith [h]

theorem hasDerivAt_twoCircle_re {a b A₀ : ℝ} {B : ℝ → ℝ} {B' t₀ : ℝ} (w P : ℝ → ℝ)
    (hB : HasDerivAt B B' t₀) :
    HasDerivAt (fun t => (twoCircle a b A₀ (B t) (w t) (P t)).re - a)
      (-(B t₀ * B') / (b - a)) t₀ := by
  simp only [twoCircle_re, add_sub_cancel_left]
  have h := ((hasDerivAt_const t₀ (A₀ ^ 2)).sub (hB.pow 2)).add_const ((b - a) ^ 2)
  have h' := h.div_const (2 * (b - a))
  refine h'.congr_deriv ?_
  by_cases hd : b - a = 0
  · simp [hd]
  · field_simp
    push_cast
    ring

theorem hasDerivAt_twoCircle_im {a b A₀ : ℝ} {B w P : ℝ → ℝ} {w' t₀ : ℝ}
    (hw : HasDerivAt w w' t₀) (hP : DifferentiableAt ℝ P t₀) (hP0 : 0 < P t₀) :
    HasDerivAt (fun t => (twoCircle a b A₀ (B t) (w t) (P t)).im)
      ((w' * Real.sqrt (P t₀) + w t₀ * deriv (fun t => Real.sqrt (P t)) t₀) / (2 * |b - a|))
      t₀ := by
  simp only [twoCircle_im]
  have hs : DifferentiableAt ℝ (fun t => Real.sqrt (P t)) t₀ := hP.sqrt hP0.ne'
  exact (hw.mul hs.hasDerivAt).div_const _

theorem hasDerivAt_halfArg_of_sq {R J : ℝ → ℝ} {S R' J' t₀ : ℝ} (hR : HasDerivAt R R' t₀)
    (hJ : HasDerivAt J J' t₀) (hS : 0 < S) (hSR : 0 < S + R t₀)
    (hc : ∀ᶠ t in 𝓝 t₀, R t ^ 2 + J t ^ 2 = S ^ 2) :
    HasDerivAt (fun t => halfArg S (R t) (J t))
      (if J t₀ = 0 then J' / S else -R' / J t₀) t₀ := by
  have h := hasDerivAt_halfArg hR hJ hSR
  have hc0 : R t₀ ^ 2 + J t₀ ^ 2 = S ^ 2 := hc.self_of_nhds
  have hd : R t₀ * R' + J t₀ * J' = 0 := by
    have h1 : HasDerivAt (fun t => R t ^ 2 + J t ^ 2) (2 * R t₀ * R' + 2 * J t₀ * J') t₀ := by
      convert (hR.pow 2).add (hJ.pow 2) using 1
      simp
    have h2 : HasDerivAt (fun t => R t ^ 2 + J t ^ 2) 0 t₀ :=
      (hasDerivAt_const t₀ (S ^ 2)).congr_of_eventuallyEq hc
    have := h1.unique h2
    linarith
  refine h.congr_deriv ?_
  split_ifs with hJ0
  · have hR0 : R t₀ = S := by
      rw [hJ0] at hc0
      have : (R t₀ - S) * (R t₀ + S) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    exact halfArg_deriv_on hS hJ0 hR0
  · exact halfArg_deriv_off hS hSR hc0 hd hJ0

theorem hasDerivAt_negHalfArg_of_sq {R J : ℝ → ℝ} {S R' J' t₀ : ℝ} (hR : HasDerivAt R R' t₀)
    (hJ : HasDerivAt J J' t₀) (hS : 0 < S) (hSR : 0 < S - R t₀)
    (hc : ∀ᶠ t in 𝓝 t₀, R t ^ 2 + J t ^ 2 = S ^ 2) :
    HasDerivAt (fun t => negHalfArg S (R t) (J t))
      (if J t₀ = 0 then -J' / S else -R' / J t₀) t₀ := by
  have h := hasDerivAt_negHalfArg hR hJ hSR
  have hc0 : R t₀ ^ 2 + J t₀ ^ 2 = S ^ 2 := hc.self_of_nhds
  have hd : R t₀ * R' + J t₀ * J' = 0 := by
    have h1 : HasDerivAt (fun t => R t ^ 2 + J t ^ 2) (2 * R t₀ * R' + 2 * J t₀ * J') t₀ := by
      convert (hR.pow 2).add (hJ.pow 2) using 1
      simp
    have h2 : HasDerivAt (fun t => R t ^ 2 + J t ^ 2) 0 t₀ :=
      (hasDerivAt_const t₀ (S ^ 2)).congr_of_eventuallyEq hc
    have := h1.unique h2
    linarith
  refine h.congr_deriv ?_
  split_ifs with hJ0
  · have hR0 : R t₀ = -S := by
      rw [hJ0] at hc0
      have : (R t₀ - S) * (R t₀ + S) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    exact negHalfArg_deriv_on hS hJ0 hR0
  · exact negHalfArg_deriv_off hS hSR hc0 hd hJ0

theorem hasDerivAt_halfArg_twoCircle {a b A₀ : ℝ} {B w P : ℝ → ℝ} {B' w' t₀ : ℝ}
    (hab : a ≠ b) (hA₀ : 0 < A₀) (hB : HasDerivAt B B' t₀) (hw : HasDerivAt w w' t₀)
    (hP : DifferentiableAt ℝ P t₀) (hP0 : ∀ᶠ t in 𝓝 t₀, 0 < P t)
    (hH : ∀ᶠ t in 𝓝 t₀,
      ((A₀ + B t) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A₀ - B t) ^ 2) = w t ^ 2 * P t)
    (hpos : 0 < A₀ + ((twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).re - a)) :
    HasDerivAt (fun t => halfArg A₀ ((twoCircle a b A₀ (B t) (w t) (P t)).re - a)
        (twoCircle a b A₀ (B t) (w t) (P t)).im)
      (if w t₀ = 0 then w' * Real.sqrt (P t₀) / (2 * |b - a| * A₀)
        else 2 * |b - a| * (B t₀ * B') / ((b - a) * w t₀ * Real.sqrt (P t₀))) t₀ := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have habs : 0 < |b - a| := abs_pos.2 hd
  have hPt := hP0.self_of_nhds
  have hsq := Real.sqrt_pos.2 hPt
  have hR := hasDerivAt_twoCircle_re (a := a) (b := b) (A₀ := A₀) w P hB
  have hJ := hasDerivAt_twoCircle_im (a := a) (b := b) (A₀ := A₀) (B := B) hw hP hPt
  have hc : ∀ᶠ t in 𝓝 t₀, ((twoCircle a b A₀ (B t) (w t) (P t)).re - a) ^ 2 +
      (twoCircle a b A₀ (B t) (w t) (P t)).im ^ 2 = A₀ ^ 2 := by
    filter_upwards [hP0, hH] with t ht1 ht2
    exact sq_add_sq_of_twoCircle hab ht1.le ht2
  have h := hasDerivAt_halfArg_of_sq hR hJ hA₀ hpos hc
  refine h.congr_deriv ?_
  have him0 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im = 0 ↔ w t₀ = 0 := by
    rw [twoCircle_im]
    constructor
    · intro h0
      have : w t₀ * Real.sqrt (P t₀) = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exfalso
          linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · exfalso
        linarith
    · intro h0
      rw [h0]
      simp
  by_cases hw0 : w t₀ = 0
  · have h1 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im = 0 := him0.2 hw0
    simp only [h1, ↓reduceIte]
    simp only [hw0, ↓reduceIte, zero_mul, add_zero]
    field_simp
  · have h1 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im ≠ 0 := fun h' => hw0 (him0.1 h')
    simp only [h1, ↓reduceIte]
    simp only [hw0, ↓reduceIte, twoCircle_im]
    field_simp

theorem hasDerivAt_negHalfArg_twoCircle {a b A₀ : ℝ} {B w P : ℝ → ℝ} {B' w' t₀ : ℝ}
    (hab : a ≠ b) (hA₀ : 0 < A₀) (hB : HasDerivAt B B' t₀) (hw : HasDerivAt w w' t₀)
    (hP : DifferentiableAt ℝ P t₀) (hP0 : ∀ᶠ t in 𝓝 t₀, 0 < P t)
    (hH : ∀ᶠ t in 𝓝 t₀,
      ((A₀ + B t) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A₀ - B t) ^ 2) = w t ^ 2 * P t)
    (hpos : 0 < A₀ - ((twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).re - a)) :
    HasDerivAt (fun t => negHalfArg A₀ ((twoCircle a b A₀ (B t) (w t) (P t)).re - a)
        (twoCircle a b A₀ (B t) (w t) (P t)).im)
      (if w t₀ = 0 then -(w' * Real.sqrt (P t₀) / (2 * |b - a| * A₀))
        else 2 * |b - a| * (B t₀ * B') / ((b - a) * w t₀ * Real.sqrt (P t₀))) t₀ := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have habs : 0 < |b - a| := abs_pos.2 hd
  have hPt := hP0.self_of_nhds
  have hsq := Real.sqrt_pos.2 hPt
  have hR := hasDerivAt_twoCircle_re (a := a) (b := b) (A₀ := A₀) w P hB
  have hJ := hasDerivAt_twoCircle_im (a := a) (b := b) (A₀ := A₀) (B := B) hw hP hPt
  have hc : ∀ᶠ t in 𝓝 t₀, ((twoCircle a b A₀ (B t) (w t) (P t)).re - a) ^ 2 +
      (twoCircle a b A₀ (B t) (w t) (P t)).im ^ 2 = A₀ ^ 2 := by
    filter_upwards [hP0, hH] with t ht1 ht2
    exact sq_add_sq_of_twoCircle hab ht1.le ht2
  have h := hasDerivAt_negHalfArg_of_sq hR hJ hA₀ hpos hc
  refine h.congr_deriv ?_
  have him0 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im = 0 ↔ w t₀ = 0 := by
    rw [twoCircle_im]
    constructor
    · intro h0
      have : w t₀ * Real.sqrt (P t₀) = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exfalso
          linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · exfalso
        linarith
    · intro h0
      rw [h0]
      simp
  by_cases hw0 : w t₀ = 0
  · have h1 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im = 0 := him0.2 hw0
    simp only [h1, ↓reduceIte]
    simp only [hw0, ↓reduceIte, zero_mul, add_zero]
    field_simp
  · have h1 : (twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).im ≠ 0 := fun h' => hw0 (him0.1 h')
    simp only [h1, ↓reduceIte]
    simp only [hw0, ↓reduceIte, twoCircle_im]
    field_simp

theorem hasDerivAt_halfArg_twoCircle' {a b A₀ : ℝ} {B w P : ℝ → ℝ} {κ w' t₀ : ℝ}
    (hab : a ≠ b) (hA₀ : 0 < A₀) (hB : HasDerivAt B (w t₀ * κ) t₀) (hw : HasDerivAt w w' t₀)
    (hP : DifferentiableAt ℝ P t₀) (hP0 : ∀ᶠ t in 𝓝 t₀, 0 < P t)
    (hH : ∀ᶠ t in 𝓝 t₀,
      ((A₀ + B t) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A₀ - B t) ^ 2) = w t ^ 2 * P t)
    (hpos : 0 < A₀ + ((twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).re - a)) :
    HasDerivAt (fun t => halfArg A₀ ((twoCircle a b A₀ (B t) (w t) (P t)).re - a)
        (twoCircle a b A₀ (B t) (w t) (P t)).im)
      (if w t₀ = 0 then w' * Real.sqrt (P t₀) / (2 * |b - a| * A₀)
        else 2 * |b - a| * B t₀ * κ / ((b - a) * Real.sqrt (P t₀))) t₀ := by
  refine (hasDerivAt_halfArg_twoCircle hab hA₀ hB hw hP hP0 hH hpos).congr_deriv ?_
  split_ifs with h0
  · rfl
  · have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hs : Real.sqrt (P t₀) ≠ 0 := (Real.sqrt_pos.2 hP0.self_of_nhds).ne'
    field_simp

theorem hasDerivAt_negHalfArg_twoCircle' {a b A₀ : ℝ} {B w P : ℝ → ℝ} {κ w' t₀ : ℝ}
    (hab : a ≠ b) (hA₀ : 0 < A₀) (hB : HasDerivAt B (w t₀ * κ) t₀) (hw : HasDerivAt w w' t₀)
    (hP : DifferentiableAt ℝ P t₀) (hP0 : ∀ᶠ t in 𝓝 t₀, 0 < P t)
    (hH : ∀ᶠ t in 𝓝 t₀,
      ((A₀ + B t) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A₀ - B t) ^ 2) = w t ^ 2 * P t)
    (hpos : 0 < A₀ - ((twoCircle a b A₀ (B t₀) (w t₀) (P t₀)).re - a)) :
    HasDerivAt (fun t => negHalfArg A₀ ((twoCircle a b A₀ (B t) (w t) (P t)).re - a)
        (twoCircle a b A₀ (B t) (w t) (P t)).im)
      (if w t₀ = 0 then -(w' * Real.sqrt (P t₀) / (2 * |b - a| * A₀))
        else 2 * |b - a| * B t₀ * κ / ((b - a) * Real.sqrt (P t₀))) t₀ := by
  refine (hasDerivAt_negHalfArg_twoCircle hab hA₀ hB hw hP hP0 hH hpos).congr_deriv ?_
  split_ifs with h0
  · rfl
  · have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hs : Real.sqrt (P t₀) ≠ 0 := (Real.sqrt_pos.2 hP0.self_of_nhds).ne'
    field_simp

end GC.Seifert
