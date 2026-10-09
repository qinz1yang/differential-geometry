import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelNested

/-!
# The nested circle family of a capped side

Lane N2d, side model, step 3 (the explicit family). In the host chart `w = hostInv l z` of the
seam circle `l`, the solid torus of `V` is the annulus `vRadius l 3 ≤ |w| ≤ vRadius l 0` swept by
the meridian discs (`vRadius l ρ = hostRadius l (2 (ρ - 3) / 3)` for `ρ ≥ 2`, compactified to a
finite outer radius: `(21 - ρ) / 6` for `l = 0`, `6 / ρ` blended into `7 - ρ` for `l = 1, 2`).
The side `t` of the split sphere is parametrized by the circles `sideFamily l t ρ`: for
`ρ ≤ 2` the circles `|w| = vRadius l (2 ρ)` about `0`, for `ρ ≥ 5/2` the images under `hostInv l`
of the collar circles of `sidePort l t` at collar depth `2 (3 - ρ) / 3`, parametrized through the
angle `ū`, and a smooth interpolation of centres, radii, rotations and real Blaschke factors in
between. The family is strictly nested on `[0, 3]` and the radii, centres, Blaschke parameters
are smooth on `(1, 4)`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

open GC.GraphManifold

def vBlend (ρ : ℝ) : ℝ := Real.smoothTransition (ρ - 1)

def vRadius (l : Fin 3) (ρ : ℝ) : ℝ :=
  if l.val = 0 then (21 - ρ) / 6 else (1 - vBlend ρ) * (7 - ρ) + vBlend ρ * (6 / ρ)

theorem vBlend_of_le {ρ : ℝ} (h : ρ ≤ 1) : vBlend ρ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem vBlend_of_ge {ρ : ℝ} (h : 2 ≤ ρ) : vBlend ρ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem vRadius_of_two_le (l : Fin 3) {ρ : ℝ} (h : 2 ≤ ρ) :
    vRadius l ρ = hostRadius l.val (2 * (ρ - 3) / 3) := by
  unfold vRadius hostRadius
  by_cases hl : l.val = 0
  · simp only [hl, ↓reduceIte]
    ring
  · simp only [hl, ↓reduceIte, vBlend_of_ge h]
    have hρ : ρ ≠ 0 := by linarith
    rw [show (2 : ℝ) + 2 * (ρ - 3) / 3 = 2 * ρ / 3 by ring]
    field_simp
    ring

theorem vRadius_eq_six_div {l : Fin 3} (hl : l.val ≠ 0) {ρ : ℝ} (h : 2 ≤ ρ) :
    vRadius l ρ = 6 / ρ := by
  simp only [vRadius, hl, ↓reduceIte, vBlend_of_ge h]
  ring

theorem vRadius_zero_eq (l : Fin 3) {ρ : ℝ} (hl : l.val = 0) : vRadius l ρ = (21 - ρ) / 6 := by
  simp [vRadius, hl]

theorem contDiffAt_vRadius (l : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) : ContDiffAt ℝ ∞ (vRadius l) ρ := by
  unfold vRadius
  by_cases hl : l.val = 0
  · simp only [hl, ↓reduceIte]
    exact (contDiffAt_const.sub contDiffAt_id).div_const 6
  · simp only [hl, ↓reduceIte]
    have hb : ContDiff ℝ ∞ vBlend :=
      Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
    exact ((contDiffAt_const.sub hb.contDiffAt).mul (contDiffAt_const.sub contDiffAt_id)).add
      (hb.contDiffAt.mul (contDiffAt_const.div contDiffAt_id hρ.ne'))

theorem continuousOn_vRadius (l : Fin 3) : ContinuousOn (vRadius l) (Ici 0) := by
  intro ρ hρ
  rcases eq_or_lt_of_le (mem_Ici.mp hρ) with h0 | hpos
  · subst h0
    unfold vRadius
    by_cases hl : l.val = 0
    · simp only [hl, ↓reduceIte]
      exact ((continuous_const.sub continuous_id).div_const 6).continuousWithinAt
    · simp only [hl, ↓reduceIte]
      have heq : (fun ρ : ℝ => (1 - vBlend ρ) * (7 - ρ) + vBlend ρ * (6 / ρ)) =ᶠ[𝓝 0]
          fun ρ => 7 - ρ := by
        filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
        rw [vBlend_of_le (le_of_lt hy)]
        ring
      exact (((continuous_const.sub continuous_id).continuousAt).congr heq.symm).continuousWithinAt
  · exact (contDiffAt_vRadius l hpos).continuousAt.continuousWithinAt

theorem hasDerivAt_vBlend (ρ : ℝ) : HasDerivAt vBlend (deriv Real.smoothTransition (ρ - 1)) ρ := by
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) (ρ - 1)).hasDerivAt
  exact h.comp_sub_const ρ 1

theorem deriv_smoothTransition_eq_zero_of_lt {y : ℝ} (hy : y < 0) :
    deriv Real.smoothTransition y = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
  rw [heq.deriv_eq]
  simp

theorem deriv_smoothTransition_eq_zero_of_gt {y : ℝ} (hy : 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
  rw [heq.deriv_eq]
  simp

theorem strictAntiOn_vRadius (l : Fin 3) : StrictAntiOn (vRadius l) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) (continuousOn_vRadius l) ?_
  intro ρ hρ
  rw [interior_Ici] at hρ
  have hρ0 : 0 < ρ := hρ
  unfold vRadius
  by_cases hl : l.val = 0
  · simp only [hl, ↓reduceIte]
    have h := ((hasDerivAt_id ρ).const_sub 21).div_const 6
    rw [show (fun ρ : ℝ => (21 - ρ) / 6) = fun x => (21 - id x) / 6 from rfl, h.deriv]
    norm_num
  · simp only [hl, ↓reduceIte]
    have hb := hasDerivAt_vBlend ρ
    have hd := ((hb.const_sub 1).mul ((hasDerivAt_id ρ).const_sub 7)).add
      (hb.mul ((hasDerivAt_const ρ (6 : ℝ)).div (hasDerivAt_id ρ) hρ0.ne'))
    rw [show deriv (fun ρ => (1 - vBlend ρ) * (7 - ρ) + vBlend ρ * (6 / ρ)) ρ = _ from hd.deriv]
    simp only [id, Pi.div_apply, zero_mul, zero_sub, mul_neg, mul_one, neg_mul]
    have hχ0 : 0 ≤ vBlend ρ := Real.smoothTransition.nonneg _
    have hχ1 : vBlend ρ ≤ 1 := Real.smoothTransition.le_one _
    have hd0 := smoothTransition_deriv_nonneg' (ρ - 1)
    have key : deriv Real.smoothTransition (ρ - 1) * (6 / ρ - (7 - ρ)) ≤ 0 := by
      by_cases h1 : ρ < 1
      · rw [deriv_smoothTransition_eq_zero_of_lt (by linarith), zero_mul]
      · by_cases h6 : 6 < ρ
        · rw [deriv_smoothTransition_eq_zero_of_gt (by linarith), zero_mul]
        · push Not at h1 h6
          apply mul_nonpos_of_nonneg_of_nonpos hd0
          rw [sub_nonpos, div_le_iff₀ hρ0]
          nlinarith
    have hpos : 0 < (1 - vBlend ρ) + vBlend ρ * (6 / ρ ^ 2) := by
      have : 0 < 6 / ρ ^ 2 := by positivity
      by_cases hχ : vBlend ρ = 1
      · rw [hχ]; linarith
      · have : 0 < 1 - vBlend ρ := by
          rcases lt_or_eq_of_le hχ1 with h | h
          · linarith
          · exact absurd h hχ
        nlinarith
    have e : -(deriv Real.smoothTransition (ρ - 1) * (7 - ρ)) + -(1 - vBlend ρ) +
        (deriv Real.smoothTransition (ρ - 1) * (6 / ρ) + vBlend ρ * (-6 / ρ ^ 2)) =
        deriv Real.smoothTransition (ρ - 1) * (6 / ρ - (7 - ρ)) -
          ((1 - vBlend ρ) + vBlend ρ * (6 / ρ ^ 2)) := by
      ring
    linarith [e, key, hpos]

theorem two_le_vRadius (l : Fin 3) {ρ : ℝ} (h0 : 0 ≤ ρ) (h3 : ρ ≤ 3) : 2 ≤ vRadius l ρ := by
  have h := (strictAntiOn_vRadius l).antitoneOn (mem_Ici.mpr h0)
    (mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 3)) h3
  have h3' : vRadius l 3 = hostRadius l.val 0 := by
    rw [vRadius_of_two_le l (by norm_num)]
    norm_num
  have hR : 2 ≤ hostRadius l.val 0 := by
    unfold hostRadius
    split_ifs <;> norm_num
  linarith

theorem nestedOn_union {c : ℝ → ℂ} {r : ℝ → ℝ} {a m b : ℝ} (h1 : NestedOn c r (Icc a m))
    (h2 : NestedOn c r (Icc m b)) : NestedOn c r (Icc a b) := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ hlt
  by_cases hm1 : ρ₂ ≤ m
  · exact h1 ρ₁ ⟨hρ₁.1, hlt.le.trans hm1⟩ ρ₂ ⟨hρ₁.1.trans hlt.le, hm1⟩ hlt
  · push Not at hm1
    by_cases hm2 : m ≤ ρ₁
    · exact h2 ρ₁ ⟨hm2, hlt.le.trans hρ₂.2⟩ ρ₂ ⟨hm1.le, hρ₂.2⟩ hlt
    · push Not at hm2
      have e1 := h1 ρ₁ ⟨hρ₁.1, hm2.le⟩ m ⟨hρ₁.1.trans hm2.le, le_rfl⟩ hm2
      have e2 := h2 m ⟨le_rfl, hm1.le.trans hρ₂.2⟩ ρ₂ ⟨hm1.le, hρ₂.2⟩ hm1
      have e3 := norm_sub_le_norm_sub_add_norm_sub (c ρ₂) (c m) (c ρ₁)
      linarith

theorem nestedOn_of_deriv {c : ℝ → ℂ} {r : ℝ → ℝ} {c' : ℝ → ℂ} {r' : ℝ → ℝ} {a b ε : ℝ}
    (hε : 0 < ε) (hc : ∀ x ∈ Icc a b, HasDerivAt c (c' x) x)
    (hr : ∀ x ∈ Icc a b, HasDerivAt r (r' x) x) (hb : ∀ x ∈ Icc a b, ‖c' x‖ ≤ -r' x - ε) :
    NestedOn c r (Icc a b) := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ hlt
  have hsub : Icc ρ₁ ρ₂ ⊆ Icc a b := Icc_subset_Icc hρ₁.1 hρ₂.2
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun x => c x - c ρ₁) (f' := c') (a := ρ₁) (b := ρ₂)
    (B := fun x => r ρ₁ - r x - ε * (x - ρ₁)) (B' := fun x => -r' x - ε)
    (fun x hx => ((hc x (hsub hx)).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun x hx => ((hc x (hsub (Ico_subset_Icc_self hx))).sub_const (c ρ₁)).hasDerivWithinAt)
    (by simp)
    (fun x hx => ((continuousAt_const.sub (hr x (hsub hx)).continuousAt).sub
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))).continuousWithinAt)
    (fun x hx => by
      have h1 := ((hr x (hsub (Ico_subset_Icc_self hx))).const_sub (r ρ₁)).sub
        (((hasDerivAt_id x).sub_const ρ₁).const_mul ε)
      convert h1.hasDerivWithinAt using 1
      · exact funext fun y => rfl
      · ring)
    (fun x hx => hb x (hsub (Ico_subset_Icc_self hx)))
    (right_mem_Icc.mpr hlt.le)
  nlinarith

def sideBlend (ρ : ℝ) : ℝ := Real.smoothTransition (2 * ρ - 4)

theorem sideBlend_of_le {ρ : ℝ} (h : ρ ≤ 2) : sideBlend ρ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem sideBlend_of_ge {ρ : ℝ} (h : 5 / 2 ≤ ρ) : sideBlend ρ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem contDiff_sideBlend : ContDiff ℝ ∞ sideBlend :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem hasDerivAt_sideBlend (ρ : ℝ) :
    HasDerivAt sideBlend (2 * deriv Real.smoothTransition (2 * ρ - 4)) ρ := by
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
    (2 * ρ - 4)).hasDerivAt
  have h2 := h.comp ρ (((hasDerivAt_id ρ).const_mul 2).sub_const 4)
  convert h2 using 1
  · exact funext fun y => rfl
  · ring

theorem deriv_sideBlend_nonneg (ρ : ℝ) : 0 ≤ 2 * deriv Real.smoothTransition (2 * ρ - 4) := by
  have := smoothTransition_deriv_nonneg' (2 * ρ - 4)
  linarith

theorem deriv_sideBlend_of_ge {ρ : ℝ} (h : 5 / 2 < ρ) :
    2 * deriv Real.smoothTransition (2 * ρ - 4) = 0 := by
  rw [deriv_smoothTransition_eq_zero_of_gt (by linarith), mul_zero]

theorem deriv_sideBlend_of_le {ρ : ℝ} (h : ρ < 2) :
    2 * deriv Real.smoothTransition (2 * ρ - 4) = 0 := by
  rw [deriv_smoothTransition_eq_zero_of_lt (by linarith), mul_zero]

def polarDeriv (l : Fin 3) (ρ : ℝ) : ℝ := if l.val = 0 then -(1 / 3) else -(3 / ρ ^ 2)

theorem hasDerivAt_vRadius_two_mul (l : Fin 3) {ρ : ℝ} (hρ : 1 < ρ) :
    HasDerivAt (fun x => vRadius l (2 * x)) (polarDeriv l ρ) ρ := by
  have heq : (fun x => vRadius l (2 * x)) =ᶠ[𝓝 ρ]
      fun x => if l.val = 0 then (21 - 2 * x) / 6 else 3 / x := by
    filter_upwards [Ioi_mem_nhds hρ] with x hx
    have hx' : 2 ≤ 2 * x := by have : (1 : ℝ) < x := hx; linarith
    by_cases hl : l.val = 0
    · simp only [hl, ↓reduceIte, vRadius_zero_eq l hl]
    · simp only [hl, ↓reduceIte, vRadius_eq_six_div hl hx']
      have : x ≠ 0 := by have : (1 : ℝ) < x := hx; linarith
      field_simp
      ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  unfold polarDeriv
  by_cases hl : l.val = 0
  · simp only [hl, ↓reduceIte]
    have h := ((((hasDerivAt_id ρ).const_mul 2).const_sub 21).div_const 6)
    convert h using 1
    · exact funext fun y => rfl
    · ring
  · simp only [hl, ↓reduceIte]
    have hρ0 : ρ ≠ 0 := by linarith
    have h := (hasDerivAt_id ρ).inv hρ0
    have h2 := h.const_mul 3
    convert h2 using 1
    · funext x
      simp [div_eq_mul_inv]
    · simp only [id]
      field_simp

structure CollarData (l : Fin 3) where
  C : ℝ → ℂ
  R : ℝ → ℝ
  a : ℝ → ℝ
  turn : ℝ
  C' : ℝ → ℂ
  R' : ℝ → ℝ
  smoothC : ContDiffOn ℝ ∞ C (Ioo 1 4)
  smoothR : ContDiffOn ℝ ∞ R (Ioo 1 4)
  smootha : ContDiffOn ℝ ∞ a (Ioo 1 4)
  hasDerivC : ∀ ρ ∈ Ioo (1 : ℝ) 4, HasDerivAt C (C' ρ) ρ
  hasDerivR : ∀ ρ ∈ Ioo (1 : ℝ) 4, HasDerivAt R (R' ρ) ρ
  margin : ∀ ρ ∈ Icc (2 : ℝ) 3, ‖C' ρ‖ ≤ -R' ρ - 1 / 200
  inside : ∀ ρ ∈ Icc (2 : ℝ) 3, ‖C ρ‖ + R ρ ≤ vRadius l (2 * ρ)
  R_pos : ∀ ρ ∈ Icc (2 : ℝ) 3, 0 < R ρ
  a_lt : ∀ ρ ∈ Ioo (2 : ℝ) 4, |a ρ| < 1

namespace CollarData

variable {l : Fin 3} (D : CollarData l)

def famC (ρ : ℝ) : ℂ := (sideBlend ρ : ℂ) * D.C ρ

def famR (ρ : ℝ) : ℝ := (1 - sideBlend ρ) * vRadius l (2 * ρ) + sideBlend ρ * D.R ρ

def famA (ρ : ℝ) : ℝ := sideBlend ρ * D.a ρ

def famMu (ρ : ℝ) : Circle := Circle.exp (Real.pi * (sideBlend ρ * D.turn))

def point (q : Circle × ℝ) : ℂ := nestedPoint D.famC D.famR D.famMu D.famA q

theorem point_of_le_two {q : Circle × ℝ} (h : q.2 ≤ 2) :
    D.point q = (vRadius l (2 * q.2) : ℂ) * (q.1 : ℂ) := by
  simp only [point, nestedPoint, famC, famR, famA, famMu, sideBlend_of_le h]
  simp [blaschke_zero]

theorem point_of_ge {q : Circle × ℝ} (h : 5 / 2 ≤ q.2) :
    D.point q = D.C q.2 + (D.R q.2 : ℂ) *
      ((Circle.exp (Real.pi * D.turn) * blaschke (D.a q.2) q.1 : Circle) : ℂ) := by
  simp only [point, nestedPoint, famC, famR, famA, famMu, sideBlend_of_ge h]
  simp

theorem famA_lt {ρ : ℝ} (h : ρ ∈ Ioo (1 : ℝ) 4) : |D.famA ρ| < 1 := by
  unfold famA
  by_cases h2 : ρ ≤ 2
  · rw [sideBlend_of_le h2, zero_mul, abs_zero]
    norm_num
  · push Not at h2
    have h0 : 0 ≤ sideBlend ρ := Real.smoothTransition.nonneg (2 * ρ - 4)
    have h1 : sideBlend ρ ≤ 1 := Real.smoothTransition.le_one (2 * ρ - 4)
    have ha := D.a_lt ρ ⟨h2, h.2⟩
    rw [abs_mul, abs_of_nonneg h0]
    calc sideBlend ρ * |D.a ρ| ≤ 1 * |D.a ρ| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact ha

theorem famA_lt' {ρ : ℝ} (h : ρ ∈ Icc (0 : ℝ) 3) : |D.famA ρ| < 1 := by
  by_cases h1 : ρ ≤ 2
  · unfold famA
    rw [sideBlend_of_le h1, zero_mul, abs_zero]
    norm_num
  · push Not at h1
    exact D.famA_lt ⟨by linarith, by linarith [h.2]⟩

theorem famR_pos {ρ : ℝ} (h : ρ ∈ Icc (0 : ℝ) 3) : 0 < D.famR ρ := by
  unfold famR
  have hv : 0 < vRadius l (2 * ρ) := by
    by_cases h1 : 2 * ρ ≤ 3
    · linarith [two_le_vRadius l (by linarith [h.1]) h1]
    · push Not at h1
      rw [vRadius_of_two_le l (by linarith)]
      apply hostRadius_pos l.val (by linarith) (by linarith [h.2])
  have h0 := Real.smoothTransition.nonneg (2 * ρ - 4)
  have h1 := Real.smoothTransition.le_one (2 * ρ - 4)
  by_cases h2 : ρ ≤ 2
  · rw [sideBlend_of_le h2]
    simpa using hv
  · push Not at h2
    have hR := D.R_pos ρ ⟨h2.le, h.2⟩
    change 0 < (1 - Real.smoothTransition (2 * ρ - 4)) * vRadius l (2 * ρ) +
      Real.smoothTransition (2 * ρ - 4) * D.R ρ
    rcases eq_or_lt_of_le h0 with he | hlt
    · rw [← he]; simpa using hv
    · have : 0 ≤ (1 - Real.smoothTransition (2 * ρ - 4)) * vRadius l (2 * ρ) :=
        mul_nonneg (by linarith) hv.le
      nlinarith

theorem polarDeriv_le (l : Fin 3) {ρ : ℝ} (h0 : 0 < ρ) (h3 : ρ ≤ 3) :
    polarDeriv l ρ ≤ -(1 / 3) := by
  unfold polarDeriv
  split_ifs
  · exact le_rfl
  · have : ρ ^ 2 ≤ 9 := by nlinarith
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith

theorem polarDeriv_neg (l : Fin 3) {ρ : ℝ} (h0 : 0 < ρ) : polarDeriv l ρ < 0 := by
  unfold polarDeriv
  split_ifs
  · norm_num
  · have : 0 < 3 / ρ ^ 2 := by positivity
    linarith

theorem famC_of_le {ρ : ℝ} (h : ρ ≤ 2) : D.famC ρ = 0 := by
  simp [famC, sideBlend_of_le h]

theorem famR_of_le {ρ : ℝ} (h : ρ ≤ 2) : D.famR ρ = vRadius l (2 * ρ) := by
  simp [famR, sideBlend_of_le h]

def famC' (ρ : ℝ) : ℂ :=
  ((2 * deriv Real.smoothTransition (2 * ρ - 4) : ℝ) : ℂ) * D.C ρ + (sideBlend ρ : ℂ) * D.C' ρ

def famR' (ρ : ℝ) : ℝ :=
  -(2 * deriv Real.smoothTransition (2 * ρ - 4)) * vRadius l (2 * ρ) +
    (1 - sideBlend ρ) * polarDeriv l ρ +
    ((2 * deriv Real.smoothTransition (2 * ρ - 4)) * D.R ρ + sideBlend ρ * D.R' ρ)

theorem hasDerivAt_famC {ρ : ℝ} (h : ρ ∈ Ioo (1 : ℝ) 4) : HasDerivAt D.famC (D.famC' ρ) ρ := by
  exact (hasDerivAt_sideBlend ρ).ofReal_comp.mul (D.hasDerivC ρ h)

theorem hasDerivAt_famR {ρ : ℝ} (h : ρ ∈ Ioo (1 : ℝ) 4) : HasDerivAt D.famR (D.famR' ρ) ρ := by
  exact (((hasDerivAt_sideBlend ρ).const_sub 1).mul (hasDerivAt_vRadius_two_mul l h.1)).add
    ((hasDerivAt_sideBlend ρ).mul (D.hasDerivR ρ h))

theorem famDeriv_bound {ρ : ℝ} (h : ρ ∈ Icc (2 : ℝ) 3) :
    ‖D.famC' ρ‖ ≤ -D.famR' ρ - 1 / 200 := by
  have hχ0 : 0 ≤ sideBlend ρ := Real.smoothTransition.nonneg _
  have hχ1 : sideBlend ρ ≤ 1 := Real.smoothTransition.le_one _
  have hd := deriv_sideBlend_nonneg ρ
  set χ' := 2 * deriv Real.smoothTransition (2 * ρ - 4) with hχ'
  have hm := D.margin ρ h
  have hin := D.inside ρ h
  have hp := polarDeriv_le l (by linarith [h.1]) h.2
  have hn : ‖D.famC' ρ‖ ≤ χ' * ‖D.C ρ‖ + sideBlend ρ * ‖D.C' ρ‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hd,
      Real.norm_of_nonneg hχ0]
  have h2 : sideBlend ρ * ‖D.C' ρ‖ ≤ sideBlend ρ * (-D.R' ρ - 1 / 200) :=
    mul_le_mul_of_nonneg_left hm hχ0
  have h3 : 0 ≤ χ' * (vRadius l (2 * ρ) - D.R ρ - ‖D.C ρ‖) :=
    mul_nonneg hd (by linarith)
  have h4 : (1 - sideBlend ρ) * (1 / 200) ≤ (1 - sideBlend ρ) * (-polarDeriv l ρ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold famR'
  rw [← hχ']
  nlinarith

theorem nestedOn_fam : NestedOn D.famC D.famR (Icc 0 3) := by
  refine nestedOn_union (m := 2) ?_ ?_
  · intro ρ₁ hρ₁ ρ₂ hρ₂ hlt
    rw [D.famC_of_le hρ₁.2, D.famC_of_le hρ₂.2, D.famR_of_le hρ₁.2, D.famR_of_le hρ₂.2,
      sub_self, norm_zero, sub_pos]
    exact strictAntiOn_vRadius l (mem_Ici.mpr (by linarith [hρ₁.1]))
      (mem_Ici.mpr (by linarith [hρ₂.1])) (by linarith)
  · exact nestedOn_of_deriv (c' := D.famC') (r' := D.famR') (by norm_num)
      (fun x hx => D.hasDerivAt_famC ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => D.hasDerivAt_famR ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => D.famDeriv_bound hx)

theorem exists_deriv_lt {ρ : ℝ} (h : ρ ∈ Ioc (1 : ℝ) 3) :
    ∃ c' r', HasDerivAt D.famC c' ρ ∧ HasDerivAt D.famR r' ρ ∧ ‖c'‖ < -r' := by
  by_cases h2 : ρ < 2
  · refine ⟨0, polarDeriv l ρ, ?_, ?_, ?_⟩
    · have heq : D.famC =ᶠ[𝓝 ρ] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h2] with y hy
        exact D.famC_of_le (le_of_lt hy)
      exact (hasDerivAt_const ρ (0 : ℂ)).congr_of_eventuallyEq heq
    · have heq : D.famR =ᶠ[𝓝 ρ] fun x => vRadius l (2 * x) := by
        filter_upwards [Iio_mem_nhds h2] with y hy
        exact D.famR_of_le (le_of_lt hy)
      exact (hasDerivAt_vRadius_two_mul l h.1).congr_of_eventuallyEq heq
    · rw [norm_zero]
      linarith [polarDeriv_neg l (show 0 < ρ by linarith [h.1])]
  · push Not at h2
    refine ⟨D.famC' ρ, D.famR' ρ, D.hasDerivAt_famC ⟨by linarith, by linarith [h.2]⟩,
      D.hasDerivAt_famR ⟨by linarith, by linarith [h.2]⟩, ?_⟩
    have := D.famDeriv_bound ⟨h2, h.2⟩
    linarith

theorem contDiffOn_famC : ContDiffOn ℝ ∞ D.famC (Ioo 1 4) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_sideBlend).contDiffOn.mul D.smoothC

theorem contDiffOn_famR : ContDiffOn ℝ ∞ D.famR (Ioo 1 4) := by
  have hv : ContDiffOn ℝ ∞ (fun x => vRadius l (2 * x)) (Ioo 1 4) := fun x hx =>
    ((contDiffAt_vRadius l (show 0 < 2 * x by linarith [hx.1])).comp x
      (contDiffAt_const.mul contDiffAt_id)).contDiffWithinAt
  exact ((contDiff_const.sub contDiff_sideBlend).contDiffOn.mul hv).add
    (contDiff_sideBlend.contDiffOn.mul D.smoothR)

theorem contDiffOn_famA : ContDiffOn ℝ ∞ D.famA (Ioo 1 4) :=
  contDiff_sideBlend.contDiffOn.mul D.smootha

theorem contMDiff_famMu : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ D.famMu :=
  contMDiff_circleExp.comp (contDiff_const.mul (contDiff_sideBlend.mul contDiff_const)).contMDiff

theorem continuousOn_famC : ContinuousOn D.famC (Icc 0 3) := by
  intro x hx
  by_cases h2 : x < 2
  · have heq : D.famC =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h2] with y hy
      exact D.famC_of_le (le_of_lt hy)
    exact (continuousAt_const.congr heq.symm).continuousWithinAt
  · push Not at h2
    exact (D.contDiffOn_famC.continuousOn.continuousAt
      (Ioo_mem_nhds (by linarith) (by linarith [hx.2]))).continuousWithinAt

theorem continuousOn_famR : ContinuousOn D.famR (Icc 0 3) := by
  intro x hx
  by_cases h2 : x < 2
  · have heq : D.famR =ᶠ[𝓝 x] fun x => vRadius l (2 * x) := by
      filter_upwards [Iio_mem_nhds h2] with y hy
      exact D.famR_of_le (le_of_lt hy)
    have hc : ContinuousWithinAt (fun x => vRadius l (2 * x)) (Icc 0 3) x :=
      (continuousOn_vRadius l).comp (continuous_const.mul continuous_id).continuousOn
        (fun y hy => mem_Ici.mpr (show 0 ≤ 2 * y by linarith [hy.1])) x hx
    exact hc.congr_of_eventuallyEq (eventually_nhdsWithin_of_eventually_nhds heq)
      (heq.eq_of_nhds)
  · push Not at h2
    exact (D.contDiffOn_famR.continuousOn.continuousAt
      (Ioo_mem_nhds (by linarith) (by linarith [hx.2]))).continuousWithinAt

theorem point_injOn : InjOn D.point (univ ×ˢ Icc 0 3) :=
  nestedPoint_injOn D.nestedOn_fam (fun _ hρ => D.famR_pos hρ) (fun _ hρ => D.famA_lt' hρ)

theorem isLocalDiffeomorphAt_point {u : Circle} {ρ : ℝ} (h : ρ ∈ Ioc (1 : ℝ) 3) (h3 : ρ < 3) :
    IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ D.point (u, ρ) := by
  obtain ⟨c', r', hc', hr', hd⟩ := D.exists_deriv_lt h
  exact isLocalDiffeomorphAt_nestedPoint isOpen_Ioo D.contDiffOn_famC D.contDiffOn_famR
    D.contMDiff_famMu.contMDiffOn D.contDiffOn_famA (fun _ hρ => D.famA_lt hρ)
    ⟨h.1, by linarith⟩ hc' hr' (D.famR_pos ⟨by linarith [h.1], h.2⟩) hd

end CollarData

section Data

def collarDepth (ρ : ℝ) : ℝ := 2 * (3 - ρ) / 3

theorem hasDerivAt_mobC (A k b : ℝ) {ρ : ℝ} (h : A ^ 2 - (b + k * ρ) ^ 2 ≠ 0) :
    HasDerivAt (fun x => A / (A ^ 2 - (b + k * x) ^ 2))
      (2 * A * (b + k * ρ) * k / (A ^ 2 - (b + k * ρ) ^ 2) ^ 2) ρ := by
  have hg : HasDerivAt (fun x => A ^ 2 - (b + k * x) ^ 2) (-(2 * (b + k * ρ) * k)) ρ := by
    have h1 := (((hasDerivAt_id ρ).const_mul k).const_add b).pow 2
    have h2 := h1.const_sub (A ^ 2)
    exact h2.congr_deriv (by simp only [id]; push_cast; ring)
  have h3 := (hasDerivAt_const ρ A).div hg h
  convert h3 using 1
  ring

theorem hasDerivAt_mobR (A k b σ : ℝ) {ρ : ℝ} (h : σ * ((b + k * ρ) ^ 2 - A ^ 2) ≠ 0) :
    HasDerivAt (fun x => (b + k * x) / (σ * ((b + k * x) ^ 2 - A ^ 2)))
      ((k * (σ * ((b + k * ρ) ^ 2 - A ^ 2)) - (b + k * ρ) * (σ * (2 * (b + k * ρ) * k))) /
        (σ * ((b + k * ρ) ^ 2 - A ^ 2)) ^ 2) ρ := by
  have hn : HasDerivAt (fun x => b + k * x) k ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul k).const_add b
  have hd : HasDerivAt (fun x => σ * ((b + k * x) ^ 2 - A ^ 2)) (σ * (2 * (b + k * ρ) * k)) ρ := by
    have h1 := ((hn.pow 2).sub_const (A ^ 2)).const_mul σ
    exact h1.congr_deriv (by push_cast; ring)
  exact hn.div hd h

theorem outer_margin_aux (A x : ℝ) (hA : |A| = 3 / 2) (hx1 : 17 / 6 ≤ x) (hx2 : x ≤ 3) :
    |2 * A * x * (1 / 6) / (A ^ 2 - x ^ 2) ^ 2| ≤
      -(((1 / 6) * (1 * (x ^ 2 - A ^ 2)) - x * (1 * (2 * x * (1 / 6)))) /
        (1 * (x ^ 2 - A ^ 2)) ^ 2) - 1 / 200 := by
  have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
  rw [hA2]
  have hD : 0 < x ^ 2 - 9 / 4 := by nlinarith
  have hD2 : 0 < (9 / 4 - x ^ 2) ^ 2 := by nlinarith
  have habs : |2 * A * x * (1 / 6) / (9 / 4 - x ^ 2) ^ 2| = x / (2 * (x ^ 2 - 9 / 4) ^ 2) := by
    rw [abs_div, abs_of_pos hD2, abs_mul, abs_mul, abs_mul, hA,
      abs_of_pos (by linarith : (0 : ℝ) < x)]
    rw [show (9 / 4 - x ^ 2) ^ 2 = (x ^ 2 - 9 / 4) ^ 2 by ring]
    norm_num
    field_simp
    ring
  rw [habs]
  set D := x ^ 2 - 9 / 4 with hDdef
  have h9 : D ≠ 0 := hD.ne'
  have key : -((1 / 6 * (1 * D) - x * (1 * (2 * x * (1 / 6)))) / (1 * D) ^ 2) - 1 / 200 -
      x / (2 * D ^ 2) = (x - 3 / 2) ^ 2 * (200 - 6 * (x + 3 / 2) ^ 2) / (1200 * D ^ 2) := by
    field_simp
    rw [hDdef]
    ring
  have hnum : 0 ≤ (x - 3 / 2) ^ 2 * (200 - 6 * (x + 3 / 2) ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ 1200 * D ^ 2)
  linarith

theorem inner_margin_aux (A x : ℝ) (hA : |A| = 3) (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 2 / 3) :
    |2 * A * x * (-1 / 6) / (A ^ 2 - x ^ 2) ^ 2| ≤
      -(((-1 / 6) * (-1 * (x ^ 2 - A ^ 2)) - x * (-1 * (2 * x * (-1 / 6)))) /
        (-1 * (x ^ 2 - A ^ 2)) ^ 2) - 1 / 200 := by
  have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
  rw [hA2]
  have hD : 0 < 9 - x ^ 2 := by nlinarith
  have hD2 : 0 < (9 - x ^ 2) ^ 2 := by positivity
  have habs : |2 * A * x * (-1 / 6) / (9 - x ^ 2) ^ 2| = x / (9 - x ^ 2) ^ 2 := by
    rw [abs_div, abs_of_pos hD2, abs_mul, abs_mul, abs_mul, hA,
      abs_of_pos (by linarith : (0 : ℝ) < x)]
    norm_num
    field_simp
  rw [habs]
  have key : -((-1 / 6 * (-1 * (x ^ 2 - 9)) - x * (-1 * (2 * x * (-1 / 6)))) /
      (-1 * (x ^ 2 - 9)) ^ 2) - 1 / 200 - x / (9 - x ^ 2) ^ 2 =
      (3 - x) ^ 2 * (200 - 6 * (3 + x) ^ 2) / (1200 * (9 - x ^ 2) ^ 2) := by
    have h9 : x ^ 2 - 9 ≠ 0 := by linarith
    field_simp
    ring
  have hnum : 0 ≤ (3 - x) ^ 2 * (200 - 6 * (3 + x) ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ 1200 * (9 - x ^ 2) ^ 2)
  linarith

theorem outer_inside_aux (A ρ : ℝ) (hA : |A| = 3 / 2) (h2 : 2 ≤ ρ) (h3 : ρ ≤ 3) :
    |A / (A ^ 2 - (5 / 2 + 1 / 6 * ρ) ^ 2)| +
      (5 / 2 + 1 / 6 * ρ) / (1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2)) ≤ 6 / (2 * ρ) := by
  have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
  rw [hA2, abs_div, hA]
  have hD : 0 < (5 / 2 + 1 / 6 * ρ) ^ 2 - 9 / 4 := by nlinarith
  rw [abs_of_neg (by linarith : 9 / 4 - (5 / 2 + 1 / 6 * ρ) ^ 2 < 0), one_mul, neg_sub]
  rw [← add_div, div_le_div_iff₀ hD (by linarith)]
  nlinarith

theorem inner_inside_aux (A ρ : ℝ) (hA : |A| = 3) (h2 : 2 ≤ ρ) (h3 : ρ ≤ 3) :
    |A / (A ^ 2 - (1 + (-1 / 6) * ρ) ^ 2)| +
      (1 + (-1 / 6) * ρ) / (-1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2)) ≤ 6 / (2 * ρ) := by
  have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
  rw [hA2, abs_div, hA]
  have hD : 0 < 9 - (1 + (-1 / 6) * ρ) ^ 2 := by nlinarith
  rw [abs_of_pos hD, show -1 * ((1 + (-1 / 6) * ρ) ^ 2 - 9) = 9 - (1 + (-1 / 6) * ρ) ^ 2 by ring]
  rw [← add_div, div_le_div_iff₀ hD (by linarith)]
  nlinarith

def zeroData (l : Fin 3) (hl : l.val = 0) (c : ℝ) (hc : |c| = 3 / 2) : CollarData l where
  C _ := (c : ℂ)
  R ρ := 1 + (-1 / 6) * ρ
  a _ := 0
  turn := 0
  C' _ := 0
  R' _ := -1 / 6
  smoothC := contDiffOn_const
  smoothR := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  smootha := contDiffOn_const
  hasDerivC ρ _ := hasDerivAt_const ρ _
  hasDerivR ρ _ := by
    simpa using ((hasDerivAt_id ρ).const_mul (-1 / 6 : ℝ)).const_add 1
  margin ρ _ := by norm_num
  inside ρ hρ := by
    rw [vRadius_zero_eq l hl, Complex.norm_real, Real.norm_eq_abs, hc]
    linarith [hρ.2]
  R_pos ρ hρ := by linarith [hρ.2]
  a_lt ρ _ := by norm_num

def outerData (l : Fin 3) (hl : l.val ≠ 0) (A : ℝ) (hA : |A| = 3 / 2) : CollarData l where
  C ρ := ((A / (A ^ 2 - (5 / 2 + 1 / 6 * ρ) ^ 2) : ℝ) : ℂ)
  R ρ := (5 / 2 + 1 / 6 * ρ) / (1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2))
  a ρ := A / (5 / 2 + 1 / 6 * ρ)
  turn := 0
  C' ρ := ((2 * A * (5 / 2 + 1 / 6 * ρ) * (1 / 6) / (A ^ 2 - (5 / 2 + 1 / 6 * ρ) ^ 2) ^ 2 : ℝ) : ℂ)
  R' ρ := ((1 / 6) * (1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2)) -
      (5 / 2 + 1 / 6 * ρ) * (1 * (2 * (5 / 2 + 1 / 6 * ρ) * (1 / 6)))) /
        (1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2)) ^ 2
  smoothC := by
    have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
    intro ρ hρ
    have hD : A ^ 2 - (5 / 2 + 1 / 6 * ρ) ^ 2 ≠ 0 := by
      rw [hA2]; nlinarith [hρ.1]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ρ (contDiffAt_const.div
      (contDiffAt_const.sub ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).pow 2))
      hD)).contDiffWithinAt
  smoothR := by
    have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
    intro ρ hρ
    have hD : 1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2) ≠ 0 := by
      rw [hA2]; nlinarith [hρ.1]
    have hf : ContDiff ℝ ∞ (fun x : ℝ => 5 / 2 + 1 / 6 * x) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ ∞ (fun x : ℝ => 1 * ((5 / 2 + 1 / 6 * x) ^ 2 - A ^ 2)) :=
      contDiff_const.mul ((hf.pow 2).sub contDiff_const)
    exact (hf.contDiffAt.div hg.contDiffAt hD).contDiffWithinAt
  smootha := by
    intro ρ hρ
    have hD : (5 / 2 + 1 / 6 * ρ) ≠ 0 := by nlinarith [hρ.1]
    exact (contDiffAt_const.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
      hD).contDiffWithinAt
  hasDerivC ρ hρ := by
    have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
    have hD : A ^ 2 - (5 / 2 + 1 / 6 * ρ) ^ 2 ≠ 0 := by rw [hA2]; nlinarith [hρ.1]
    exact (hasDerivAt_mobC A (1 / 6) (5 / 2) hD).ofReal_comp
  hasDerivR ρ hρ := by
    have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
    have hD : 1 * ((5 / 2 + 1 / 6 * ρ) ^ 2 - A ^ 2) ≠ 0 := by rw [hA2]; nlinarith [hρ.1]
    exact hasDerivAt_mobR A (1 / 6) (5 / 2) 1 hD
  margin ρ hρ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact outer_margin_aux A _ hA (by linarith [hρ.1]) (by linarith [hρ.2])
  inside ρ hρ := by
    rw [vRadius_eq_six_div hl (by linarith [hρ.1]), Complex.norm_real, Real.norm_eq_abs]
    exact outer_inside_aux A ρ hA hρ.1 hρ.2
  R_pos ρ hρ := by
    have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
    rw [hA2, one_mul]
    apply div_pos (by linarith [hρ.1]) (by nlinarith [hρ.1])
  a_lt ρ hρ := by
    rw [abs_div, hA, abs_of_pos (by linarith [hρ.1] : (0 : ℝ) < 5 / 2 + 1 / 6 * ρ),
      div_lt_one (by linarith [hρ.1])]
    linarith [hρ.1]

def innerData (l : Fin 3) (hl : l.val ≠ 0) (A : ℝ) (hA : |A| = 3) : CollarData l where
  C ρ := ((A / (A ^ 2 - (1 + (-1 / 6) * ρ) ^ 2) : ℝ) : ℂ)
  R ρ := (1 + (-1 / 6) * ρ) / (-1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2))
  a ρ := (1 + (-1 / 6) * ρ) / A
  turn := 1
  C' ρ := ((2 * A * (1 + (-1 / 6) * ρ) * (-1 / 6) / (A ^ 2 - (1 + (-1 / 6) * ρ) ^ 2) ^ 2 : ℝ) : ℂ)
  R' ρ := ((-1 / 6) * (-1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2)) -
      (1 + (-1 / 6) * ρ) * (-1 * (2 * (1 + (-1 / 6) * ρ) * (-1 / 6)))) /
        (-1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2)) ^ 2
  smoothC := by
    have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
    intro ρ hρ
    have hD : A ^ 2 - (1 + (-1 / 6) * ρ) ^ 2 ≠ 0 := by
      rw [hA2]; nlinarith [hρ.1, hρ.2]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ρ (contDiffAt_const.div
      (contDiffAt_const.sub ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).pow 2))
      hD)).contDiffWithinAt
  smoothR := by
    have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
    intro ρ hρ
    have hD : -1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2) ≠ 0 := by
      rw [hA2]; nlinarith [hρ.1, hρ.2]
    have hf : ContDiff ℝ ∞ (fun x : ℝ => 1 + (-1 / 6) * x) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ ∞ (fun x : ℝ => -1 * ((1 + (-1 / 6) * x) ^ 2 - A ^ 2)) :=
      contDiff_const.mul ((hf.pow 2).sub contDiff_const)
    exact (hf.contDiffAt.div hg.contDiffAt hD).contDiffWithinAt
  smootha := by
    have hA0 : A ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; norm_num at hA
    exact ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const A).contDiffOn
  hasDerivC ρ hρ := by
    have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
    have hD : A ^ 2 - (1 + (-1 / 6) * ρ) ^ 2 ≠ 0 := by rw [hA2]; nlinarith [hρ.1, hρ.2]
    exact (hasDerivAt_mobC A (-1 / 6) 1 hD).ofReal_comp
  hasDerivR ρ hρ := by
    have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
    have hD : -1 * ((1 + (-1 / 6) * ρ) ^ 2 - A ^ 2) ≠ 0 := by rw [hA2]; nlinarith [hρ.1, hρ.2]
    exact hasDerivAt_mobR A (-1 / 6) 1 (-1) hD
  margin ρ hρ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact inner_margin_aux A _ hA (by linarith [hρ.2]) (by linarith [hρ.1])
  inside ρ hρ := by
    rw [vRadius_eq_six_div hl (by linarith [hρ.1]), Complex.norm_real, Real.norm_eq_abs]
    exact inner_inside_aux A ρ hA hρ.1 hρ.2
  R_pos ρ hρ := by
    have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
    rw [hA2]
    apply div_pos (by linarith [hρ.2]) (by nlinarith [hρ.1, hρ.2])
  a_lt ρ hρ := by
    rw [abs_div, hA, abs_of_pos (by linarith [hρ.2] : (0 : ℝ) < 1 + (-1 / 6) * ρ),
      div_lt_one (by norm_num)]
    linarith [hρ.1]

theorem mobius_outer (A x u : ℂ) (hu : u ≠ 0) (hx : x ≠ 0) (hD : x ^ 2 - A ^ 2 ≠ 0)
    (h1 : A * u + x ≠ 0) :
    (A / (A ^ 2 - x ^ 2) + x / (x ^ 2 - A ^ 2) * ((u + A / x) / (1 + A / x * u))) *
      (A + x * u⁻¹) = 1 := by
  have hD' : A ^ 2 - x ^ 2 ≠ 0 := fun h0 => hD (by linear_combination -h0)
  have e1 : (u + A / x) / (1 + A / x * u) = (x * u + A) / (A * u + x) := by
    have h1' : 1 + A / x * u ≠ 0 := by
      intro h0; apply h1
      have : A * u + x = x * (1 + A / x * u) := by field_simp; ring
      rw [this, h0, mul_zero]
    rw [div_eq_div_iff h1' h1]
    field_simp
    ring
  rw [e1]
  have e2 : A / (A ^ 2 - x ^ 2) + x / (x ^ 2 - A ^ 2) * ((x * u + A) / (A * u + x)) =
      u / (A * u + x) := by
    field_simp
    ring
  rw [e2]
  field_simp
  exact div_self (by rw [mul_comm]; exact h1)

theorem mobius_inner (A x u : ℂ) (hA : A ≠ 0) (hD : A ^ 2 - x ^ 2 ≠ 0) (h2 : A + x * u ≠ 0) :
    (A / (A ^ 2 - x ^ 2) + x / (-1 * (x ^ 2 - A ^ 2)) * (-1 * ((u + x / A) / (1 + x / A * u)))) *
      (A + x * u) = 1 := by
  have e1 : (u + x / A) / (1 + x / A * u) = (A * u + x) / (A + x * u) := by
    have h1' : 1 + x / A * u ≠ 0 := by
      intro h0; apply h2
      have : A + x * u = A * (1 + x / A * u) := by field_simp
      rw [this, h0, mul_zero]
    rw [div_eq_div_iff h1' h2]
    field_simp
  rw [e1]
  have hD2 : -1 * (x ^ 2 - A ^ 2) = A ^ 2 - x ^ 2 := by ring
  rw [hD2]
  field_simp
  ring

theorem coe_exp_pi_mul_one : ((Circle.exp (Real.pi * 1) : Circle) : ℂ) = -1 := by
  rw [Circle.coe_exp, mul_one]
  exact Complex.exp_pi_mul_I

theorem coe_exp_pi_mul_zero : ((Circle.exp (Real.pi * 0) : Circle) : ℂ) = 1 := by
  rw [mul_zero, Circle.exp_zero, Circle.coe_one]

theorem point_zeroData {l : Fin 3} (hl : l.val = 0) (c : ℝ) (hc : |c| = 3 / 2) {u : Circle}
    {ρ : ℝ} (h : 5 / 2 ≤ ρ) :
    (zeroData l hl c hc).point (u, ρ) = c + ((1 + (-1 / 6) * ρ : ℝ) : ℂ) * (u : ℂ) := by
  rw [CollarData.point_of_ge _ h]
  simp only [zeroData, Circle.coe_mul, coe_exp_pi_mul_zero, one_mul, blaschke_zero]

theorem point_outerData {l : Fin 3} (hl : l.val ≠ 0) (A : ℝ) (hA : |A| = 3 / 2) {u : Circle}
    {ρ : ℝ} (h : 5 / 2 ≤ ρ) (h4 : ρ < 4) :
    (outerData l hl A hA).point (u, ρ) =
      ((A : ℂ) + ((5 / 2 + 1 / 6 * ρ : ℝ) : ℂ) * (u : ℂ)⁻¹)⁻¹ := by
  have hA2 : A ^ 2 = 9 / 4 := by rw [← sq_abs, hA]; norm_num
  rw [CollarData.point_of_ge _ h]
  have ha : |A / (5 / 2 + 1 / 6 * ρ)| < 1 := (outerData l hl A hA).a_lt ρ ⟨by linarith, h4⟩
  simp only [outerData, Circle.coe_mul, coe_exp_pi_mul_zero, one_mul]
  rw [coe_blaschke ha, blaschkeVal]
  set x : ℝ := 5 / 2 + 1 / 6 * ρ with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hD : x ^ 2 - A ^ 2 ≠ 0 := by rw [hA2]; nlinarith
  have hD' : A ^ 2 - x ^ 2 ≠ 0 := fun h0 => hD (by linarith)
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  have h1 : (1 : ℂ) + ((A / x : ℝ) : ℂ) * u ≠ 0 := one_add_mul_ne_zero ha u
  have h2 : (A : ℂ) + (x : ℂ) * (u : ℂ)⁻¹ ≠ 0 := by
    intro h0
    have hn : ‖(x : ℂ) * (u : ℂ)⁻¹‖ = ‖(A : ℂ)‖ := by
      rw [show (x : ℂ) * (u : ℂ)⁻¹ = -(A : ℂ) by linear_combination h0, norm_neg]
    rw [norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx0.le, Real.norm_eq_abs, hA] at hn
    rw [hx] at hn
    linarith
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hDc : ((x : ℂ) ^ 2 - (A : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD
  have hDc' : ((A : ℂ) ^ 2 - (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD'
  have h1' : (A : ℂ) * u + x ≠ 0 := by
    have e : (A : ℂ) * u + x = x * (1 + ((A / x : ℝ) : ℂ) * u) := by
      push_cast
      field_simp
      ring
    rw [e]
    exact mul_ne_zero hxc h1
  apply eq_inv_of_mul_eq_one_left
  push_cast
  linear_combination mobius_outer (A : ℂ) (x : ℂ) (u : ℂ) hu hxc hDc h1'

theorem point_innerData {l : Fin 3} (hl : l.val ≠ 0) (A : ℝ) (hA : |A| = 3) {u : Circle}
    {ρ : ℝ} (h : 5 / 2 ≤ ρ) (h4 : ρ < 4) :
    (innerData l hl A hA).point (u, ρ) = ((A : ℂ) + ((1 + (-1 / 6) * ρ : ℝ) : ℂ) * (u : ℂ))⁻¹ := by
  have hA2 : A ^ 2 = 9 := by rw [← sq_abs, hA]; norm_num
  rw [CollarData.point_of_ge _ h]
  have ha : |(1 + (-1 / 6) * ρ) / A| < 1 := (innerData l hl A hA).a_lt ρ ⟨by linarith, h4⟩
  simp only [innerData, Circle.coe_mul, coe_exp_pi_mul_one]
  rw [coe_blaschke ha, blaschkeVal]
  set x : ℝ := 1 + (-1 / 6) * ρ with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hA0 : A ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; norm_num at hA
  have hD : A ^ 2 - x ^ 2 ≠ 0 := by rw [hA2]; nlinarith
  have h1 : (1 : ℂ) + ((x / A : ℝ) : ℂ) * u ≠ 0 := one_add_mul_ne_zero ha u
  have h2 : (A : ℂ) + (x : ℂ) * u ≠ 0 := by
    intro h0
    have hn : ‖(x : ℂ) * (u : ℂ)‖ = ‖(A : ℂ)‖ := by
      rw [show (x : ℂ) * (u : ℂ) = -(A : ℂ) by linear_combination h0, norm_neg]
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, Real.norm_eq_abs, hA] at hn
    rw [hx] at hn
    linarith
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA0
  have hDc : ((A : ℂ) ^ 2 - (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD
  have hDc' : (-1 * ((x : ℂ) ^ 2 - (A : ℂ) ^ 2)) ≠ 0 := by
    intro h0; apply hDc; linear_combination h0
  apply eq_inv_of_mul_eq_one_left
  push_cast
  linear_combination mobius_inner (A : ℂ) (x : ℂ) (u : ℂ) hAc hDc h2

theorem planarCollarFormula_inner {p : Fin 3} (hp : p.val ≠ 0) (u : Circle) (d : ℝ) :
    planarCollarFormula 3 p (((u⁻¹ : Circle) : ℂ), d) =
      (planarCenter 3 p : ℂ) + ((1 / 2 + d / 4 : ℝ) : ℂ) * (u : ℂ) := by
  simp only [planarCollarFormula, planarRadius, planarSign, planarTwist, hp, ↓reduceIte,
    Circle.coe_inv_eq_conj, Complex.conj_conj, Complex.real_smul]
  push_cast
  ring

theorem planarCollarFormula_outer {p : Fin 3} (hp : p.val = 0) (u : Circle) (d : ℝ) :
    planarCollarFormula 3 p (((u⁻¹ : Circle) : ℂ), d) = ((3 - d / 4 : ℝ) : ℂ) * (u : ℂ)⁻¹ := by
  simp only [planarCollarFormula, planarRadius, planarSign, planarTwist, hp, ↓reduceIte,
    planarCenter_zero hp, Circle.coe_inv, Complex.real_smul]
  push_cast
  ring

theorem abs_planarCenter_sidePort_zero {l : Fin 3} (hl : l.val = 0) (t : Bool) :
    |planarCenter 3 (sidePort l t)| = 3 / 2 := by
  fin_cases l <;> cases t <;> simp_all [sidePort, planarCenter]
  all_goals norm_num

theorem abs_sidePort_outer {l : Fin 3} (hl : l.val ≠ 0) {t : Bool} (hp : (sidePort l t).val = 0) :
    |planarCenter 3 (sidePort l t) - planarCenter 3 l| = 3 / 2 := by
  fin_cases l <;> cases t <;> simp_all [sidePort, planarCenter]
  all_goals norm_num

theorem abs_sidePort_inner {l : Fin 3} (hl : l.val ≠ 0) {t : Bool} (hp : (sidePort l t).val ≠ 0) :
    |planarCenter 3 (sidePort l t) - planarCenter 3 l| = 3 := by
  fin_cases l <;> cases t <;> simp_all [sidePort, planarCenter]
  all_goals norm_num

def sideData (l : Fin 3) (t : Bool) : CollarData l :=
  if hl : l.val = 0 then
    zeroData l hl (planarCenter 3 (sidePort l t)) (abs_planarCenter_sidePort_zero hl t)
  else if hp : (sidePort l t).val = 0 then
    outerData l hl (planarCenter 3 (sidePort l t) - planarCenter 3 l) (abs_sidePort_outer hl hp)
  else
    innerData l hl (planarCenter 3 (sidePort l t) - planarCenter 3 l) (abs_sidePort_inner hl hp)

theorem sideData_point_collar (l : Fin 3) (t : Bool) {u : Circle} {ρ : ℝ} (h : 5 / 2 ≤ ρ)
    (h4 : ρ < 4) : (sideData l t).point (u, ρ) =
      hostInv l (planarCollarFormula 3 (sidePort l t) (((u⁻¹ : Circle) : ℂ), collarDepth ρ)) := by
  unfold sideData
  split_ifs with hl hp
  · rw [point_zeroData hl _ _ h, hostInv_of_zero hl,
      planarCollarFormula_inner (by fin_cases l <;> cases t <;> simp_all [sidePort])]
    simp only [collarDepth]
    push_cast
    ring
  · rw [point_outerData hl _ _ h h4, hostInv_of_ne hl, planarCollarFormula_outer hp,
      planarCenter_zero hp]
    congr 1
    simp only [collarDepth]
    push_cast
    ring
  · rw [point_innerData hl _ _ h h4, hostInv_of_ne hl, planarCollarFormula_inner hp]
    congr 1
    simp only [collarDepth]
    push_cast
    ring

end Data

end GC.Seifert.SplitTube
