import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Local-to-global convexity on intervals of `ℝ`

* `convexOn_Icc_union`: a function convex on `[a, c]` and on `[b, d]` with `b < c` (overlap with
  nonempty interior) is convex on `[a, d]`.
* `convexOn_of_locally`: a function convex near every point of a convex set `J ⊆ ℝ` (on `J`
  intersected with a small closed interval) is convex on `J`.

No continuity is assumed. Route: adjacent slopes (`convexOn_of_slope_mono_adjacent`) for the
gluing; a Lebesgue number on `[x, z]` and induction over steps of half its length for the
globalization.
-/

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Analysis.Convex

/-- Slopes along `x < p < y`: if the left slope is at most the right slope, the total slope lies
between them. -/
theorem slope_le_slope_and_slope_le_of_adjacent {f : ℝ → ℝ} {x p y : ℝ} (hxp : x < p)
    (hpy : p < y) (h : (f p - f x) / (p - x) ≤ (f y - f p) / (y - p)) :
    (f p - f x) / (p - x) ≤ (f y - f x) / (y - x) ∧
      (f y - f x) / (y - x) ≤ (f y - f p) / (y - p) := by
  have h1 : 0 < p - x := sub_pos.mpr hxp
  have h2 : 0 < y - p := sub_pos.mpr hpy
  have h3 : 0 < y - x := sub_pos.mpr (hxp.trans hpy)
  rw [div_le_div_iff₀ h1 h2] at h
  constructor
  · rw [div_le_div_iff₀ h1 h3]
    linarith
  · rw [div_le_div_iff₀ h3 h2]
    linarith

/-- **Gluing.** Convex on `[a, c]` and on `[b, d]` with `b < c` implies convex on `[a, d]`. -/
theorem convexOn_Icc_union {f : ℝ → ℝ} {a b c d : ℝ} (hbc : b < c)
    (h₁ : ConvexOn ℝ (Icc a c) f) (h₂ : ConvexOn ℝ (Icc b d) f) : ConvexOn ℝ (Icc a d) f := by
  refine convexOn_of_slope_mono_adjacent (convex_Icc a d) ?_
  intro x y z hx hz hxy hyz
  by_cases hzc : z ≤ c
  · exact h₁.slope_mono_adjacent ⟨hx.1, (hxy.trans hyz).le.trans hzc⟩
      ⟨hx.1.trans (hxy.trans hyz).le, hzc⟩ hxy hyz
  by_cases hbx : b ≤ x
  · exact h₂.slope_mono_adjacent ⟨hbx, (hxy.trans hyz).le.trans hz.2⟩
      ⟨hbx.trans (hxy.trans hyz).le, hz.2⟩ hxy hyz
  push Not at hzc hbx
  -- `x < b < p < q < c < z`
  set p : ℝ := (2 * b + c) / 3 with hp
  set q : ℝ := (b + 2 * c) / 3 with hq
  have hbp : b < p := by rw [hp]; linarith
  have hpq : p < q := by rw [hp, hq]; linarith
  have hqc : q < c := by rw [hq]; linarith
  have hab : a ≤ b := hx.1.trans hbx.le
  have hcd : c ≤ d := hzc.le.trans hz.2
  have hpI₁ : p ∈ Icc a c := ⟨hab.trans hbp.le, (hpq.trans hqc).le⟩
  have hqI₁ : q ∈ Icc a c := ⟨hab.trans (hbp.trans hpq).le, hqc.le⟩
  have hpI₂ : p ∈ Icc b d := ⟨hbp.le, (hpq.trans hqc).le.trans hcd⟩
  have hqI₂ : q ∈ Icc b d := ⟨(hbp.trans hpq).le, hqc.le.trans hcd⟩
  have hzI₂ : z ∈ Icc b d := ⟨(hbp.trans (hpq.trans (hqc.trans hzc))).le, hz.2⟩
  have hxI₁ : x ∈ Icc a c := ⟨hx.1, (hbx.trans (hbp.trans (hpq.trans hqc))).le⟩
  rcases lt_or_ge y q with hyq | hqy
  · -- `s(x,y) ≤ s(y,q) ≤ s(y,z)`
    have hA := h₁.slope_mono_adjacent hxI₁ hqI₁ hxy hyq
    have hqz : q < z := hqc.trans hzc
    have hB : (f q - f y) / (q - y) ≤ (f z - f q) / (z - q) := by
      by_cases hby : b ≤ y
      · exact h₂.slope_mono_adjacent ⟨hby, hyq.le.trans hqI₂.2⟩ hzI₂ hyq hqz
      · push Not at hby
        have hyp : y < p := hby.trans hbp
        have hyI₁ : y ∈ Icc a c := ⟨hx.1.trans hxy.le, (hyp.trans (hpq.trans hqc)).le⟩
        have h1 := (slope_le_slope_and_slope_le_of_adjacent hyp hpq
          (h₁.slope_mono_adjacent hyI₁ hqI₁ hyp hpq)).2
        have h2 := h₂.slope_mono_adjacent hpI₂ hzI₂ hpq hqz
        exact h1.trans h2
    exact hA.trans (slope_le_slope_and_slope_le_of_adjacent hyq hqz hB).1
  · -- `s(x,y) ≤ s(p,y) ≤ s(y,z)`
    have hpy : p < y := hpq.trans_le hqy
    have hxp : x < p := hbx.trans hbp
    have hA := h₂.slope_mono_adjacent hpI₂ hzI₂ hpy hyz
    have hB : (f p - f x) / (p - x) ≤ (f y - f p) / (y - p) := by
      by_cases hyc : y ≤ c
      · exact h₁.slope_mono_adjacent hxI₁ ⟨hx.1.trans hxy.le, hyc⟩ hxp hpy
      · push Not at hyc
        have hqy' : q < y := hqc.trans hyc
        have hyI₂ : y ∈ Icc b d := ⟨(hbp.trans hpy).le, hyz.le.trans hz.2⟩
        have h1 := h₁.slope_mono_adjacent hxI₁ hqI₁ hxp hpq
        have h2 := (slope_le_slope_and_slope_le_of_adjacent hpq hqy'
          (h₂.slope_mono_adjacent hpI₂ hyI₂ hpq hqy')).1
        exact h1.trans h2
    exact (slope_le_slope_and_slope_le_of_adjacent hxp hpy hB).2.trans hA

/-- Convex near every point of `[x, z]` (on windows of a uniform length) implies convex on
`[x, z]`. -/
theorem convexOn_Icc_of_forall_window {f : ℝ → ℝ} {x z η : ℝ} (hη : 0 < η)
    (hwin : ∀ u ∈ Icc x z, ConvexOn ℝ (Icc u (min z (u + η))) f) :
    ConvexOn ℝ (Icc x z) f := by
  rcases lt_or_ge z x with hzx | hxz
  · rw [Icc_eq_empty (not_le.mpr hzx)]
    exact ⟨convex_empty, fun _ hx => hx.elim⟩
  set h : ℝ := η / 2 with hh
  have hh0 : 0 < h := by positivity
  have key : ∀ k : ℕ, ConvexOn ℝ (Icc x (min z (x + (k + 1) * h))) f := by
    intro k
    induction k with
    | zero =>
      refine (hwin x ⟨le_rfl, hxz⟩).subset (Icc_subset_Icc le_rfl ?_) (convex_Icc _ _)
      refine min_le_min le_rfl ?_
      simp only [Nat.cast_zero, zero_add, one_mul]
      linarith
    | succ k ih =>
      rcases le_or_gt z (x + (k + 1) * h) with hzv | hvz
      · have e1 : min z (x + (k + 1) * h) = z := min_eq_left hzv
        have e2 : min z (x + ((k + 1 : ℕ) + 1) * h) = z := by
          refine min_eq_left (hzv.trans ?_)
          push_cast
          nlinarith
        rw [e2]
        rwa [e1] at ih
      · set u : ℝ := x + k * h with hu
        have hxu : x ≤ u := by rw [hu]; have : (0 : ℝ) ≤ k * h := by positivity
                               linarith
        have huz : u ≤ z := by rw [hu]; nlinarith
        have hw := hwin u ⟨hxu, huz⟩
        have e : u + η = x + ((k + 1 : ℕ) + 1) * h := by rw [hu, hh]; push_cast; ring
        rw [e] at hw
        have hlt : u < min z (x + (k + 1) * h) := by
          rw [min_eq_right hvz.le, hu]
          nlinarith
        exact convexOn_Icc_union hlt ih hw
  obtain ⟨k, hk⟩ := exists_nat_gt ((z - x) / h)
  have hzk : z ≤ x + (k + 1) * h := by
    rw [div_lt_iff₀ hh0] at hk
    nlinarith
  have hk' := key k
  rwa [min_eq_left hzk] at hk'

/-- **Local-to-global convexity.** If `f` is convex on `J ∩ [t - ε, t + ε]` for some `ε > 0`
around every point `t` of a convex set `J ⊆ ℝ`, then `f` is convex on `J`. -/
theorem convexOn_of_locally {J : Set ℝ} (hJ : Convex ℝ J) {f : ℝ → ℝ}
    (hloc : ∀ t ∈ J, ∃ ε > 0, ConvexOn ℝ (J ∩ Icc (t - ε) (t + ε)) f) : ConvexOn ℝ J f := by
  choose ε hε hconv using hloc
  have hseg : ∀ x ∈ J, ∀ z ∈ J, ConvexOn ℝ (Icc x z) f := by
    intro x hx z hz
    have hsub : Icc x z ⊆ J := hJ.ordConnected.out hx hz
    obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := x) (b := z))
      (c := fun i : J => ball (i : ℝ) (ε i i.2)) (fun _ => isOpen_ball)
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hsub hp⟩, mem_ball_self (hε p (hsub hp))⟩)
    refine convexOn_Icc_of_forall_window (η := δ / 2) (by positivity) fun u hu => ?_
    obtain ⟨i, hi⟩ := hcov u hu
    refine (hconv i i.2).subset (fun s hs => ⟨hsub ⟨hu.1.trans hs.1, hs.2.trans (min_le_left _ _)⟩,
      ?_⟩) (convex_Icc _ _)
    have hsb : s ∈ ball (i : ℝ) (ε i i.2) := by
      refine hi ?_
      rw [mem_ball, Real.dist_eq, abs_lt]
      have h2 := hs.2.trans (min_le_right _ _)
      constructor <;> linarith [hs.1]
    rw [mem_ball, Real.dist_eq, abs_lt] at hsb
    exact ⟨by linarith [hsb.1], by linarith [hsb.2]⟩
  refine convexOn_of_slope_mono_adjacent hJ fun hx hz hxy hyz => ?_
  exact (hseg _ hx _ hz).slope_mono_adjacent ⟨le_rfl, (hxy.trans hyz).le⟩
    ⟨(hxy.trans hyz).le, le_rfl⟩ hxy hyz

end DifferentialGeometry.Analysis.Convex
