import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Chapter-14 assembly, item L1, step T2′ (handles in product form): the height profile

Lane ASM-L1b2 (from the parked scratch of ASM-L1b). `exists_handleHeight`: two smooth height
profiles `T₀`, `T₁` (positive derivative on `[0, a]`, `a < 1/2`) whose end strips are separated
(`T₀ a < 1 - T₁ a`) are glued to ONE smooth profile `φ` with positive derivative on `[0, 1]`, equal
to `T₀` on `(-∞, a]` and to `t ↦ 1 - T₁ (1 - t)` on `[1 - a, ∞)`. Route: on `[a, a']` blend `T₀`
into the line `L` through `(a, T₀ a')` and `(1 - a, 1 - T₁ a')`, on `[1 - a', 1 - a]` blend `L` into
`1 - T₁ (1 - ·)`; the blending terms `step' · (L - T₀)` and `step' · (U - L)` are nonnegative
because `L` lies above `T₀` and below `U` on the blending intervals.

`handleStep c d` is the smooth step from `0` (left of `c`) to `1` (right of `d`); it also drives
the rotation and the radial interpolation of the handle (`AssemblyL1HandleProductMap`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The smooth step from `0` (for `t ≤ c`) to `1` (for `t ≥ d`). -/
def handleStep (c d t : ℝ) : ℝ := Real.smoothTransition ((t - c) / (d - c))

theorem handleStep_of_le {c d t : ℝ} (hcd : c < d) (ht : t ≤ c) : handleStep c d t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem handleStep_of_ge {c d t : ℝ} (hcd : c < d) (ht : d ≤ t) : handleStep c d t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by linarith)).mpr (by linarith))

theorem handleStep_nonneg (c d t : ℝ) : 0 ≤ handleStep c d t := Real.smoothTransition.nonneg _

theorem handleStep_le_one (c d t : ℝ) : handleStep c d t ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_handleStep (c d : ℝ) : ContDiff ℝ ∞ (handleStep c d) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).div_const _)

theorem hasDerivAt_handleStep {c d : ℝ} (hcd : c < d) (t : ℝ) :
    ∃ s : ℝ, 0 ≤ s ∧ HasDerivAt (handleStep c d) s t := by
  have h := ((contDiff_handleStep c d).differentiable (by simp) t).hasDerivAt
  refine ⟨_, ?_, h⟩
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem handleStep_pos {c d t : ℝ} (hcd : c < d) (ht : c < t) : 0 < handleStep c d t :=
  Real.smoothTransition.pos_of_pos (div_pos (by linarith) (by linarith))

theorem lt_of_handleStep_pos {c d t : ℝ} (hcd : c < d) (h : 0 < handleStep c d t) : c < t := by
  by_contra hct
  rw [handleStep_of_le hcd (not_lt.mp hct)] at h
  exact lt_irrefl 0 h

theorem lt_of_handleStep_lt_one {c d t : ℝ} (hcd : c < d) (h : handleStep c d t < 1) : t < d := by
  by_contra hdt
  rw [handleStep_of_ge hcd (not_lt.mp hdt)] at h
  exact lt_irrefl 1 h

/-- Outside `[c, d]` the derivative of the step vanishes. -/
theorem handleStep_deriv_eq_zero {c d t s : ℝ} (hcd : c < d)
    (hs : HasDerivAt (handleStep c d) s t) (ht : t < c ∨ d < t) : s = 0 := by
  rcases ht with ht | ht
  · have hev : handleStep c d =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact handleStep_of_le hcd (le_of_lt hx)
    exact hs.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)
  · have hev : handleStep c d =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact handleStep_of_ge hcd (le_of_lt hx)
    exact hs.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hev)

/-- **The height profile of a handle.** -/
theorem exists_handleHeight {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) {T₀ T₁ : ℝ → ℝ}
    (h0 : ContDiff ℝ ∞ T₀) (h1 : ContDiff ℝ ∞ T₁)
    (hd0 : ∀ s ∈ Icc (0 : ℝ) a, 0 < deriv T₀ s) (hd1 : ∀ s ∈ Icc (0 : ℝ) a, 0 < deriv T₁ s)
    (hsep : T₀ a < 1 - T₁ a) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 < deriv φ t) ∧
      (∀ t ≤ a, φ t = T₀ t) ∧ ∀ t, 1 - a ≤ t → φ t = 1 - T₁ (1 - t) := by
  -- a slightly larger strip `[0, a']` on which both profiles still increase and stay separated
  have hcd0 : Continuous (deriv T₀) := h0.continuous_deriv (by simp)
  have hcd1 : Continuous (deriv T₁) := h1.continuous_deriv (by simp)
  let O : Set ℝ := {s | 0 < deriv T₀ s ∧ 0 < deriv T₁ s}
  have hO : IsOpen O := (isOpen_lt continuous_const hcd0).inter (isOpen_lt continuous_const hcd1)
  obtain ⟨η, hη, hηO⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a)).exists_thickening_subset_open hO
    (fun s hs => ⟨hd0 s hs, hd1 s hs⟩)
  have hsepO : ∀ᶠ s in 𝓝 a, T₀ s < 1 - T₁ s :=
    (h0.continuous.continuousAt.prodMk (continuous_const.sub h1.continuous).continuousAt).eventually
      (isOpen_lt continuous_fst continuous_snd |>.mem_nhds hsep)
  obtain ⟨κ, hκ, hκsep⟩ := Metric.eventually_nhds_iff.mp hsepO
  set a' := a + min (min (η / 2) (κ / 2)) ((1 / 2 - a) / 2) with ha'def
  have hm : 0 < min (min (η / 2) (κ / 2)) ((1 / 2 - a) / 2) :=
    lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have haa' : a < a' := by rw [ha'def]; linarith
  have ha'q : a' < 1 / 2 := by
    have := min_le_right (min (η / 2) (κ / 2)) ((1 / 2 - a) / 2)
    rw [ha'def]
    linarith
  have hderO : ∀ s ∈ Icc (0 : ℝ) a', 0 < deriv T₀ s ∧ 0 < deriv T₁ s := by
    intro s hs
    apply hηO
    rw [Metric.mem_thickening_iff]
    refine ⟨min s a, ⟨le_min hs.1 ha.le, min_le_right _ _⟩, ?_⟩
    rw [Real.dist_eq]
    have h1 := (min_le_left (min (η / 2) (κ / 2)) ((1 / 2 - a) / 2)).trans (min_le_left _ _)
    rcases le_total s a with hsa | hsa
    · rw [min_eq_left hsa, sub_self, abs_zero]
      exact hη
    · rw [min_eq_right hsa, abs_of_nonneg (by linarith)]
      have : s - a ≤ η / 2 := by
        have := hs.2
        rw [ha'def] at this
        linarith
      linarith
  have hsep' : T₀ a' < 1 - T₁ a' := by
    apply hκsep
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    have h2 := (min_le_left (min (η / 2) (κ / 2)) ((1 / 2 - a) / 2)).trans (min_le_right _ _)
    rw [ha'def]
    linarith
  -- monotonicity of the profiles on `[0, a']`
  have hmono : ∀ T : ℝ → ℝ, ContDiff ℝ ∞ T → (∀ s ∈ Icc (0 : ℝ) a', 0 < deriv T s) →
      MonotoneOn T (Icc (0 : ℝ) a') := by
    intro T hT hdT
    apply (strictMonoOn_of_deriv_pos (convex_Icc 0 a') hT.continuous.continuousOn _).monotoneOn
    intro s hs
    rw [interior_Icc] at hs
    exact hdT s (Ioo_subset_Icc_self hs)
  have hm0 := hmono T₀ h0 (fun s hs => (hderO s hs).1)
  have hm1 := hmono T₁ h1 (fun s hs => (hderO s hs).2)
  -- the line and the pieces
  set u₀ := T₀ a'
  set u₁ := 1 - T₁ a'
  let L : ℝ → ℝ := fun t => u₀ + (u₁ - u₀) * ((t - a) / (1 - 2 * a))
  let U : ℝ → ℝ := fun t => 1 - T₁ (1 - t)
  let β₁ := handleStep a a'
  let β₂ := handleStep (1 - a') (1 - a)
  let M : ℝ → ℝ := fun t => (1 - β₂ t) * L t + β₂ t * U t
  let φ : ℝ → ℝ := fun t => (1 - β₁ t) * T₀ t + β₁ t * M t
  have hden : 0 < 1 - 2 * a := by linarith
  have hslope : 0 < (u₁ - u₀) / (1 - 2 * a) := div_pos (by linarith) hden
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · exact (((contDiff_const.sub (contDiff_handleStep a a')).mul h0).add
      ((contDiff_handleStep a a').mul
        (((contDiff_const.sub (contDiff_handleStep _ _)).mul
          (contDiff_const.add (contDiff_const.mul
            ((contDiff_id.sub contDiff_const).div_const _)))).add
          ((contDiff_handleStep _ _).mul (contDiff_const.sub (h1.comp
            (contDiff_const.sub contDiff_id)))))))
  · intro t ht
    obtain ⟨b1', hb1', hβ₁⟩ := hasDerivAt_handleStep haa' t
    obtain ⟨b2', hb2', hβ₂⟩ := hasDerivAt_handleStep (show 1 - a' < 1 - a by linarith) t
    have hT₀ : HasDerivAt T₀ (deriv T₀ t) t := (h0.differentiable (by simp) t).hasDerivAt
    have hU : HasDerivAt U (deriv T₁ (1 - t)) t := by
      have h := ((h1.differentiable (by simp) (1 - t)).hasDerivAt).comp t
        ((hasDerivAt_id t).const_sub 1)
      exact ((hasDerivAt_const t (1 : ℝ)).sub h).congr_deriv (by ring)
    have hL : HasDerivAt L ((u₁ - u₀) / (1 - 2 * a)) t := by
      have h := (((hasDerivAt_id t).sub_const a).div_const (1 - 2 * a)).const_mul (u₁ - u₀)
      exact ((hasDerivAt_const t u₀).add h).congr_deriv (by ring)
    have hM : HasDerivAt M ((-b2') * L t + (1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) +
        (b2' * U t + β₂ t * deriv T₁ (1 - t))) t := by
      exact ((((hasDerivAt_const t (1 : ℝ)).sub hβ₂).mul hL).add (hβ₂.mul hU)).congr_deriv
        (by simp only [Pi.sub_apply]; ring)
    have hφ : HasDerivAt φ ((-b1') * T₀ t + (1 - β₁ t) * deriv T₀ t +
        (b1' * M t + β₁ t * ((-b2') * L t + (1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) +
          (b2' * U t + β₂ t * deriv T₁ (1 - t))))) t := by
      exact ((((hasDerivAt_const t (1 : ℝ)).sub hβ₁).mul hT₀).add (hβ₁.mul hM)).congr_deriv
        (by simp only [Pi.sub_apply]; ring)
    rw [hφ.deriv]
    -- the two blending terms are nonnegative
    have hterm1 : 0 ≤ b1' * (M t - T₀ t) := by
      rcases lt_or_ge t a with hta | hta
      · rw [handleStep_deriv_eq_zero haa' hβ₁ (Or.inl hta), zero_mul]
      rcases le_or_gt t a' with hta' | hta'
      · apply mul_nonneg hb1'
        have hb2 : β₂ t = 0 := handleStep_of_le (by linarith) (by linarith)
        change 0 ≤ (1 - β₂ t) * L t + β₂ t * U t - T₀ t
        rw [hb2]
        have hLt : u₀ ≤ L t := by
          change u₀ ≤ u₀ + (u₁ - u₀) * ((t - a) / (1 - 2 * a))
          have : 0 ≤ (u₁ - u₀) * ((t - a) / (1 - 2 * a)) :=
            mul_nonneg (by linarith) (div_nonneg (by linarith) hden.le)
          linarith
        have hT : T₀ t ≤ u₀ := hm0 ⟨by linarith [ht.1], hta'⟩ ⟨by linarith, le_rfl⟩ hta'
        linarith
      · rw [handleStep_deriv_eq_zero haa' hβ₁ (Or.inr hta'), zero_mul]
    have hterm2 : 0 ≤ b2' * (U t - L t) := by
      rcases lt_or_ge t (1 - a') with hta | hta
      · rw [handleStep_deriv_eq_zero (show 1 - a' < 1 - a by linarith) hβ₂ (Or.inl hta), zero_mul]
      rcases le_or_gt t (1 - a) with hta' | hta'
      · apply mul_nonneg hb2'
        have hLt : L t ≤ u₁ := by
          change u₀ + (u₁ - u₀) * ((t - a) / (1 - 2 * a)) ≤ u₁
          have h1 : (t - a) / (1 - 2 * a) ≤ 1 := (div_le_one hden).mpr (by linarith)
          nlinarith
        have hUt : u₁ ≤ U t := by
          change 1 - T₁ a' ≤ 1 - T₁ (1 - t)
          have := hm1 ⟨by linarith [ht.2], by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith :
            1 - t ≤ a')
          linarith
        linarith
      · rw [handleStep_deriv_eq_zero (show 1 - a' < 1 - a by linarith) hβ₂ (Or.inr hta'),
          zero_mul]
    -- the positive part
    have hβ₁0 : 0 ≤ β₁ t := handleStep_nonneg a a' t
    have hβ₁1 : β₁ t ≤ 1 := handleStep_le_one a a' t
    have hβ₂0 : 0 ≤ β₂ t := handleStep_nonneg (1 - a') (1 - a) t
    have hβ₂1 : β₂ t ≤ 1 := handleStep_le_one (1 - a') (1 - a) t
    have hX : 0 < (1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) + β₂ t * deriv T₁ (1 - t) := by
      rcases eq_or_lt_of_le hβ₂0 with h | h
      · rw [← h]
        simpa using hslope
      · have htt : 1 - a' < t := lt_of_handleStep_pos (by linarith) h
        have hU' : 0 < deriv T₁ (1 - t) := (hderO (1 - t) ⟨by linarith [ht.2], by linarith⟩).2
        have h1 : 0 ≤ (1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) :=
          mul_nonneg (by linarith) hslope.le
        nlinarith
    have hY : 0 ≤ (1 - β₁ t) * deriv T₀ t := by
      rcases eq_or_lt_of_le hβ₁1 with h | h
      · rw [h, sub_self, zero_mul]
      · have hta : t < a' := lt_of_handleStep_lt_one haa' h
        exact mul_nonneg (by linarith) (hderO t ⟨ht.1, hta.le⟩).1.le
    have hYpos : β₁ t = 0 → 0 < deriv T₀ t := by
      intro h
      by_contra hneg
      have hta : t ≤ a := by
        by_contra hta
        have := handleStep_pos haa' (not_le.mp hta)
        change 0 < β₁ t at this
        rw [h] at this
        exact lt_irrefl 0 this
      exact hneg (hderO t ⟨ht.1, by linarith⟩).1
    have hsplit : (-b1') * T₀ t + (1 - β₁ t) * deriv T₀ t +
        (b1' * M t + β₁ t * ((-b2') * L t + (1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) +
          (b2' * U t + β₂ t * deriv T₁ (1 - t)))) =
        (1 - β₁ t) * deriv T₀ t +
          β₁ t * ((1 - β₂ t) * ((u₁ - u₀) / (1 - 2 * a)) + β₂ t * deriv T₁ (1 - t)) +
          β₁ t * (b2' * (U t - L t)) + b1' * (M t - T₀ t) := by ring
    rw [hsplit]
    have hZ : 0 ≤ β₁ t * (b2' * (U t - L t)) := mul_nonneg hβ₁0 hterm2
    rcases eq_or_lt_of_le hβ₁0 with h | h
    · have := hYpos h.symm
      rw [← h]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      linarith
    · have := mul_pos h hX
      linarith
  · intro t ht
    change (1 - β₁ t) * T₀ t + β₁ t * M t = T₀ t
    rw [show β₁ t = 0 from handleStep_of_le haa' ht]
    ring
  · intro t ht
    have hb1 : β₁ t = 1 := handleStep_of_ge haa' (by linarith)
    have hb2 : β₂ t = 1 := handleStep_of_ge (by linarith) ht
    change (1 - β₁ t) * T₀ t + β₁ t * ((1 - β₂ t) * L t + β₂ t * U t) = 1 - T₁ (1 - t)
    rw [hb1, hb2]
    ring

end GC.GraphManifold.Assembly
