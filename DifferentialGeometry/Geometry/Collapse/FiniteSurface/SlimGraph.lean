import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# LFR20 kernels: the whole level is a graph, the interpolation is enclosed

Blueprint LFR20 (master207A:26358), steps 1, 3 and 4. For the model function `f = η ∘ j` on the
cylinder `[-b,b] × Z` the proof uses only: `f` is continuous, increasing in `t`, and `|f - t| < 2e`.
This file proves, for any topological space `Z`:

* `exists_continuousOn_root`: for every `s ∈ [-a,a]` and `z` the equation `f(t,z) = s` has exactly
  one root `T(s,z) ∈ (-b,b)`, with `|T(s,z) - s| < c`, and `T` is continuous on `[-a,a] × Z`
  (so the ENTIRE level `f = s` in the cylinder is the graph of a continuous function on `Z`);
* `exists_continuousOn_root_of_deriv`: the same from a positive `t`-derivative (LFR20.1);
* `interpolation_enclosure`, `three_quarters_lt_interpolation_deriv`: the straight interpolation
  `(1-u)t + u f` keeps the value error and the derivative bound, and its inverse images of
  `[-a,a]` lie in `|t| < a + c` (the compact `Q` of item 3);
* `slimPacket_constants`: the numerical inequalities of the proof for `L = 10⁶Δ`, `D = 10³Δ`,
  `e = Δ/100`, `a = 9L/10`, `b = 19L/20`.

The binding (the compactness-contradiction frame over LFR14–LFR19) is not proved here; see
`build-logs/resume/sheet-W4-F7c.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **LFR20, step 4 (kernel).** A continuous function on `ℝ × Z`, strictly increasing in `t` on
`[-b,b]`, within `c` of `t` there, has for each `s ∈ [-a,a]` (`a + c ≤ b`) exactly one root in
`[-b,b]`; it lies in `(-b,b)` and within `c` of `s`, and depends continuously on `(s,z)`. -/
theorem exists_continuousOn_root {Z : Type*} [TopologicalSpace Z] {f : ℝ × Z → ℝ} {a b c : ℝ}
    (hf : Continuous f) (hmono : ∀ z, StrictMonoOn (fun t => f (t, z)) (Icc (-b) b))
    (hval : ∀ t ∈ Icc (-b) b, ∀ z, |f (t, z) - t| < c) (hc : 0 < c) (habc : a + c ≤ b) :
    ∃ T : ℝ × Z → ℝ, ContinuousOn T (Icc (-a) a ×ˢ univ) ∧
      ∀ s ∈ Icc (-a) a, ∀ z, T (s, z) ∈ Ioo (-b) b ∧ f (T (s, z), z) = s ∧
        |T (s, z) - s| < c ∧ ∀ t ∈ Icc (-b) b, f (t, z) = s → t = T (s, z) := by
  classical
  have hcont_t : ∀ z, Continuous fun t => f (t, z) := fun z =>
    hf.comp (continuous_id.prodMk continuous_const)
  have hexists : ∀ s ∈ Icc (-a) a, ∀ z, ∃ t ∈ Icc (-b) b, f (t, z) = s := by
    intro s hs z
    have hb : -b ≤ b := by linarith [hs.1, hs.2]
    have h₁ := abs_lt.mp (hval (-b) ⟨le_rfl, hb⟩ z)
    have h₂ := abs_lt.mp (hval b ⟨hb, le_rfl⟩ z)
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc hb (hcont_t z).continuousOn
      (show s ∈ Icc (f (-b, z)) (f (b, z)) from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    exact ⟨t, ht, hts⟩
  let T : ℝ × Z → ℝ := fun p =>
    if h : ∃ t ∈ Icc (-b) b, f (t, p.2) = p.1 then h.choose else 0
  have hTspec : ∀ s ∈ Icc (-a) a, ∀ z, T (s, z) ∈ Icc (-b) b ∧ f (T (s, z), z) = s := by
    intro s hs z
    have h := hexists s hs z
    have hT : T (s, z) = h.choose :=
      show (if h' : ∃ t ∈ Icc (-b) b, f (t, z) = s then h'.choose else 0) = h.choose from
        dite_eq_left_of_eq_true (eq_true h)
    rw [hT]
    exact h.choose_spec
  have hTIoo : ∀ s ∈ Icc (-a) a, ∀ z, T (s, z) ∈ Ioo (-b) b := by
    intro s hs z
    obtain ⟨hT, hfT⟩ := hTspec s hs z
    have hval' := abs_lt.mp (hval _ hT z)
    rw [hfT] at hval'
    refine ⟨lt_of_le_of_ne hT.1 fun h => ?_, lt_of_le_of_ne hT.2 fun h => ?_⟩
    · rw [← h] at hval'; linarith [hs.1, hval'.2]
    · rw [h] at hval'; linarith [hs.2, hval'.1]
  refine ⟨T, ?_, fun s hs z => ⟨hTIoo s hs z, (hTspec s hs z).2, ?_, fun t ht hts => ?_⟩⟩
  · rintro ⟨s₀, z₀⟩ hp
    have hs₀ : s₀ ∈ Icc (-a) a := hp.1
    obtain ⟨hT₀, hfT₀⟩ := hTspec s₀ hs₀ z₀
    have hT₀' := hTIoo s₀ hs₀ z₀
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    set t₀ := T (s₀, z₀) with ht₀
    set η := min (ε / 2) (min (t₀ + b) (b - t₀) / 2) with hη
    have hηpos : 0 < η := lt_min (by linarith) (by
      have := hT₀'.1; have := hT₀'.2
      exact div_pos (lt_min (by linarith) (by linarith)) two_pos)
    have hη₁ : η ≤ ε / 2 := min_le_left _ _
    have hη₂ : η ≤ min (t₀ + b) (b - t₀) / 2 := min_le_right _ _
    have hη₃ : min (t₀ + b) (b - t₀) ≤ t₀ + b := min_le_left _ _
    have hη₄ : min (t₀ + b) (b - t₀) ≤ b - t₀ := min_le_right _ _
    have hlo_mem : t₀ - η ∈ Icc (-b) b := ⟨by linarith, by linarith⟩
    have hhi_mem : t₀ + η ∈ Icc (-b) b := ⟨by linarith, by linarith⟩
    have hlo : f (t₀ - η, z₀) < s₀ := hfT₀ ▸ hmono z₀ hlo_mem hT₀ (by linarith)
    have hhi : s₀ < f (t₀ + η, z₀) := hfT₀ ▸ hmono z₀ hT₀ hhi_mem (by linarith)
    have hev₁ : ∀ᶠ p in 𝓝 ((s₀, z₀) : ℝ × Z), f (t₀ - η, p.2) < p.1 :=
      ContinuousAt.eventually_lt
        ((hf.comp (continuous_const.prodMk continuous_snd)).continuousAt) continuous_fst.continuousAt
        hlo
    have hev₂ : ∀ᶠ p in 𝓝 ((s₀, z₀) : ℝ × Z), p.1 < f (t₀ + η, p.2) :=
      ContinuousAt.eventually_lt continuous_fst.continuousAt
        ((hf.comp (continuous_const.prodMk continuous_snd)).continuousAt) hhi
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev₁, nhdsWithin_le_nhds hev₂] with
      p hpS h₁ h₂
    obtain ⟨s, z⟩ := p
    obtain ⟨hTp, hfTp⟩ := hTspec s hpS.1 z
    have hgt : t₀ - η < T (s, z) := by
      by_contra hle
      have := (hmono z).monotoneOn hTp hlo_mem (not_lt.mp hle)
      simp only at this h₁
      linarith
    have hlt : T (s, z) < t₀ + η := by
      by_contra hle
      have := (hmono z).monotoneOn hhi_mem hTp (not_lt.mp hle)
      simp only at this h₂
      linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · obtain ⟨hT, hfT⟩ := hTspec s hs z
    have := hval _ hT z
    rwa [hfT, abs_sub_comm] at this
  · exact (hmono z).injOn ht (hTspec s hs z).1 (hts.trans (hTspec s hs z).2.symm)

/-- **LFR20, step 4 from the derivative bound (LFR20.1).** -/
theorem exists_continuousOn_root_of_deriv {Z : Type*} [TopologicalSpace Z] {f : ℝ × Z → ℝ}
    {a b c : ℝ} (hf : Continuous f)
    (hderiv : ∀ z, ∀ t ∈ Ioo (-b) b, 0 < deriv (fun t => f (t, z)) t)
    (hval : ∀ t ∈ Icc (-b) b, ∀ z, |f (t, z) - t| < c) (hc : 0 < c) (habc : a + c ≤ b) :
    ∃ T : ℝ × Z → ℝ, ContinuousOn T (Icc (-a) a ×ˢ univ) ∧
      ∀ s ∈ Icc (-a) a, ∀ z, T (s, z) ∈ Ioo (-b) b ∧ f (T (s, z), z) = s ∧
        |T (s, z) - s| < c ∧ ∀ t ∈ Icc (-b) b, f (t, z) = s → t = T (s, z) := by
  refine exists_continuousOn_root hf (fun z => ?_) hval hc habc
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  exact hderiv z t ht

/-- **LFR20, the interpolation keeps the value error and is enclosed.** -/
theorem interpolation_enclosure {t f c a u : ℝ} (hc : |f - t| < c) (hu : u ∈ Icc (0 : ℝ) 1) :
    |(1 - u) * t + u * f - t| < c ∧ (|(1 - u) * t + u * f| ≤ a → |t| < a + c) := by
  have heq : (1 - u) * t + u * f - t = u * (f - t) := by ring
  have hlt : |(1 - u) * t + u * f - t| < c := by
    rw [heq, abs_mul, abs_of_nonneg hu.1]
    calc u * |f - t| ≤ 1 * |f - t| := mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _)
      _ < c := by rw [one_mul]; exact hc
  refine ⟨hlt, fun ha => ?_⟩
  have := abs_sub_abs_le_abs_sub ((1 - u) * t + u * f) t
  have h2 := abs_sub_comm ((1 - u) * t + u * f) t
  linarith [abs_sub_abs_le_abs_sub t ((1 - u) * t + u * f)]

/-- **LFR20, the interpolation keeps `∂_t > 3/4`.** -/
theorem three_quarters_lt_interpolation_deriv {d u : ℝ} (hd : 3 / 4 < d) (hu : u ∈ Icc (0 : ℝ) 1) :
    3 / 4 < (1 - u) * 1 + u * d := by
  rcases eq_or_lt_of_le hu.2 with h | h
  · rw [h]; linarith
  · have : 0 ≤ u * (d - 3 / 4) := mul_nonneg hu.1 (by linarith)
    linarith

/-- **LFR20, the numerical inequalities.** For `Δ ≥ 1`, `0 < σ ≤ 1/100`, `β ≤ 1`, with
`L = 10⁶Δ`, `D = 10³Δ`, `e = Δ/100`, `a = 9L/10`, `b = 19L/20`: the cylinder `[-b,b] × Z` lies in
the model ball of radius `0.96L`; the shifted test points lie in radius `3L`; (LFR20.2)
`√((a+e)² + D²) + β < 0.91L`; `2e < b - a`; `a + 3e < b`; and `4L < T = L/σ`. -/
theorem slimPacket_constants {Δ σ β : ℝ} (hΔ : 1 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ ≤ 1 / 100)
    (hβ : β ≤ 1) :
    Real.sqrt ((19 * (10 ^ 6 * Δ) / 20) ^ 2 + (10 ^ 3 * Δ) ^ 2) < 96 / 100 * (10 ^ 6 * Δ) ∧
    Real.sqrt ((19 * (10 ^ 6 * Δ) / 20 + 2 * (10 ^ 6 * Δ)) ^ 2 + (10 ^ 3 * Δ) ^ 2) <
      3 * (10 ^ 6 * Δ) ∧
    Real.sqrt ((9 * (10 ^ 6 * Δ) / 10 + Δ / 100) ^ 2 + (10 ^ 3 * Δ) ^ 2) + β <
      91 / 100 * (10 ^ 6 * Δ) ∧
    2 * (Δ / 100) < 19 * (10 ^ 6 * Δ) / 20 - 9 * (10 ^ 6 * Δ) / 10 ∧
    9 * (10 ^ 6 * Δ) / 10 + 3 * (Δ / 100) < 19 * (10 ^ 6 * Δ) / 20 ∧
    4 * (10 ^ 6 * Δ) < 10 ^ 6 * Δ / σ := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔsq : 0 < Δ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, by linarith, by linarith, ?_⟩
  · rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  · rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  · have hpos : 0 < 91 / 100 * (10 ^ 6 * Δ) - β := by linarith
    have hlow : 909999 * Δ ≤ 91 / 100 * (10 ^ 6 * Δ) - β := by linarith
    have hsq : (909999 * Δ) ^ 2 ≤ (91 / 100 * (10 ^ 6 * Δ) - β) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have : Real.sqrt ((9 * (10 ^ 6 * Δ) / 10 + Δ / 100) ^ 2 + (10 ^ 3 * Δ) ^ 2) <
        91 / 100 * (10 ^ 6 * Δ) - β := by
      rw [Real.sqrt_lt' hpos]
      nlinarith
    linarith
  · rw [lt_div_iff₀ hσ₀]
    nlinarith

end DifferentialGeometry.Geometry.Collapse
