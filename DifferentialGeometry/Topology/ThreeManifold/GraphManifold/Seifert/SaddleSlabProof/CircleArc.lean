import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Analysis.Calculus.Inverse.InjectiveParameterizedInverse
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Circle diffeomorphisms with a prescribed arc

Lane RG03c. `contDiff_periodize`: a smooth function supported in `(v, v + 1)` becomes a smooth
`1`-periodic function `s ↦ φ (v + fract (s - v))`. `exists_periodic_lift_eq`: an increasing
smooth `g` on a neighbourhood of `[u₀, u₁]` with `u₁ - u₀ < 1` and `g u₁ - g u₀ < 1` agrees on
`[u₀, u₁]` with a smooth `G` of positive derivative and `G (t + 1) = G t + 1`. Its derivative is
`λ g' + (1 - λ) μ` periodised, for a bump `λ` equal to `1` on `[u₀, u₁]` and the constant `μ > 0`
that makes the integral over a period equal to `1`. `exists_addCircle_diffeo_comp_eqOn` matches
two increasing lifts `b`, `b'` (`k ↑(b t) = ↑(b' t)` on `[u₀, u₁]`) after extending them to
increasing diffeomorphisms of `ℝ`. `exists_addCircle_diffeo_arc`: two smooth immersed arcs
`β, β' : (-T, T) → ℝ/ℤ`, injective, are matched on `[-T₁, T₁]` by a diffeomorphism `k` of the
circle, `k ∘ β = β'`; the arcs are lifted through the covering `ℝ → ℝ/ℤ` and reversed by
`addCircleNeg` when they decrease.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology Manifold

namespace GC.Seifert.SaddleSlabProof

def periodize (v : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := φ (v + Int.fract (s - v))

theorem periodize_periodic (v : ℝ) (φ : ℝ → ℝ) : Function.Periodic (periodize v φ) 1 := by
  intro s
  simp only [periodize, add_sub_right_comm, Int.fract_add_one]

theorem periodize_eq_of_mem {v : ℝ} (φ : ℝ → ℝ) {s : ℝ} (hs : s ∈ Ico v (v + 1)) :
    periodize v φ s = φ s := by
  unfold periodize
  rw [Int.fract_eq_self.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  ring_nf

theorem contDiff_periodize {φ : ℝ → ℝ} {v : ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : tsupport φ ⊆ Ioo v (v + 1)) : ContDiff ℝ ∞ (periodize v φ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  set n := ⌊s - v⌋ with hn
  by_cases hfr : Int.fract (s - v) = 0
  · have hO : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
    have hv : v ∈ (tsupport φ)ᶜ := fun h => (lt_irrefl v) (hsupp h).1
    have hv1 : v + 1 ∈ (tsupport φ)ᶜ := fun h => (lt_irrefl (v + 1)) (hsupp h).2
    obtain ⟨η₁, hη₁, hb₁⟩ := Metric.isOpen_iff.mp hO v hv
    obtain ⟨η₂, hη₂, hb₂⟩ := Metric.isOpen_iff.mp hO (v + 1) hv1
    have hsv : s - v = n := by
      have := Int.floor_add_fract (s - v)
      rw [hfr, add_zero] at this
      rw [hn, this]
    have hzero : ∀ s' ∈ Metric.ball s (min (min η₁ η₂) (1 / 2)), periodize v φ s' = 0 := by
      intro s' hs'
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs'
      have h1 := (min_le_left (min η₁ η₂) (1 / 2)).trans (min_le_left η₁ η₂)
      have h2 := (min_le_left (min η₁ η₂) (1 / 2)).trans (min_le_right η₁ η₂)
      have h3 := min_le_right (min η₁ η₂) (1 / 2)
      unfold periodize
      apply image_eq_zero_of_notMem_tsupport
      rcases le_or_gt (n : ℝ) (s' - v) with hle | hlt
      · have hfl : ⌊s' - v⌋ = n := by
          rw [Int.floor_eq_iff]
          constructor
          · exact hle
          · linarith
        have hfr' : Int.fract (s' - v) = s' - v - n := by
          rw [Int.fract, hfl]
        apply hb₁
        rw [Metric.mem_ball, Real.dist_eq, hfr', abs_lt]
        constructor <;> linarith
      · have hfl : ⌊s' - v⌋ = n - 1 := by
          rw [Int.floor_eq_iff]
          push_cast
          constructor <;> linarith
        have hfr' : Int.fract (s' - v) = s' - v - n + 1 := by
          rw [Int.fract, hfl]
          push_cast
          ring
        apply hb₂
        rw [Metric.mem_ball, Real.dist_eq, hfr', abs_lt]
        constructor <;> linarith
    have hev : periodize v φ =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
      eventually_of_mem (Metric.ball_mem_nhds s (lt_min (lt_min hη₁ hη₂) one_half_pos)) hzero
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hlo : (n : ℝ) < s - v := lt_of_le_of_ne (Int.floor_le _) fun h => hfr (by
      rw [Int.fract, ← hn, ← h, sub_self])
    have hhi : s - v < n + 1 := Int.lt_floor_add_one _
    have hev : periodize v φ =ᶠ[𝓝 s] fun s' => φ (s' - n) := by
      have hmem : Ioo (v + n) (v + n + 1) ∈ 𝓝 s :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      refine eventually_of_mem hmem fun s' hs' => ?_
      have hfl : ⌊s' - v⌋ = n := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith [hs'.1, hs'.2]
      unfold periodize
      rw [Int.fract, hfl]
      ring_nf
    exact ((hφ.comp (contDiff_id.sub contDiff_const)).contDiffAt).congr_of_eventuallyEq hev

theorem exists_interval_margin {g : ℝ → ℝ} {u₀ u₁ : ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hJu : Icc u₀ u₁ ⊆ J) (hu : u₀ ≤ u₁) (hg : ContinuousOn g J) (hlen : u₁ - u₀ < 1)
    (hglen : g u₁ - g u₀ < 1) :
    ∃ ρ > 0, Icc (u₀ - ρ) (u₁ + ρ) ⊆ J ∧ u₁ + ρ - (u₀ - ρ) < 1 ∧
      g (u₁ + ρ) - g (u₀ - ρ) < 1 := by
  have h0 : u₀ ∈ J := hJu ⟨le_rfl, hu⟩
  have h1 : u₁ ∈ J := hJu ⟨hu, le_rfl⟩
  obtain ⟨ρ₀, hρ₀, hb₀⟩ := Metric.isOpen_iff.mp hJ u₀ h0
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.isOpen_iff.mp hJ u₁ h1
  set η := (1 - (g u₁ - g u₀)) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨δ₀, hδ₀, hc₀⟩ := Metric.continuousAt_iff.mp
    (hg.continuousAt (hJ.mem_nhds h0)) η hηpos
  obtain ⟨δ₁, hδ₁, hc₁⟩ := Metric.continuousAt_iff.mp
    (hg.continuousAt (hJ.mem_nhds h1)) η hηpos
  set ρ := min (min (min ρ₀ ρ₁) (min δ₀ δ₁)) ((1 - (u₁ - u₀)) / 4) / 2 with hρ
  have hm : 0 < min (min (min ρ₀ ρ₁) (min δ₀ δ₁)) ((1 - (u₁ - u₀)) / 4) :=
    lt_min (lt_min (lt_min hρ₀ hρ₁) (lt_min hδ₀ hδ₁)) (by linarith)
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hle := min_le_left (min (min ρ₀ ρ₁) (min δ₀ δ₁)) ((1 - (u₁ - u₀)) / 4)
  have hle' := min_le_right (min (min ρ₀ ρ₁) (min δ₀ δ₁)) ((1 - (u₁ - u₀)) / 4)
  have hρ₀' : ρ < ρ₀ := by
    have := (min_le_left (min ρ₀ ρ₁) (min δ₀ δ₁)).trans (min_le_left ρ₀ ρ₁)
    linarith
  have hρ₁' : ρ < ρ₁ := by
    have := (min_le_left (min ρ₀ ρ₁) (min δ₀ δ₁)).trans (min_le_right ρ₀ ρ₁)
    linarith
  have hδ₀' : ρ < δ₀ := by
    have := (min_le_right (min ρ₀ ρ₁) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
    linarith
  have hδ₁' : ρ < δ₁ := by
    have := (min_le_right (min ρ₀ ρ₁) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
    linarith
  refine ⟨ρ, hρpos, fun x hx => ?_, by linarith, ?_⟩
  · rcases lt_or_ge x u₀ with hx0 | hx0
    · apply hb₀
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1]
    · rcases le_or_gt x u₁ with hx1 | hx1
      · exact hJu ⟨hx0, hx1⟩
      · apply hb₁
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hx.2]
  · have e0 := hc₀ (x := u₀ - ρ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have e1 := hc₁ (x := u₁ + ρ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at e0 e1
    linarith [e0.1, e1.2]

theorem exists_bump {u₀ u₁ ρ : ℝ} (hu : u₀ ≤ u₁) (hρ : 0 < ρ) :
    ∃ l : ℝ → ℝ, ContDiff ℝ ∞ l ∧ (∀ s, 0 ≤ l s ∧ l s ≤ 1) ∧ (∀ s ∈ Icc u₀ u₁, l s = 1) ∧
      tsupport l ⊆ Icc (u₀ - ρ / 2) (u₁ + ρ / 2) := by
  let B : ContDiffBump ((u₀ + u₁) / 2) :=
    ⟨(u₁ - u₀) / 2 + ρ / 4, (u₁ - u₀) / 2 + ρ / 2, by linarith, by linarith⟩
  refine ⟨B, B.contDiff, fun s => ⟨B.nonneg, B.le_one⟩, fun s hs => ?_, ?_⟩
  · apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -((u₁ - u₀) / 2 + ρ / 4) ≤ _ ∧ _ ≤ (u₁ - u₀) / 2 + ρ / 4
    constructor <;> linarith [hs.1, hs.2]
  · rw [B.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    change -((u₁ - u₀) / 2 + ρ / 2) ≤ _ ∧ _ ≤ (u₁ - u₀) / 2 + ρ / 2 at hx
    constructor <;> linarith [hx.1, hx.2]

theorem periodize_eq_of_mem_Icc {v : ℝ} {φ : ℝ → ℝ} (hsupp : tsupport φ ⊆ Ioo v (v + 1)) {s : ℝ}
    (hs : s ∈ Icc v (v + 1)) : periodize v φ s = φ s := by
  rcases hs.2.lt_or_eq with h | h
  · exact periodize_eq_of_mem φ ⟨hs.1, h⟩
  · have h1 : periodize v φ s = φ v := by
      unfold periodize
      rw [h, add_sub_cancel_left, Int.fract_one, add_zero]
    rw [h1, h, image_eq_zero_of_notMem_tsupport fun hv => lt_irrefl v (hsupp hv).1,
      image_eq_zero_of_notMem_tsupport fun hv => lt_irrefl (v + 1) (hsupp hv).2]

theorem exists_periodic_lift_eq {g : ℝ → ℝ} {u₀ u₁ : ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hJu : Icc u₀ u₁ ⊆ J) (hu : u₀ ≤ u₁) (hg : ContDiffOn ℝ ∞ g J)
    (hpos : ∀ t ∈ J, 0 < deriv g t) (hlen : u₁ - u₀ < 1) (hglen : g u₁ - g u₀ < 1) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ (∀ t, G (t + 1) = G t + 1) ∧ (∀ t, 0 < deriv G t) ∧
      EqOn G g (Icc u₀ u₁) := by
  obtain ⟨ρ, hρ, hJρ, hlenρ, hglenρ⟩ :=
    exists_interval_margin hJ hJu hu hg.continuousOn hlen hglen
  obtain ⟨l, hl, hl01, hl1, hlsupp⟩ := exists_bump hu hρ
  set v₀ := u₀ - ρ with hv₀
  set v₁ := u₁ + ρ with hv₁
  have hg' : ContDiffOn ℝ ∞ (deriv g) J := hg.deriv_of_isOpen hJ (by simp)
  have hgd : ∀ x ∈ J, HasDerivAt g (deriv g x) x := fun x hx =>
    ((hg.contDiffAt (hJ.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hlJ : tsupport l ⊆ J := hlsupp.trans fun x hx =>
    hJρ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlzero : ∀ s, s ∉ Icc (u₀ - ρ / 2) (u₁ + ρ / 2) → l s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hs (hlsupp h)
  set φ₁ : ℝ → ℝ := fun s => l s * deriv g s with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := by
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s ∈ J
    · exact hl.contDiffAt.mul (hg'.contDiffAt (hJ.mem_nhds hs))
    · have hs' : s ∉ tsupport l := fun h => hs (hlJ h)
      have hev : φ₁ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport l).isOpen_compl.mem_nhds hs'] with x hx
        simp only [hφ₁def, image_eq_zero_of_notMem_tsupport hx, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hv01 : v₁ ≤ v₀ + 1 := by linarith
  have hsplit : ∀ {k : ℝ → ℝ}, Continuous k → (∀ s, l s = 0 → k s = 0) →
      ∫ s in v₀..v₀ + 1, k s = ∫ s in v₀..v₁, k s := by
    intro k hk hkl
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := v₁)
      (hk.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
    have h0 : ∫ s in v₁..v₀ + 1, k s = ∫ s in v₁..v₀ + 1, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hv01] at hs
      exact hkl s (hlzero s fun h => by linarith [h.2, hs.1])
    rw [h0, intervalIntegral.integral_zero, add_zero]
  have hv₀₁ : v₀ ≤ v₁ := by linarith
  have hsubJ : uIcc v₀ v₁ ⊆ J := by
    rw [uIcc_of_le hv₀₁]
    exact hJρ
  have hderivInt : IntervalIntegrable (deriv g) MeasureTheory.volume v₀ v₁ :=
    (hg'.continuousOn.mono hsubJ).intervalIntegrable
  set A := ∫ s in v₀..v₀ + 1, φ₁ s with hA
  set Λ := ∫ s in v₀..v₀ + 1, l s with hΛ
  have hΛlt : Λ < 1 := by
    rw [hΛ, hsplit hl.continuous fun s h => h]
    have hle : ∫ s in v₀..v₁, l s ≤ ∫ s in v₀..v₁, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hv₀₁ (hl.continuous.intervalIntegrable _ _)
        intervalIntegrable_const fun s _ => (hl01 s).2
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
    linarith
  have hAlt : A < 1 := by
    rw [hA, hsplit hφ₁.continuous fun s h => by simp only [hφ₁def, h, zero_mul]]
    have hle : ∫ s in v₀..v₁, φ₁ s ≤ ∫ s in v₀..v₁, deriv g s :=
      intervalIntegral.integral_mono_on hv₀₁ (hφ₁.continuous.intervalIntegrable _ _)
        hderivInt fun s hs => by
          have hsJ : s ∈ J := hJρ hs
          have h1 := hpos s hsJ
          have h2 := hl01 s
          simp only [hφ₁def]
          nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hgd x (hsubJ hx))
      hderivInt] at hle
    linarith
  set μ := (1 - A) / (1 - Λ) with hμ
  have hμpos : 0 < μ := div_pos (by linarith) (by linarith)
  set φ : ℝ → ℝ := fun s => φ₁ s - μ * l s with hφdef
  have hφ : ContDiff ℝ ∞ φ := hφ₁.sub (contDiff_const.mul hl)
  have hφsupp : tsupport φ ⊆ Ioo v₀ (v₀ + 1) := by
    have hsub : Function.support φ ⊆ Function.support l := fun s hs h => hs (by
      simp only [hφdef, hφ₁def, h, zero_mul, mul_zero, sub_zero])
    refine (closure_mono hsub).trans (hlsupp.trans fun x hx => ⟨?_, ?_⟩)
    · linarith [hx.1]
    · linarith [hx.2]
  set d : ℝ → ℝ := fun s => μ + periodize v₀ φ s with hddef
  have hd : ContDiff ℝ ∞ d := contDiff_const.add (contDiff_periodize hφ hφsupp)
  have hdper : Function.Periodic d 1 := fun s => by
    simp only [hddef, periodize_periodic v₀ φ s]
  have hdpos : ∀ s, 0 < d s := by
    intro s
    set s' := v₀ + Int.fract (s - v₀)
    have hval : d s = μ * (1 - l s') + l s' * deriv g s' := by
      simp only [hddef, periodize, hφdef, hφ₁def]
      ring
    rw [hval]
    rcases (hl01 s').1.lt_or_eq with h | h
    · have hs'J : s' ∈ J := hlJ (subset_tsupport l (ne_of_gt h))
      have := hpos s' hs'J
      nlinarith [(hl01 s').2]
    · rw [← h]
      simpa using hμpos
  set G : ℝ → ℝ := fun t => g u₀ + ∫ s in u₀..t, d s with hGdef
  have hGd : ∀ t, HasDerivAt G (d t) t := fun t =>
    ((hd.continuous.integral_hasStrictDerivAt u₀ t).hasDerivAt).const_add (g u₀)
  have hGderiv : deriv G = d := funext fun t => (hGd t).deriv
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact contDiff_infty_iff_deriv.mpr ⟨fun t => (hGd t).differentiableAt, hGderiv ▸ hd⟩
  · intro t
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hd.continuous.intervalIntegrable u₀ t) (hd.continuous.intervalIntegrable t (t + 1))
    have hper := Function.Periodic.intervalIntegral_add_eq hdper t v₀
    have hint : ∫ s in v₀..v₀ + 1, d s = 1 := by
      have hc : ∫ s in v₀..v₀ + 1, d s = ∫ s in v₀..v₀ + 1, (μ + (φ₁ s - μ * l s)) :=
        intervalIntegral.integral_congr fun s hs => by
          rw [uIcc_of_le (by linarith)] at hs
          change μ + periodize v₀ φ s = _
          rw [periodize_eq_of_mem_Icc hφsupp hs]
      have e1 : ∫ x in v₀..v₀ + 1, (φ₁ x - μ * l x) = A - μ * Λ := by
        rw [intervalIntegral.integral_sub (f := φ₁) (g := fun x => μ * l x)
          (hφ₁.continuous.intervalIntegrable _ _)
          ((continuous_const.mul hl.continuous).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul]
      rw [hc, intervalIntegral.integral_add intervalIntegrable_const
        ((hφ₁.sub (contDiff_const.mul hl)).continuous.intervalIntegrable _ _),
        intervalIntegral.integral_const, e1, smul_eq_mul, add_sub_cancel_left, one_mul, hμ]
      have hne : (1 - Λ) ≠ 0 := (sub_pos.mpr hΛlt).ne'
      field_simp
      ring
    simp only [hGdef]
    rw [← hadd, hper, hint]
    ring
  · intro t
    rw [hGderiv]
    exact hdpos t
  · intro t ht
    simp only [hGdef]
    have hsub : uIcc u₀ t ⊆ Icc u₀ u₁ := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hc : ∫ s in u₀..t, d s = ∫ s in u₀..t, deriv g s :=
      intervalIntegral.integral_congr fun s hs => by
        have hs' := hsub hs
        have hmem : s ∈ Ico v₀ (v₀ + 1) := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
        have h1 : periodize v₀ φ s = φ s := periodize_eq_of_mem φ hmem
        change μ + periodize v₀ φ s = deriv g s
        rw [h1]
        simp only [hφdef, hφ₁def, hl1 s hs']
        ring
    rw [hc, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hgd x (hJu (hsub hx)))
      ((hg'.continuousOn.mono (hsub.trans hJu)).intervalIntegrable)]
    ring

theorem add_int_of_add_one {G : ℝ → ℝ} (hper : ∀ t, G (t + 1) = G t + 1) (x : ℝ) (n : ℤ) :
    G (x + n) = G x + n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k hk =>
    push_cast at hk ⊢
    rw [← add_assoc, hper, hk]
    ring
  | pred k hk =>
    have h := hper (x + (-(k : ℝ) - 1))
    push_cast at hk ⊢
    rw [show x + (-(k : ℝ) - 1) + 1 = x + -(k : ℝ) by ring, hk] at h
    linarith

theorem bijective_of_deriv_pos_of_add_one {G : ℝ → ℝ} (hpos : ∀ x, 0 < deriv G x)
    (hper : ∀ t, G (t + 1) = G t + 1) : Function.Bijective G := by
  have hmono : StrictMono G := strictMono_of_deriv_pos hpos
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun x =>
    (differentiableAt_of_deriv_ne_zero (hpos x).ne').continuousAt
  refine ⟨hmono.injective, fun y => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_gt (|y - G 0|)
  have ha : G (0 + (-n : ℤ)) ≤ y := by
    rw [add_int_of_add_one hper]
    push_cast
    have := neg_abs_le (y - G 0)
    linarith
  have hb : y ≤ G (0 + (n : ℤ)) := by
    rw [add_int_of_add_one hper]
    have := le_abs_self (y - G 0)
    linarith
  have hle : (0 : ℝ) + (-n : ℤ) ≤ 0 + (n : ℤ) := by
    push_cast
    have : (0 : ℝ) ≤ n := le_trans (abs_nonneg _) hn.le
    linarith
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc hle hcont.continuousOn ⟨ha, hb⟩
  exact ⟨c, hc⟩

theorem exists_addCircle_diffeo_eqOn {g : ℝ → ℝ} {u₀ u₁ : ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hJu : Icc u₀ u₁ ⊆ J) (hu : u₀ ≤ u₁) (hg : ContDiffOn ℝ ∞ g J)
    (hpos : ∀ t ∈ J, 0 < deriv g t) (hlen : u₁ - u₀ < 1) (hglen : g u₁ - g u₀ < 1) :
    ∃ k : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∀ t ∈ Icc u₀ u₁, k (t : AddCircle (1 : ℝ)) = (g t : AddCircle (1 : ℝ)) := by
  obtain ⟨G, hG, hper, hGpos, heq⟩ := exists_periodic_lift_eq hJ hJu hu hg hpos hlen hglen
  have hbij := bijective_of_deriv_pos_of_add_one hGpos hper
  obtain ⟨R, hR, hleft, hright⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_inverse_of_bijective (E := ℝ)
      (h := fun q : ℝ × ℝ => G q.2) (V := univ) isOpen_univ
      (hG.comp contDiff_snd).contDiffOn (fun p _ => hbij)
      (by
        intro p _ x
        have hd : HasFDerivAt (fun q : ℝ × ℝ => G q.2)
            ((fderiv ℝ G x).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p, x) :=
          ((hG.differentiable (by simp)) x).hasFDerivAt.comp (p, x) (hasFDerivAt_snd)
        rw [hd.fderiv]
        change fderiv ℝ G x 1 ≠ 0
        rw [fderiv_apply_one_eq_deriv]
        exact (hGpos x).ne')
  set S : ℝ → ℝ := fun y => R (0, y) with hSdef
  have hS : ContDiff ℝ ∞ S := by
    rw [← contDiffOn_univ]
    refine (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn ?_)
    intro y _
    exact ⟨mem_univ _, mem_univ _⟩
  have hSG : ∀ x, S (G x) = x := fun x => hleft 0 (mem_univ _) x
  have hGS : ∀ y, G (S y) = y := fun y => hright 0 (mem_univ _) y
  have hSper : ∀ y, S (y + 1) = S y + 1 := by
    intro y
    apply hbij.1
    rw [hGS, hper, hGS]
  have hpG : Function.Periodic (fun t : ℝ => (G t : AddCircle (1 : ℝ))) 1 := fun t => by
    simp only [hper, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hpS : Function.Periodic (fun t : ℝ => (S t : AddCircle (1 : ℝ))) 1 := fun t => by
    simp only [hSper, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  let kf : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := hpG.lift
  let kb : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := hpS.lift
  have hkf : ∀ t : ℝ, kf (t : AddCircle (1 : ℝ)) = (G t : AddCircle (1 : ℝ)) :=
    fun t => hpG.lift_coe t
  have hkb : ∀ t : ℝ, kb (t : AddCircle (1 : ℝ)) = (S t : AddCircle (1 : ℝ)) :=
    fun t => hpS.lift_coe t
  refine ⟨{ toFun := kf
            invFun := kb
            left_inv := fun z => by
              obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
              rw [hkf, hkb, hSG]
            right_inv := fun z => by
              obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
              rw [hkb, hkf, hGS]
            contMDiff_toFun :=
              AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
                QuotientAddGroup.mk_surjective (by
                  change ContMDiff _ _ _ (kf ∘ fun t : ℝ => (t : AddCircle (1 : ℝ)))
                  have h : (kf ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
                      fun t => (G t : AddCircle (1 : ℝ)) := funext hkf
                  rw [h]
                  exact AddCircle.contMDiff_coe.comp hG.contMDiff)
            contMDiff_invFun :=
              AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
                QuotientAddGroup.mk_surjective (by
                  change ContMDiff _ _ _ (kb ∘ fun t : ℝ => (t : AddCircle (1 : ℝ)))
                  have h : (kb ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
                      fun t => (S t : AddCircle (1 : ℝ)) := funext hkb
                  rw [h]
                  exact AddCircle.contMDiff_coe.comp hS.contMDiff) }, fun t ht => ?_⟩
  change kf (t : AddCircle (1 : ℝ)) = _
  rw [hkf, heq ht]

theorem exists_Icc_margin {u₀ u₁ : ℝ} {J : Set ℝ} (hJ : IsOpen J) (hJu : Icc u₀ u₁ ⊆ J)
    (hu : u₀ ≤ u₁) : ∃ ρ > 0, Icc (u₀ - ρ) (u₁ + ρ) ⊆ J := by
  obtain ⟨ρ₀, hρ₀, hb₀⟩ := Metric.isOpen_iff.mp hJ u₀ (hJu ⟨le_rfl, hu⟩)
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.isOpen_iff.mp hJ u₁ (hJu ⟨hu, le_rfl⟩)
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, fun x hx => ?_⟩
  have h0 := min_le_left ρ₀ ρ₁
  have h1 := min_le_right ρ₀ ρ₁
  rcases lt_or_ge x u₀ with hx0 | hx0
  · apply hb₀
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1]
  · rcases le_or_gt x u₁ with hx1 | hx1
    · exact hJu ⟨hx0, hx1⟩
    · apply hb₁
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.2]

theorem exists_global_extension {b : ℝ → ℝ} {u₀ u₁ : ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hJu : Icc u₀ u₁ ⊆ J) (hu : u₀ ≤ u₁) (hb : ContDiffOn ℝ ∞ b J)
    (hpos : ∀ t ∈ J, 0 < deriv b t) :
    ∃ B : ℝ → ℝ, ContDiff ℝ ∞ B ∧ (∀ t, 0 < deriv B t) ∧ Function.Bijective B ∧
      EqOn B b (Icc u₀ u₁) := by
  obtain ⟨ρ, hρ, hJρ⟩ := exists_Icc_margin hJ hJu hu
  obtain ⟨l, hl, hl01, hl1, hlsupp⟩ := exists_bump hu hρ
  have hb' : ContDiffOn ℝ ∞ (deriv b) J := hb.deriv_of_isOpen hJ (by simp)
  have hbd : ∀ x ∈ J, HasDerivAt b (deriv b x) x := fun x hx =>
    ((hb.contDiffAt (hJ.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hlJ : tsupport l ⊆ J := hlsupp.trans fun x hx =>
    hJρ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlzero : ∀ s, s ∉ Icc (u₀ - ρ / 2) (u₁ + ρ / 2) → l s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hs (hlsupp h)
  set d : ℝ → ℝ := fun s => l s * deriv b s + (1 - l s) with hddef
  have hd : ContDiff ℝ ∞ d := by
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s ∈ J
    · exact (hl.contDiffAt.mul (hb'.contDiffAt (hJ.mem_nhds hs))).add
        (contDiffAt_const.sub hl.contDiffAt)
    · have hs' : s ∉ tsupport l := fun h => hs (hlJ h)
      have hev : d =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [(isClosed_tsupport l).isOpen_compl.mem_nhds hs'] with x hx
        simp only [hddef, image_eq_zero_of_notMem_tsupport hx, zero_mul, sub_zero, zero_add]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hdpos : ∀ s, 0 < d s := by
    intro s
    rcases (hl01 s).1.lt_or_eq with h | h
    · have hsJ : s ∈ J := hlJ (subset_tsupport l (ne_of_gt h))
      have := hpos s hsJ
      simp only [hddef]
      nlinarith [(hl01 s).2]
    · simp only [hddef, ← h, zero_mul, sub_zero, zero_add, zero_lt_one]
  set B : ℝ → ℝ := fun t => b u₀ + ∫ s in u₀..t, d s with hBdef
  have hBd : ∀ t, HasDerivAt B (d t) t := fun t =>
    ((hd.continuous.integral_hasStrictDerivAt u₀ t).hasDerivAt).const_add (b u₀)
  have hBderiv : deriv B = d := funext fun t => (hBd t).deriv
  have hBpos : ∀ t, 0 < deriv B t := fun t => by rw [hBderiv]; exact hdpos t
  have hBc : Continuous B := continuous_iff_continuousAt.mpr fun t => (hBd t).continuousAt
  have htail : ∀ {c t : ℝ}, (∀ s ∈ uIcc c t, l s = 0) → B t = B c + (t - c) := by
    intro c t hct
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hd.continuous.intervalIntegrable u₀ c) (hd.continuous.intervalIntegrable c t)
    have hc : ∫ s in c..t, d s = ∫ s in c..t, (1 : ℝ) :=
      intervalIntegral.integral_congr fun s hs => by
        simp only [hddef, hct s hs, zero_mul, sub_zero, zero_add]
    simp only [hBdef]
    rw [← hadd, hc, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  refine ⟨B, contDiff_infty_iff_deriv.mpr ⟨fun t => (hBd t).differentiableAt, hBderiv ▸ hd⟩,
    hBpos, ⟨(strictMono_of_deriv_pos hBpos).injective, fun y => ?_⟩, fun t ht => ?_⟩
  · set cR := u₁ + ρ
    set cL := u₀ - ρ
    have hR : ∀ t, cR ≤ t → B t = B cR + (t - cR) := fun t ht => htail fun s hs => by
      rw [uIcc_of_le ht] at hs
      exact hlzero s fun h => by linarith [h.2, hs.1]
    have hL : ∀ t, t ≤ cL → B t = B cL + (t - cL) := fun t ht => htail fun s hs => by
      rw [uIcc_of_ge ht] at hs
      exact hlzero s fun h => by linarith [h.1, hs.2]
    set t₁ := max cR (cR + (y - B cR)) with ht₁
    set t₀ := min cL (cL + (y - B cL)) with ht₀
    have h1 : y ≤ B t₁ := by
      rw [hR t₁ (le_max_left _ _)]
      linarith [le_max_right cR (cR + (y - B cR))]
    have h0 : B t₀ ≤ y := by
      rw [hL t₀ (min_le_left _ _)]
      linarith [min_le_right cL (cL + (y - B cL))]
    have hle : t₀ ≤ t₁ := (min_le_left _ _).trans ((by linarith : cL ≤ cR).trans
      (le_max_left _ _))
    obtain ⟨c, -, hc⟩ := intermediate_value_Icc hle hBc.continuousOn ⟨h0, h1⟩
    exact ⟨c, hc⟩
  · simp only [hBdef]
    have hsub : uIcc u₀ t ⊆ Icc u₀ u₁ := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hc : ∫ s in u₀..t, d s = ∫ s in u₀..t, deriv b s :=
      intervalIntegral.integral_congr fun s hs => by
        simp only [hddef, hl1 s (hsub hs), one_mul, sub_self, add_zero]
    rw [hc, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hbd x (hJu (hsub hx)))
      ((hb'.continuousOn.mono (hsub.trans hJu)).intervalIntegrable)]
    ring

theorem exists_smooth_inverse {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hpos : ∀ x, 0 < deriv G x)
    (hbij : Function.Bijective G) :
    ∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧ (∀ x, S (G x) = x) ∧ (∀ y, G (S y) = y) ∧
      ∀ y, 0 < deriv S y := by
  obtain ⟨R, hR, hleft, hright⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_inverse_of_bijective (E := ℝ)
      (h := fun q : ℝ × ℝ => G q.2) (V := univ) isOpen_univ
      (hG.comp contDiff_snd).contDiffOn (fun p _ => hbij)
      (by
        intro p _ x
        have hd : HasFDerivAt (fun q : ℝ × ℝ => G q.2)
            ((fderiv ℝ G x).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (p, x) :=
          ((hG.differentiable (by simp)) x).hasFDerivAt.comp (p, x) (hasFDerivAt_snd)
        rw [hd.fderiv]
        change fderiv ℝ G x 1 ≠ 0
        rw [fderiv_apply_one_eq_deriv]
        exact (hpos x).ne')
  set S : ℝ → ℝ := fun y => R (0, y) with hSdef
  have hS : ContDiff ℝ ∞ S := by
    rw [← contDiffOn_univ]
    refine (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn ?_)
    intro y _
    exact ⟨mem_univ _, mem_univ _⟩
  have hSG : ∀ x, S (G x) = x := fun x => hleft 0 (mem_univ _) x
  have hGS : ∀ y, G (S y) = y := fun y => hright 0 (mem_univ _) y
  refine ⟨S, hS, hSG, hGS, fun y => ?_⟩
  have hSd : HasDerivAt S (deriv S y) y :=
    ((hS.differentiable (by simp)) y).hasDerivAt
  have hGd : HasDerivAt G (deriv G (S y)) (S y) :=
    ((hG.differentiable (by simp)) (S y)).hasDerivAt
  have hcomp := hGd.comp y hSd
  have hid : HasDerivAt (G ∘ S) 1 y := by
    have h : G ∘ S = id := funext hGS
    rw [h]
    exact hasDerivAt_id y
  have h1 := hcomp.unique hid
  have h2 := hpos (S y)
  by_contra hneg
  push Not at hneg
  nlinarith

theorem exists_addCircle_diffeo_comp_eqOn {b b' : ℝ → ℝ} {u₀ u₁ : ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hJu : Icc u₀ u₁ ⊆ J) (hu : u₀ ≤ u₁) (hb : ContDiffOn ℝ ∞ b J)
    (hb' : ContDiffOn ℝ ∞ b' J) (hpos : ∀ t ∈ J, 0 < deriv b t)
    (hpos' : ∀ t ∈ J, 0 < deriv b' t) (hlen : b u₁ - b u₀ < 1) (hlen' : b' u₁ - b' u₀ < 1) :
    ∃ k : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∀ t ∈ Icc u₀ u₁, k (b t : AddCircle (1 : ℝ)) = (b' t : AddCircle (1 : ℝ)) := by
  obtain ⟨B, hB, hBpos, hBbij, hBb⟩ := exists_global_extension hJ hJu hu hb hpos
  obtain ⟨B', hB', hB'pos, -, hB'b⟩ := exists_global_extension hJ hJu hu hb' hpos'
  obtain ⟨S, hS, hSB, hBS, hSpos⟩ := exists_smooth_inverse hB hBpos hBbij
  set g : ℝ → ℝ := fun y => B' (S y) with hgdef
  have hg : ContDiff ℝ ∞ g := hB'.comp hS
  have hgpos : ∀ y, 0 < deriv g y := by
    intro y
    have hd := (((hB'.differentiable (by simp)) (S y)).hasDerivAt).comp y
      (((hS.differentiable (by simp)) y).hasDerivAt)
    have he : deriv g y = deriv B' (S y) * deriv S y := hd.deriv
    rw [he]
    exact mul_pos (hB'pos _) (hSpos y)
  have hmono : StrictMono B := strictMono_of_deriv_pos hBpos
  have hu₀ : u₀ ∈ Icc u₀ u₁ := ⟨le_rfl, hu⟩
  have hu₁ : u₁ ∈ Icc u₀ u₁ := ⟨hu, le_rfl⟩
  obtain ⟨k, hk⟩ := exists_addCircle_diffeo_eqOn (g := g) (u₀ := b u₀) (u₁ := b u₁) isOpen_univ
    (subset_univ _) (by rw [← hBb hu₀, ← hBb hu₁]; exact hmono.monotone hu)
    hg.contDiffOn (fun y _ => hgpos y) hlen (by
      simp only [hgdef]
      rw [← hBb hu₀, ← hBb hu₁, hSB, hSB, hB'b hu₀, hB'b hu₁]
      exact hlen')
  refine ⟨k, fun t ht => ?_⟩
  have hbt : b t ∈ Icc (b u₀) (b u₁) := by
    rw [← hBb hu₀, ← hBb hu₁, ← hBb ht]
    exact ⟨hmono.monotone ht.1, hmono.monotone ht.2⟩
  rw [hk (b t) hbt]
  simp only [hgdef]
  rw [← hBb ht, hSB, hB'b ht]

def addCircleNeg : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞ where
  toFun z := -z
  invFun z := -z
  left_inv z := neg_neg z
  right_inv z := neg_neg z
  contMDiff_toFun :=
    AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective (by
        change ContMDiff _ _ _
          ((fun z : AddCircle (1 : ℝ) => -z) ∘ fun t : ℝ => (t : AddCircle (1 : ℝ)))
        have h : ((fun z : AddCircle (1 : ℝ) => -z) ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
            fun t : ℝ => ((-t : ℝ) : AddCircle (1 : ℝ)) :=
          funext fun t => (AddCircle.coe_neg (1 : ℝ)).symm
        rw [h]
        exact AddCircle.contMDiff_coe.comp contDiff_neg.contMDiff)
  contMDiff_invFun :=
    AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective (by
        change ContMDiff _ _ _
          ((fun z : AddCircle (1 : ℝ) => -z) ∘ fun t : ℝ => (t : AddCircle (1 : ℝ)))
        have h : ((fun z : AddCircle (1 : ℝ) => -z) ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
            fun t : ℝ => ((-t : ℝ) : AddCircle (1 : ℝ)) :=
          funext fun t => (AddCircle.coe_neg (1 : ℝ)).symm
        rw [h]
        exact AddCircle.contMDiff_coe.comp contDiff_neg.contMDiff)

theorem addCircleNeg_apply (z : AddCircle (1 : ℝ)) : addCircleNeg z = -z := rfl

theorem exists_lift_of_arc {β : ℝ → AddCircle (1 : ℝ)} {T₂ T : ℝ} (hT₂ : 0 ≤ T₂)
    (hT : T₂ < T) (hβ : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β t)
    (himm : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β t ≠ 0) :
    ∃ b : ℝ → ℝ, ContDiffOn ℝ ∞ b (Ioo (-T₂) T₂) ∧ Continuous b ∧
      (∀ t ∈ Icc (-T₂) T₂, (b t : AddCircle (1 : ℝ)) = β t) ∧
      ((∀ t ∈ Ioo (-T₂) T₂, 0 < deriv b t) ∨ (∀ t ∈ Ioo (-T₂) T₂, deriv b t < 0)) := by
  have hle : -T₂ ≤ T₂ := by linarith
  have hsub : Icc (-T₂) T₂ ⊆ Ioo (-T) T := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hβc : ContinuousOn β (Icc (-T₂) T₂) := fun t ht =>
    (hβ t (hsub ht)).continuousAt.continuousWithinAt
  let γ : C(ℝ, AddCircle (1 : ℝ)) :=
    ⟨fun t => β (projIcc (-T₂) T₂ hle t),
      hβc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun t => (projIcc (-T₂) T₂ hle t).2⟩
  obtain ⟨e₀, he₀⟩ := QuotientAddGroup.mk_surjective (γ 0)
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ :=
    IsCoveringMap.existsUnique_continuousMap_lifts (AddCircle.isCoveringMap_coe (1 : ℝ)) γ 0 e₀
      he₀
  have hlift : ∀ t ∈ Icc (-T₂) T₂, ((F t : ℝ) : AddCircle (1 : ℝ)) = β t := by
    intro t ht
    have h := congrFun hFlift t
    change ((F t : ℝ) : AddCircle (1 : ℝ)) = β (projIcc (-T₂) T₂ hle t) at h
    rw [h, projIcc_of_mem hle ht]
  have hev : ∀ t ∈ Ioo (-T₂) T₂, (fun y => ((F y : ℝ) : AddCircle (1 : ℝ))) =ᶠ[𝓝 t] β :=
    fun t ht => eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun y hy =>
      hlift y (Ioo_subset_Icc_self hy)
  have hFat : ∀ t ∈ Ioo (-T₂) T₂, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ F t := by
    intro t ht
    have hlocal := AddCircle.isLocalDiffeomorph_coe (F t)
    have hβt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β t := hβ t (hsub (Ioo_subset_Icc_self ht))
    have he : ((F t : ℝ) : AddCircle (1 : ℝ)) = β t := hlift t (Ioo_subset_Icc_self ht)
    have hli : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hlocal.localInverse (β t) := by
      rw [← he]
      exact hlocal.contMDiffAt_localInverse
    have hsmooth : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (hlocal.localInverse ∘ β) t :=
      hli.comp t hβt
    apply hsmooth.congr_of_eventuallyEq
    have hevent : ∀ᶠ y in 𝓝 t, F y ∈ hlocal.localInverse.target :=
      F.continuous.continuousAt
        (hlocal.localInverse.open_target.mem_nhds hlocal.localInverse_mem_target)
    filter_upwards [hevent, hev t ht] with y hy hyβ
    change F y = hlocal.localInverse (β y)
    rw [← hyβ]
    exact (hlocal.localInverse_left_inv hy).symm
  have hFon : ContDiffOn ℝ ∞ F (Ioo (-T₂) T₂) := fun t ht =>
    (contMDiffAt_iff_contDiffAt.mp (hFat t ht)).contDiffWithinAt
  have hderiv : ∀ t ∈ Ioo (-T₂) T₂, deriv F t ≠ 0 := by
    intro t ht h0
    apply himm t (hsub (Ioo_subset_Icc_self ht))
    have hFd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) F t := (hFat t ht).mdifferentiableAt (by simp)
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => (x : AddCircle (1 : ℝ))) (F t) :=
      AddCircle.contMDiff_coe.contMDiffAt.mdifferentiableAt (by simp)
    have hF0 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) F t = 0 := by
      rw [mfderiv_eq_fderiv]
      have : fderiv ℝ F t = 0 := by
        ext
        rw [fderiv_apply_one_eq_deriv, h0]
        rfl
      rw [this]
      rfl
    have hFd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) F t 0 := by
      have h := hFd.hasMFDerivAt
      rwa [hF0] at h
    have hc := hcd.hasMFDerivAt.comp t hFd'
    have hβd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => (x : AddCircle (1 : ℝ))) (F t)).comp 0) :=
      hc.congr_of_eventuallyEq (hev t ht).symm
    rw [hβd.mfderiv, ContinuousLinearMap.comp_zero]
    rfl
  have hcont : ContinuousOn (deriv F) (Ioo (-T₂) T₂) :=
    hFon.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  refine ⟨F, hFon, F.continuous, hlift, ?_⟩
  by_cases hpos : ∀ t ∈ Ioo (-T₂) T₂, 0 < deriv F t
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨s, hs, hs0⟩ := hpos
    have hsneg : deriv F s < 0 := lt_of_le_of_ne hs0 (hderiv s hs)
    intro t ht
    by_contra htn
    push Not at htn
    have htpos : 0 < deriv F t := lt_of_le_of_ne htn (hderiv t ht).symm
    obtain ⟨r, hr, hr0⟩ := isPreconnected_Ioo.intermediate_value hs ht hcont
      ⟨hsneg.le, htpos.le⟩
    exact hderiv r hr hr0

theorem exists_increasing_lift_of_arc {β : ℝ → AddCircle (1 : ℝ)} {T₂ T : ℝ} (hT₂ : 0 ≤ T₂)
    (hT : T₂ < T) (hβ : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β t)
    (himm : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β t ≠ 0) :
    ∃ e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∃ b : ℝ → ℝ, ContDiffOn ℝ ∞ b (Ioo (-T₂) T₂) ∧ Continuous b ∧
        (∀ t ∈ Icc (-T₂) T₂, (b t : AddCircle (1 : ℝ)) = e (β t)) ∧
        ∀ t ∈ Ioo (-T₂) T₂, 0 < deriv b t := by
  obtain ⟨b, hb, hbc, hlift, hsign⟩ := exists_lift_of_arc hT₂ hT hβ himm
  rcases hsign with hpos | hneg
  · exact ⟨Diffeomorph.refl _ _ _, b, hb, hbc, fun t ht => hlift t ht, hpos⟩
  · refine ⟨addCircleNeg, fun t => -b t, hb.neg, hbc.neg, fun t ht => ?_, fun t ht => ?_⟩
    · rw [addCircleNeg_apply, ← hlift t ht, AddCircle.coe_neg]
    · rw [deriv.fun_neg]
      linarith [hneg t ht]

theorem exists_addCircle_diffeo_arc {β β' : ℝ → AddCircle (1 : ℝ)} {T₁ T : ℝ} (hT₁ : 0 ≤ T₁)
    (hT : T₁ < T) (hβ : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β t)
    (hβ' : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β' t)
    (hinj : InjOn β (Ioo (-T) T)) (hinj' : InjOn β' (Ioo (-T) T))
    (himm : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β t ≠ 0)
    (himm' : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β' t ≠ 0) :
    ∃ k : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∀ t ∈ Icc (-T₁) T₁, k (β t) = β' t := by
  set T₂ := (T₁ + T) / 2 with hT₂def
  have hT₂ : 0 ≤ T₂ := by rw [hT₂def]; linarith
  have hT₂T : T₂ < T := by rw [hT₂def]; linarith
  have hT₁₂ : T₁ < T₂ := by rw [hT₂def]; linarith
  obtain ⟨e, b, hb, hbc, hlift, hpos⟩ := exists_increasing_lift_of_arc hT₂ hT₂T hβ himm
  obtain ⟨e', b', hb', hbc', hlift', hpos'⟩ := exists_increasing_lift_of_arc hT₂ hT₂T hβ' himm'
  have hIcc : Icc (-T₁) T₁ ⊆ Icc (-T₂) T₂ := Icc_subset_Icc (by linarith) hT₁₂.le
  have hIoo : Icc (-T₂) T₂ ⊆ Ioo (-T) T := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlen : ∀ {γ : ℝ → AddCircle (1 : ℝ)} {c : ℝ → ℝ}
      {ε : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞},
      InjOn γ (Ioo (-T) T) → Continuous c →
      (∀ t ∈ Icc (-T₂) T₂, (c t : AddCircle (1 : ℝ)) = ε (γ t)) →
      (∀ t ∈ Ioo (-T₂) T₂, 0 < deriv c t) → c T₁ - c (-T₁) < 1 := by
    intro γ c ε hγ hc hcl hcpos
    by_contra hge
    push Not at hge
    have hle : -T₁ ≤ T₁ := by linarith
    obtain ⟨s, hs, hcs⟩ := intermediate_value_Icc hle hc.continuousOn
      (show c (-T₁) + 1 ∈ Icc (c (-T₁)) (c T₁) from ⟨by linarith, by linarith⟩)
    have h1 : ε (γ s) = ε (γ (-T₁)) := by
      rw [← hcl s (hIcc hs), ← hcl (-T₁) (hIcc ⟨le_rfl, hle⟩), hcs, AddCircle.coe_add,
        AddCircle.coe_period, add_zero]
    have h2 := hγ (hIoo (hIcc hs)) (hIoo (hIcc ⟨le_rfl, hle⟩)) (ε.injective h1)
    rw [h2] at hcs
    linarith
  obtain ⟨k₁, hk₁⟩ := exists_addCircle_diffeo_comp_eqOn (J := Ioo (-T₂) T₂) isOpen_Ioo
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) (by linarith) hb hb' hpos hpos'
    (hlen hinj hbc hlift hpos) (hlen hinj' hbc' hlift' hpos')
  refine ⟨e.trans (k₁.trans e'.symm), fun t ht => ?_⟩
  change e'.symm (k₁ (e (β t))) = β' t
  rw [← hlift t (hIcc ht), hk₁ t ht, hlift' t (hIcc ht), Diffeomorph.symm_apply_apply]

end GC.Seifert.SaddleSlabProof
