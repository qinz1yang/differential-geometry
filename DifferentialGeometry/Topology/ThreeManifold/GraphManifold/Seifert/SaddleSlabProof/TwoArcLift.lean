import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.CircleArc
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Joining two increasing functions

Lane RG03c (MD2b). `exists_two_piece_lift`: let `g₁` be smooth and increasing near `[p₀, p₁]`,
`g₂` near `[q₀, q₁]`, with `p₁ < q₀` and `g₁ p₁ < g₂ q₀`. Then a smooth `G` with positive
derivative near `[p₀, q₁]` agrees with `g₁` on `[p₀, p₁]` and with `g₂` on `[q₀, q₁]`. Its
derivative is `λ₁ g₁' + λ₂ g₂' + μ ρ` for bumps `λ₁`, `λ₂` around the two intervals, the function
`ρ = smoothTransition (s - p₁) · smoothTransition (q₀ - s)`, positive exactly on `(p₁, q₀)`, and the
constant `μ > 0` fixed by the increase `g₂ q₀ - g₁ p₁` required over the gap.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace GC.Seifert.SaddleSlabProof

def gapBump (p q s : ℝ) : ℝ := Real.smoothTransition (s - p) * Real.smoothTransition (q - s)

theorem contDiff_gapBump (p q : ℝ) : ContDiff ℝ ∞ (gapBump p q) :=
  ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id))

theorem gapBump_nonneg (p q s : ℝ) : 0 ≤ gapBump p q s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem gapBump_pos {p q s : ℝ} (hs : s ∈ Ioo p q) : 0 < gapBump p q s :=
  mul_pos (Real.smoothTransition.pos_of_pos (by linarith [hs.1]))
    (Real.smoothTransition.pos_of_pos (by linarith [hs.2]))

theorem gapBump_eq_zero_of_le {p q s : ℝ} (hs : s ≤ p) : gapBump p q s = 0 := by
  unfold gapBump
  rw [Real.smoothTransition.zero_of_nonpos (show s - p ≤ 0 by linarith), zero_mul]

theorem gapBump_eq_zero_of_ge {p q s : ℝ} (hs : q ≤ s) : gapBump p q s = 0 := by
  unfold gapBump
  rw [Real.smoothTransition.zero_of_nonpos (show q - s ≤ 0 by linarith), mul_zero]

theorem contDiff_bump_mul_deriv {g l : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hg : ContDiffOn ℝ ∞ g J) (hl : ContDiff ℝ ∞ l) (hlJ : tsupport l ⊆ J) :
    ContDiff ℝ ∞ (fun s => l s * deriv g s) := by
  have hg' : ContDiffOn ℝ ∞ (deriv g) J := hg.deriv_of_isOpen hJ (by simp)
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ J
  · exact hl.contDiffAt.mul (hg'.contDiffAt (hJ.mem_nhds hs))
  · have hs' : s ∉ tsupport l := fun h => hs (hlJ h)
    have hev : (fun s => l s * deriv g s) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport l).isOpen_compl.mem_nhds hs'] with x hx
      simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem bump_mul_deriv_nonneg {g l : ℝ → ℝ} {J : Set ℝ} (hl : ∀ s, 0 ≤ l s ∧ l s ≤ 1)
    (hlJ : tsupport l ⊆ J) (hpos : ∀ t ∈ J, 0 < deriv g t) (s : ℝ) :
    0 ≤ l s * deriv g s := by
  rcases (hl s).1.lt_or_eq with h | h
  · exact mul_nonneg h.le (hpos s (hlJ (subset_tsupport l (ne_of_gt h)))).le
  · rw [← h, zero_mul]

theorem exists_two_piece_lift {g₁ g₂ : ℝ → ℝ} {J₁ J₂ : Set ℝ} {p₀ p₁ q₀ q₁ : ℝ}
    (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂) (hp : p₀ ≤ p₁) (hpq : p₁ < q₀) (hq : q₀ ≤ q₁)
    (hJp : Icc p₀ p₁ ⊆ J₁) (hJq : Icc q₀ q₁ ⊆ J₂) (hg₁ : ContDiffOn ℝ ∞ g₁ J₁)
    (hg₂ : ContDiffOn ℝ ∞ g₂ J₂) (hpos₁ : ∀ t ∈ J₁, 0 < deriv g₁ t)
    (hpos₂ : ∀ t ∈ J₂, 0 < deriv g₂ t) (hgap : g₁ p₁ < g₂ q₀) :
    ∃ G : ℝ → ℝ, ∃ δ > 0, ContDiff ℝ ∞ G ∧ (∀ t ∈ Ioo (p₀ - δ) (q₁ + δ), 0 < deriv G t) ∧
      EqOn G g₁ (Icc p₀ p₁) ∧ EqOn G g₂ (Icc q₀ q₁) := by
  obtain ⟨ρ₁, hρ₁, hJρ₁⟩ := exists_Icc_margin hJ₁ hJp hp
  obtain ⟨ρ₂, hρ₂, hJρ₂⟩ := exists_Icc_margin hJ₂ hJq hq
  have hp₁J : p₁ ∈ J₁ := hJp ⟨hp, le_rfl⟩
  have hq₀J : q₀ ∈ J₂ := hJq ⟨le_rfl, hq⟩
  set η := (g₂ q₀ - g₁ p₁) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨δ₁, hδ₁, hc₁⟩ := Metric.continuousAt_iff.mp
    (hg₁.continuousOn.continuousAt (hJ₁.mem_nhds hp₁J)) η hηpos
  obtain ⟨δ₂, hδ₂, hc₂⟩ := Metric.continuousAt_iff.mp
    (hg₂.continuousOn.continuousAt (hJ₂.mem_nhds hq₀J)) η hηpos
  set δ := min (min (min ρ₁ ρ₂) (min δ₁ δ₂)) ((q₀ - p₁) / 8) / 4 with hδdef
  have hm : 0 < min (min (min ρ₁ ρ₂) (min δ₁ δ₂)) ((q₀ - p₁) / 8) :=
    lt_min (lt_min (lt_min hρ₁ hρ₂) (lt_min hδ₁ hδ₂)) (by linarith)
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hle := min_le_left (min (min ρ₁ ρ₂) (min δ₁ δ₂)) ((q₀ - p₁) / 8)
  have hle' := min_le_right (min (min ρ₁ ρ₂) (min δ₁ δ₂)) ((q₀ - p₁) / 8)
  have hδρ₁ : 2 * δ < ρ₁ := by
    have := (min_le_left (min ρ₁ ρ₂) (min δ₁ δ₂)).trans (min_le_left ρ₁ ρ₂)
    linarith
  have hδρ₂ : 2 * δ < ρ₂ := by
    have := (min_le_left (min ρ₁ ρ₂) (min δ₁ δ₂)).trans (min_le_right ρ₁ ρ₂)
    linarith
  have hδδ₁ : 2 * δ < δ₁ := by
    have := (min_le_right (min ρ₁ ρ₂) (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂)
    linarith
  have hδδ₂ : 2 * δ < δ₂ := by
    have := (min_le_right (min ρ₁ ρ₂) (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂)
    linarith
  have hδgap : 8 * δ < q₀ - p₁ := by linarith
  obtain ⟨l₁, hl₁, hl₁01, hl₁1, hl₁supp⟩ := exists_bump (u₀ := p₀ - δ) (u₁ := p₁) (by linarith)
    (show 0 < 2 * δ by linarith)
  obtain ⟨l₂, hl₂, hl₂01, hl₂1, hl₂supp⟩ := exists_bump (u₀ := q₀) (u₁ := q₁ + δ) (by linarith)
    (show 0 < 2 * δ by linarith)
  have hl₁J : tsupport l₁ ⊆ J₁ := hl₁supp.trans fun x hx =>
    hJρ₁ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hl₂J : tsupport l₂ ⊆ J₂ := hl₂supp.trans fun x hx =>
    hJρ₂ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hl₁z : ∀ s, p₁ + δ < s → l₁ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => by linarith [(hl₁supp h).2]
  have hl₂z : ∀ s, s < q₀ - δ → l₂ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => by linarith [(hl₂supp h).1]
  set φ₁ : ℝ → ℝ := fun s => l₁ s * deriv g₁ s with hφ₁
  set φ₂ : ℝ → ℝ := fun s => l₂ s * deriv g₂ s with hφ₂
  have hφ₁c : ContDiff ℝ ∞ φ₁ := contDiff_bump_mul_deriv hJ₁ hg₁ hl₁ hl₁J
  have hφ₂c : ContDiff ℝ ∞ φ₂ := contDiff_bump_mul_deriv hJ₂ hg₂ hl₂ hl₂J
  have hφ₁n : ∀ s, 0 ≤ φ₁ s := bump_mul_deriv_nonneg hl₁01 hl₁J hpos₁
  have hφ₂n : ∀ s, 0 ≤ φ₂ s := bump_mul_deriv_nonneg hl₂01 hl₂J hpos₂
  have hg₁d : ∀ x ∈ J₁, HasDerivAt g₁ (deriv g₁ x) x := fun x hx =>
    ((hg₁.contDiffAt (hJ₁.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hg₂d : ∀ x ∈ J₂, HasDerivAt g₂ (deriv g₂ x) x := fun x hx =>
    ((hg₂.contDiffAt (hJ₂.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hg₁' : ContinuousOn (deriv g₁) J₁ := hg₁.continuousOn_deriv_of_isOpen hJ₁ (by simp)
  have hg₂' : ContinuousOn (deriv g₂) J₂ := hg₂.continuousOn_deriv_of_isOpen hJ₂ (by simp)
  have hA₁ : ∫ s in p₁..q₀, φ₁ s ≤ g₁ (p₁ + 2 * δ) - g₁ p₁ := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (b := p₁ + 2 * δ)
      (μ := MeasureTheory.volume) (hφ₁c.continuous.intervalIntegrable p₁ (p₁ + 2 * δ))
      (hφ₁c.continuous.intervalIntegrable (p₁ + 2 * δ) q₀)
    have hz : ∫ s in p₁ + 2 * δ..q₀, φ₁ s = 0 := by
      rw [← intervalIntegral.integral_zero (a := p₁ + 2 * δ) (b := q₀)
        (μ := MeasureTheory.volume) (E := ℝ)]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by linarith)] at hs
      simp only [hφ₁, hl₁z s (by linarith [hs.1]), zero_mul]
    have hsub : uIcc p₁ (p₁ + 2 * δ) ⊆ J₁ := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => hJρ₁ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmono : ∫ s in p₁..p₁ + 2 * δ, φ₁ s ≤ ∫ s in p₁..p₁ + 2 * δ, deriv g₁ s :=
      intervalIntegral.integral_mono_on (by linarith)
        (hφ₁c.continuous.intervalIntegrable _ _) ((hg₁'.mono hsub).intervalIntegrable)
        fun s hs => by
          have h1 := hpos₁ s (hsub (by rw [uIcc_of_le (by linarith)]; exact hs))
          have h2 := hl₁01 s
          simp only [hφ₁]
          nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hg₁d x (hsub hx))
      ((hg₁'.mono hsub).intervalIntegrable)] at hmono
    rw [← hsplit, hz, add_zero]
    exact hmono
  have hA₂ : ∫ s in p₁..q₀, φ₂ s ≤ g₂ q₀ - g₂ (q₀ - 2 * δ) := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (b := q₀ - 2 * δ)
      (μ := MeasureTheory.volume) (hφ₂c.continuous.intervalIntegrable p₁ (q₀ - 2 * δ))
      (hφ₂c.continuous.intervalIntegrable (q₀ - 2 * δ) q₀)
    have hz : ∫ s in p₁..q₀ - 2 * δ, φ₂ s = 0 := by
      rw [← intervalIntegral.integral_zero (a := p₁) (b := q₀ - 2 * δ)
        (μ := MeasureTheory.volume) (E := ℝ)]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by linarith)] at hs
      simp only [hφ₂, hl₂z s (by linarith [hs.2]), zero_mul]
    have hsub : uIcc (q₀ - 2 * δ) q₀ ⊆ J₂ := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => hJρ₂ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmono : ∫ s in q₀ - 2 * δ..q₀, φ₂ s ≤ ∫ s in q₀ - 2 * δ..q₀, deriv g₂ s :=
      intervalIntegral.integral_mono_on (by linarith)
        (hφ₂c.continuous.intervalIntegrable _ _) ((hg₂'.mono hsub).intervalIntegrable)
        fun s hs => by
          have h1 := hpos₂ s (hsub (by rw [uIcc_of_le (by linarith)]; exact hs))
          have h2 := hl₂01 s
          simp only [hφ₂]
          nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hg₂d x (hsub hx))
      ((hg₂'.mono hsub).intervalIntegrable)] at hmono
    rw [← hsplit, hz, zero_add]
    exact hmono
  have hgc₁ : g₁ (p₁ + 2 * δ) - g₁ p₁ < η := by
    have h := hc₁ (x := p₁ + 2 * δ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  have hgc₂ : g₂ q₀ - g₂ (q₀ - 2 * δ) < η := by
    have h := hc₂ (x := q₀ - 2 * δ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  set A := ∫ s in p₁..q₀, (φ₁ s + φ₂ s) with hA
  have hAlt : A < g₂ q₀ - g₁ p₁ := by
    rw [hA, intervalIntegral.integral_add (hφ₁c.continuous.intervalIntegrable _ _)
      (hφ₂c.continuous.intervalIntegrable _ _)]
    linarith
  set P := ∫ s in p₁..q₀, gapBump p₁ q₀ s with hP
  have hPpos : 0 < P :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((contDiff_gapBump p₁ q₀).continuous.intervalIntegrable _ _) (fun x hx => gapBump_pos hx)
      hpq
  set μ := (g₂ q₀ - g₁ p₁ - A) / P with hμ
  have hμpos : 0 < μ := div_pos (by linarith) hPpos
  set d : ℝ → ℝ := fun s => φ₁ s + φ₂ s + μ * gapBump p₁ q₀ s with hd
  have hdc : ContDiff ℝ ∞ d := (hφ₁c.add hφ₂c).add (contDiff_const.mul (contDiff_gapBump _ _))
  set G : ℝ → ℝ := fun t => g₁ p₀ + ∫ s in p₀..t, d s with hG
  have hGd : ∀ t, HasDerivAt G (d t) t := fun t =>
    ((hdc.continuous.integral_hasStrictDerivAt p₀ t).hasDerivAt).const_add (g₁ p₀)
  have hGderiv : deriv G = d := funext fun t => (hGd t).deriv
  have hdeq₁ : ∀ s ∈ Icc (p₀ - δ) p₁, d s = deriv g₁ s := by
    intro s hs
    simp only [hd, hφ₁, hφ₂, hl₁1 s hs, hl₂z s (by linarith [hs.2]),
      gapBump_eq_zero_of_le hs.2, one_mul, zero_mul, mul_zero, add_zero]
  have hdeq₂ : ∀ s ∈ Icc q₀ (q₁ + δ), d s = deriv g₂ s := by
    intro s hs
    simp only [hd, hφ₁, hφ₂, hl₂1 s hs, hl₁z s (by linarith [hs.1]),
      gapBump_eq_zero_of_ge hs.1, one_mul, zero_mul, mul_zero, add_zero, zero_add]
  have hGeq₁ : EqOn G g₁ (Icc p₀ p₁) := by
    intro t ht
    have hsub : uIcc p₀ t ⊆ Icc p₀ p₁ := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hc : ∫ s in p₀..t, d s = ∫ s in p₀..t, deriv g₁ s :=
      intervalIntegral.integral_congr fun s hs => hdeq₁ s
        ⟨by linarith [(hsub hs).1], (hsub hs).2⟩
    simp only [hG]
    rw [hc, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hg₁d x (hJp (hsub hx)))
      ((hg₁'.mono (hsub.trans hJp)).intervalIntegrable)]
    ring
  have hGq₀ : G q₀ = g₂ q₀ := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hdc.continuous.intervalIntegrable p₀ p₁) (hdc.continuous.intervalIntegrable p₁ q₀)
    have hGp₁ := hGeq₁ ⟨hp, le_rfl⟩
    simp only [hG] at hGp₁ ⊢
    have hgap' : ∫ s in p₁..q₀, d s = A + μ * P := by
      simp only [hd]
      rw [intervalIntegral.integral_add (f := fun s => φ₁ s + φ₂ s)
        (g := fun s => μ * gapBump p₁ q₀ s)
        ((hφ₁c.add hφ₂c).continuous.intervalIntegrable _ _)
        ((continuous_const.mul (contDiff_gapBump _ _).continuous).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
    rw [← hadd, ← add_assoc, hGp₁, hgap', hμ]
    field_simp
    ring
  have hGeq₂ : EqOn G g₂ (Icc q₀ q₁) := by
    intro t ht
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hdc.continuous.intervalIntegrable p₀ q₀) (hdc.continuous.intervalIntegrable q₀ t)
    have hsub : uIcc q₀ t ⊆ Icc q₀ q₁ := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hc : ∫ s in q₀..t, d s = ∫ s in q₀..t, deriv g₂ s :=
      intervalIntegral.integral_congr fun s hs => hdeq₂ s
        ⟨(hsub hs).1, by linarith [(hsub hs).2]⟩
    have hGq₀' := hGq₀
    simp only [hG] at hGq₀' ⊢
    rw [← hadd, ← add_assoc, hGq₀', hc,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hg₂d x (hJq (hsub hx)))
      ((hg₂'.mono (hsub.trans hJq)).intervalIntegrable)]
    ring
  refine ⟨G, δ, hδ, contDiff_infty_iff_deriv.mpr ⟨fun t => (hGd t).differentiableAt,
    hGderiv ▸ hdc⟩, fun t ht => ?_, hGeq₁, hGeq₂⟩
  rw [hGderiv]
  rcases le_or_gt t p₁ with h1 | h1
  · rw [hdeq₁ t ⟨ht.1.le, h1⟩]
    exact hpos₁ t (hJρ₁ ⟨by linarith [ht.1], by linarith⟩)
  · rcases lt_or_ge t q₀ with h2 | h2
    · have h3 := gapBump_pos (show t ∈ Ioo p₁ q₀ from ⟨h1, h2⟩)
      simp only [hd]
      nlinarith [hφ₁n t, hφ₂n t]
    · rw [hdeq₂ t ⟨h2, ht.2.le⟩]
      exact hpos₂ t (hJρ₂ ⟨by linarith, by linarith [ht.2]⟩)

end GC.Seifert.SaddleSlabProof
