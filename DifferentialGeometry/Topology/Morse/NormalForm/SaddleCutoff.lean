import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import DifferentialGeometry.Topology.Diffeomorph.SaddleFiberFlow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Set Metric Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE
  (saddleBandCurve saddleBandCurve_zero saddleBandCurve_height saddleBandCurve_reverse)

namespace DifferentialGeometry.Topology.Morse

private theorem saddle_cutoff_height_pos_of_ne_zero
    {s h t₀ ε t u : ℝ} {θ : ℝ × ℝ → ℝ}
    (hs : 0 < s) (ht₀ : 0 < t₀) (hε : ε < s * h ^ 2 / 16)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (ht : -ε ≤ t) (hu : |u| ≤ h) (hne : θ (t, u) * (t₀ - t) ≠ 0) :
    0 < t + s * u ^ 2 := by
  by_cases htime : t ≤ t₀ / 4
  · have houter : h / 4 < |u| := lt_of_not_ge (fun hsmall => by
      apply hne
      rw [hθ0 t u htime hsmall, zero_mul])
    have hnonneg : 0 ≤ h := (abs_nonneg u).trans hu
    have hsq : h ^ 2 / 16 ≤ u ^ 2 := by
      nlinarith only [houter, hnonneg, sq_abs u, abs_nonneg u]
    have hmul := mul_le_mul_of_nonneg_left hsq hs.le
    linarith only [ht, hε, hmul]
  · have htime' : t₀ / 4 < t := lt_of_not_ge htime
    have hterm := mul_nonneg hs.le (sq_nonneg u)
    linarith only [htime', ht₀, hterm]

private theorem saddle_cutoff_filled_preimage
    {s h t₀ ε t : ℝ} {θ : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hs : 0 < s) (hh : h < 1) (ht₀ : 0 < t₀) (hε : ε < s * h ^ 2 / 16)
    (hθ01 : ∀ p, θ p ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (ht : t ∈ Icc (-ε) t₀) (hu : |y.1| ≤ h)
    (hlower : s + t + θ (t, y.1) * (t₀ - t) ≤
      (1 - y.1 ^ 2) * (y.2 ^ 2 + 2 * s) / 2)
    (hupper : (1 - y.1 ^ 2) * (y.2 ^ 2 + 2 * s) / 2 ≤ s + t₀) :
    let z := saddleBandCurve y (-(θ (t, y.1) * (t₀ - t)))
    z.1 = y.1 ∧
      (θ (t, y.1) * (t₀ - t) = 0 ∨
        (y.2 ≠ 0 ∧ 0 < 1 + 2 * (1 - y.1 ^ 2)⁻¹ *
          (-(θ (t, y.1) * (t₀ - t))) / y.2 ^ 2)) ∧
      s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤
        s + t + (1 - θ (t, z.1)) * (t₀ - t) ∧
      saddleBandCurve z (θ (t, z.1) * (t₀ - t)) = y := by
  intro z
  by_cases hzero : θ (t, y.1) * (t₀ - t) = 0
  · have hzy : z = y := by dsimp only [z]; rw [hzero, neg_zero, saddleBandCurve_zero]
    rw [hzy]
    refine ⟨rfl, Or.inl hzero, ?_, ?_, ?_⟩
    · simpa only [hzero, add_zero] using hlower
    · have heq : s + t + (1 - θ (t, y.1)) * (t₀ - t) = s + t₀ := by
        nlinarith only [hzero]
      rwa [heq]
    · rw [hzero, saddleBandCurve_zero]
  · have htreg := saddle_cutoff_height_pos_of_ne_zero hs ht₀ hε hθ0 ht.1 hu hzero
    have hden : 0 < 1 - y.1 ^ 2 := by
      have huy := abs_lt.mp (hu.trans_lt hh)
      nlinarith only [huy.1, huy.2]
    have hshift : 0 ≤ θ (t, y.1) * (t₀ - t) :=
      mul_nonneg (hθ01 _).1 (sub_nonneg.mpr ht.2)
    have hnum : 0 < (1 - y.1 ^ 2) * y.2 ^ 2 - 2 * (θ (t, y.1) * (t₀ - t)) := by
      nlinarith only [hlower, htreg]
    have hv : y.2 ≠ 0 := by
      intro hv
      norm_num [hv] at hnum
      linarith only [hnum, hshift]
    have hrad : 0 < 1 + 2 * (1 - y.1 ^ 2)⁻¹ *
        (-(θ (t, y.1) * (t₀ - t))) / y.2 ^ 2 := by
      have heq : 1 + 2 * (1 - y.1 ^ 2)⁻¹ *
          (-(θ (t, y.1) * (t₀ - t))) / y.2 ^ 2 =
          ((1 - y.1 ^ 2) * y.2 ^ 2 - 2 * (θ (t, y.1) * (t₀ - t))) /
            ((1 - y.1 ^ 2) * y.2 ^ 2) := by
        field_simp
        ring
      rw [heq]
      exact div_pos hnum (mul_pos hden (sq_pos_of_ne_zero hv))
    have henergy : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 =
        (1 - y.1 ^ 2) * (y.2 ^ 2 + 2 * s) / 2 - θ (t, y.1) * (t₀ - t) := by
      dsimp only [z]
      simpa only [zero_add, sub_eq_add_neg] using saddleBandCurve_height hden.ne' hv hrad.le 0 s
    refine ⟨rfl, Or.inr ⟨hv, hrad⟩, ?_, ?_, ?_⟩
    · rw [henergy]
      linarith only [hlower]
    · rw [henergy]
      change _ ≤ s + t + (1 - θ (t, y.1)) * (t₀ - t)
      nlinarith only [hupper]
    · change saddleBandCurve (saddleBandCurve y (-(θ (t, y.1) * (t₀ - t))))
        (θ (t, y.1) * (t₀ - t)) = y
      simpa only [neg_neg] using saddleBandCurve_reverse hrad

theorem image_saddle_band_cutoff_region
    {s h t₀ ε t : ℝ} {θ : ℝ × ℝ → ℝ}
    (hs : 0 < s) (hh : h < 1) (ht₀ : 0 < t₀) (hε : ε < s * h ^ 2 / 16)
    (hθ01 : ∀ p, θ p ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (ht : t ∈ Icc (-ε) t₀) :
    (fun z : ℝ × ℝ => saddleBandCurve z (θ (t, z.1) * (t₀ - t))) ''
      {z : ℝ × ℝ | |z.1| ≤ h ∧
        s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤
          s + t + (1 - θ (t, z.1)) * (t₀ - t)} =
      {y : ℝ × ℝ | |y.1| ≤ h ∧
        s + t + θ (t, y.1) * (t₀ - t) ≤
          (1 - y.1 ^ 2) * (y.2 ^ 2 + 2 * s) / 2 ∧
        (1 - y.1 ^ 2) * (y.2 ^ 2 + 2 * s) / 2 ≤ s + t₀} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have henergy :
        (1 - (saddleBandCurve z (θ (t, z.1) * (t₀ - t))).1 ^ 2) *
          ((saddleBandCurve z (θ (t, z.1) * (t₀ - t))).2 ^ 2 + 2 * s) / 2 =
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 + θ (t, z.1) * (t₀ - t) := by
      by_cases hzero : θ (t, z.1) * (t₀ - t) = 0
      · rw [hzero, saddleBandCurve_zero, add_zero]
      · have htreg := saddle_cutoff_height_pos_of_ne_zero hs ht₀ hε hθ0 ht.1 hz.1 hzero
        have hden : 0 < 1 - z.1 ^ 2 := by
          have huz := abs_lt.mp (hz.1.trans_lt hh)
          nlinarith only [huz.1, huz.2]
        have hv : z.2 ≠ 0 := by
          intro hv
          have hlower := hz.2.1
          norm_num [hv] at hlower
          nlinarith only [hlower, htreg]
        have hrad : 0 ≤ 1 + 2 * (1 - z.1 ^ 2)⁻¹ *
            (θ (t, z.1) * (t₀ - t)) / z.2 ^ 2 := by
          have hshift := mul_nonneg (hθ01 (t, z.1)).1 (sub_nonneg.mpr ht.2)
          positivity
        simpa only [zero_add] using saddleBandCurve_height hden.ne' hv hrad 0 s
    refine ⟨hz.1, ?_, ?_⟩
    · change s + t + θ (t, z.1) * (t₀ - t) ≤ _
      rw [henergy]
      linarith only [hz.2.1]
    · rw [henergy]
      nlinarith only [hz.2.2]
  · intro hy
    obtain ⟨hfst, _, hlower, hupper, hforward⟩ :=
      saddle_cutoff_filled_preimage hs hh ht₀ hε hθ01 hθ0 ht hy.1 hy.2.1 hy.2.2
    exact ⟨saddleBandCurve y (-(θ (t, y.1) * (t₀ - t))),
      ⟨by rw [hfst]; exact hy.1, hlower, hupper⟩, hforward⟩


theorem saddleBandLevelCurve_mem_image_cutoff_region
    {s h t₀ ε t σ u : ℝ} {θ : ℝ × ℝ → ℝ}
    (hs : 0 < s) (hh : h < 1) (ht₀ : 0 < t₀) (hε : ε < s * h ^ 2 / 16)
    (hθ01 : ∀ p, θ p ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (ht : t ∈ Icc (-ε) t₀) (hu : |u| ≤ h) (hσ : σ ^ 2 = 1) :
    saddleBandLevelCurve s t₀ σ u ∈
      (fun z : ℝ × ℝ => saddleBandCurve z (θ (t, z.1) * (t₀ - t))) ''
        {z : ℝ × ℝ | |z.1| ≤ h ∧
          s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤
            s + t + (1 - θ (t, z.1)) * (t₀ - t)} := by
  rw [image_saddle_band_cutoff_region hs hh ht₀ hε hθ01 hθ0 ht]
  have hheight := saddleBandLevelCurve_height_of_nonneg
    (add_nonneg ht₀.le (mul_nonneg hs.le (sq_nonneg u))) hσ
    (abs_lt.mp (hu.trans_lt hh)) (0 : ℝ)
  simp only [zero_add] at hheight
  refine ⟨hu, ?_, hheight.le⟩
  change s + t + θ (t, u) * (t₀ - t) ≤ _
  rw [hheight]
  have hmul := mul_le_mul_of_nonneg_right (hθ01 (t, u)).2 (sub_nonneg.mpr ht.2)
  linarith only [hmul]

theorem exists_partialDiffeomorph_saddle_band_cutoff_profile_superlevel {s h t₀ : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (ht₀ : 0 < t₀) :
    ∃ δ > 0, δ < t₀ / 4 ∧ δ < s * h ^ 2 / 16 ∧
      ∃ θ ψ : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ψ ∧
        (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p, ψ p = θ p * (t₀ - p.1)) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport ψ) ∧
        ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
          (∀ t u, θ (t, u) = 1 -
            (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
        ∃ D : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ))
            𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ∞,
          (∀ p ∈ D.source, (p.1, p.2.1) ∉ tsupport
              (fun q : (ℝ × ℝ) × ℝ => q.1.1 * ψ (q.1.2, q.2)) ∨
            (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
              0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1.1 * ψ (p.1.2, p.2.1)) /
                p.2.2 ^ 2)) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 → ((r, t), z) ∈ D.source) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
            (t, (D ((r, t), z)).2.1) ∉ tsupport θ ∨
              (1 - (D ((r, t), z)).2.1 ^ 2) * (D ((r, t), z)).2.2 ≠ 0) ∧
          (∀ p, D p = (p.1, saddleBandCurve p.2 (p.1.1 * ψ (p.1.2, p.2.1)))) ∧
          (∀ p, D.symm p = (p.1, saddleBandCurve p.2 (-(p.1.1 * ψ (p.1.2, p.2.1))))) ∧
          D '' (D.source ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1.2}) =
            D.target ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 =
              s + p.1.2 + p.1.1 * ψ (p.1.2, p.2.1)} := by
  let β : ContDiffBump (0 : ℝ) := ⟨h / 4, h / 2, by positivity, by linarith⟩
  let χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (t₀ / 4))
  have hχ01 (t : ℝ) : χ t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hχ0 (t : ℝ) (ht : t ≤ t₀ / 4) : χ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) (by positivity))
  have hχ1 (t : ℝ) (ht : t₀ / 2 ≤ t) : χ t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : 0 < t₀ / 4)).mpr
      (by linarith))
  let θ : ℝ × ℝ → ℝ := fun p => 1 - (1 - χ p.1) * β p.2
  let ψ : ℝ × ℝ → ℝ := fun p => θ p * (t₀ - p.1)
  have hθ : ContDiff ℝ ∞ θ :=
    contDiff_const.sub ((contDiff_const.sub (hχ.comp contDiff_fst)).mul
      (β.contDiff.comp contDiff_snd))
  have hψ : ContDiff ℝ ∞ ψ := hθ.mul (contDiff_const.sub contDiff_fst)
  have hθ01 (p : ℝ × ℝ) : θ p ∈ Icc (0 : ℝ) 1 := by
    have hb0 : 0 ≤ β p.2 := β.nonneg
    have hb1 : β p.2 ≤ 1 := β.le_one
    have hc := hχ01 p.1
    have hp0 := mul_nonneg (sub_nonneg.mpr hc.2) hb0
    have hp1 : (1 - χ p.1) * β p.2 ≤ 1 :=
      mul_le_one₀ (by linarith [hc.1]) hb0 hb1
    dsimp only [θ]
    constructor <;> linarith
  have hθ0 (t u : ℝ) (ht : t ≤ t₀ / 4) (hu : |u| ≤ h / 4) : θ (t, u) = 0 := by
    have hβ : β u = 1 := β.one_of_mem_closedBall (by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hu)
    simp only [θ, hχ0 t ht, hβ, sub_zero, mul_one, sub_self]
  have hθ1 (t u : ℝ) (hp : t₀ / 2 ≤ t ∨ h / 2 ≤ |u|) : θ (t, u) = 1 := by
    rcases hp with ht | hu
    · simp only [θ, hχ1 t ht, sub_self, zero_mul, sub_zero]
    · have hβ : β u = 0 := β.zero_of_le_dist (by
        simpa only [Real.dist_eq, sub_zero] using hu)
      simp only [θ, hβ, mul_zero, sub_zero]
  have hzeroθ (t u : ℝ) (ht : t < t₀ / 4) (hu : |u| < h / 4) :
      (t, u) ∉ tsupport θ := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have htn : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, u), p.1 < t₀ / 4 :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds ht
    have hun : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, u), |p.2| < h / 4 :=
      (isOpen_lt continuous_snd.abs continuous_const).mem_nhds hu
    filter_upwards [htn, hun] with p hpt hpu
    exact hθ0 p.1 p.2 hpt.le hpu.le
  have hzero (t u : ℝ) (ht : t < t₀ / 4) (hu : |u| < h / 4) :
      (t, u) ∉ tsupport ψ :=
    fun hp => hzeroθ t u ht hu (tsupport_mul_subset_left hp)
  obtain ⟨δ, hδ, hδupper⟩ := exists_between
    (lt_min (by positivity : 0 < t₀ / 4) (by positivity : 0 < s * h ^ 2 / 16))
  have hδt : δ < t₀ / 4 := hδupper.trans_le (min_le_left _ _)
  have hδh : δ < s * h ^ 2 / 16 := hδupper.trans_le (min_le_right _ _)
  let U : Set (ℝ × (ℝ × ℝ)) := {p | (p.1, p.2.1) ∉ tsupport θ ∨
    (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2)}
  have hgraphdom : ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 → (t, z) ∈ U := by
    intro t ht z hz hgraph
    by_cases hcore : t < t₀ / 4 ∧ |z.1| < h / 4
    · exact Or.inl (hzeroθ t z.1 hcore.1 hcore.2)
    · have hzu : 1 - z.1 ^ 2 > 0 := by
        have hz1 : |z.1| < 1 := hz.trans_lt hh1
        nlinarith [sq_abs z.1, (abs_lt.mp hz1).1, (abs_lt.mp hz1).2]
      have hregular : 0 < t + s * z.1 ^ 2 := by
        by_cases htime : t < t₀ / 4
        · have huz : h / 4 ≤ |z.1| := le_of_not_gt (fun hu => hcore ⟨htime, hu⟩)
          have hsq : h ^ 2 / 16 ≤ z.1 ^ 2 := by nlinarith [sq_abs z.1, abs_nonneg z.1]
          have hmul := mul_le_mul_of_nonneg_left hsq hs.le
          nlinarith
        · have htime' : t₀ / 4 ≤ t := le_of_not_gt htime
          have hterm := mul_nonneg hs.le (sq_nonneg z.1)
          linarith
      have hzv : z.2 ≠ 0 := by
        intro hv
        rw [hv] at hgraph
        nlinarith
      have hrad : 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * ψ (t, z.1) / z.2 ^ 2 := by
        by_cases htime : t ≤ t₀
        · have hψnonneg : 0 ≤ ψ (t, z.1) :=
            mul_nonneg (hθ01 (t, z.1)).1 (sub_nonneg.mpr htime)
          have hterm : 0 ≤ 2 * (1 - z.1 ^ 2)⁻¹ * ψ (t, z.1) / z.2 ^ 2 := by positivity
          linarith
        · have htime' : t₀ < t := lt_of_not_ge htime
          have hψeq : ψ (t, z.1) = t₀ - t := by
            change θ (t, z.1) * (t₀ - t) = _
            rw [hθ1 t z.1 (Or.inl (by linarith)), one_mul]
          have hid : (1 + 2 * (1 - z.1 ^ 2)⁻¹ * ψ (t, z.1) / z.2 ^ 2) *
              ((1 - z.1 ^ 2) * z.2 ^ 2) = (1 - z.1 ^ 2) * z.2 ^ 2 + 2 * ψ (t, z.1) := by
            field_simp
          have hprod : 0 < (1 + 2 * (1 - z.1 ^ 2)⁻¹ * ψ (t, z.1) / z.2 ^ 2) *
              ((1 - z.1 ^ 2) * z.2 ^ 2) := by
            rw [hid, hψeq]
            nlinarith [mul_nonneg hs.le (sq_nonneg z.1)]
          exact (mul_pos_iff_of_pos_right (mul_pos hzu (sq_pos_of_ne_zero hzv))).mp hprod
      exact Or.inr ⟨hzu.ne', hzv, hrad⟩
  let Ψ : (ℝ × ℝ) × ℝ → ℝ := fun p => p.1.1 * ψ (p.1.2, p.2)
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_fst.fst.mul
    (hψ.comp (contDiff_fst.snd.prodMk contDiff_snd))
  let V : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | (p.1, p.2.1) ∉ tsupport Ψ ∨
    (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * Ψ (p.1, p.2.1) / p.2.2 ^ 2)}
  have hgraphdom_r : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      (t, z.1) ∉ tsupport θ ∨ (1 - z.1 ^ 2 ≠ 0 ∧ z.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (r * ψ (t, z.1)) / z.2 ^ 2) := by
    intro r hr t ht z hz hgraph
    rcases hgraphdom t ht z hz hgraph with hoff | hreg
    · exact Or.inl hoff
    · right
      refine ⟨hreg.1, hreg.2.1, ?_⟩
      have heq : 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (r * ψ (t, z.1)) / z.2 ^ 2 =
          (1 - r) + r * (1 + 2 * (1 - z.1 ^ 2)⁻¹ * ψ (t, z.1) / z.2 ^ 2) := by ring
      rw [heq]
      by_cases hr0 : r = 0
      · simp only [hr0, sub_zero, zero_mul, add_zero, zero_lt_one]
      · have hp := mul_pos (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hreg.2.2
        linarith [hr.2]
  have hVgraph : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 → ((r, t), z) ∈ V := by
    intro r hr t ht z hz hgraph
    rcases hgraphdom_r r hr t ht z hz hgraph with hoff | hreg
    · left
      have hoffψ : (t, z.1) ∉ tsupport ψ :=
        fun hp => hoff (tsupport_mul_subset_left hp)
      rw [notMem_tsupport_iff_eventuallyEq] at hoffψ ⊢
      have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.2, p.2)) := by fun_prop
      have hev := hoffψ.comp_tendsto (hc.tendsto ((r, t), z.1))
      filter_upwards [hev] with p hp
      change ψ (p.1.2, p.2) = 0 at hp
      change p.1.1 * ψ (p.1.2, p.2) = 0
      rw [hp, mul_zero]
    · exact Or.inr hreg
  have hnormalized : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      (t, (saddleBandCurve z (r * ψ (t, z.1))).1) ∉ tsupport θ ∨
        (1 - (saddleBandCurve z (r * ψ (t, z.1))).1 ^ 2) *
          (saddleBandCurve z (r * ψ (t, z.1))).2 ≠ 0 := by
    intro r hr t ht z hz hgraph
    rcases hgraphdom_r r hr t ht z hz hgraph with hoff | hreg
    · exact Or.inl hoff
    · right
      apply mul_ne_zero hreg.1
      exact DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_ne_zero _ hreg.2.1
        (by simpa only [Real.norm_eq_abs, sq_abs] using hreg.2.2)
  obtain ⟨D, hDs, hDt, hDf, hDi⟩ :=
    PartialDiffeomorph.exists_saddleBandCurve_time_change_on hΨ
      (DifferentialGeometry.Analysis.ODE.isOpen_saddleBandCurve_time_change_domain hΨ.continuous)
      (fun p (hp : p ∈ V) => hp)
  refine ⟨δ, hδ, hδt, hδh, θ, ψ, hθ, hψ, hθ01, (fun _ => rfl), hθ0, hθ1,
    hzeroθ, hzero, β, rfl, rfl, (fun _ _ => rfl), D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hDs] at hp
    exact hp
  · simpa only [hDs] using hVgraph
  · intro r hr t ht z hz hgraph
    rw [hDf]
    exact hnormalized r hr t ht z hz hgraph
  · intro p
    rw [hDf]
  · intro p
    rw [hDi]
  · rw [hDf, hDs, hDt]
    apply image_saddleBand_graph_time_change (τ := Prod.snd)
    intro p hp
    rcases hp with hp | hp
    · exact Or.inl (image_eq_zero_of_notMem_tsupport hp)
    · exact Or.inr ⟨hp.1, hp.2.1, hp.2.2.le⟩

theorem exists_partialDiffeomorph_saddle_band_cutoff_profile {s h t₀ : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (ht₀ : 0 < t₀) :
    ∃ δ > 0, δ < t₀ / 4 ∧ δ < s * h ^ 2 / 16 ∧
      ∃ θ ψ : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ψ ∧
        (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p, ψ p = θ p * (t₀ - p.1)) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport ψ) ∧
        ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
          (∀ t u, θ (t, u) = 1 -
            (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
        ∃ D : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ))
            𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ∞,
          (∀ p ∈ D.source, (p.1, p.2.1) ∉ tsupport
              (fun q : (ℝ × ℝ) × ℝ => q.1.1 * ψ (q.1.2, q.2)) ∨
            (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
              0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1.1 * ψ (p.1.2, p.2.1)) /
                p.2.2 ^ 2)) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → ((r, t), z) ∈ D.source) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t →
            (t, (D ((r, t), z)).2.1) ∉ tsupport θ ∨
              (1 - (D ((r, t), z)).2.1 ^ 2) * (D ((r, t), z)).2.2 ≠ 0) ∧
          (∀ p, D p = (p.1, saddleBandCurve p.2 (p.1.1 * ψ (p.1.2, p.2.1)))) ∧
          (∀ p, D.symm p = (p.1, saddleBandCurve p.2 (-(p.1.1 * ψ (p.1.2, p.2.1))))) ∧
          D '' (D.source ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1.2}) =
            D.target ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 =
              s + p.1.2 + p.1.1 * ψ (p.1.2, p.2.1)} := by
  obtain ⟨δ, hδ, hδt, hδh, θ, ψ, hθ, hψ, hθ01, hψeq, hθ0, hθ1, hθzero, hψzero,
      κ, hκin, hκout, hθprofile, D, hDdom, hDsuper, hNsuper, hDf, hDi, hDimage⟩ :=
    exists_partialDiffeomorph_saddle_band_cutoff_profile_superlevel hs hh hh1 ht₀
  refine ⟨δ, hδ, hδt, hδh, θ, ψ, hθ, hψ, hθ01, hψeq, hθ0, hθ1, hθzero, hψzero,
    κ, hκin, hκout, hθprofile, D, hDdom, ?_, ?_, hDf, hDi, hDimage⟩
  · intro r hr t ht z hz hgraph
    exact hDsuper r hr t ht z hz hgraph.ge
  · intro r hr t ht z hz hgraph
    exact hNsuper r hr t ht z hz hgraph.ge

theorem exists_partialDiffeomorph_saddle_band_cutoff {s h t₀ : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (ht₀ : 0 < t₀) :
    ∃ δ > 0, δ < t₀ / 4 ∧ δ < s * h ^ 2 / 16 ∧
      ∃ θ ψ : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ψ ∧
        (∀ p, θ p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p, ψ p = θ p * (t₀ - p.1)) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport ψ) ∧
        ∃ D : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ))
            𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ∞,
          (∀ p ∈ D.source, (p.1, p.2.1) ∉ tsupport
              (fun q : (ℝ × ℝ) × ℝ => q.1.1 * ψ (q.1.2, q.2)) ∨
            (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
              0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1.1 * ψ (p.1.2, p.2.1)) /
                p.2.2 ^ 2)) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → ((r, t), z) ∈ D.source) ∧
          (∀ r ∈ Icc (0 : ℝ) 1, ∀ t ≥ -δ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t →
            (t, (D ((r, t), z)).2.1) ∉ tsupport θ ∨
              (1 - (D ((r, t), z)).2.1 ^ 2) * (D ((r, t), z)).2.2 ≠ 0) ∧
          (∀ p, D p = (p.1, saddleBandCurve p.2 (p.1.1 * ψ (p.1.2, p.2.1)))) ∧
          (∀ p, D.symm p = (p.1, saddleBandCurve p.2 (-(p.1.1 * ψ (p.1.2, p.2.1))))) ∧
          D '' (D.source ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1.2}) =
            D.target ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 =
              s + p.1.2 + p.1.1 * ψ (p.1.2, p.2.1)} := by
  obtain ⟨δ, hδ, hδt, hδh, θ, ψ, hθ, hψ, hθ01, hψeq, hθ0, hθ1, hθzero, hψzero,
      _, _, _, _, D, hD⟩ := exists_partialDiffeomorph_saddle_band_cutoff_profile hs hh hh1 ht₀
  exact ⟨δ, hδ, hδt, hδh, θ, ψ, hθ, hψ, hθ01, hψeq, hθ0, hθ1, hθzero, hψzero, D, hD⟩

end DifferentialGeometry.Topology.Morse
