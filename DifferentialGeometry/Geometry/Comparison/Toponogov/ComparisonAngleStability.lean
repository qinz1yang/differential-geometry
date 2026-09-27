import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set
open scoped Topology

theorem comparisonAngle_uniform_stability_on_side_window
    {Lmin Lmax eta : ℝ} (hmin : 0 < Lmin) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a b c a' b' c' : ℝ,
      a ∈ Icc Lmin Lmax → b ∈ Icc Lmin Lmax → c ∈ Icc 0 (2 * Lmax) →
      a' ∈ Icc Lmin Lmax → b' ∈ Icc Lmin Lmax → c' ∈ Icc 0 (2 * Lmax) →
      |a - a'| < delta → |b - b'| < delta → |c - c'| < delta →
      |comparisonAngle a b c - comparisonAngle a' b' c'| < eta := by
  let K : Set (ℝ × ℝ × ℝ) := Icc Lmin Lmax ×ˢ (Icc Lmin Lmax ×ˢ Icc 0 (2 * Lmax))
  let f : ℝ × ℝ × ℝ → ℝ := fun z => comparisonAngle z.1 z.2.1 z.2.2
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : ContinuousOn f K := by
    intro z hz
    have hzcont : ContinuousAt f z :=
      tendsto_comparisonAngle continuous_fst.continuousAt.tendsto
        (continuous_fst.comp continuous_snd).continuousAt.tendsto
        (continuous_snd.comp continuous_snd).continuousAt.tendsto
        (hmin.trans_le hz.1.1) (hmin.trans_le hz.2.1.1)
    exact hzcont.continuousWithinAt
  obtain ⟨delta, hdelta, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) eta heta
  refine ⟨delta, hdelta, ?_⟩
  intro a b c a' b' c' ha hb hc ha' hb' hc' hab hbb hcc
  have hdist : dist (a, b, c) (a', b', c') < delta := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using ⟨hab, hbb, hcc⟩
  exact hd (a, b, c) ⟨ha, hb, hc⟩ (a', b', c') ⟨ha', hb', hc'⟩ hdist

theorem comparisonAngle_half_lt_of_side_perturbation
    {Lmin Lmax theta : ℝ} (hmin : 0 < Lmin) (htheta : 0 < theta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a b c a' b' c' : ℝ,
      a ∈ Icc Lmin Lmax → b ∈ Icc Lmin Lmax → c ∈ Icc 0 (2 * Lmax) →
      a' ∈ Icc Lmin Lmax → b' ∈ Icc Lmin Lmax → c' ∈ Icc 0 (2 * Lmax) →
      |a - a'| < delta → |b - b'| < delta → |c - c'| < delta →
      theta ≤ comparisonAngle a b c → theta / 2 < comparisonAngle a' b' c' := by
  obtain ⟨delta, hdelta, hd⟩ := comparisonAngle_uniform_stability_on_side_window
    (Lmax := Lmax) hmin (half_pos htheta)
  refine ⟨delta, hdelta, ?_⟩
  intro a b c a' b' c' ha hb hc ha' hb' hc' hab hbb hcc hangle
  have hdiff := (abs_lt.mp (hd a b c a' b' c' ha hb hc ha' hb' hc' hab hbb hcc)).2
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

end

section
set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem eventually_comparisonAngle_half_lt_of_sub_tendsto_zero
    {ι : Type*} {f : Filter ι} {a b : ι → ℝ} {r theta : ℝ}
    (hr : 0 < r) (htheta : 0 < theta)
    (ha : ∀ᶠ i in f, 0 ≤ a i ∧ a i ≤ 2 * r)
    (hb : ∀ᶠ i in f, 0 ≤ b i)
    (hclose : Tendsto (fun i => b i - a i) f (𝓝 0))
    (hangle : ∀ᶠ i in f, theta ≤ comparisonAngle r r (a i)) :
    ∀ᶠ i in f, theta / 2 < comparisonAngle r r (b i) := by
  obtain ⟨eta, heta, htransfer⟩ := comparisonAngle_half_lt_of_side_perturbation
    (Lmax := 2 * r) hr htheta
  have herr := Metric.tendsto_nhds.mp hclose (min eta r) (lt_min heta hr)
  filter_upwards [ha, hb, herr, hangle] with i hai hbi hdiff hang
  have habs : |a i - b i| < min eta r := by
    simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hdiff
  have hnear : |a i - b i| < eta := habs.trans_le (min_le_left _ _)
  have hbound : b i ≤ 4 * r := by
    have hh := (abs_lt.mp (habs.trans_le (min_le_right _ _))).1
    linarith [hai.2]
  exact htransfer r r (a i) r r (b i)
    ⟨le_rfl, by linarith⟩ ⟨le_rfl, by linarith⟩ ⟨hai.1, by linarith [hai.2]⟩
    ⟨le_rfl, by linarith⟩ ⟨le_rfl, by linarith⟩ ⟨hbi, by linarith⟩
    (by simpa using heta) (by simpa using heta) hnear hang

end DifferentialGeometry.Geometry.Comparison.Toponogov

end

section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set

theorem exists_opposite_axial_coordinates_threshold
    {D theta : ℝ} (hD : 0 ≤ D) (htheta : 0 < theta) (H : ℝ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ a b c k l : ℝ,
      a ∈ Icc L (2 * L) → b ∈ Icc L (2 * L) → 0 ≤ c →
      |a - (|k|)| ≤ D → |b - (|l|)| ≤ D → |c - (|k - l|)| ≤ D →
      theta ≤ comparisonAngle a b c → k * l < 0 ∧ H ≤ |k| ∧ H ≤ |l| := by
  obtain ⟨eta, heta, hangle⟩ := comparisonAngle_uniform_stability_on_side_window
    (Lmin := (1 : ℝ) / 2) (Lmax := 3) (by norm_num) htheta
  let L₀ := 2 * D + D / eta + |H| + 1
  have hL₀ : 0 < L₀ := by dsimp only [L₀]; positivity
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLL a b c k l ha hb hc hka hlb hkc htheta'
  have hL : 0 < L := hL₀.trans_le hLL
  have hratio : 0 ≤ D / eta := div_nonneg hD heta.le
  have hlarge : 2 * D < L := by dsimp only [L₀] at hLL; linarith [abs_nonneg H]
  have hdelta : D / L < eta := by
    have hlt : D / eta < L := by dsimp only [L₀] at hLL; linarith [abs_nonneg H]
    apply (div_lt_iff₀ hL).mpr
    have hmul := (div_lt_iff₀ heta).mp hlt
    linarith
  have hka' := abs_le.mp hka
  have hlb' := abs_le.mp hlb
  have hkc' := abs_le.mp hkc
  have hkLower : L - D ≤ |k| := by linarith [ha.1]
  have hlLower : L - D ≤ |l| := by linarith [hb.1]
  have hkUpper : |k| ≤ 2 * L + D := by linarith [ha.2]
  have hlUpper : |l| ≤ 2 * L + D := by linarith [hb.2]
  have hkpos : 0 < |k| := by linarith
  have hlpos : 0 < |l| := by linarith
  have hdiffUpper : |k - l| ≤ |k| + |l| := abs_sub k l
  have hcUpper : c ≤ 6 * L := by linarith
  have hsourceA : a / L ∈ Icc ((1 : ℝ) / 2) 3 := by
    constructor
    · apply (le_div_iff₀ hL).mpr; linarith [ha.1]
    · apply (div_le_iff₀ hL).mpr; linarith [ha.2]
  have hsourceB : b / L ∈ Icc ((1 : ℝ) / 2) 3 := by
    constructor
    · apply (le_div_iff₀ hL).mpr; linarith [hb.1]
    · apply (div_le_iff₀ hL).mpr; linarith [hb.2]
  have hsourceC : c / L ∈ Icc 0 (2 * (3 : ℝ)) :=
    ⟨div_nonneg hc hL.le, (div_le_iff₀ hL).mpr (by linarith)⟩
  have htargetA : |k| / L ∈ Icc ((1 : ℝ) / 2) 3 := by
    constructor
    · apply (le_div_iff₀ hL).mpr; linarith
    · apply (div_le_iff₀ hL).mpr; linarith
  have htargetB : |l| / L ∈ Icc ((1 : ℝ) / 2) 3 := by
    constructor
    · apply (le_div_iff₀ hL).mpr; linarith
    · apply (div_le_iff₀ hL).mpr; linarith
  have htargetC : |k - l| / L ∈ Icc 0 (2 * (3 : ℝ)) :=
    ⟨div_nonneg (abs_nonneg _) hL.le, (div_le_iff₀ hL).mpr (by linarith)⟩
  have herror (u v : ℝ) (huv : |u - v| ≤ D) : |u / L - v / L| < eta := by
    rw [← sub_div, abs_div, abs_of_pos hL]
    exact (div_le_div_of_nonneg_right huv hL.le).trans_lt hdelta
  have hclose := hangle (a / L) (b / L) (c / L) (|k| / L) (|l| / L) (|k - l| / L)
    hsourceA hsourceB hsourceC htargetA htargetB htargetC
    (herror a |k| hka) (herror b |l| hlb) (herror c |k - l| hkc)
  have hscale : comparisonAngle (a / L) (b / L) (c / L) = comparisonAngle a b c := by
    simpa only [div_eq_mul_inv, mul_comm] using
      comparisonAngle_scale a b c (inv_pos.mpr hL)
  have hopposite : k * l < 0 := by
    by_contra! hn
    have hsame : |k - l| = |(|k|) - (|l|)| := by
      rcases mul_nonneg_iff.mp hn with ⟨hk, hl⟩ | ⟨hk, hl⟩
      · rw [abs_of_nonneg hk, abs_of_nonneg hl]
      · rw [abs_of_nonpos hk, abs_of_nonpos hl, neg_sub_neg, abs_sub_comm]
    have hc' : |k - l| / L = |(|k|) / L - (|l|) / L| := by
      rw [← sub_div, abs_div, abs_of_pos hL, hsame]
    rw [hscale, hc', comparisonAngle_abs_sub (div_pos hkpos hL) (div_pos hlpos hL),
      sub_zero] at hclose
    exact (not_lt_of_ge htheta') ((le_abs_self _).trans_lt hclose)
  refine ⟨hopposite, ?_, ?_⟩ <;> dsimp only [L₀] at hLL <;> linarith [le_abs_self H]

end DifferentialGeometry.Geometry.Comparison.Toponogov

end
