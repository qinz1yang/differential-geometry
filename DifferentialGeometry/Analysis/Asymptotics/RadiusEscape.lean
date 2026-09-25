import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis

private theorem exists_radius_of_not_eventually_bounded
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {r₀ : ℝ}
    (hsmall : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r₀ → f n y ≤ C)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) :
    ∃ R : ℝ, r₀ ≤ R ∧
      (∀ r : ℝ, r < R → ∃ C : ℝ,
        ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) ∧
      (∀ r : ℝ, R < r → ∀ C : ℝ, ∀ N : ℕ,
        ∃ n, N ≤ n ∧ ∃ y, d n y < ENNReal.ofReal r ∧ C < f n y) := by
  let S : Set ℝ := {r | ∃ C : ℝ,
    ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C}
  have hSne : S.Nonempty := ⟨r₀, hsmall⟩
  obtain ⟨rBad, _, hbad⟩ := hfail
  have hSbdd : BddAbove S := by
    refine ⟨rBad, fun r hr => le_of_not_gt fun hlt => ?_⟩
    apply hbad
    obtain ⟨C, hC⟩ := hr
    refine ⟨C, hC.mono fun n hn y hy => hn y ?_⟩
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hlt.le)
  refine ⟨sSup S, le_csSup hSbdd hsmall, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, hrs⟩ := (lt_csSup_iff hSbdd hSne).mp hr
    obtain ⟨C, hC⟩ := hs
    exact ⟨C, hC.mono fun n hn y hy => hn y
      (hy.trans_le (ENNReal.ofReal_le_ofReal hrs.le))⟩
  · intro r hr C N
    by_contra! h
    have hrS : r ∈ S := ⟨C, eventually_atTop.mpr ⟨N, h⟩⟩
    exact (not_le_of_gt hr) (le_csSup hSbdd hrS)

private theorem abs_sub_lt_div_of_escape_radii {R d : ℝ} {k : ℕ} (hR : 0 < R)
    (hlo : R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ d)
    (hhi : d < R * (((k : ℝ) + 2) / ((k : ℝ) + 1))) :
    |d - R| < R / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hkey1 : R - R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) = R / ((k : ℝ) + 2) := by
    field_simp [hk2]
    ring
  have hkey2 : R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) - R = R / ((k : ℝ) + 1) := by
    field_simp
    ring
  have h1 : R - d ≤ R / ((k : ℝ) + 2) := by linarith
  have h2 : d - R < R / ((k : ℝ) + 1) := by linarith
  have h3 : R / ((k : ℝ) + 2) < R / ((k : ℝ) + 1) :=
    div_lt_div_of_pos_left hR (by positivity) (by linarith)
  rw [abs_lt]
  constructor <;> linarith

theorem exists_subsequence_radius_escape
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsmall : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r₀ → f n y ≤ C)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), r₀ ≤ R ∧ StrictMono ind ∧
      (∀ r : ℝ, r < R → ∃ C : ℝ,
        ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) ∧
      ∃ y : ∀ n, M (ind n),
        (∀ n, d (ind n) (y n) ≠ ⊤) ∧
        Tendsto (fun n => (d (ind n) (y n)).toReal) atTop (𝓝 R) ∧
        Tendsto (fun n => f (ind n) (y n)) atTop atTop := by
  classical
  obtain ⟨R, hR₀, hinner, houter⟩ := exists_radius_of_not_eventually_bounded d f hsmall hfail
  have hR : 0 < R := hr₀.trans_le hR₀
  let rIn (k : ℕ) := R * (((k : ℝ) + 1) / ((k : ℝ) + 2))
  let rOut (k : ℕ) := R * (((k : ℝ) + 2) / ((k : ℝ) + 1))
  have hIn (k : ℕ) : 0 < rIn k ∧ rIn k < R := by
    have hk : ((k : ℝ) + 1) / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    exact ⟨by dsimp [rIn]; positivity, by dsimp [rIn]; nlinarith⟩
  have hOut (k : ℕ) : R < rOut k := by
    have hk : 1 < ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    dsimp [rOut]
    nlinarith
  choose C hC using fun k => hinner (rIn k) (hIn k).2
  choose start hstart using fun k => eventually_atTop.mp (hC k)
  have hgood (k N : ℕ) : ∃ n, N ≤ n ∧ ∃ y,
      ENNReal.ofReal (rIn k) ≤ d n y ∧ d n y < ENNReal.ofReal (rOut k) ∧
      (k : ℝ) < f n y := by
    obtain ⟨n, hn, y, hyd, hyf⟩ := houter (rOut k) (hOut k) (max (C k) k) (max N (start k))
    refine ⟨n, (le_max_left _ _).trans hn, y, ?_, hyd, (le_max_right _ _).trans_lt hyf⟩
    by_contra hlo
    have hs := hstart k n ((le_max_right _ _).trans hn) y (lt_of_not_ge hlo)
    exact (not_lt_of_ge hs) ((le_max_left _ _).trans_lt hyf)
  let base : ℕ := Classical.choose (hgood 0 0)
  let step : ℕ → ℕ → ℕ := fun k prev => Classical.choose (hgood (k + 1) (prev + 1))
  let ind : ℕ → ℕ := fun k => Nat.rec base step k
  have hind (k : ℕ) : ind k < ind (k + 1) :=
    Nat.lt_of_succ_le (Classical.choose_spec (hgood (k + 1) (ind k + 1))).1
  have hpoint (k : ℕ) : ∃ y : M (ind k),
      ENNReal.ofReal (rIn k) ≤ d (ind k) y ∧
      d (ind k) y < ENNReal.ofReal (rOut k) ∧ (k : ℝ) < f (ind k) y := by
    cases k with
    | zero => exact (Classical.choose_spec (hgood 0 0)).2
    | succ k => exact (Classical.choose_spec (hgood (k + 1) (ind k + 1))).2
  choose y hy using hpoint
  have hfinite (k) : d (ind k) (y k) ≠ ⊤ := ne_top_of_lt (hy k).2.1
  have habs (k) : |(d (ind k) (y k)).toReal - R| < R / ((k : ℝ) + 1) := by
    apply abs_sub_lt_div_of_escape_radii hR
    · exact (ENNReal.ofReal_le_iff_le_toReal (hfinite k)).mp (hy k).1
    · exact ENNReal.toReal_lt_of_lt_ofReal (hy k).2.1
  have hlim : Tendsto (fun k : ℕ => R / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
  have habslim := squeeze_zero (fun k => abs_nonneg _) (fun k => (habs k).le) hlim
  refine ⟨R, ind, hR₀, strictMono_nat_of_lt_succ hind, hinner, y, hfinite, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [habslim.eventually (eventually_lt_nhds heps)] with k hk
    rwa [Real.dist_eq]
  · apply tendsto_atTop_mono (fun n => (hy n).2.2.le)
    exact tendsto_natCast_atTop_atTop (R := ℝ)


theorem tendsto_radius_of_inner_bounds_of_escape
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {R : ℝ}
    (hinner : ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C)
    (z y : ∀ n, M n) (hfinite : ∀ n, d n (z n) ≠ ⊤)
    (hupper : ∀ n, d n (y n) ≤ d n (z n))
    (hdist : Tendsto (fun n => (d n (z n)).toReal) atTop (𝓝 R))
    (hscalar : Tendsto (fun n => f n (y n)) atTop atTop) :
    (∀ n, d n (y n) ≠ ⊤) ∧ Tendsto (fun n => (d n (y n)).toReal) atTop (𝓝 R) := by
  have hfin (n) : d n (y n) ≠ ⊤ := ne_top_of_le_ne_top (hfinite n) (hupper n)
  refine ⟨hfin, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun _ => ha0.trans_le ENNReal.toReal_nonneg
    obtain ⟨r, har, hrhi⟩ := exists_between ha
    have hr : 0 < r := (le_of_not_gt ha0).trans_lt har
    obtain ⟨C, hC⟩ := hinner r hr hrhi
    filter_upwards [hC, hscalar.eventually_gt_atTop C] with n hn hhigh
    have hnot : ¬ d n (y n) < ENNReal.ofReal r := fun h => (not_lt_of_ge (hn _ h)) hhigh
    have hlow : r ≤ (d n (y n)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin n)).mp (le_of_not_gt hnot)
    exact har.trans_le hlow
  · intro b hb
    filter_upwards [hdist.eventually_lt_const hb] with n hn
    exact (ENNReal.toReal_mono (hfinite n) (hupper n)).trans_lt hn


end DifferentialGeometry.Analysis
