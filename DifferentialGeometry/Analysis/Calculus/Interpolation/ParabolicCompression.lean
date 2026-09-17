import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set Filter Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_contDiff_interval_compression {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, 0 < deriv f x) ∧
      (∀ x, f x ≤ x) ∧ f β < ε ∧
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo 0 1 ∧ EqOn f id Kᶜ := by
  let c := min ε β / 2
  have hc : 0 < c := half_pos (lt_min hε hβ)
  have hcε : c < ε := (half_lt_self (lt_min hε hβ)).trans_le (min_le_left _ _)
  have hcβ : c < β := (half_lt_self (lt_min hε hβ)).trans_le (min_le_right _ _)
  let z := (c + β) / 2
  let rin := (β - c) / 2
  let rout := (rin + min z (1 - z)) / 2
  have hri : 0 < rin := by dsimp [rin]; linarith
  have hmargin : rin < min z (1 - z) := by rw [lt_min_iff]; dsimp [rin, z]; constructor <;> linarith
  have hrir : rin < rout := by dsimp [rout]; linarith
  have hrout : rout < min z (1 - z) := by dsimp [rout]; linarith
  let b : ContDiffBump z := ⟨rin, rout, hri, hrir⟩
  have hK : closedBall z rout ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hab : |x - z| ≤ rout := by simpa only [mem_closedBall, Real.dist_eq] using hx
    exact ⟨by linarith [(abs_le.mp hab).1, hrout.trans_le (min_le_left _ _)],
      by linarith [(abs_le.mp hab).2, hrout.trans_le (min_le_right _ _)]⟩
  have hb1 {x : ℝ} (hx : x ∈ Icc c β) : b x = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall, Real.dist_eq, abs_le]
    change -rin ≤ x - z ∧ x - z ≤ rin
    dsimp [rin, z]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport b.contDiff
    (show (∞ : ℕ∞ω) ≠ 0 by simp)
  let δ : ℝ := (2 * ((L : ℝ) + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδL : δ * (L : ℝ) < 1 := by
    dsimp [δ]
    rw [inv_mul_eq_div, div_lt_one (by positivity)]
    linarith [L.coe_nonneg]
  let g : ℝ → ℝ := fun x => x - δ * b x
  have hg : ContDiff ℝ ∞ g := contDiff_id.sub (contDiff_const.mul b.contDiff)
  have hgder (x : ℝ) : deriv g x = 1 - δ * deriv b x :=
    ((hasDerivAt_id x).sub
      ((((show ContDiff ℝ ∞ (b : ℝ → ℝ) from b.contDiff).differentiable (by simp))
        x).hasDerivAt.const_mul δ)).deriv
  have hgpos (x : ℝ) : 0 < deriv g x := by
    rw [hgder]
    have hb : ‖deriv b x‖ ≤ (L : ℝ) := norm_deriv_le_of_lipschitz (x₀ := x) hL
    have hd : deriv b x ≤ (L : ℝ) :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
    nlinarith [mul_le_mul_of_nonneg_left hd hδ.le]
  have hgle (x : ℝ) : g x ≤ x := by
    change x - δ * b x ≤ x
    exact sub_le_self _ (mul_nonneg hδ.le b.nonneg)
  have hfix {x : ℝ} (hx : x ∉ closedBall z rout) : g x = x := by
    have hx' : x ∉ Function.support b := fun hb => hx (ball_subset_closedBall (b.support_eq ▸ hb))
    have hb := Function.notMem_support.mp hx'
    dsimp [g]
    rw [hb, mul_zero, sub_zero]
  have hiterle : ∀ n : ℕ, ∀ x : ℝ, g^[n] x ≤ x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [Function.iterate_succ_apply']; exact (hgle _).trans (ih x)
  have hiter : ∀ n : ℕ, ContDiff ℝ ∞ (g^[n]) ∧ ∀ x, 0 < deriv (g^[n]) x := by
    intro n
    induction n with
    | zero => exact ⟨contDiff_id, fun x => by simp⟩
    | succ n ih =>
      have he : g^[n + 1] = g ∘ g^[n] := funext (Function.iterate_succ_apply' g n)
      rw [he]
      refine ⟨hg.comp ih.1, ?_⟩
      intro x
      rw [deriv_comp x (hg.differentiable (by simp) _) (ih.1.differentiable (by simp) _)]
      exact mul_pos (hgpos _) (ih.2 x)
  have hex : ∃ n : ℕ, g^[n] β < c := by
    by_contra hn
    push Not at hn
    have he : ∀ n : ℕ, g^[n] β = β - n * δ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        change g^[n] β - δ * b (g^[n] β) = _
        rw [hb1 ⟨hn n, hiterle n β⟩, mul_one, ih, Nat.cast_add, Nat.cast_one]
        ring
    obtain ⟨n, hn'⟩ := exists_nat_gt ((β - c) / δ)
    have hnn := hn n
    rw [he n] at hnn
    have hmul := (div_lt_iff₀ hδ).mp hn'
    linarith
  obtain ⟨n, hn⟩ := hex
  refine ⟨g^[n], (hiter n).1, (hiter n).2, hiterle n, hn.trans hcε,
    closedBall z rout, isCompact_closedBall _ _, hK, ?_⟩
  intro x hx
  exact Function.IsFixedPt.iterate (hfix hx) n


private theorem exists_contDiff_unit_lens_compression
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hinner : ∀ p ∈ K, 0 < p.1 ∧ p.1 < 1 - p.2 ^ 2)
    {f : (ℝ × ℝ) → ℝ} (hf : ContinuousOn f K) (hpos : ∀ p ∈ K, 0 < f p) :
    ∃ H : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ H ∧
      (∀ p, 0 < fderiv ℝ H p (1, 0)) ∧
      (∀ p, H p ≤ p.1) ∧ (∀ p, 0 ≤ p.1 → 0 ≤ H p) ∧
      (∀ p ∈ K, H p < f p) ∧
      ∃ L : Set (ℝ × ℝ), IsCompact L ∧
        L ⊆ {p | 0 < p.1 ∧ p.1 < 1 - p.2 ^ 2} ∧ EqOn H Prod.fst Lᶜ := by
  classical
  by_cases hne : K.Nonempty
  swap
  · have he : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst K
    refine ⟨Prod.fst, contDiff_fst, ?_, fun _ => le_rfl, fun _ hp => hp,
      by simp, ∅, isCompact_empty, empty_subset _, ?_⟩
    · intro p
      rw [fderiv_fst]
      exact zero_lt_one
    · exact fun _ _ => rfl
  have hu {p : ℝ × ℝ} (hp : p ∈ K) : |p.2| < 1 := by
    have hh := hinner p hp
    exact abs_lt.mpr ⟨by nlinarith [sq_nonneg (p.2 + 1)], by nlinarith [sq_nonneg (p.2 - 1)]⟩
  obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hne continuous_snd.abs.continuousOn
  let ρ₀ := (|p₀.2| + 1) / 2
  let ρ₁ := (ρ₀ + 1) / 2
  let ρ₂ := (ρ₁ + 1) / 2
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; linarith [abs_nonneg p₀.2]
  have hρ₀₁ : ρ₀ < 1 := by dsimp [ρ₀]; linarith [hu hp₀]
  have hρ₀ρ₁ : ρ₀ < ρ₁ := by dsimp [ρ₁]; linarith
  have hρ₁ρ₂ : ρ₁ < ρ₂ := by dsimp [ρ₁, ρ₂]; linarith
  have hρ₂₁ : ρ₂ < 1 := by dsimp [ρ₁, ρ₂]; linarith
  have hku {p : ℝ × ℝ} (hp : p ∈ K) : |p.2| < ρ₀ := by
    have hh : |p.2| ≤ |p₀.2| := hmax hp
    dsimp [ρ₀]
    linarith [hu hp₀]
  let κ : ContDiffBump (0 : ℝ) := ⟨ρ₀, ρ₁, hρ₀, hρ₀ρ₁⟩
  let η : ContDiffBump (0 : ℝ) := ⟨ρ₁, ρ₂, hρ₀.trans hρ₀ρ₁, hρ₁ρ₂⟩
  let w : ℝ → ℝ := fun u => 1 - (η u * u) ^ 2
  have hw : ContDiff ℝ ∞ w := contDiff_const.sub ((η.contDiff.mul contDiff_id).pow 2)
  have hwpos (u : ℝ) : 0 < w u := by
    by_cases huu : u ∈ ball (0 : ℝ) ρ₂
    · have hule : |η u * u| ≤ |u| := by
        rw [abs_mul, abs_of_nonneg η.nonneg]
        exact mul_le_of_le_one_left (abs_nonneg u) η.le_one
      have huu' : |u| < ρ₂ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using huu
      have hh := hule.trans_lt (huu'.trans hρ₂₁)
      change 0 < 1 - (η u * u) ^ 2
      have hh' := (sq_lt_one_iff_abs_lt_one _).mpr hh
      linarith
    · have hz : η u = 0 := Function.notMem_support.mp (by rwa [η.support_eq])
      simp only [w, hz, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero, zero_lt_one]
  have hweq {u : ℝ} (hu : u ∈ closedBall (0 : ℝ) ρ₁) : w u = 1 - u ^ 2 := by
    dsimp [w]
    rw [η.one_of_mem_closedBall hu, one_mul]
  have hkone {p : ℝ × ℝ} (hp : p ∈ K) : κ p.2 = 1 := by
    apply κ.one_of_mem_closedBall
    change dist p.2 0 ≤ ρ₀
    simpa only [Real.dist_eq, sub_zero] using (hku hp).le
  have hwK {p : ℝ × ℝ} (hp : p ∈ K) : w p.2 = 1 - p.2 ^ 2 :=
    hweq (by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ((hku hp).trans hρ₀ρ₁).le)
  let v : (ℝ × ℝ) → ℝ := fun p => p.1 / w p.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.div (hw.comp contDiff_snd) (fun p => (hwpos p.2).ne')
  have hvK {p : ℝ × ℝ} (hp : p ∈ K) : 0 < v p ∧ v p < 1 := by
    refine ⟨div_pos (hinner p hp).1 (hwpos p.2), ?_⟩
    apply (div_lt_one (hwpos p.2)).mpr
    rw [hwK hp]
    exact (hinner p hp).2
  obtain ⟨p₁, hp₁, hvmax⟩ := hK.exists_isMaxOn hne hv.continuous.continuousOn
  let β := (v p₁ + 1) / 2
  have hβ : 0 < β := by dsimp [β]; linarith [(hvK hp₁).1]
  have hβ₁ : β < 1 := by dsimp [β]; linarith [(hvK hp₁).2]
  have hvβ {p : ℝ × ℝ} (hp : p ∈ K) : v p ≤ β := by
    have hh : v p ≤ v p₁ := hvmax hp
    dsimp [β]
    linarith [(hvK hp₁).2]
  have hratio : ContinuousOn (fun p => f p / w p.2) K :=
    hf.div (hw.continuous.comp continuous_snd).continuousOn (fun p _ => (hwpos p.2).ne')
  obtain ⟨p₂, hp₂, hmin⟩ := hK.exists_isMinOn hne hratio
  obtain ⟨φ, hφ, hφd, hφle, hφβ, M, hM, hM01, hφfix⟩ :=
    exists_contDiff_interval_compression (div_pos (hpos p₂ hp₂) (hwpos p₂.2)) hβ hβ₁
  have hφ0 : φ 0 = 0 := hφfix (fun h => (hM01 h).1.false)
  have hφmono : StrictMono φ := strictMono_of_deriv_pos hφd
  let H : (ℝ × ℝ) → ℝ := fun p => (1 - κ p.2) * p.1 + κ p.2 * w p.2 * φ (v p)
  have hH : ContDiff ℝ ∞ H :=
    ((contDiff_const.sub (κ.contDiff.comp contDiff_snd)).mul contDiff_fst).add
      (((κ.contDiff.comp contDiff_snd).mul (hw.comp contDiff_snd)).mul (hφ.comp hv))
  have hcancel (p : ℝ × ℝ) : w p.2 * v p = p.1 := by
    dsimp [v]
    exact mul_div_cancel₀ _ (hwpos p.2).ne'
  let L := (fun p : ℝ × ℝ => (w p.2 * p.1, p.2)) '' (M ×ˢ closedBall (0 : ℝ) ρ₁)
  have hL : IsCompact L :=
    (hM.prod (isCompact_closedBall _ _)).image
      (((hw.continuous.comp continuous_snd).mul continuous_fst).prodMk continuous_snd)
  have hLinner : L ⊆ {p | 0 < p.1 ∧ p.1 < 1 - p.2 ^ 2} := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    refine ⟨mul_pos (hwpos u) (hM01 ht).1, ?_⟩
    change w u * t < 1 - u ^ 2
    rw [← hweq hu]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (hM01 ht).2 (hwpos u)
  refine ⟨H, hH, ?_, ?_, ?_, ?_, L, hL, hLinner, ?_⟩
  · intro p
    have hpath : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have hd : HasDerivAt (fun t : ℝ => H (t, p.2)) (fderiv ℝ H p (1, 0)) p.1 := by
      have hh := ((hH.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt_of_eq
        p.1 hpath (Prod.eta p).symm
      exact hh
    have hφv := ((hφ.differentiable (by simp)) (v p)).hasDerivAt.comp p.1
      ((hasDerivAt_id p.1).div_const (w p.2))
    have hh := ((hasDerivAt_id p.1).const_mul (1 - κ p.2)).add
      (hφv.const_mul (κ p.2 * w p.2))
    have he : fderiv ℝ H p (1, 0) = (1 - κ p.2) + κ p.2 * deriv φ (v p) := by
      have he := hd.unique hh
      convert he using 1
      field_simp [(hwpos p.2).ne']
    rw [he]
    by_cases hk : κ p.2 = 0
    · rw [hk]; norm_num
    · have hkp : 0 < κ p.2 := lt_of_le_of_ne κ.nonneg (Ne.symm hk)
      have hh := mul_pos hkp (hφd (v p))
      linarith [κ.le_one (x := p.2)]
  · intro p
    have hh := mul_le_mul_of_nonneg_left (hφle (v p)) (mul_nonneg (κ.nonneg' p.2) (hwpos p.2).le)
    have he : κ p.2 * w p.2 * v p = κ p.2 * p.1 := by rw [mul_assoc, hcancel]
    change (1 - κ p.2) * p.1 + κ p.2 * w p.2 * φ (v p) ≤ p.1
    rw [he] at hh
    nlinarith
  · intro p hp
    have hvp : 0 ≤ v p := div_nonneg hp (hwpos p.2).le
    have hφp : 0 ≤ φ (v p) := by simpa only [hφ0] using hφmono.monotone hvp
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr κ.le_one) hp)
      (mul_nonneg (mul_nonneg (κ.nonneg' p.2) (hwpos p.2).le) hφp)
  · intro p hp
    have hcmp := ((hφmono.monotone (hvβ hp)).trans_lt hφβ).trans_le (hmin hp)
    have hh := mul_lt_mul_of_pos_left hcmp (hwpos p.2)
    rw [mul_div_cancel₀ _ (hwpos p.2).ne'] at hh
    simpa only [H, hkone hp, sub_self, zero_mul, one_mul, zero_add] using hh
  · intro p hp
    by_cases hk : κ p.2 = 0
    · simp only [H, hk, sub_zero, one_mul, zero_mul, add_zero]
    · have hu : p.2 ∈ closedBall (0 : ℝ) ρ₁ := ball_subset_closedBall (κ.support_eq ▸ hk)
      have hvM : v p ∉ M := by
        intro hvm
        exact hp ⟨(v p, p.2), ⟨hvm, hu⟩, Prod.ext (hcancel p) rfl⟩
      rw [show H p = (1 - κ p.2) * p.1 + κ p.2 * w p.2 * φ (v p) from rfl, hφfix hvM]
      change (1 - κ p.2) * p.1 + κ p.2 * w p.2 * v p = p.1
      rw [mul_assoc, hcancel]
      ring

theorem exists_contDiff_parabolic_compression_below_on_isCompact
    {a A B : ℝ} (ha : a < A) (hB : 0 < B)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hinner : ∀ p ∈ K, a < p.1 ∧ p.1 < A - B * p.2 ^ 2)
    {f : (ℝ × ℝ) → ℝ} (hf : ContinuousOn f K) (hpos : ∀ p ∈ K, a < f p) :
    ∃ H : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ H ∧
      (∀ p, 0 < fderiv ℝ H p (1, 0)) ∧
      (∀ p, H p ≤ p.1) ∧ (∀ p, a ≤ p.1 → a ≤ H p) ∧
      (∀ p ∈ K, H p < f p) ∧
      ∃ L : Set (ℝ × ℝ), IsCompact L ∧
        L ⊆ {p | a < p.1 ∧ p.1 < A - B * p.2 ^ 2} ∧ EqOn H Prod.fst Lᶜ := by
  let d := A - a
  let r := Real.sqrt (d / B)
  have hd : 0 < d := sub_pos.mpr ha
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hd hB)
  have hrsq : B * r ^ 2 = d := by
    rw [Real.sq_sqrt (div_pos hd hB).le, mul_div_cancel₀ _ hB.ne']
  let N : (ℝ × ℝ) → (ℝ × ℝ) := fun p => ((p.1 - a) / d, p.2 / r)
  let S : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (a + d * p.1, r * p.2)
  have hN : ContDiff ℝ ∞ N := ((contDiff_fst.sub contDiff_const).div_const d).prodMk
    (contDiff_snd.div_const r)
  have hS : ContDiff ℝ ∞ S := (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk
    (contDiff_const.mul contDiff_snd)
  have hSN (p : ℝ × ℝ) : S (N p) = p := by
    dsimp [S, N]
    rw [mul_div_cancel₀ _ hd.ne', mul_div_cancel₀ _ hr.ne', add_sub_cancel]
  have hNS (p : ℝ × ℝ) : N (S p) = p := by
    dsimp [S, N]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hd.ne', mul_div_cancel_left₀ _ hr.ne']
  have hSmem {p : ℝ × ℝ} (hp : 0 < p.1 ∧ p.1 < 1 - p.2 ^ 2) :
      a < (S p).1 ∧ (S p).1 < A - B * (S p).2 ^ 2 := by
    have hsq : B * (r * p.2) ^ 2 = d * p.2 ^ 2 := by nlinarith [hrsq]
    dsimp [S]
    rw [hsq]
    constructor
    · exact lt_add_of_pos_right _ (mul_pos hd hp.1)
    · have hh := mul_lt_mul_of_pos_left hp.2 hd
      dsimp [d] at *
      nlinarith
  have hNmem {p : ℝ × ℝ} (hp : a < p.1 ∧ p.1 < A - B * p.2 ^ 2) :
      0 < (N p).1 ∧ (N p).1 < 1 - (N p).2 ^ 2 := by
    have he := congrArg Prod.fst (hSN p)
    have he' := congrArg Prod.snd (hSN p)
    change a + d * (N p).1 = p.1 at he
    change r * (N p).2 = p.2 at he'
    have hsq : B * p.2 ^ 2 = d * (N p).2 ^ 2 := by rw [← he']; nlinarith [hrsq]
    refine ⟨div_pos (sub_pos.mpr hp.1) hd, ?_⟩
    have hh := hp.2
    rw [hsq] at hh
    have : d * (N p).1 < d * (1 - (N p).2 ^ 2) := by dsimp [d] at *; nlinarith
    exact (mul_lt_mul_iff_right₀ hd).mp this
  let fN := fun p => (f (S p) - a) / d
  have hfN : ContinuousOn fN (N '' K) :=
    ((hf.comp hS.continuous.continuousOn (by rintro _ ⟨p, hp, rfl⟩; simpa only [hSN] using hp)).sub
      continuousOn_const).div_const d
  obtain ⟨H₀, hH₀, hH₀d, hH₀le, hH₀pos, hH₀f, L₀, hL₀, hL₀in, hH₀fix⟩ :=
    exists_contDiff_unit_lens_compression (hK.image hN.continuous)
      (by rintro _ ⟨p, hp, rfl⟩; exact hNmem (hinner p hp)) hfN
      (by rintro _ ⟨p, hp, rfl⟩; dsimp [fN]; rw [hSN]; exact div_pos (sub_pos.mpr (hpos p hp)) hd)
  let H := fun p => a + d * H₀ (N p)
  have hH : ContDiff ℝ ∞ H := contDiff_const.add (contDiff_const.mul (hH₀.comp hN))
  refine ⟨H, hH, ?_, ?_, ?_, ?_, S '' L₀, hL₀.image hS.continuous,
    by rintro _ ⟨p, hp, rfl⟩; exact hSmem (hL₀in hp), ?_⟩
  · intro p
    have hpath : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have hnpath : HasDerivAt (fun t : ℝ => N (t, p.2)) (d⁻¹ • (1, 0)) p.1 := by
      simpa [N, div_eq_mul_inv] using
        HasDerivAt.prodMk (((hasDerivAt_id p.1).sub_const a).div_const d)
          (hasDerivAt_const p.1 (p.2 / r))
    have hc := (((hH₀.differentiable (by simp)) (N p)).hasFDerivAt.comp_hasDerivAt_of_eq
      p.1 hnpath (congrArg N (Prod.eta p)).symm).const_mul d |>.const_add a
    have hdirect := ((hH.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt_of_eq
      p.1 hpath (Prod.eta p).symm
    have heq : fderiv ℝ H p (1, 0) = d * (d⁻¹ * fderiv ℝ H₀ (N p) (1, 0)) := by
      simpa only [map_smul, smul_eq_mul] using hdirect.unique hc
    rw [heq, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
    exact hH₀d _
  · intro p
    have hh := mul_le_mul_of_nonneg_left (hH₀le (N p)) hd.le
    have he := congrArg Prod.fst (hSN p)
    change a + d * (N p).1 = p.1 at he
    dsimp [H]
    linarith
  · intro p hp
    exact le_add_of_nonneg_right
      (mul_nonneg hd.le (hH₀pos (N p) (div_nonneg (sub_nonneg.mpr hp) hd.le)))
  · intro p hp
    have hh := mul_lt_mul_of_pos_left (hH₀f (N p) (mem_image_of_mem N hp)) hd
    dsimp [fN] at hh
    rw [hSN, mul_div_cancel₀ _ hd.ne'] at hh
    dsimp [H]
    linarith
  · intro p hp
    have hn : N p ∉ L₀ := fun hn => hp ⟨N p, hn, hSN p⟩
    change a + d * H₀ (N p) = p.1
    rw [hH₀fix hn]
    exact congrArg Prod.fst (hSN p)

end DifferentialGeometry.Analysis
