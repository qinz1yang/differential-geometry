/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Order.Compact

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def smoothRamp (ε r : ℝ) : ℝ := (r + Real.smoothAbs ε r) / 2

theorem contDiff_smoothRamp (ε : ℝ) : ContDiff ℝ ∞ (smoothRamp ε) :=
  (contDiff_id.add (Real.smoothAbs.contDiff ε)).div_const 2

theorem hasDerivAt_smoothRamp (ε r : ℝ) :
    HasDerivAt (smoothRamp ε) (1 - Real.smoothTransition ((ε - r) / (2 * ε))) r := by
  have h := ((hasDerivAt_id' r).add (Real.smoothAbs.hasDerivAt ε r)).div_const 2
  have heq : (1 + (1 - 2 * Real.smoothTransition ((ε - r) / (2 * ε)))) / 2 =
      1 - Real.smoothTransition ((ε - r) / (2 * ε)) := by ring
  rw [heq] at h
  exact h

theorem smoothRamp_of_le {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ -ε) : smoothRamp ε r = 0 := by
  rw [smoothRamp, Real.smoothAbs.eq_neg_of_le hε hr]
  ring

theorem smoothRamp_of_ge {ε r : ℝ} (hε : 0 < ε) (hr : ε ≤ r) : smoothRamp ε r = r := by
  rw [smoothRamp, Real.smoothAbs.eq_self_of_le hε hr]
  ring

theorem abs_smoothRamp_sub_max_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |smoothRamp ε r - max r 0| ≤ ε := by
  have h := Real.smoothAbs.sub_abs_mem_Icc hε r
  have hmax : max r 0 = (r + |r|) / 2 := by
    rcases le_total 0 r with h0 | h0
    · rw [max_eq_left h0, abs_of_nonneg h0]
      ring
    · rw [max_eq_right h0, abs_of_nonpos h0]
      ring
  rw [smoothRamp, hmax, abs_le]
  constructor <;> linarith [h.1, h.2]

theorem smoothRamp_sub_le {ε s t : ℝ} (hst : s ≤ t) :
    0 ≤ smoothRamp ε t - smoothRamp ε s ∧ smoothRamp ε t - smoothRamp ε s ≤ t - s := by
  have hd : ∀ r, HasDerivAt (smoothRamp ε) (1 - Real.smoothTransition ((ε - r) / (2 * ε))) r :=
    hasDerivAt_smoothRamp ε
  have hmono : Monotone (smoothRamp ε) := by
    apply monotone_of_hasDerivAt_nonneg hd
    intro r
    simp only [Pi.zero_apply]
    linarith [Real.smoothTransition.le_one ((ε - r) / (2 * ε))]
  have hlip : Monotone (fun r => r - smoothRamp ε r) := by
    apply monotone_of_hasDerivAt_nonneg (fun r => (hasDerivAt_id r).sub (hd r))
    intro r
    simp only [Pi.zero_apply]
    linarith [Real.smoothTransition.nonneg ((ε - r) / (2 * ε))]
  exact ⟨sub_nonneg.mpr (hmono hst), by linarith [hlip hst]⟩

noncomputable def rampPath (φ : ℝ → ℝ) (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E) (m : ℕ)
    (t : ℝ) : E :=
  P + (t - T 0) • w₀ + ∑ k ∈ Finset.range (m + 1), φ (t - T k) • d k

theorem rampPath_sub (φ : ℝ → ℝ) (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E) (m : ℕ) (s t : ℝ) :
    rampPath φ P T w₀ d m t - rampPath φ P T w₀ d m s =
      (t - s) • w₀ + ∑ k ∈ Finset.range (m + 1), (φ (t - T k) - φ (s - T k)) • d k := by
  simp only [rampPath, sub_smul, Finset.sum_sub_distrib]
  abel

theorem contDiff_rampPath_smoothRamp (ε : ℝ) (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E)
    (m : ℕ) : ContDiff ℝ ∞ (rampPath (smoothRamp ε) P T w₀ d m) := by
  unfold rampPath
  refine (contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)).add ?_
  exact ContDiff.sum fun k _ =>
    ((contDiff_smoothRamp ε).comp (contDiff_id.sub contDiff_const)).smul contDiff_const

theorem hasDerivAt_rampPath_smoothRamp (ε : ℝ) (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E)
    (m : ℕ) (t : ℝ) :
    HasDerivAt (rampPath (smoothRamp ε) P T w₀ d m)
      (w₀ + ∑ k ∈ Finset.range (m + 1),
        (1 - Real.smoothTransition ((ε - (t - T k)) / (2 * ε))) • d k) t := by
  unfold rampPath
  have h1 : HasDerivAt (fun t : ℝ => P + (t - T 0) • w₀) w₀ t := by
    have := ((hasDerivAt_id t).sub_const (T 0)).smul_const w₀
    simpa using this.const_add P
  have h2 : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range (m + 1), smoothRamp ε (t - T k) • d k)
      (∑ k ∈ Finset.range (m + 1),
        (1 - Real.smoothTransition ((ε - (t - T k)) / (2 * ε))) • d k) t := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := (hasDerivAt_smoothRamp ε (t - T k)).comp t ((hasDerivAt_id t).sub_const (T k))
    simpa using hk.smul_const (d k)
  exact h1.add h2

theorem norm_rampPath_smoothRamp_sub_le {ε : ℝ} (hε : 0 < ε) (P : E) (T : ℕ → ℝ) (w₀ : E)
    (d : ℕ → E) (m : ℕ) (t : ℝ) :
    ‖rampPath (smoothRamp ε) P T w₀ d m t - rampPath (fun r => max r 0) P T w₀ d m t‖ ≤
      ε * ∑ k ∈ Finset.range (m + 1), ‖d k‖ := by
  have heq : rampPath (smoothRamp ε) P T w₀ d m t - rampPath (fun r => max r 0) P T w₀ d m t =
      ∑ k ∈ Finset.range (m + 1), (smoothRamp ε (t - T k) - max (t - T k) 0) • d k := by
    simp only [rampPath, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [heq, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_smoothRamp_sub_max_le hε _) (norm_nonneg _)

theorem rampPath_eq_of_forall {φ ψ : ℝ → ℝ} (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E) (m : ℕ)
    {t : ℝ} (h : ∀ k ≤ m, φ (t - T k) = ψ (t - T k)) :
    rampPath φ P T w₀ d m t = rampPath ψ P T w₀ d m t := by
  unfold rampPath
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    rw [h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

theorem rampPath_smoothRamp_eq {ε : ℝ} (hε : 0 < ε) (P : E) (T : ℕ → ℝ) (w₀ : E) (d : ℕ → E)
    (m : ℕ) {t : ℝ} (h : ∀ k ≤ m, ε ≤ |t - T k|) :
    rampPath (smoothRamp ε) P T w₀ d m t = rampPath (fun r => max r 0) P T w₀ d m t := by
  apply rampPath_eq_of_forall
  intro k hk
  rcases le_abs'.mp (h k hk) with hle | hge
  · rw [smoothRamp_of_le hε hle, max_eq_right (by linarith)]
  · rw [smoothRamp_of_ge hε hge, max_eq_left (by linarith)]

theorem velocity_combination_ne_zero {w₀ : E} {d : ℕ → E} {m : ℕ}
    (hcomb : ∀ K ≤ m, ∀ μ ∈ Icc (0 : ℝ) 1,
      w₀ + ∑ k ∈ Finset.range K, d k + μ • d K ≠ 0)
    (lam : ℕ → ℝ) (hlam : ∀ k ≤ m, lam k ∈ Icc (0 : ℝ) 1) (K : ℕ)
    (hlow : ∀ k < K, k ≤ m → lam k = 1) (hhigh : ∀ k, K < k → k ≤ m → lam k = 0) :
    w₀ + ∑ k ∈ Finset.range (m + 1), lam k • d k ≠ 0 := by
  rcases le_or_gt K m with hKm | hKm
  · have hsplit : ∑ k ∈ Finset.range (m + 1), lam k • d k =
        ∑ k ∈ Finset.range K, d k + lam K • d K := by
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : K ≤ m + 1),
        Finset.sum_eq_sum_Ico_succ_bot (by omega : K < m + 1)]
      have h1 : ∑ k ∈ Finset.range K, lam k • d k = ∑ k ∈ Finset.range K, d k :=
        Finset.sum_congr rfl fun k hk => by
          rw [hlow k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega),
            one_smul]
      have h2 : ∑ k ∈ Finset.Ico (K + 1) (m + 1), lam k • d k = 0 :=
        Finset.sum_eq_zero fun k hk => by
          have := Finset.mem_Ico.mp hk
          rw [hhigh k (by omega) (by omega), zero_smul]
      rw [h1, h2, add_zero]
    rw [hsplit, ← add_assoc]
    exact hcomb K hKm (lam K) (hlam K hKm)
  · have hall : ∑ k ∈ Finset.range (m + 1), lam k • d k = ∑ k ∈ Finset.range (m + 1), d k :=
      Finset.sum_congr rfl fun k hk => by
        rw [hlow k (by have := Finset.mem_range.mp hk; omega)
          (by have := Finset.mem_range.mp hk; omega), one_smul]
    rw [hall, Finset.sum_range_succ, ← add_assoc]
    have := hcomb m le_rfl 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_smul] at this

theorem exists_breakIndex {T : ℕ → ℝ} {g : ℝ} (hg : 0 < g) (hgap : ∀ j, g ≤ T (j + 1) - T j)
    (c : ℝ) : ∃ K : ℕ, (∀ k < K, T k ≤ c) ∧ c < T K := by
  classical
  have hlin : ∀ k, T 0 + k * g ≤ T k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hgap k
      push_cast
      linarith
  have hex : ∃ k, c < T k := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((c - T 0) / g)
    refine ⟨k, ?_⟩
    have := hlin k
    have hk' : c - T 0 < k * g := by rwa [div_lt_iff₀ hg] at hk
    linarith
  refine ⟨Nat.find hex, fun k hk => ?_, Nat.find_spec hex⟩
  exact not_lt.mp (Nat.find_min hex hk)

theorem rampPath_smoothRamp_ne_of_lt {ε g : ℝ} (hε : 0 < ε) {P : E} {T : ℕ → ℝ} {w₀ : E}
    {d : ℕ → E} {m : ℕ} (hg : 0 < g) (hgap : ∀ j, g ≤ T (j + 1) - T j)
    (hcomb : ∀ K ≤ m, ∀ μ ∈ Icc (0 : ℝ) 1,
      w₀ + ∑ k ∈ Finset.range K, d k + μ • d K ≠ 0)
    {s t : ℝ} (hst : s < t) (hshort : t - s + 2 * ε < g) :
    rampPath (smoothRamp ε) P T w₀ d m s ≠ rampPath (smoothRamp ε) P T w₀ d m t := by
  intro heq
  have hts : 0 < t - s := sub_pos.mpr hst
  let lam : ℕ → ℝ := fun k => (smoothRamp ε (t - T k) - smoothRamp ε (s - T k)) / (t - s)
  have hlam : ∀ k, lam k ∈ Icc (0 : ℝ) 1 := by
    intro k
    obtain ⟨h0, h1⟩ := smoothRamp_sub_le (ε := ε) (by linarith : s - T k ≤ t - T k)
    refine ⟨div_nonneg h0 hts.le, (div_le_one hts).mpr (by linarith)⟩
  have hstrict : StrictMono T := strictMono_nat_of_lt_succ fun j => by
    have := hgap j
    linarith
  obtain ⟨K, hKlow, hKc⟩ := exists_breakIndex hg hgap (s - ε)
  have hlow : ∀ k < K, k ≤ m → lam k = 1 := by
    intro k hk _
    have hTk := hKlow k hk
    change (smoothRamp ε (t - T k) - smoothRamp ε (s - T k)) / (t - s) = 1
    rw [smoothRamp_of_ge hε (by linarith), smoothRamp_of_ge hε (by linarith)]
    field_simp
    ring
  have hhigh : ∀ k, K < k → k ≤ m → lam k = 0 := by
    intro k hk _
    have hTk : T K + g ≤ T k := by
      have h1 := hgap K
      have h2 : T (K + 1) ≤ T k := hstrict.monotone (by omega)
      linarith
    change (smoothRamp ε (t - T k) - smoothRamp ε (s - T k)) / (t - s) = 0
    rw [smoothRamp_of_le hε (by linarith), smoothRamp_of_le hε (by linarith)]
    simp
  have hne := velocity_combination_ne_zero hcomb lam (fun k _ => hlam k) K hlow hhigh
  apply hne
  have hdiff := rampPath_sub (smoothRamp ε) P T w₀ d m s t
  rw [heq, sub_self] at hdiff
  have hsum : ∑ k ∈ Finset.range (m + 1), (smoothRamp ε (t - T k) - smoothRamp ε (s - T k)) • d k
      = (t - s) • ∑ k ∈ Finset.range (m + 1), lam k • d k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
    congr 1
    change _ = (t - s) * ((smoothRamp ε (t - T k) - smoothRamp ε (s - T k)) / (t - s))
    field_simp
  rw [hsum, ← smul_add] at hdiff
  exact (smul_eq_zero.mp hdiff.symm).resolve_left hts.ne'

theorem deriv_rampPath_smoothRamp_ne_zero {ε g : ℝ} (hε : 0 < ε) {T : ℕ → ℝ} {w₀ : E}
    {d : ℕ → E} {m : ℕ} (hg : 0 < g) (hgap : ∀ j, g ≤ T (j + 1) - T j) (h2ε : 2 * ε < g)
    (hcomb : ∀ K ≤ m, ∀ μ ∈ Icc (0 : ℝ) 1,
      w₀ + ∑ k ∈ Finset.range K, d k + μ • d K ≠ 0) (t : ℝ) :
    w₀ + ∑ k ∈ Finset.range (m + 1),
      (1 - Real.smoothTransition ((ε - (t - T k)) / (2 * ε))) • d k ≠ 0 := by
  have hstrict : StrictMono T := strictMono_nat_of_lt_succ fun j => by
    have := hgap j
    linarith
  obtain ⟨K, hKlow, hKc⟩ := exists_breakIndex hg hgap (t - ε)
  refine velocity_combination_ne_zero hcomb _ (fun k _ =>
    ⟨by linarith [Real.smoothTransition.le_one ((ε - (t - T k)) / (2 * ε))],
      by linarith [Real.smoothTransition.nonneg ((ε - (t - T k)) / (2 * ε))]⟩) K ?_ ?_
  · intro k hk _
    have hTk := hKlow k hk
    have : (ε - (t - T k)) / (2 * ε) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [Real.smoothTransition.zero_of_nonpos this, sub_zero]
  · intro k hk _
    have hTk : T K + g ≤ T k := by
      have h1 := hgap K
      have h2 : T (K + 1) ≤ T k := hstrict.monotone (by omega)
      linarith
    have : 1 ≤ (ε - (t - T k)) / (2 * ε) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [Real.smoothTransition.one_of_one_le this, sub_self]

omit [NormedSpace ℝ E] in
theorem exists_pos_le_norm_sub_of_injOn {p : ℝ → E} {a b η : ℝ}
    (hp : ContinuousOn p (Icc a b)) (hinj : InjOn p (Icc a b)) (hη : 0 < η) :
    ∃ κ > 0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s + η ≤ t → κ ≤ ‖p t - p s‖ := by
  let K : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc a b) ∩ {q | q.1 + η ≤ q.2}
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le (continuous_fst.add continuous_const) continuous_snd)
  have hcont : ContinuousOn (fun q : ℝ × ℝ => ‖p q.2 - p q.1‖) K := by
    refine ((hp.comp continuousOn_snd ?_).sub (hp.comp continuousOn_fst ?_)).norm
    · exact fun q hq => hq.1.2
    · exact fun q hq => hq.1.1
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun s hs t ht hst => ?_⟩
    have : (s, t) ∈ K := ⟨⟨hs, ht⟩, hst⟩
    rw [hKe] at this
    exact this.elim
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hKne hcont
  refine ⟨‖p q.2 - p q.1‖, ?_, fun s hs t ht hst =>
    isMinOn_iff.mp hmin (s, t) ⟨⟨hs, ht⟩, hst⟩⟩
  refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => ?_)
  have := hinj hq.1.2 hq.1.1 h
  have h2 := hq.2
  simp only [mem_ofPred_eq] at h2
  rw [this] at h2
  linarith

omit [NormedSpace ℝ E] in
theorem injOn_of_near_injOn {p γ : ℝ → E} {a b η κ : ℝ}
    (hκ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s + η ≤ t → κ ≤ ‖p t - p s‖)
    (hclose : ∀ t ∈ Icc a b, ‖γ t - p t‖ < κ / 2)
    (hloc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → t < s + η → γ s ≠ γ t) :
    InjOn γ (Icc a b) := by
  have hkey : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → γ s ≠ γ t := by
    intro s hs t ht hst heq
    rcases lt_or_ge t (s + η) with hshort | hlong
    · exact hloc s hs t ht hst hshort heq
    · have h1 := hκ s hs t ht hlong
      have h2 := hclose s hs
      have h3 := hclose t ht
      have htri : ‖p t - p s‖ ≤ ‖γ t - p t‖ + ‖γ s - p s‖ := by
        have : p t - p s = -(γ t - p t) + (γ s - p s) + (γ t - γ s) := by abel
        rw [this, heq, sub_self, add_zero]
        exact (norm_add_le _ _).trans (by rw [norm_neg])
      linarith
  intro s hs t ht heq
  rcases lt_trichotomy s t with hlt | hst | hgt
  · exact (hkey s hs t ht hlt heq).elim
  · exact hst
  · exact (hkey t ht s hs hgt heq.symm).elim

end DifferentialGeometry.Topology.PiecewiseLinear
