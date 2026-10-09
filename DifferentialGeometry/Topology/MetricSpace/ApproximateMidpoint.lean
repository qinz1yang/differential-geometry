import DifferentialGeometry.Topology.MetricSpace.CurveVariation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace Metric

variable {X : Type*}

private def dyadicRefinement (m : ℕ → X → X → X) (a b : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then a else b
  | n + 1, k => if k % 2 = 0 then dyadicRefinement m a b n (k / 2)
    else m n (dyadicRefinement m a b n (k / 2)) (dyadicRefinement m a b n (k / 2 + 1))

private theorem dyadicRefinement_even (m : ℕ → X → X → X) (a b : X) (n k : ℕ) :
    dyadicRefinement m a b (n + 1) (2 * k) = dyadicRefinement m a b n k := by
  have hmod : 2 * k % 2 = 0 := by omega
  have hdiv : 2 * k / 2 = k := by omega
  rw [dyadicRefinement, hmod, ite_eq_left rfl, hdiv]

private theorem dyadicRefinement_odd (m : ℕ → X → X → X) (a b : X) (n k : ℕ) :
    dyadicRefinement m a b (n + 1) (2 * k + 1) =
      m n (dyadicRefinement m a b n k) (dyadicRefinement m a b n (k + 1)) := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  rw [dyadicRefinement, hmod, ite_eq_right (by omega), hdiv]

variable [MetricSpace X]

theorem exists_lipschitz_curve_of_approximate_midpoints [CompleteSpace X]
    (h : ∀ a b : X, ∀ ε : ℝ, 0 < ε → ∃ z, dist a z ≤ dist a b / 2 + ε ∧
      dist b z ≤ dist a b / 2 + ε) (a b : X) {τ : ℝ} (hτ : 0 < τ) :
    ∃ f : Icc (0 : ℝ) 1 → X,
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      LipschitzWith ⟨dist a b + τ / 2, by positivity⟩ f := by
  classical
  let D := dist a b
  let C := D + τ / 2
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  let ε : ℕ → ℝ := fun n => τ / 8 * (r n) ^ 2
  let δ : ℕ → ℝ := fun n => C * r n - τ / 2 * (r n) ^ 2
  have hC : 0 ≤ C := by dsimp [C, D]; positivity
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose m hmleft hmright using fun n x y => h x y (ε n) (hε n)
  let f := dyadicRefinement m a b
  have heven (n k : ℕ) : f (n + 1) (2 * k) = f n k := dyadicRefinement_even m a b n k
  have hodd (n k : ℕ) : f (n + 1) (2 * k + 1) = m n (f n k) (f n (k + 1)) :=
    dyadicRefinement_odd m a b n k
  have hδrec (n : ℕ) : δ n / 2 + ε n = δ (n + 1) := by
    dsimp [δ, ε, r]
    rw [pow_succ]
    ring
  have hzero (n : ℕ) : f n 0 = a := by
    induction n with
    | zero => simp [f, dyadicRefinement]
    | succ n ih => simpa only [Nat.mul_zero] using (heven n 0).trans ih
  have hend (n : ℕ) : f n (2 ^ n) = b := by
    induction n with
    | zero => simp [f, dyadicRefinement]
    | succ n ih =>
      rw [pow_succ, Nat.mul_comm]
      exact (heven n (2 ^ n)).trans ih
  have hstep (n : ℕ) : ∀ k < 2 ^ n, dist (f n k) (f n (k + 1)) ≤ δ n := by
    induction n with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      simp only [hk0, f, dyadicRefinement, zero_add, ite_eq_right (by omega : (1 : ℕ) ≠ 0)]
      dsimp [δ, r, C, D]
      ring_nf
      exact le_refl _
    | succ n ih =>
      intro k hk
      have hkdiv : k / 2 < 2 ^ n := by rw [pow_succ] at hk; omega
      have hh := ih (k / 2) hkdiv
      by_cases hkmod : k % 2 = 0
      · have hkform : k = 2 * (k / 2) := by omega
        have hnext : k + 1 = 2 * (k / 2) + 1 := by omega
        rw [hkform, heven, hodd]
        have hm := hmleft n (f n (k / 2)) (f n (k / 2 + 1))
        have hbound : dist (f n (k / 2)) (m n (f n (k / 2)) (f n (k / 2 + 1))) ≤
            δ n / 2 + ε n := by linarith
        exact hbound.trans_eq (hδrec n)
      · have hkform : k = 2 * (k / 2) + 1 := by omega
        have hnext : k + 1 = 2 * (k / 2 + 1) := by omega
        rw [hnext, hkform, hodd, heven]
        have hm := hmright n (f n (k / 2)) (f n (k / 2 + 1))
        rw [dist_comm] at hm
        have hbound : dist (m n (f n (k / 2)) (f n (k / 2 + 1))) (f n (k / 2 + 1)) ≤
            δ n / 2 + ε n := by linarith
        simpa only [show (2 * (k / 2) + 1) / 2 = k / 2 by omega] using
          hbound.trans_eq (hδrec n)
  have hstepC (n : ℕ) : ∀ k < 2 ^ n, dist (f n k) (f n (k + 1)) ≤ C * r n := by
    intro k hk
    have hh := hstep n k hk
    have he : 0 ≤ τ / 2 * (r n) ^ 2 := by positivity
    dsimp only [δ] at hh
    linarith
  have hprod (n : ℕ) : (2 ^ n : ℕ) * (C * r n) = C := by
    dsimp only [r]
    push_cast
    calc
      (2 : ℝ) ^ n * (C * (1 / 2 : ℝ) ^ n) = C * ((2 : ℝ) * (1 / 2)) ^ n := by
        rw [mul_pow]
        ring
      _ = C := by norm_num
  let k (n : ℕ) (t : Icc (0 : ℝ) 1) : ℕ := ⌊(t : ℝ) * (2 ^ n : ℕ)⌋₊
  have hk (n : ℕ) (t : Icc (0 : ℝ) 1) : k n t ≤ 2 ^ n := by
    dsimp only [k]
    calc
      ⌊(t : ℝ) * (2 ^ n : ℕ)⌋₊ ≤ ⌊((2 ^ n : ℕ) : ℝ)⌋₊ := Nat.floor_mono (by
        nlinarith [t.property.2, (show (0 : ℝ) ≤ (2 ^ n : ℕ) from Nat.cast_nonneg _)])
      _ = 2 ^ n := Nat.floor_natCast _
  let g (n : ℕ) (t : Icc (0 : ℝ) 1) := f n (k n t)
  have hordered (n : ℕ) (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
      dist (g n s) (g n t) ≤ C * dist s t + C * r n := by
    have hks : k n s ≤ k n t :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg (2 ^ n)))
    have hslo := Nat.lt_floor_add_one ((s : ℝ) * (2 ^ n : ℕ))
    have hthi := Nat.floor_le (mul_nonneg t.property.1 (Nat.cast_nonneg (2 ^ n)))
    have hdiff : (k n t : ℝ) - (k n s : ℝ) ≤
        ((t : ℝ) - (s : ℝ)) * (2 ^ n : ℕ) + 1 := by
      dsimp only [k]
      nlinarith only [hslo, hthi]
    have hh : dist (g n s) (g n t) ≤ (k n t - k n s : ℕ) * (C * r n) := by
      calc
        dist (g n s) (g n t) ≤ ∑ j ∈ Finset.Ico (k n s) (k n t), C * r n :=
          dist_le_Ico_sum_of_dist_le hks (fun hji hjt =>
            hstepC n _ (lt_of_lt_of_le hjt (hk n t)))
        _ = (k n t - k n s : ℕ) * (C * r n) := by simp
    rw [Nat.cast_sub hks] at hh
    have hstDist : dist s t = (t : ℝ) - (s : ℝ) := by
      change |(s : ℝ) - (t : ℝ)| = (t : ℝ) - (s : ℝ)
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    rw [hstDist]
    calc
      dist (g n s) (g n t) ≤ ((k n t : ℝ) - (k n s : ℝ)) * (C * r n) := hh
      _ ≤ (((t : ℝ) - (s : ℝ)) * (2 ^ n : ℕ) + 1) * (C * r n) :=
        mul_le_mul_of_nonneg_right hdiff (mul_nonneg hC (hr n).le)
      _ = ((t : ℝ) - (s : ℝ)) * ((2 ^ n : ℕ) * (C * r n)) + C * r n := by ring
      _ = C * ((t : ℝ) - (s : ℝ)) + C * r n := by rw [hprod]; ring
  have hdist (n : ℕ) (s t : Icc (0 : ℝ) 1) :
      dist (g n s) (g n t) ≤ C * dist s t + C * r n := by
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact hordered n s t hst
    · rw [dist_comm (g n s) (g n t), dist_comm s t]
      exact hordered n t s hts
  have hindex (n : ℕ) (t : Icc (0 : ℝ) 1) : k (n + 1) t / 2 = k n t := by
    dsimp only [k]
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc]
    exact Nat.mul_cast_floor_div_cancel (by norm_num : (2 : ℕ) ≠ 0) _
  have hsucc (n : ℕ) (t : Icc (0 : ℝ) 1) :
      dist (g n t) (g (n + 1) t) ≤ C * r n := by
    let j := k (n + 1) t
    have hjdiv : j / 2 = k n t := hindex n t
    by_cases hjmod : j % 2 = 0
    · have hj : j = 2 * (k n t) := by omega
      change dist (f n (k n t)) (f (n + 1) j) ≤ C * r n
      rw [hj, heven, dist_self]
      exact mul_nonneg hC (hr n).le
    · have hj : j = 2 * (k n t) + 1 := by omega
      have hjbound : k n t < 2 ^ n := by
        have hh := hk (n + 1) t
        change j ≤ 2 ^ (n + 1) at hh
        rw [pow_succ] at hh
        omega
      change dist (f n (k n t)) (f (n + 1) j) ≤ C * r n
      rw [hj, hodd]
      have hleft := hmleft n (f n (k n t)) (f n (k n t + 1))
      have hchain := hstep n (k n t) hjbound
      have hh : dist (f n (k n t)) (m n (f n (k n t)) (f n (k n t + 1))) ≤
          δ (n + 1) := by rw [← hδrec]; linarith
      have he : 0 ≤ τ / 2 * (r (n + 1)) ^ 2 := by positivity
      have hrrec : r (n + 1) = r n / 2 := by dsimp [r]; rw [pow_succ]; ring
      dsimp only [δ] at hh
      rw [hrrec] at hh
      have hCr : 0 ≤ C * r n := mul_nonneg hC (hr n).le
      rw [hrrec] at he
      nlinarith
  have hlimit (t : Icc (0 : ℝ) 1) : ∃ x, Tendsto (fun n => g n t) atTop (𝓝 x) := by
    apply cauchySeq_tendsto_of_complete
    exact cauchySeq_of_le_geometric (1 / 2) C (by norm_num) (fun n => hsucc n t)
  choose F hconv using hlimit
  have hrlim : Tendsto r atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hLip : LipschitzWith ⟨dist a b + τ / 2, by positivity⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hh := le_of_tendsto_of_tendsto ((hconv s).dist (hconv t))
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hrlim))
      (Eventually.of_forall (fun n => hdist n s t))
    change dist (F s) (F t) ≤ C * dist s t
    simpa only [mul_zero, add_zero] using hh
  have hgzero : ∀ n, g n ⟨0, by norm_num⟩ = a := by
    intro n
    simpa only [g, k, zero_mul, Nat.floor_zero] using hzero n
  have hgone : ∀ n, g n ⟨1, by norm_num⟩ = b := by
    intro n
    simpa only [g, k, one_mul, Nat.floor_natCast] using hend n
  refine ⟨F, ?_, ?_, hLip⟩
  · exact tendsto_nhds_unique (hconv ⟨0, by norm_num⟩)
      (by simpa only [hgzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)))
  · exact tendsto_nhds_unique (hconv ⟨1, by norm_num⟩)
      (by simpa only [hgone] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)))

theorem exists_curve_eVariationOn_lt_of_approximate_midpoints [CompleteSpace X]
    (h : ∀ a b : X, ∀ ε : ℝ, 0 < ε → ∃ z, dist a z ≤ dist a b / 2 + ε ∧
      dist b z ≤ dist a b / 2 + ε) (a b : X) {τ : ℝ} (hτ : 0 < τ) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      LipschitzWith ⟨dist a b + τ / 2, by positivity⟩ f ∧
      eVariationOn f univ < ENNReal.ofReal (dist a b + τ) := by
  classical
  obtain ⟨f, hf0, hf1, hLip⟩ := exists_lipschitz_curve_of_approximate_midpoints h a b hτ
  let K : ℝ≥0 := ⟨dist a b + τ / 2, by positivity⟩
  let g : ℝ → X := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then f ⟨t, ht⟩ else a
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f ⟨t, ht⟩ := by
    simp only [g, dite_eq_left ht]
  have hgLip : LipschitzOnWith K g (Icc (0 : ℝ) 1) := by
    intro s hs t ht
    rw [hg s hs, hg t ht]
    exact hLip ⟨s, hs⟩ ⟨t, ht⟩
  have hgVar : eVariationOn g (Icc (0 : ℝ) 1) ≤ (K : ℝ≥0∞) := by
    simpa only [sub_zero, ENNReal.ofReal_one, mul_one] using
      eVariationOn_Icc_le_of_lipschitzOnWith hgLip
  have hsub : eVariationOn f univ ≤ eVariationOn g (Icc (0 : ℝ) 1) := by
    have hh := eVariationOn.comp_le_of_monotoneOn g
      (fun t : unitInterval => (t : ℝ))
      (show MonotoneOn (fun t : unitInterval => (t : ℝ)) univ from fun s _ t _ hst => hst)
      (show MapsTo (fun t : unitInterval => (t : ℝ)) univ (Icc (0 : ℝ) 1)
        from fun t _ => t.property)
    have heq : g ∘ (fun t : unitInterval => (t : ℝ)) = f := by
      funext t
      exact hg t t.property
    rw [heq] at hh
    exact hh
  refine ⟨f, hLip.continuous, hf0, hf1, hLip, (hsub.trans hgVar).trans_lt ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < dist a b + τ)).mpr
  change dist a b + τ / 2 < dist a b + τ
  linarith

end Metric
