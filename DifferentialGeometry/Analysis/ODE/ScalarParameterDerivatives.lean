import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Weighted
import Mathlib.Analysis.ODE.Gronwall

open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem iteratedDeriv_neg_mul (v q : ℝ → ℝ) (j : ℕ) (x : ℝ)
    (hv : ContDiffAt ℝ j v x) (hq : ContDiffAt ℝ j q x) :
    iteratedDeriv j (fun y => -(q y * v y)) x =
      -q x * iteratedDeriv j v x -
        ∑ i ∈ Finset.range j,
          (j.choose i : ℝ) * iteratedDeriv (j - i) q x * iteratedDeriv i v x := by
  have hmul : (fun y => -(q y * v y)) = fun y => (-1 : ℝ) * (v y * q y) := by
    funext y
    ring
  rw [hmul, iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hv hq,
    Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.sub_self, iteratedDeriv_zero, Nat.cast_one, one_mul]
  have hsum : (∑ i ∈ Finset.range j,
      (j.choose i : ℝ) * iteratedDeriv i v x * iteratedDeriv (j - i) q x) =
      ∑ i ∈ Finset.range j,
        (j.choose i : ℝ) * iteratedDeriv (j - i) q x * iteratedDeriv i v x := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

end DifferentialGeometry.Analysis


namespace DifferentialGeometry.Analysis

theorem hasDerivWithinAt_iteratedDeriv_of_derivWithin_eq_neg_mul
    {v q : ℝ → ℝ → ℝ} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ J))
    {j : ℕ} {x t : ℝ} (hx : x ∈ U) (ht : t ∈ J)
    (hq : ContDiffAt ℝ j (fun y => q y t) x)
    (heq : ∀ y ∈ U, derivWithin (v y) J t = -(q y t * v y t)) :
    HasDerivWithinAt (fun s => iteratedDeriv j (fun y => v y s) x)
      (-q x t * iteratedDeriv j (fun y => v y t) x -
        ∑ i ∈ Finset.range j,
          (j.choose i : ℝ) * iteratedDeriv (j - i) (fun y => q y t) x *
            iteratedDeriv i (fun y => v y t) x) J t := by
  have hvx : ContDiffAt ℝ j (fun y => v y t) x :=
    (((hv (x, t) ⟨hx, ht⟩).comp (s := U) (f := fun y : ℝ => (y, t)) x
      (contDiffWithinAt_id.prodMk contDiffWithinAt_const)
      (fun y hy => ⟨hy, ht⟩)).contDiffAt (hU.mem_nhds hx)).of_le
        (by exact_mod_cast le_top)
  have hjet := hasDerivWithinAt_iteratedDeriv_fst hU hJ hacc hv j hx ht
  have heqjet := Set.EqOn.iteratedDeriv_of_isOpen heq hU j hx
  rw [heqjet, iteratedDeriv_neg_mul _ _ j x hvx hq] at hjet
  exact hjet

end DifferentialGeometry.Analysis


namespace DifferentialGeometry.Analysis

theorem hasDerivAt_iteratedDeriv_of_deriv_eq_neg_mul
    {v q : ℝ → ℝ → ℝ} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ V))
    {j : ℕ} {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V)
    (hq : ContDiffAt ℝ j (fun y => q y t) x)
    (heq : ∀ y ∈ U, deriv (v y) t = -(q y t * v y t)) :
    HasDerivAt (fun s => iteratedDeriv j (fun y => v y s) x)
      (-q x t * iteratedDeriv j (fun y => v y t) x -
        ∑ i ∈ Finset.range j,
          (j.choose i : ℝ) * iteratedDeriv (j - i) (fun y => q y t) x *
            iteratedDeriv i (fun y => v y t) x) t := by
  have hacc : V ⊆ closure (interior V) := by
    rw [hV.interior_eq]
    exact subset_closure
  have heqWithin : ∀ y ∈ U, derivWithin (v y) V t = -(q y t * v y t) := by
    intro y hy
    simpa only [derivWithin_of_isOpen hV ht] using heq y hy
  exact (hasDerivWithinAt_iteratedDeriv_of_derivWithin_eq_neg_mul
    hU hV.uniqueDiffOn hacc hv hx ht hq heqWithin).hasDerivAt (hV.mem_nhds ht)

end DifferentialGeometry.Analysis

open Set

namespace DifferentialGeometry.Analysis

theorem norm_iteratedDeriv_le_gronwallBound_of_deriv_eq_neg_mul
    {v q : ℝ → ℝ → ℝ} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ V))
    {j : ℕ} {x s T t R : ℝ} (hx : x ∈ U) (ht : t ∈ Ico s T)
    (hwindow : Ico s T ⊆ V)
    (hq : ∀ r ∈ Ico s T, ContDiffAt ℝ j (fun y => q y r) x)
    (heq : ∀ r ∈ Ico s T, ∀ y ∈ U, deriv (v y) r = -(q y r * v y r))
    {Q A : ℕ → ℝ}
    (hQ : ∀ i ≤ j, ∀ r ∈ Ico s T, ‖iteratedDeriv i (fun y => q y r) x‖ ≤ Q i)
    (hA : ∀ i < j, ∀ r ∈ Ico s T, ‖iteratedDeriv i (fun y => v y r) x‖ ≤ A i)
    (hinit : ‖iteratedDeriv j (fun y => v y s) x‖ ≤ R) :
    ‖iteratedDeriv j (fun y => v y t) x‖ ≤
      gronwallBound R (Q 0)
        (∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i) (t - s) := by
  let w := fun r => iteratedDeriv j (fun y => v y r) x
  let w' := fun r => -q x r * w r -
    ∑ i ∈ Finset.range j, (j.choose i : ℝ) *
      iteratedDeriv (j - i) (fun y => q y r) x * iteratedDeriv i (fun y => v y r) x
  have hsub : Icc s t ⊆ Ico s T := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hd (r : ℝ) (hr : r ∈ Ico s T) : HasDerivAt w (w' r) r :=
    hasDerivAt_iteratedDeriv_of_deriv_eq_neg_mul hU hV hv hx (hwindow hr)
      (hq r hr) (heq r hr)
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (fun r hr => (hd r (hsub hr)).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (hsub (Ico_subset_Icc_self hr))).hasDerivWithinAt)
    hinit ?_ t (right_mem_Icc.mpr ht.1)
  intro r hr
  have hr' := hsub (Ico_subset_Icc_self hr)
  have hq0 : ‖q x r‖ ≤ Q 0 := by simpa only [iteratedDeriv_zero] using hQ 0 (Nat.zero_le j) r hr'
  have hsum : ‖∑ i ∈ Finset.range j, (j.choose i : ℝ) *
      iteratedDeriv (j - i) (fun y => q y r) x * iteratedDeriv i (fun y => v y r) x‖ ≤
      ∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hij := Finset.mem_range.mp hi
    have hqi := hQ (j - i) (Nat.sub_le j i) r hr'
    have hai := hA i hij r hr'
    have hQnonneg : 0 ≤ Q (j - i) := (norm_nonneg _).trans hqi
    rw [norm_mul, norm_mul, Real.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hqi (Nat.cast_nonneg _)) hai
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hQnonneg)
  calc
    ‖w' r‖ ≤ ‖-q x r * w r‖ + ‖∑ i ∈ Finset.range j, (j.choose i : ℝ) *
        iteratedDeriv (j - i) (fun y => q y r) x * iteratedDeriv i (fun y => v y r) x‖ :=
      norm_sub_le _ _
    _ ≤ Q 0 * ‖w r‖ + ∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i := by
      apply add_le_add _ hsum
      simpa only [norm_mul, norm_neg] using mul_le_mul_of_nonneg_right hq0 (norm_nonneg (w r))


theorem norm_iteratedDeriv_le_of_deriv_eq_neg_mul
    {v q : ℝ → ℝ → ℝ} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ V))
    {j : ℕ} {x s T t R : ℝ} (hx : x ∈ U) (ht : t ∈ Ico s T)
    (hwindow : Ico s T ⊆ V)
    (hq : ∀ r ∈ Ico s T, ContDiffAt ℝ j (fun y => q y r) x)
    (heq : ∀ r ∈ Ico s T, ∀ y ∈ U, deriv (v y) r = -(q y r * v y r))
    {Q A : ℕ → ℝ}
    (hQ : ∀ i ≤ j, ∀ r ∈ Ico s T, ‖iteratedDeriv i (fun y => q y r) x‖ ≤ Q i)
    (hA : ∀ i < j, ∀ r ∈ Ico s T, ‖iteratedDeriv i (fun y => v y r) x‖ ≤ A i)
    (hinit : ‖iteratedDeriv j (fun y => v y s) x‖ ≤ R) :
    ‖iteratedDeriv j (fun y => v y t) x‖ ≤
      gronwallBound R (Q 0)
        (∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i) (T - s) := by
  have hs : s ∈ Ico s T := ⟨le_rfl, lt_of_le_of_lt ht.1 ht.2⟩
  have hRnonneg : 0 ≤ R := (norm_nonneg _).trans hinit
  have hQnonneg (i : ℕ) (hi : i ≤ j) : 0 ≤ Q i :=
    (norm_nonneg _).trans (hQ i hi s hs)
  have hAnonneg (i : ℕ) (hi : i < j) : 0 ≤ A i :=
    (norm_nonneg _).trans (hA i hi s hs)
  have hsum : 0 ≤ ∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hQnonneg (j - i) (Nat.sub_le j i)))
      (hAnonneg i (Finset.mem_range.mp hi))
  exact (norm_iteratedDeriv_le_gronwallBound_of_deriv_eq_neg_mul hU hV hv hx ht hwindow
    hq heq hQ hA hinit).trans
    (gronwallBound_mono hRnonneg hsum (hQnonneg 0 (Nat.zero_le j))
      (sub_le_sub_right ht.2.le s))

end DifferentialGeometry.Analysis


namespace DifferentialGeometry.Analysis

theorem exists_iteratedDeriv_bounds_of_weightedDeriv_and_deriv_eq_neg_mul
    {v q : ℝ → ℝ → ℝ} {U V : Set ℝ} {s T : ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ V))
    (hwindow : Ico s T ⊆ V)
    (hq : ∀ x ∈ U, ∀ t ∈ Ico s T, ContDiffAt ℝ ∞ (fun y => q y t) x)
    (hvn : ∀ x ∈ U, ∀ t ∈ Ico s T, v x t ≠ 0)
    (heq : ∀ t ∈ Ico s T, ∀ x ∈ U, deriv (v x) t = -(q x t * v x t))
    (hinit : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖iteratedDeriv j (fun y => v y s) x‖ ≤ C)
    (hqb : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ t ∈ Ico s T,
      ‖((weightedDeriv (fun y => (v y t)⁻¹))^[j] (fun y => q y t)) x‖ ≤ C) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ t ∈ Ico s T,
      ‖iteratedDeriv j (fun y => v y t) x‖ ≤ C := by
  classical
  have hfin (k : ℕ) : (k : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hvx (x : ℝ) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ico s T) :
      ContDiffAt ℝ ∞ (fun y => v y t) x :=
    ((hv (x, t) ⟨hx, hwindow ht⟩).contDiffAt ((hU.prod hV).mem_nhds ⟨hx, hwindow ht⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hqderiv (i : ℕ) (hi : i ≤ j) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ t ∈ Ico s T,
          ‖iteratedDeriv i (fun y => q y t) x‖ ≤ C := by
      let P := {p : ℝ × ℝ // p.1 ∈ U ∧ p.2 ∈ Ico s T}
      obtain ⟨C, hC, hbound⟩ := exists_iteratedDeriv_bound_of_weightedDeriv i
        (fun p : P => p.1.1) (fun p : P => fun y => v y p.1.2)
        (fun p : P => fun y => q y p.1.2)
        (fun p => (hvx p.1.1 p.2.1 p.1.2 p.2.2).of_le (hfin (i - 1)))
        (fun p => (hq p.1.1 p.2.1 p.1.2 p.2.2).of_le (hfin i))
        (fun p => hvn p.1.1 p.2.1 p.1.2 p.2.2)
        (fun k hk => by
          obtain ⟨A, hA, hb⟩ := ih k (lt_of_lt_of_le hk hi)
          exact ⟨A, hA, fun p => hb p.1.1 p.2.1 p.1.2 p.2.2⟩)
        (fun k _ => by
          obtain ⟨A, hA, hb⟩ := hqb k
          exact ⟨A, hA, fun p => hb p.1.1 p.2.1 p.1.2 p.2.2⟩)
      exact ⟨C, hC, fun x hx t ht => hbound ⟨(x, t), hx, ht⟩⟩
    have hQ (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
        (i ≤ j → ∀ x ∈ U, ∀ t ∈ Ico s T, ‖iteratedDeriv i (fun y => q y t) x‖ ≤ C) := by
      by_cases hi : i ≤ j
      · obtain ⟨C, hC, hb⟩ := hqderiv i hi
        exact ⟨C, hC, fun _ => hb⟩
      · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
    have hA (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
        (i < j → ∀ x ∈ U, ∀ t ∈ Ico s T, ‖iteratedDeriv i (fun y => v y t) x‖ ≤ C) := by
      by_cases hi : i < j
      · obtain ⟨C, hC, hb⟩ := ih i hi
        exact ⟨C, hC, fun _ => hb⟩
      · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
    choose Q hQpos hQbound using hQ
    choose A hApos hAbound using hA
    obtain ⟨R, hR, hRbound⟩ := hinit j
    let C := gronwallBound R (Q 0)
      (∑ i ∈ Finset.range j, (j.choose i : ℝ) * Q (j - i) * A i) (T - s)
    refine ⟨max 0 C, le_max_left _ _, fun x hx t ht => ?_⟩
    exact (norm_iteratedDeriv_le_of_deriv_eq_neg_mul hU hV hv hx ht hwindow
      (fun r hr => (hq x hx r hr).of_le (hfin j)) heq
      (fun i hi r hr => hQbound i hi x hx r hr)
      (fun i hi r hr => hAbound i hi x hx r hr) (hRbound x hx)).trans (le_max_right _ _)

end DifferentialGeometry.Analysis
