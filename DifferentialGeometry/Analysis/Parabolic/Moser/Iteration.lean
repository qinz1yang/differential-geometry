import DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration.Recurrence
import DifferentialGeometry.Analysis.HoleFilling
import DifferentialGeometry.Analysis.Integration.LpLimit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed


noncomputable section

open Filter Metric

namespace DifferentialGeometry.Analysis.Parabolic.Moser

variable (n : ℕ) [NeZero n]

def parabolicMoserGain : ℝ :=
  1 + 2 / (n : ℝ)

def parabolicMoserDecay : ℝ :=
  (n : ℝ) / ((n : ℝ) + 2)

def parabolicMoserExponent (p₀ : ℝ) (k : ℕ) : ℝ :=
  p₀ * parabolicMoserGain n ^ k

def moserIterationCost (theta a b : ℝ) (k : ℕ) : ℝ :=
  (a + b * k) * theta ^ k

theorem one_lt_parabolicMoserGain :
    1 < parabolicMoserGain n := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiv : 0 < (2 : ℝ) / (n : ℝ) := div_pos (by norm_num) hn
  simp only [parabolicMoserGain]
  linarith

theorem parabolicMoserGain_pos :
    0 < parabolicMoserGain n :=
  (zero_lt_one.trans (one_lt_parabolicMoserGain n))

theorem parabolicMoserDecay_pos :
    0 < parabolicMoserDecay n := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [parabolicMoserDecay]
  positivity

theorem parabolicMoserDecay_lt_one :
    parabolicMoserDecay n < 1 := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [parabolicMoserDecay]
  exact (div_lt_one (by positivity)).2 (by linarith)

omit [NeZero n] in
theorem one_sub_parabolicMoserDecay :
    1 - parabolicMoserDecay n = 2 / ((n : ℝ) + 2) := by
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold parabolicMoserDecay
  field_simp
  ring

omit [NeZero n] in
theorem inv_one_sub_parabolicMoserDecay :
    (1 - parabolicMoserDecay n)⁻¹ = ((n : ℝ) + 2) / 2 := by
  rw [one_sub_parabolicMoserDecay]
  field_simp

omit [NeZero n] in
theorem four_mul_inv_one_sub_parabolicMoserDecay_sq :
    4 * (1 - parabolicMoserDecay n)⁻¹ ^ 2 = ((n : ℝ) + 2) ^ 2 := by
  rw [inv_one_sub_parabolicMoserDecay]
  ring

omit [NeZero n] in
theorem two_mul_inv_one_sub_parabolicMoserDecay :
    2 * (1 - parabolicMoserDecay n)⁻¹ = (n : ℝ) + 2 := by
  rw [inv_one_sub_parabolicMoserDecay]
  ring

theorem parabolicMoserDecay_eq_inv_gain :
    parabolicMoserDecay n = (parabolicMoserGain n)⁻¹ := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  simp only [parabolicMoserDecay, parabolicMoserGain]
  field_simp

omit [NeZero n] in
theorem parabolicMoserExponent_zero (p₀ : ℝ) :
    parabolicMoserExponent n p₀ 0 = p₀ := by
  simp [parabolicMoserExponent]

omit [NeZero n] in
theorem parabolicMoserExponent_succ (p₀ : ℝ) (k : ℕ) :
    parabolicMoserExponent n p₀ (k + 1) =
      parabolicMoserGain n * parabolicMoserExponent n p₀ k := by
  rw [parabolicMoserExponent, pow_succ, parabolicMoserExponent]
  ring

omit [NeZero n] in
theorem parabolicMoserExponent_half_mul_critical
    (p₀ : ℝ) (k : ℕ) :
    (parabolicMoserExponent n p₀ k / 2) * (2 + 4 / (n : ℝ)) =
      parabolicMoserExponent n p₀ (k + 1) := by
  rw [parabolicMoserExponent_succ, parabolicMoserGain]
  ring

omit [NeZero n] in
theorem abs_mul_rpow_half_critical
    {a b p₀ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (k : ℕ) :
    |a * b ^ (parabolicMoserExponent n p₀ k / 2)| ^ (2 + 4 / (n : ℝ)) =
      a ^ (2 + 4 / (n : ℝ)) * b ^ parabolicMoserExponent n p₀ (k + 1) := by
  have hbrpow : 0 ≤ b ^ (parabolicMoserExponent n p₀ k / 2) :=
    Real.rpow_nonneg hb.le _
  rw [abs_of_nonneg (mul_nonneg ha hbrpow), Real.mul_rpow ha hbrpow,
    ← Real.rpow_mul hb.le, parabolicMoserExponent_half_mul_critical]

omit [NeZero n] in
theorem abs_mul_rpow_half_parabolic_gain
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |a * b ^ (q / 2)| ^ (2 + 4 / (n : ℝ)) =
      a ^ (2 + 4 / (n : ℝ)) * b ^ (parabolicMoserGain n * q) := by
  have hbrpow : 0 ≤ b ^ (q / 2) := Real.rpow_nonneg hb.le _
  rw [abs_of_nonneg (mul_nonneg ha hbrpow), Real.mul_rpow ha hbrpow,
    ← Real.rpow_mul hb.le]
  congr 1
  rw [parabolicMoserGain]
  ring_nf

theorem parabolicMoserExponent_pos {p₀ : ℝ} (hp₀ : 0 < p₀) (k : ℕ) :
    0 < parabolicMoserExponent n p₀ k := by
  rw [parabolicMoserExponent]
  exact mul_pos hp₀ (pow_pos (parabolicMoserGain_pos n) k)

theorem parabolicMoserExponent_strictMono {p₀ : ℝ} (hp₀ : 0 < p₀) :
    StrictMono (parabolicMoserExponent n p₀) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [parabolicMoserExponent_succ]
  exact lt_mul_of_one_lt_left (parabolicMoserExponent_pos n hp₀ k)
    (one_lt_parabolicMoserGain n)

theorem parabolicMoserExponent_decay_mul_self (q : ℝ) (m : ℕ) :
    parabolicMoserExponent n (q * parabolicMoserDecay n ^ m) m = q := by
  rw [parabolicMoserExponent, parabolicMoserDecay_eq_inv_gain, inv_pow]
  field_simp [(parabolicMoserGain_pos n).ne']

theorem parabolicMoserExponent_tendsto_atTop {p₀ : ℝ} (hp₀ : 0 < p₀) :
    Tendsto (parabolicMoserExponent n p₀) atTop atTop := by
  simpa only [parabolicMoserExponent, mul_comm] using
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_parabolicMoserGain n)).atTop_mul_const hp₀

theorem exists_parabolic_moser_iteration_depth
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∃ m : ℕ,
      let p₀ := q * parabolicMoserDecay n ^ m
      p₀ < p ∧ p ≤ parabolicMoserGain n * p₀ := by
  let rho := parabolicMoserDecay n
  have hrho_pos : 0 < rho := parabolicMoserDecay_pos n
  have hrho_one : rho < 1 := parabolicMoserDecay_lt_one n
  have hpq_ratio_pos : 0 < p / q := div_pos hp (hp.trans hpq)
  have hpq_ratio_le : p / q ≤ 1 := (div_le_one (hp.trans hpq)).2 hpq.le
  obtain ⟨m, hm_lt, hm_le⟩ :=
    exists_nat_pow_near_of_lt_one hpq_ratio_pos hpq_ratio_le hrho_pos hrho_one
  refine ⟨m + 1, ?_⟩
  dsimp only
  constructor
  · have hmul := mul_lt_mul_of_pos_left hm_lt (hp.trans hpq)
    simpa [rho, div_eq_mul_inv, (hp.trans hpq).ne', mul_assoc, mul_left_comm, mul_comm]
      using hmul
  · have hmul := mul_le_mul_of_nonneg_left hm_le (hp.trans hpq).le
    have hp_le : p ≤ q * rho ^ m := by
      simpa [rho, div_eq_mul_inv, (hp.trans hpq).ne', mul_assoc, mul_left_comm, mul_comm]
        using hmul
    calc
      p ≤ q * rho ^ m := hp_le
      _ = parabolicMoserGain n *
          (q * parabolicMoserDecay n ^ (m + 1)) := by
        change q * parabolicMoserDecay n ^ m = _
        rw [pow_succ, parabolicMoserDecay_eq_inv_gain]
        field_simp [(parabolicMoserGain_pos n).ne']

theorem inv_parabolicMoserExponent {p₀ : ℝ} (hp₀ : 0 < p₀) (k : ℕ) :
    1 / parabolicMoserExponent n p₀ k =
      parabolicMoserDecay n ^ k / p₀ := by
  rw [parabolicMoserExponent, parabolicMoserDecay_eq_inv_gain]
  have hgain : parabolicMoserGain n ≠ 0 := (parabolicMoserGain_pos n).ne'
  rw [inv_pow]
  field_simp [hp₀.ne', pow_ne_zero k hgain]

theorem inv_le_exponent_gap_div_one_sub
    {p₀ q : ℝ} {m : ℕ} (hp₀ : 0 < p₀) (hm : 0 < m)
    (htarget : parabolicMoserExponent n p₀ m = q) :
    1 / p₀ ≤ (1 / p₀ - 1 / q) / (1 - parabolicMoserDecay n) := by
  let theta := parabolicMoserDecay n
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have htheta_one : theta ≤ 1 := (parabolicMoserDecay_lt_one n).le
  have hdenom : 0 < 1 - theta := sub_pos.mpr (parabolicMoserDecay_lt_one n)
  have hpow : theta ^ m ≤ theta :=
    pow_le_of_le_one htheta htheta_one (Nat.ne_of_gt hm)
  have hinv : 1 / q = theta ^ m / p₀ := by
    rw [← htarget]
    simpa only [theta] using inv_parabolicMoserExponent n hp₀ m
  apply (le_div_iff₀ hdenom).2
  rw [hinv]
  have hinv_p₀ : 0 ≤ 1 / p₀ := (div_pos one_pos hp₀).le
  calc
    1 / p₀ * (1 - theta) ≤ 1 / p₀ * (1 - theta ^ m) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hpow 1) hinv_p₀
    _ = 1 / p₀ - theta ^ m / p₀ := by ring

theorem exp_div_le_rpow_exponent_gap
    {D p₀ q : ℝ} {m : ℕ} (hD : 0 ≤ D) (hp₀ : 0 < p₀) (hm : 0 < m)
    (htarget : parabolicMoserExponent n p₀ m = q) :
    Real.exp (D / p₀) ≤
      Real.exp (D / (1 - parabolicMoserDecay n)) ^ (1 / p₀ - 1 / q) := by
  let theta := parabolicMoserDecay n
  have hgap := inv_le_exponent_gap_div_one_sub n hp₀ hm htarget
  have hexponent : D / p₀ ≤
      (1 / p₀ - 1 / q) * (D / (1 - theta)) := by
    have hmul := mul_le_mul_of_nonneg_left hgap hD
    dsimp only [theta] at hmul ⊢
    calc
      D / p₀ = D * (1 / p₀) := by ring
      _ ≤ D * ((1 / p₀ - 1 / q) / (1 - parabolicMoserDecay n)) := hmul
      _ = (1 / p₀ - 1 / q) *
          (D / (1 - parabolicMoserDecay n)) := by ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    D / p₀ ≤ (1 / p₀ - 1 / q) *
        (D / (1 - parabolicMoserDecay n)) := by
      simpa only [theta] using hexponent
    _ = D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / q) := mul_comm _ _

omit [NeZero n] in
theorem moserIterationCost_nonneg
    {theta a b : ℝ} (htheta : 0 ≤ theta) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ moserIterationCost theta a b k := by
  exact mul_nonneg (add_nonneg ha (mul_nonneg hb (Nat.cast_nonneg k)))
    (pow_nonneg htheta k)

omit [NeZero n] in
theorem summable_moserIterationCost
    {theta a b : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta < 1) :
    Summable (moserIterationCost theta a b) := by
  have htheta_norm : ‖theta‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg htheta] using htheta_one
  have hgeom : Summable (fun k : ℕ => theta ^ k) :=
    summable_geometric_of_lt_one htheta htheta_one
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * theta ^ k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 htheta_norm
    simpa only [pow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg htheta _))] using h
  refine ((hgeom.mul_left a).add (hlinear.mul_left b)).congr ?_
  intro k
  simp only [moserIterationCost]
  ring

omit [NeZero n] in
theorem summable_geometric_mul_nat_add_pow
    {r : ℝ} (hr₀ : r ≠ 0) (hr : ‖r‖ < 1) (m : ℕ) :
    Summable (fun k : ℕ => r ^ k * (k + 1 : ℝ) ^ m) := by
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ m * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hr
  have hshift : Summable (fun k : ℕ =>
      (k + 1 : ℝ) ^ m * r ^ (k + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hbase
  refine (hshift.mul_left r⁻¹).congr ?_
  intro k
  rw [pow_succ]
  field_simp

omit [NeZero n] in
theorem summable_geometric_mul_nat_add_rpow
    {r : ℝ} (hr₀ : r ≠ 0) (hr : ‖r‖ < 1) (s : ℝ) :
    Summable (fun k : ℕ ↦ r ^ k * (k + 1 : ℝ) ^ s) := by
  let m := ⌈max s 0⌉₊
  have hrnorm₀ : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr₀
  have hrnorm : ‖‖r‖‖ < 1 := by simpa using hr
  have hmajor : Summable (fun k : ℕ ↦ ‖r‖ ^ k * (k + 1 : ℝ) ^ m) :=
    summable_geometric_mul_nat_add_pow hrnorm₀ hrnorm m
  apply Summable.of_norm_bounded hmajor
  intro k
  have hbase : 1 ≤ (k + 1 : ℝ) := by norm_num
  have hsm : s ≤ (m : ℝ) := by
    exact (le_max_left s 0).trans (Nat.le_ceil (max s 0))
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hbase hsm)
    (pow_nonneg (norm_nonneg r) k)

omit [NeZero n] in
theorem tsum_moserIterationCost
    {theta a b : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta < 1) :
    ∑' k, moserIterationCost theta a b k =
      a / (1 - theta) + b * (theta / (1 - theta) ^ 2) := by
  have htheta_norm : ‖theta‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg htheta] using htheta_one
  have hgeom : Summable (fun k : ℕ => theta ^ k) :=
    summable_geometric_of_lt_one htheta htheta_one
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * theta ^ k) := by
    exact summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 htheta_norm
      |>.congr (fun k => by simp only [pow_one])
  calc
    ∑' k, moserIterationCost theta a b k =
        ∑' k : ℕ, (a * theta ^ k + b * ((k : ℝ) * theta ^ k)) := by
      apply tsum_congr
      intro k
      simp only [moserIterationCost]
      ring
    _ = a * (∑' k : ℕ, theta ^ k) +
        b * (∑' k : ℕ, (k : ℝ) * theta ^ k) := by
      rw [Summable.tsum_add (hgeom.mul_left a) (hlinear.mul_left b),
        tsum_mul_left, tsum_mul_left]
    _ = a * (1 - theta)⁻¹ + b * (theta / (1 - theta) ^ 2) := by
      rw [tsum_geometric_of_lt_one htheta htheta_one,
        tsum_coe_mul_geometric_of_norm_lt_one htheta_norm]
    _ = a / (1 - theta) + b * (theta / (1 - theta) ^ 2) := by
      simp only [div_eq_mul_inv]

omit [NeZero n] in
theorem additive_iteration_le_initial_add_tsum
    {X cost : ℕ → ℝ}
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ X k + cost k) (k : ℕ) :
    X k ≤ X 0 + ∑' j, cost j := by
  have hfinite : ∀ m : ℕ, X m ≤ X 0 + ∑ j ∈ Finset.range m, cost j := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X (m + 1) ≤ X m + cost m := hstep m
          _ ≤ (X 0 + ∑ j ∈ Finset.range m, cost j) + cost m := by linarith
          _ = X 0 + ∑ j ∈ Finset.range (m + 1), cost j := by
            rw [Finset.sum_range_succ]
            ring
  refine (hfinite k).trans ?_
  gcongr
  exact hcost.sum_le_tsum (Finset.range k) (fun j _ => hcost_nonneg j)

omit [NeZero n] in
theorem geometric_hole_filling
    {X : ℕ → ℝ} {theta A B : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (hB : 1 ≤ B) (hA : 0 ≤ A)
    (hthetaB : theta * B < 1)
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + A * B ^ k) :
    X 0 ≤ A / (1 - theta * B) := by
  exact DifferentialGeometry.Analysis.geometric_hole_filling
    hX_bdd htheta hB hA hthetaB hstep

omit [NeZero n] in
theorem summable_hole_filling
    {X cost : ℕ → ℝ} {theta : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hcost : Summable (fun k : ℕ => theta ^ k * cost k))
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + cost k) :
    X 0 ≤ ∑' k : ℕ, theta ^ k * cost k := by
  exact DifferentialGeometry.Analysis.summable_hole_filling
    hX_bdd htheta htheta_one hcost_nonneg hcost hstep

omit [NeZero n] in
theorem multiplicative_iteration_bound
    {X cost : ℕ → ℝ}
    (hX_zero : 0 ≤ X 0)
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ Real.exp (cost k) * X k) (k : ℕ) :
    X k ≤ Real.exp (∑' j, cost j) * X 0 := by
  have hfinite : ∀ m : ℕ,
      X m ≤ Real.exp (∑ j ∈ Finset.range m, cost j) * X 0 := by
    intro m
    induction m with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, one_mul]
        exact le_rfl
    | succ m hm =>
        calc
          X (m + 1) ≤ Real.exp (cost m) * X m := hstep m
          _ ≤ Real.exp (cost m) *
              (Real.exp (∑ j ∈ Finset.range m, cost j) * X 0) := by
            gcongr
          _ = Real.exp (∑ j ∈ Finset.range (m + 1), cost j) * X 0 := by
            rw [Finset.sum_range_succ, Real.exp_add]
            ring
  refine (hfinite k).trans ?_
  gcongr
  exact hcost.sum_le_tsum (Finset.range k) (fun j _ => hcost_nonneg j)

omit [NeZero n] in
theorem finite_multiplicative_iteration
    {X factor : ℕ → ℝ}
    (k : ℕ) (hfactor : ∀ j < k, 0 ≤ factor j)
    (hstep : ∀ j < k, X (j + 1) ≤ factor j * X j) :
    X k ≤ (∏ j ∈ Finset.range k, factor j) * X 0 := by
  induction k with
  | zero => simp
  | succ k hk =>
      calc
        X (k + 1) ≤ factor k * X k := hstep k (Nat.lt_succ_self k)
        _ ≤ factor k * ((∏ j ∈ Finset.range k, factor j) * X 0) :=
          mul_le_mul_of_nonneg_left
            (hk
              (fun j hj => hfactor j (hj.trans (Nat.lt_succ_self k)))
              (fun j hj => hstep j (hj.trans (Nat.lt_succ_self k))))
            (hfactor k (Nat.lt_succ_self k))
        _ = (∏ j ∈ Finset.range (k + 1), factor j) * X 0 := by
          rw [Finset.prod_range_succ]
          ring

omit [NeZero n] in
theorem finite_moser_iteration_bound
    {X : ℕ → ℝ} {theta a b : ℝ} (k : ℕ)
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ j < k, X (j + 1) ≤
      Real.exp (moserIterationCost theta a b j) * X j) :
    X k ≤ Real.exp (∑' j, moserIterationCost theta a b j) * X 0 := by
  have hcost : Summable (moserIterationCost theta a b) :=
    summable_moserIterationCost htheta htheta_one
  have hcost_nonneg : ∀ j, 0 ≤ moserIterationCost theta a b j :=
    moserIterationCost_nonneg htheta ha hb
  have hfinite := finite_multiplicative_iteration k
    (fun _ _ => (Real.exp_pos _).le) hstep
  calc
    X k ≤ (∏ j ∈ Finset.range k,
          Real.exp (moserIterationCost theta a b j)) * X 0 := hfinite
    _ = Real.exp (∑ j ∈ Finset.range k,
          moserIterationCost theta a b j) * X 0 := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (∑' j, moserIterationCost theta a b j) * X 0 := by
      gcongr
      exact hcost.sum_le_tsum (Finset.range k)
        (fun j _ => hcost_nonneg j)

omit [NeZero n] in
theorem bddAbove_range_of_multiplicative_iteration
    {X cost : ℕ → ℝ}
    (hX_zero : 0 ≤ X 0)
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ Real.exp (cost k) * X k) :
    BddAbove (Set.range X) := by
  refine ⟨Real.exp (∑' j, cost j) * X 0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact multiplicative_iteration_bound hX_zero hcost hcost_nonneg hstep k

omit [NeZero n] in
theorem moser_iteration_bound
    {X : ℕ → ℝ} {theta a b : ℝ}
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) (k : ℕ) :
    X k ≤ Real.exp (∑' j, moserIterationCost theta a b j) * X 0 := by
  exact multiplicative_iteration_bound hX_zero
    (summable_moserIterationCost htheta htheta_one)
    (moserIterationCost_nonneg htheta ha hb) hstep k

omit [NeZero n] in
theorem moser_iteration_bddAbove
    {X : ℕ → ℝ} {theta a b : ℝ}
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    BddAbove (Set.range X) := by
  exact bddAbove_range_of_multiplicative_iteration hX_zero
    (summable_moserIterationCost htheta htheta_one)
    (moserIterationCost_nonneg htheta ha hb) hstep

omit [NeZero n] in
theorem normalized_exponent_gain_step
    {L L' sobolev coefficient gain p : ℝ}
    (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hsobolev : 0 ≤ sobolev) (hcoefficient : 0 ≤ coefficient)
    (hgain : 0 < gain) (hp : 0 < p)
    (hstep : L' ≤ sobolev * (coefficient * L) ^ gain) :
    L' ^ (1 / (gain * p)) ≤
      sobolev ^ (1 / (gain * p)) * coefficient ^ (1 / p) * L ^ (1 / p) := by
  have hgp : 0 < gain * p := mul_pos hgain hp
  have hcoefficientL : 0 ≤ coefficient * L := mul_nonneg hcoefficient hL
  have hright : 0 ≤ sobolev * (coefficient * L) ^ gain :=
    mul_nonneg hsobolev (Real.rpow_nonneg hcoefficientL _)
  have hroot := Real.rpow_le_rpow hL' hstep (div_nonneg zero_le_one hgp.le)
  calc
    L' ^ (1 / (gain * p)) ≤
        (sobolev * (coefficient * L) ^ gain) ^ (1 / (gain * p)) := hroot
    _ = sobolev ^ (1 / (gain * p)) *
        ((coefficient * L) ^ gain) ^ (1 / (gain * p)) := by
      rw [Real.mul_rpow hsobolev (Real.rpow_nonneg hcoefficientL _)]
    _ = sobolev ^ (1 / (gain * p)) *
        (coefficient * L) ^ (1 / p) := by
      rw [← Real.rpow_mul hcoefficientL]
      congr 2
      field_simp [hgain.ne', hp.ne']
    _ = sobolev ^ (1 / (gain * p)) * coefficient ^ (1 / p) * L ^ (1 / p) := by
      rw [Real.mul_rpow hcoefficient hL]
      ring

theorem normalized_moser_step
    {p₀ C A L L' : ℝ}
    (hp₀ : 0 < p₀) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (k : ℕ)
    (hstep : L' ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n) :
    L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) ≤
      Real.exp
          (moserIterationCost (parabolicMoserDecay n)
            ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
            (Real.log 16 / p₀) k) *
        L ^ (1 / parabolicMoserExponent n p₀ k) := by
  have hp : 0 < parabolicMoserExponent n p₀ k :=
    parabolicMoserExponent_pos n hp₀ k
  have hp' : 0 < parabolicMoserExponent n p₀ (k + 1) :=
    parabolicMoserExponent_pos n hp₀ (k + 1)
  have hgain : 0 < parabolicMoserGain n := parabolicMoserGain_pos n
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hApos : 0 < A := zero_lt_one.trans_le hA
  by_cases hLzero : L = 0
  · have hL'le : L' ≤ 0 := by
      simpa only [hLzero, mul_zero, Real.zero_rpow hgain.ne', mul_zero] using hstep
    have hL'zero : L' = 0 := le_antisymm hL'le hL'
    rw [hL'zero, hLzero, Real.zero_rpow (one_div_ne_zero hp'.ne'),
      Real.zero_rpow (one_div_ne_zero hp.ne'), mul_zero]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
    have hfactor_pos : 0 < A * 16 ^ k :=
      mul_pos hApos (pow_pos (by norm_num) k)
    have hbase_pos : 0 < (A * 16 ^ k) * L := mul_pos hfactor_pos hLpos
    have htotal_nonneg : 0 ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n :=
      mul_nonneg hCpos.le (Real.rpow_nonneg hbase_pos.le _)
    have hroot := Real.rpow_le_rpow hL' hstep (by positivity :
      0 ≤ 1 / parabolicMoserExponent n p₀ (k + 1))
    have hexponent :
        parabolicMoserGain n *
            (1 / parabolicMoserExponent n p₀ (k + 1)) =
          1 / parabolicMoserExponent n p₀ k := by
      rw [parabolicMoserExponent_succ]
      field_simp [hgain.ne', hp.ne']
    have hprefactor :
        C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
              A ^ (1 / parabolicMoserExponent n p₀ k) *
              (16 ^ k : ℝ) ^ (1 / parabolicMoserExponent n p₀ k) =
          Real.exp
            (moserIterationCost (parabolicMoserDecay n)
              ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
              (Real.log 16 / p₀) k) := by
      rw [Real.rpow_def_of_pos hCpos, Real.rpow_def_of_pos hApos,
        Real.rpow_def_of_pos (pow_pos (by norm_num) k), ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      rw [inv_parabolicMoserExponent n hp₀ k,
        inv_parabolicMoserExponent n hp₀ (k + 1), pow_succ, Real.log_pow]
      simp only [moserIterationCost]
      ring
    calc
      L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) ≤
          (C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n) ^
            (1 / parabolicMoserExponent n p₀ (k + 1)) := hroot
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          (((A * 16 ^ k) * L) ^ parabolicMoserGain n) ^
            (1 / parabolicMoserExponent n p₀ (k + 1)) := by
        rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hbase_pos.le _)]
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          ((A * 16 ^ k) * L) ^
            (1 / parabolicMoserExponent n p₀ k) := by
        rw [← Real.rpow_mul hbase_pos.le, hexponent]
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
            A ^ (1 / parabolicMoserExponent n p₀ k) *
            (16 ^ k : ℝ) ^ (1 / parabolicMoserExponent n p₀ k) *
            L ^ (1 / parabolicMoserExponent n p₀ k) := by
        rw [Real.mul_rpow hfactor_pos.le hLpos.le,
          Real.mul_rpow hApos.le (pow_nonneg (by norm_num) k)]
        ring
      _ = Real.exp
            (moserIterationCost (parabolicMoserDecay n)
              ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
              (Real.log 16 / p₀) k) *
          L ^ (1 / parabolicMoserExponent n p₀ k) := by
        rw [hprefactor]

theorem local_boundedness_on_open_of_moser_iteration
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {μ : MeasureTheory.Measure Y} {U : Set Y}
    [MeasureTheory.IsFiniteMeasure (μ.restrict U)] [μ.IsOpenPosMeasure]
    {f : Y → ℝ} {X : ℕ → ℝ} {p₀ theta a b : ℝ}
    (hU : IsOpen U)
    (hp₀ : 0 < p₀)
    (hf : ContinuousOn f U)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_integrable : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) (μ.restrict U))
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hintegral : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    ∀ y ∈ U, f y ≤
      Real.exp (∑' k, moserIterationCost theta a b k) * X 0 := by
  let C := Real.exp (∑' k, moserIterationCost theta a b k) * X 0
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le hX_zero
  have hroot_le : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ C := by
    intro k
    exact (hintegral k).trans
      (moser_iteration_bound hX_zero htheta htheta_one ha hb hstep k)
  have hbound : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ≤
        C ^ parabolicMoserExponent n p₀ k := by
    intro k
    let p := parabolicMoserExponent n p₀ k
    let integral := ∫ y, f y ^ p ∂μ.restrict U
    have hp : 0 < p := by
      dsimp [p, parabolicMoserExponent]
      exact mul_pos hp₀ (pow_pos (by
        dsimp [parabolicMoserGain]
        have hn : 0 < (n : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
        positivity) k)
    have hintegral_nonneg : 0 ≤ integral := by
      dsimp [integral]
      exact MeasureTheory.integral_nonneg fun y => Real.rpow_nonneg (hf_nonneg y) _
    have hroot : integral ^ (1 / p) ≤ C := by
      simpa only [integral, p] using hroot_le k
    calc
      integral = integral ^ (1 : ℝ) := (Real.rpow_one integral).symm
      _ = integral ^ ((1 / p) * p) := by
        congr 2
        field_simp [hp.ne']
      _ = (integral ^ (1 / p)) ^ p := by
        rw [Real.rpow_mul hintegral_nonneg]
      _ ≤ C ^ p := Real.rpow_le_rpow
        (Real.rpow_nonneg hintegral_nonneg _) hroot hp.le
  exact DifferentialGeometry.Analysis.Integration.le_on_open_of_integral_rpow_le
    hU hC
    (parabolicMoserExponent_pos n hp₀)
    (parabolicMoserExponent_tendsto_atTop n hp₀)
    hf hf_nonneg hf_integrable hbound

theorem local_boundedness_of_moser_iteration
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {μ : MeasureTheory.Measure Y}
    [MeasureTheory.IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : Y → ℝ} {X : ℕ → ℝ} {p₀ theta a b : ℝ}
    (hp₀ : 0 < p₀)
    (hf : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_integrable : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) μ)
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hintegral : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    ∀ y, f y ≤
      Real.exp (∑' k, moserIterationCost theta a b k) * X 0 := by
  have hf_integrable' : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) (μ.restrict Set.univ) := by
    simpa only [MeasureTheory.Measure.restrict_univ] using hf_integrable
  have hintegral' : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict Set.univ) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k := by
    simpa only [MeasureTheory.Measure.restrict_univ] using hintegral
  have h := local_boundedness_on_open_of_moser_iteration (n := n)
    (μ := μ) (U := Set.univ) isOpen_univ hp₀ hf.continuousOn hf_nonneg
    hf_integrable' hX_zero htheta htheta_one ha hb hintegral' hstep
  exact fun y => h y (Set.mem_univ y)

omit [NeZero n] in
theorem superlinear_recurrence_tendsto_zero
    {Y : ℕ → ℝ} {C B alpha : ℝ}
    (hC : 0 < C) (hB : 1 < B) (halpha : 0 < alpha)
    (hY_nonneg : ∀ k, 0 ≤ Y k)
    (hrec : ∀ k, Y (k + 1) ≤ C * B ^ k * Y k ^ (1 + alpha))
    (hsmall : Y 0 ≤ C ^ (-(1 : ℝ) / alpha) * B ^ (-(1 : ℝ) / alpha ^ 2)) :
    Tendsto Y atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := DeGiorgi.deGiorgi_recurrence_closeout
    hC hB halpha hY_nonneg hrec hsmall epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hY_nonneg k)]
  exact hN k hk

end DifferentialGeometry.Analysis.Parabolic.Moser

end
