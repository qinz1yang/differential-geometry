import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

open scoped BigOperators

namespace DifferentialGeometry
namespace Combinatorics

noncomputable def markGrid (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, w => antidiagonalTupleGridWindow b (w + 1)
  | u + 1, w => ∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w - c)

@[simp] lemma markGrid_zero (b : ℕ → ℝ) (w : ℕ) :
    markGrid b 0 w = antidiagonalTupleGridWindow b (w + 1) := rfl

lemma markGrid_succ (b : ℕ → ℝ) (u w : ℕ) :
    markGrid b (u + 1) w =
      ∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w - c) := rfl

lemma markGrid_nn (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (u w : ℕ) :
    0 ≤ markGrid b u w := by
  induction u generalizing w with
  | zero => exact antidiagonalTupleGridWindow_nonneg b hb _
  | succ u ih =>
      rw [markGrid_succ]
      exact Finset.sum_nonneg (fun c _ => mul_nonneg (hb _) (ih _))

lemma one_le_markGrid0 (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (w : ℕ) :
    (1 : ℝ) ≤ markGrid b 0 w :=
  one_le_antidiagonalTupleGridWindow b hb (by omega)

lemma markGrid_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (u : ℕ) {w w' : ℕ} (h : w ≤ w') :
    markGrid b u w ≤ markGrid b u w' := by
  induction u generalizing w w' with
  | zero => exact antidiagonalTupleGridWindow_mono b hb (by omega)
  | succ u ih =>
      rw [markGrid_succ, markGrid_succ]
      have hstep : (∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w - c)) ≤
          ∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w' - c) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        rw [Finset.mem_range] at hc
        exact mul_le_mul_of_nonneg_left (ih (by omega)) (hb _)
      have hsub : (∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w' - c)) ≤
          ∑ c ∈ Finset.range (w' + 1), b (c + 1) * markGrid b u (w' - c) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega))
          (fun c _ _ => mul_nonneg (hb _) (markGrid_nn b hb u _))
      exact le_trans hstep hsub

lemma mulConst_mono {a c a' c' : ℕ} (ha : a ≤ a') (hc : c ≤ c') :
    antidiagonalTupleGridWindowMulConst a c ≤
      antidiagonalTupleGridWindowMulConst a' c' := by
  have hnn : ∀ j k : ℕ, (0 : ℝ) ≤
      antidiagonalTupleGridCount j * antidiagonalTupleGridCount k :=
    fun j k => mul_nonneg (antidiagonalTupleGridCount_nonneg j)
      (antidiagonalTupleGridCount_nonneg k)
  rw [antidiagonalTupleGridWindowMulConst, antidiagonalTupleGridWindowMulConst]
  have h1 : (∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c + 1),
        antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) ≤
      ∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c' + 1),
        antidiagonalTupleGridCount j * antidiagonalTupleGridCount k := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega)) (fun k _ _ => hnn j k)
  have h2 : (∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c' + 1),
        antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) ≤
      ∑ j ∈ Finset.range (a' + 1), ∑ k ∈ Finset.range (c' + 1),
        antidiagonalTupleGridCount j * antidiagonalTupleGridCount k :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega))
      (fun j _ _ => Finset.sum_nonneg (fun k _ => hnn j k))
  exact le_trans h1 h2

lemma markGrid_shift (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (u w t : ℕ) :
    (∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w - c + t)) ≤
      markGrid b (u + 1) (w + t) := by
  rw [markGrid_succ]
  have hstep : (∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w - c + t)) ≤
      ∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w + t - c) := by
    refine Finset.sum_le_sum (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hb _)
    congr 1
    omega
  have hsub : (∑ c ∈ Finset.range (w + 1), b (c + 1) * markGrid b u (w + t - c)) ≤
      ∑ c ∈ Finset.range (w + t + 1), b (c + 1) * markGrid b u (w + t - c) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega))
      (fun c _ _ => mul_nonneg (hb _) (markGrid_nn b hb u _))
  exact le_trans hstep hsub

theorem markGrid_mul (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (u₁ u₂ w₁ w₂ : ℕ) :
    markGrid b u₁ w₁ * markGrid b u₂ w₂ ≤
      antidiagonalTupleGridWindowMulConst w₁ w₂ *
        markGrid b (u₁ + u₂) (w₁ + w₂) := by
  induction u₁ generalizing u₂ w₁ w₂ with
  | zero =>
      simp only [Nat.zero_add]
      induction u₂ generalizing w₁ w₂ with
      | zero => exact antidiagonalTupleGridWindow_mul_le b hb w₁ w₂
      | succ v ihv =>
          rw [markGrid_succ, Finset.mul_sum]
          have hstep : ∀ d ∈ Finset.range (w₂ + 1),
              markGrid b 0 w₁ * (b (d + 1) * markGrid b v (w₂ - d)) ≤
                antidiagonalTupleGridWindowMulConst w₁ w₂ *
                  (b (d + 1) * markGrid b v (w₂ - d + w₁)) := by
            intro d hd
            rw [Finset.mem_range] at hd
            have hih := ihv w₁ (w₂ - d)
            have hmc : antidiagonalTupleGridWindowMulConst w₁ (w₂ - d) ≤
                antidiagonalTupleGridWindowMulConst w₁ w₂ :=
              mulConst_mono (le_refl _) (by omega)
            have hmg_nn : 0 ≤ markGrid b v (w₁ + (w₂ - d)) := markGrid_nn b hb v _
            have heq : w₁ + (w₂ - d) = w₂ - d + w₁ := by omega
            calc markGrid b 0 w₁ * (b (d + 1) * markGrid b v (w₂ - d))
                = b (d + 1) * (markGrid b 0 w₁ * markGrid b v (w₂ - d)) := by ring
              _ ≤ b (d + 1) * (antidiagonalTupleGridWindowMulConst w₁ (w₂ - d) *
                    markGrid b v (w₁ + (w₂ - d))) :=
                  mul_le_mul_of_nonneg_left hih (hb _)
              _ ≤ b (d + 1) * (antidiagonalTupleGridWindowMulConst w₁ w₂ *
                    markGrid b v (w₁ + (w₂ - d))) := by
                  refine mul_le_mul_of_nonneg_left ?_ (hb _)
                  exact mul_le_mul_of_nonneg_right hmc hmg_nn
              _ = antidiagonalTupleGridWindowMulConst w₁ w₂ *
                    (b (d + 1) * markGrid b v (w₂ - d + w₁)) := by
                  rw [heq]; ring
          refine le_trans (Finset.sum_le_sum hstep) ?_
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_
            (antidiagonalTupleGridWindowMulConst_nonneg _ _)
          have hsh := markGrid_shift b hb v w₂ w₁
          have hcomm : w₂ + w₁ = w₁ + w₂ := by omega
          rw [hcomm] at hsh
          exact hsh
  | succ u ihu =>
      rw [markGrid_succ, Finset.sum_mul]
      have hstep : ∀ c ∈ Finset.range (w₁ + 1),
          b (c + 1) * markGrid b u (w₁ - c) * markGrid b u₂ w₂ ≤
            antidiagonalTupleGridWindowMulConst w₁ w₂ *
              (b (c + 1) * markGrid b (u + u₂) (w₁ - c + w₂)) := by
        intro c hc
        rw [Finset.mem_range] at hc
        have hih := ihu u₂ (w₁ - c) w₂
        have hmc : antidiagonalTupleGridWindowMulConst (w₁ - c) w₂ ≤
            antidiagonalTupleGridWindowMulConst w₁ w₂ :=
          mulConst_mono (by omega) (le_refl _)
        have hmg_nn : 0 ≤ markGrid b (u + u₂) (w₁ - c + w₂) := markGrid_nn b hb _ _
        calc b (c + 1) * markGrid b u (w₁ - c) * markGrid b u₂ w₂
            = b (c + 1) * (markGrid b u (w₁ - c) * markGrid b u₂ w₂) := by ring
          _ ≤ b (c + 1) * (antidiagonalTupleGridWindowMulConst (w₁ - c) w₂ *
                markGrid b (u + u₂) (w₁ - c + w₂)) :=
              mul_le_mul_of_nonneg_left hih (hb _)
          _ ≤ b (c + 1) * (antidiagonalTupleGridWindowMulConst w₁ w₂ *
                markGrid b (u + u₂) (w₁ - c + w₂)) := by
              refine mul_le_mul_of_nonneg_left ?_ (hb _)
              exact mul_le_mul_of_nonneg_right hmc hmg_nn
          _ = antidiagonalTupleGridWindowMulConst w₁ w₂ *
                (b (c + 1) * markGrid b (u + u₂) (w₁ - c + w₂)) := by ring
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_
        (antidiagonalTupleGridWindowMulConst_nonneg _ _)
      have hidx : u + 1 + u₂ = (u + u₂) + 1 := by omega
      rw [hidx]
      exact markGrid_shift b hb (u + u₂) w₁ w₂

lemma markOne_of_term (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {j c k : ℕ}
    (h : c + 1 + k ≤ j + 1) :
    b (c + 1) * antidiagonalTupleGrid b k ≤ markGrid b 1 j := by
  rw [markGrid_succ]
  have hc : c ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun c' => b (c' + 1) * markGrid b 0 (j - c'))
    (fun c' _ => mul_nonneg (hb _) (markGrid_nn b hb 0 _)) hc)
  refine mul_le_mul_of_nonneg_left ?_ (hb _)
  rw [markGrid_zero]
  exact antidiagonalTupleGrid_le_window b hb (by omega)

lemma prodLeGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hb0 : b 0 ≤ 1) :
    ∀ (n : ℕ) (e : Fin n → ℕ),
      (∏ m : Fin n, b (e m)) ≤ antidiagonalTupleGrid b (∑ m, e m)
  | 0, e => by
      rw [Fin.prod_univ_zero, Fin.sum_univ_zero, antidiagonalTupleGrid_zero]
  | (n + 1), e => by
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      have hih := prodLeGrid b hb hb0 n (fun m => e m.succ)
      have htail : (0 : ℝ) ≤ ∏ m : Fin n, b (e m.succ) :=
        Finset.prod_nonneg (fun m _ => hb _)
      match hq : e 0 with
      | 0 =>
          rw [Nat.zero_add]
          exact le_trans (mul_le_of_le_one_left htail hb0) hih
      | (q + 1) =>
          refine le_trans (mul_le_mul_of_nonneg_left hih (hb _)) ?_
          have h := single_factor_mul_antidiagonalTupleGrid_le b hb
            (∑ m : Fin n, e m.succ) (q + 1) (by omega)
          rwa [Nat.add_comm (∑ m : Fin n, e m.succ) (q + 1)] at h

lemma prodLeMark1 (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hb0 : b 0 ≤ 1) (i : ℕ) :
    ∀ (n : ℕ) (e : Fin n → ℕ), (∑ m, e m) = i + 1 →
      (∏ m : Fin n, b (e m)) ≤ markGrid b 1 i
  | 0, e, he => by
      rw [Fin.sum_univ_zero] at he
      omega
  | (n + 1), e, he => by
      rw [Fin.sum_univ_succ] at he
      rw [Fin.prod_univ_succ]
      have htail : (0 : ℝ) ≤ ∏ m : Fin n, b (e m.succ) :=
        Finset.prod_nonneg (fun m _ => hb _)
      match hq : e 0 with
      | 0 =>
          have hih := prodLeMark1 b hb hb0 i n (fun m => e m.succ)
            (by rw [hq] at he; simpa using he)
          exact le_trans (mul_le_of_le_one_left htail hb0) hih
      | (c + 1) =>
          have hsum : (∑ m : Fin n, e m.succ) = i - c := by rw [hq] at he; omega
          refine le_trans (mul_le_mul_of_nonneg_left
            (prodLeGrid b hb hb0 n (fun m => e m.succ)) (hb _)) ?_
          rw [hsum]
          exact markOne_of_term b hb (by rw [hq] at he; omega)

lemma atgLeMark1 (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hb0 : b 0 ≤ 1) (i : ℕ) :
    antidiagonalTupleGrid b (i + 1) ≤
      antidiagonalTupleGridCount (i + 1) * markGrid b 1 i := by
  classical
  rw [antidiagonalTupleGrid, antidiagonalTupleGridCount, Finset.sum_mul]
  refine Finset.sum_le_sum (fun n _ => ?_)
  calc (∑ e ∈ Finset.Nat.antidiagonalTuple n (i + 1), ∏ m : Fin n, b (e m))
      ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n (i + 1), markGrid b 1 i := by
        refine Finset.sum_le_sum (fun e he => ?_)
        rw [Finset.Nat.mem_antidiagonalTuple] at he
        exact prodLeMark1 b hb hb0 i n e he
    _ = ((Finset.Nat.antidiagonalTuple n (i + 1)).card : ℝ) * markGrid b 1 i := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Combinatorics
end DifferentialGeometry
