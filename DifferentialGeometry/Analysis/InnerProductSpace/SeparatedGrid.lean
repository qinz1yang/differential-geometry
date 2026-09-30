import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set

namespace EuclideanSpace

theorem exists_separated_grid (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : Finset (EuclideanSpace ℝ (Fin k)),
      (δ⁻¹) ^ k ≤ (G.card : ℝ) ∧
      (∀ x ∈ G, ‖x‖ ≤ Real.sqrt k) ∧
      (G : Set (EuclideanSpace ℝ (Fin k))).Pairwise (fun a b => δ ≤ dist a b) := by
  classical
  let N := ⌊δ⁻¹⌋₊ + 1
  let g (v : Fin k → Fin N) : EuclideanSpace ℝ (Fin k) :=
    WithLp.toLp 2 (fun i => δ * (v i).val)
  have hginj : Function.Injective g := by
    intro v w h
    funext i
    apply Fin.ext
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin k) => x i) h
    change δ * ((v i).val : ℝ) = δ * ((w i).val : ℝ) at hi
    exact_mod_cast mul_left_cancel₀ hδ.ne' hi
  let G := Finset.univ.image g
  refine ⟨G, ?_, ?_, ?_⟩
  · have hcard : G.card = N ^ k := by
      rw [Finset.card_image_of_injective _ hginj]
      simp
    rw [hcard, Nat.cast_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hf := (Nat.lt_floor_add_one (δ⁻¹)).le
    simpa only [N, Nat.cast_add, Nat.cast_one] using hf
  · intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    have hv (i : Fin k) : 0 ≤ (g v) i ∧ (g v) i ≤ 1 := by
      have hi : (v i).val ≤ ⌊δ⁻¹⌋₊ := Nat.le_of_lt_succ (v i).isLt
      have hir : ((v i).val : ℝ) ≤ ⌊δ⁻¹⌋₊ := by exact_mod_cast hi
      have hf := Nat.floor_le (by positivity : 0 ≤ δ⁻¹)
      have hm := mul_le_mul_of_nonneg_left (hir.trans hf) hδ.le
      change 0 ≤ δ * ((v i).val : ℝ) ∧ δ * ((v i).val : ℝ) ≤ 1
      refine ⟨by positivity, ?_⟩
      simpa only [mul_inv_cancel₀ hδ.ne'] using hm
    have hsq : ‖g v‖ ^ 2 ≤ (k : ℝ) := by
      rw [real_norm_sq_eq]
      calc
        ∑ i, (g v i) ^ 2 ≤ ∑ _i : Fin k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          nlinarith [(hv i).1, (hv i).2]
        _ = k := by simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) by positivity),
      Real.sqrt_nonneg (k : ℝ), norm_nonneg (g v)]
  · intro x hx y hy hxy
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
    have hvw : v ≠ w := fun h => hxy (congrArg g h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hvw
    have hval : (v i).val ≠ (w i).val := fun he => hi (Fin.ext he)
    have hgap : 1 ≤ |((v i).val : ℝ) - (w i).val| := by
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · have hn : (v i).val + 1 ≤ (w i).val := hlt
        have hr : ((v i).val : ℝ) + 1 ≤ (w i).val := by exact_mod_cast hn
        rw [abs_of_neg (by linarith)]
        linarith
      · have hn : (w i).val + 1 ≤ (v i).val := hgt
        have hr : ((w i).val : ℝ) + 1 ≤ (v i).val := by exact_mod_cast hn
        rw [abs_of_pos (by linarith)]
        linarith
    have hcoord : δ ≤ dist (g v i) (g w i) := by
      change δ ≤ |δ * ((v i).val : ℝ) - δ * ((w i).val : ℝ)|
      rw [← mul_sub, abs_mul, abs_of_pos hδ]
      nlinarith
    exact hcoord.trans (PiLp.dist_apply_le (g v) (g w) i)

end EuclideanSpace
