import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.Analysis

theorem exists_target_modulus (P : ℝ → ℕ → Prop)
    (hP : ∀ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η → P δ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ modulus : ℝ → ℝ,
      MapsTo modulus (Ioc 0 δ₀) (Ioc 0 1) ∧ Tendsto modulus (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ n : ℕ, modulus δ = ((n : ℝ) + 1)⁻¹ ∧ P δ n := by
  classical
  choose η hη htarget using hP
  let τ : ℕ → ℝ := Nat.rec (min (η 0) 1)
    (fun n prev => min (η (n + 1)) (min (((n : ℝ) + 2)⁻¹) (prev / 2)))
  have hτ : ∀ n : ℕ, 0 < τ n ∧ τ n ≤ η n ∧ τ n ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n
    induction n with
    | zero =>
      simpa only [τ, Nat.rec_zero, Nat.cast_zero, zero_add, inv_one] using
        (show 0 < min (η 0) 1 ∧ min (η 0) 1 ≤ η 0 ∧ min (η 0) 1 ≤ 1 from
          ⟨lt_min (hη 0) zero_lt_one, min_le_left _ _, min_le_right _ _⟩)
    | succ n ih =>
      change 0 < min (η (n + 1)) (min (((n : ℝ) + 2)⁻¹) (τ n / 2)) ∧ _
      refine ⟨lt_min (hη _) (lt_min (inv_pos.mpr (by positivity)) (half_pos ih.1)), min_le_left _ _, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        (min_le_right (η (n + 1)) (min (((n : ℝ) + 2)⁻¹) (τ n / 2))).trans (min_le_left _ _)
  have hstep (n : ℕ) : τ (n + 1) < τ n :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self (hτ n).1)
  have hanti : Antitone τ := (strictAnti_nat_of_succ_lt hstep).antitone
  have hex (δ : ℝ) (hδ : 0 < δ) : ∃ n : ℕ, τ n < δ := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, (hτ n).2.2.trans_lt (by simpa only [one_div] using hn)⟩
  let index : (δ : ℝ) → 0 < δ → ℕ := fun δ hδ =>
    @Nat.find (fun n => τ n < δ) (fun _ => Classical.propDecidable _) (hex δ hδ)
  let modulus (δ : ℝ) : ℝ := if hδ : 0 < δ then (index δ hδ : ℝ)⁻¹ else 1
  have hindex (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hδN : δ ≤ τ N) : N + 1 ≤ index δ hδ := by
    apply (@Nat.le_find_iff (fun n => τ n < δ) (fun _ => Classical.propDecidable _)
      (hex δ hδ) (N + 1)).mpr
    intro r hr
    exact not_lt_of_ge (hδN.trans (hanti (Nat.le_of_lt_succ hr)))
  refine ⟨τ 0, (hτ 0).1, modulus, ?_, ?_, ?_⟩
  · intro δ hδ
    have hi := hindex δ hδ.1 0 hδ.2
    have hir : (1 : ℝ) ≤ (index δ hδ.1 : ℝ) := by exact_mod_cast hi
    simp only [modulus, dif_pos hδ.1, mem_Ioc]
    exact ⟨inv_pos.mpr (zero_lt_one.trans_le hir), (inv_le_one₀ (zero_lt_one.trans_le hir)).mpr hir⟩
  · apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [] with δ
      have hnonneg : 0 ≤ modulus δ := by
        dsimp only [modulus]
        split_ifs <;> positivity
      exact ha.trans_le hnonneg
    · intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      filter_upwards [Ioo_mem_nhdsGT (hτ N).1] with δ hδ
      have hi := hindex δ hδ.1 N hδ.2.le
      have hir : (N : ℝ) + 1 ≤ (index δ hδ.1 : ℝ) := by exact_mod_cast hi
      have hpos : 0 < (N : ℝ) + 1 := by positivity
      have hinv : (index δ hδ.1 : ℝ)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := inv_anti₀ hpos hir
      have hN' : ((N : ℝ) + 1)⁻¹ < ε := by simpa only [one_div] using hN
      simpa only [modulus, dif_pos hδ.1] using hinv.trans_lt hN'
  · intro δ hδ hle
    let n := index δ hδ - 1
    have hi := hindex δ hδ 0 hle
    have hn : n + 1 = index δ hδ := by dsimp only [n]; omega
    have hlt : n < index δ hδ := by dsimp only [n]; omega
    have hmin : δ ≤ τ n := le_of_not_gt
      (@Nat.find_min (fun r => τ r < δ) (fun _ => Classical.propDecidable _) (hex δ hδ) n hlt)
    refine ⟨n, ?_, htarget n δ hδ (hmin.trans (hτ n).2.1)⟩
    simp only [modulus, dif_pos hδ]
    congr 1
    exact_mod_cast hn.symm
end DifferentialGeometry.Analysis
