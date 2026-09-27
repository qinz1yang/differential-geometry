import DifferentialGeometry.Topology.Homology.Algebra.EulerCharacteristic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace DifferentialGeometry.ShortComplex

variable {k : Type u} [Field k]

theorem finrank_eq_range_add_range (S : CategoryTheory.ShortComplex (ModuleCat.{v} k))
    [FiniteDimensional k S.X₂] (hS : S.Exact) :
    Module.finrank k S.X₂ = Module.finrank k (LinearMap.range S.f.hom) +
      Module.finrank k (LinearMap.range S.g.hom) := by
  have heq := S.moduleCat_exact_iff_range_eq_ker.mp hS
  rw [heq]
  exact S.g.hom.finrank_range_add_finrank_ker.symm.trans (add_comm _ _)

end DifferentialGeometry.ShortComplex

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type u} [Field k]
  (S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{v} k) ℕ)) (hS : S.ShortExact)
  [∀ n : ℕ, FiniteDimensional k (S.X₁.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₂.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₃.homology n)]

private def connectingRank (n : ℕ) : ℤ :=
  Module.finrank k (LinearMap.range (hS.δ (n + 1) n rfl).hom)

include hS

omit [∀ n : ℕ, FiniteDimensional k (S.X₂.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₃.homology n)] in
private theorem homology_rank_one (n : ℕ) :
    (Module.finrank k (S.X₁.homology n) : ℤ) = connectingRank S hS n +
      Module.finrank k (LinearMap.range (_root_.HomologicalComplex.homologyMap S.f n).hom) := by
  unfold connectingRank
  exact_mod_cast DifferentialGeometry.ShortComplex.finrank_eq_range_add_range _ (hS.homology_exact₁ (n + 1) n rfl)

omit [∀ n : ℕ, FiniteDimensional k (S.X₁.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₃.homology n)] in
private theorem homology_rank_two (n : ℕ) :
    (Module.finrank k (S.X₂.homology n) : ℤ) =
      Module.finrank k (LinearMap.range (_root_.HomologicalComplex.homologyMap S.f n).hom) +
        Module.finrank k (LinearMap.range (_root_.HomologicalComplex.homologyMap S.g n).hom) := by
  exact_mod_cast DifferentialGeometry.ShortComplex.finrank_eq_range_add_range _ (hS.homology_exact₂ n)

omit [∀ n : ℕ, FiniteDimensional k (S.X₁.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₂.homology n)] in
private theorem homology_rank_three (n : ℕ) :
    (Module.finrank k (S.X₃.homology (n + 1)) : ℤ) =
      Module.finrank k (LinearMap.range (_root_.HomologicalComplex.homologyMap S.g (n + 1)).hom) +
        connectingRank S hS n := by
  unfold connectingRank
  exact_mod_cast DifferentialGeometry.ShortComplex.finrank_eq_range_add_range _ (hS.homology_exact₃ (n + 1) n rfl)

omit [∀ n : ℕ, FiniteDimensional k (S.X₁.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₂.homology n)]
  [∀ n : ℕ, FiniteDimensional k (S.X₃.homology n)] in
private theorem homology_rank_three_zero :
    Module.finrank k (S.X₃.homology 0) =
      Module.finrank k (LinearMap.range (_root_.HomologicalComplex.homologyMap S.g 0).hom) := by
  have := hS.epi_g
  have := _root_.HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
    intro j
    change ¬ j + 1 = 0
    omega)
  rw [LinearMap.range_eq_top.mpr (ModuleCat.epi_iff_surjective _ |>.mp inferInstance),
    finrank_top]

omit [∀ n : ℕ, FiniteDimensional k (S.X₃.homology n)] in
private theorem homology_euler_summand_zero :
    (Module.finrank k (S.X₁.homology 0) : ℤ) - Module.finrank k (S.X₂.homology 0) +
      Module.finrank k (S.X₃.homology 0) = connectingRank S hS 0 := by
  rw [homology_rank_one S hS, homology_rank_two S hS, homology_rank_three_zero S hS]
  ring

private theorem homology_euler_summand_succ (n : ℕ) :
    (Module.finrank k (S.X₁.homology (n + 1)) : ℤ) - Module.finrank k (S.X₂.homology (n + 1)) +
      Module.finrank k (S.X₃.homology (n + 1)) = connectingRank S hS (n + 1) + connectingRank S hS n := by
  rw [homology_rank_one S hS, homology_rank_two S hS, homology_rank_three S hS]
  ring

theorem sum_homology_finrank_exactSequence (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k (S.X₁.homology n)) -
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k (S.X₂.homology n)) +
        (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k (S.X₃.homology n)) =
          (-1 : ℤ) ^ N * Module.finrank k (LinearMap.range (hS.δ (N + 1) N rfl).hom) := by
  have hh : ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n *
        ((Module.finrank k (S.X₁.homology n) : ℤ) - Module.finrank k (S.X₂.homology n) +
          Module.finrank k (S.X₃.homology n))) = (-1 : ℤ) ^ N * connectingRank S hS N := by
    intro N
    induction N with
    | zero => simpa using homology_euler_summand_zero S hS
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, homology_euler_summand_succ S hS, pow_succ]
      ring
  simpa only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    connectingRank] using hh N

theorem homologyEulerChar_additive
    (h₁ : ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero (S.X₁.homology n))
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero (S.X₂.homology n))
    (h₃ : ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero (S.X₃.homology n)) :
    S.X₂.homologyEulerChar = S.X₁.homologyEulerChar + S.X₃.homologyEulerChar := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  obtain ⟨N₃, h₃⟩ := h₃
  let N := max N₁ (max N₂ N₃)
  have hbound (K : ChainComplex (ModuleCat.{v} k) ℕ)
      (hK : ∀ n : ℕ, N < n → IsZero (K.homology n)) :
      GradedObject.finrankSupport (fun n ↦ K.homology n) ⊆ Finset.range (N + 1) := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have := ModuleCat.subsingleton_of_isZero (hK n (by simpa [Finset.mem_range] using hn))
    exact Module.finrank_zero_of_subsingleton
  have hN₁ : N₁ ≤ N := le_max_left _ _
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  rw [_root_.HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      S.X₁ _ (hbound S.X₁ (fun n hn ↦ h₁ n (lt_of_le_of_lt hN₁ hn))),
    _root_.HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      S.X₂ _ (hbound S.X₂ (fun n hn ↦ h₂ n (lt_of_le_of_lt hN₂ hn))),
    _root_.HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      S.X₃ _ (hbound S.X₃ (fun n hn ↦ h₃ n (lt_of_le_of_lt hN₃ hn)))]
  have hz : hS.δ (N + 1) N rfl = 0 :=
    (h₃ (N + 1) (lt_of_le_of_lt hN₃ (Nat.lt_succ_self N))).eq_of_src _ _
  have hzero : Module.finrank k (LinearMap.range (hS.δ (N + 1) N rfl).hom) = 0 := by
    rw [hz]
    change Module.finrank k (LinearMap.range (0 : S.X₃.homology (N + 1) →ₗ[k]
      S.X₁.homology N)) = 0
    rw [LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton
  have h := sum_homology_finrank_exactSequence S hS N
  rw [hzero, Nat.cast_zero, mul_zero] at h
  simp [ComplexShape.χ]
  linarith

end DifferentialGeometry.HomologicalComplex
