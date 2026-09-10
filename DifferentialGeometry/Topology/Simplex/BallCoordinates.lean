import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Set Metric Topology
open scoped BigOperators

namespace DifferentialGeometry.Simplex

def coordinateSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def stdSimplexCoordinateHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ coordinateSimplex n where
  toFun x := ⟨fun i ↦ x.val i.succ, fun i ↦ x.prop.1 i.succ, by
    have h := x.prop.2
    rw [Fin.sum_univ_succ] at h
    linarith [x.prop.1 0]⟩
  invFun x := ⟨Fin.cons (1 - ∑ i, x.val i) x.val, by
    constructor
    · intro i
      exact Fin.cases (sub_nonneg.mpr x.prop.2) (fun j ↦ x.prop.1 j) i
    · simp [Fin.sum_univ_succ]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ ↦ rfl) i
    have h := x.prop.2
    rw [Fin.sum_univ_succ] at h
    change 1 - ∑ j : Fin n, x.val j.succ = x.val 0
    linarith
  right_inv x := rfl
  continuous_toFun := (continuous_pi (fun i ↦
    (continuous_apply i.succ).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ (fun j _ ↦
        (continuous_apply j).comp continuous_subtype_val))
    · exact (continuous_apply j).comp continuous_subtype_val


@[simp]
theorem stdSimplexCoordinateHomeomorph_apply (n : ℕ)
    (x : stdSimplex ℝ (Fin (n + 1))) (i : Fin n) :
    (stdSimplexCoordinateHomeomorph n x).val i = x.val i.succ := rfl

@[simp]
theorem stdSimplexCoordinateHomeomorph_symm_apply_zero (n : ℕ) (x : coordinateSimplex n) :
    ((stdSimplexCoordinateHomeomorph n).symm x).val 0 = 1 - ∑ i, x.val i := rfl


@[simp]
theorem stdSimplexCoordinateHomeomorph_symm_apply_succ (n : ℕ)
    (x : coordinateSimplex n) (i : Fin n) :
    ((stdSimplexCoordinateHomeomorph n).symm x).val i.succ = x.val i := rfl


theorem isCompact_coordinateSimplex (n : ℕ) : IsCompact (coordinateSimplex n) := by
  have : CompactSpace (coordinateSimplex n) :=
    (stdSimplexCoordinateHomeomorph n).surjective.compactSpace
      (stdSimplexCoordinateHomeomorph n).continuous
  exact isCompact_iff_compactSpace.mpr this


theorem convex_coordinateSimplex (n : ℕ) : Convex ℝ (coordinateSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa using hab

theorem interior_coordinateSimplex (n : ℕ) :
    interior (coordinateSimplex n) = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  have heval (i : Fin n) : interior {x : Fin n → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
    simpa [Set.preimage, Function.eval] using
      ((isOpenMap_eval (X := fun _ : Fin n ↦ ℝ) i).preimage_interior_eq_interior_preimage
      (continuous_apply i) (Ici (0 : ℝ))).symm
  have hsum : interior {x : Fin n → ℝ | ∑ i, x i ≤ 1} = {x | ∑ i, x i < 1} := by
    cases n with
    | zero => simp
    | succ n =>
      let l : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
      have hl : Function.Surjective l := by
        intro r
        exact ⟨Pi.single 0 r, by simp [l]⟩
      have hc : Continuous l := by
        exact l.continuous_of_finiteDimensional
      simpa [l, Set.preimage, Function.eval] using
        ((l.isOpenMap_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
        hc (Iic (1 : ℝ))).symm
  have hrepr : coordinateSimplex n =
      (⋂ i : Fin n, {x | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x
    simp [coordinateSimplex]
  rw [hrepr, interior_inter, interior_iInter_of_finite, hsum]
  simp_rw [heval]
  ext x
  simp


theorem interior_coordinateSimplex_nonempty (n : ℕ) :
    (interior (coordinateSimplex n)).Nonempty := by
  rw [interior_coordinateSimplex]
  refine ⟨fun _ ↦ ((n : ℝ) + 1)⁻¹, (fun _ ↦ by positivity), ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hi := mul_inv_cancel₀ hp.ne'
  have hip : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hp
  nlinarith

theorem mem_frontier_coordinateSimplex_iff (n : ℕ) (x : coordinateSimplex n) :
    x.val ∈ frontier (coordinateSimplex n) ↔
      (stdSimplexCoordinateHomeomorph n).symm x ∈ boundary (Fin (n + 1)) := by
  rw [frontier, (isCompact_coordinateSimplex n).isClosed.closure_eq,
    mem_sdiff, interior_coordinateSimplex]
  simp only [x.prop, true_and, mem_ofPred_eq]
  constructor
  · intro h
    change ∃ i, ((stdSimplexCoordinateHomeomorph n).symm x).val i = 0
    by_cases hs : ∑ i, x.val i = 1
    · exact ⟨0, by simp [hs]⟩
    · have hs' : ∑ i, x.val i < 1 := lt_of_le_of_ne x.prop.2 hs
      have hi : ¬∀ i, 0 < x.val i := fun hi ↦ h ⟨hi, hs'⟩
      push Not at hi
      obtain ⟨i, hi⟩ := hi
      exact ⟨i.succ, le_antisymm hi (x.prop.1 i)⟩
  · rintro ⟨i, hi⟩ ⟨hpos, hsum⟩
    revert hi
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · intro hi
      change 1 - ∑ i, x.val i = 0 at hi
      linarith
    · intro hi
      exact (hpos j).ne' hi

end DifferentialGeometry.Simplex
