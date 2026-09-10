import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Simplex

variable {I : Type*} [Fintype I] [Nonempty I]


def minimumCoordinate (x : stdSimplex ℝ I) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x.val


theorem continuous_minimumCoordinate : Continuous (minimumCoordinate (I := I)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ ↦
    (continuous_apply i).comp continuous_subtype_val)


theorem minimumCoordinate_le (x : stdSimplex ℝ I) (i : I) : minimumCoordinate x ≤ x.val i :=
  Finset.inf'_le _ (Finset.mem_univ i)


theorem minimumCoordinate_nonneg (x : stdSimplex ℝ I) : 0 ≤ minimumCoordinate x :=
  Finset.le_inf' Finset.univ_nonempty _ (fun i _ ↦ x.property.1 i)


theorem exists_minimumCoordinate (x : stdSimplex ℝ I) :
    ∃ i : I, minimumCoordinate x = x.val i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x.val
  exact ⟨i, hi⟩

private theorem card_mul_minimumCoordinate_le (x : stdSimplex ℝ I) :
    (Fintype.card I : ℝ) * minimumCoordinate x ≤ 1 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦
    minimumCoordinate_le x i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    x.property.2] using h


theorem normalizationDenominator_pos (x : stdSimplex ℝ I) (hx : x ≠ stdSimplex.barycenter) :
    0 < 1 - (Fintype.card I : ℝ) * minimumCoordinate x := by
  have hle := card_mul_minimumCoordinate_le x
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  by_contra h
  have he : (Fintype.card I : ℝ) * minimumCoordinate x = 1 := by linarith
  have hm : minimumCoordinate x = (Fintype.card I : ℝ)⁻¹ := by
    apply (mul_left_cancel₀ (ne_of_gt hcard))
    rw [he, mul_inv_cancel₀ (ne_of_gt hcard)]
  have hsum : ∑ _ : I, minimumCoordinate x = ∑ i : I, x.val i := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      x.property.2] using he
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ minimumCoordinate_le x i)).mp hsum
  apply hx
  apply Subtype.ext
  funext i
  exact (heq i (Finset.mem_univ i)).symm.trans hm


theorem minimumCoordinate_lt_barycenter (x : stdSimplex ℝ I) (hx : x ≠ stdSimplex.barycenter) :
    minimumCoordinate x < (Fintype.card I : ℝ)⁻¹ := by
  have hd := normalizationDenominator_pos x hx
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hcard.le
  rw [mul_inv_cancel₀ (ne_of_gt hcard)] at hm
  linarith


def boundary (I : Type*) [Fintype I] : Set (stdSimplex ℝ I) :=
  {x | ∃ i : I, x.val i = 0}


def punctured (I : Type*) [Fintype I] [Nonempty I] : Set (stdSimplex ℝ I) :=
  {x | x ≠ stdSimplex.barycenter}


theorem isOpen_punctured : IsOpen (punctured I) :=
  isOpen_compl_singleton

omit [Nonempty I] in
theorem isClosed_boundary : IsClosed (boundary I) := by
  change IsClosed (Set.ofPred (fun x : stdSimplex ℝ I ↦ ∃ i : I, x.val i = 0))
  rw [Set.ofPred_exists]
  exact isClosed_iUnion_of_finite (fun i ↦
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const)


theorem minimumCoordinate_eq_zero {x : stdSimplex ℝ I} (hx : x ∈ boundary I) :
    minimumCoordinate x = 0 := by
  obtain ⟨i, hi⟩ := hx
  exact le_antisymm (hi ▸ minimumCoordinate_le x i) (minimumCoordinate_nonneg x)


theorem boundary_ne_barycenter {x : stdSimplex ℝ I} (hx : x ∈ boundary I) :
    x ≠ stdSimplex.barycenter := by
  obtain ⟨i, hi⟩ := hx
  intro he
  rw [he, stdSimplex.barycenter_apply] at hi
  have hp : (0 : ℝ) < (Fintype.card I : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  exact (ne_of_gt hp) hi


theorem boundary_subset_punctured : boundary I ⊆ punctured I :=
  fun _ hx ↦ boundary_ne_barycenter hx


def boundaryInclusion : C(boundary I, punctured I) :=
  ⟨fun x ↦ ⟨x.val, boundary_ne_barycenter x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def radialRetractionPoint (x : punctured I) : boundary I :=
  ⟨⟨fun i ↦ (x.val.val i - minimumCoordinate x.val) /
      (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val),
    ⟨fun i ↦ div_nonneg (sub_nonneg.mpr (minimumCoordinate_le x.val i))
      (normalizationDenominator_pos x.val x.property).le, by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [Finset.sum_sub_distrib, x.val.property.2,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt (normalizationDenominator_pos x.val x.property))⟩⟩, by
    obtain ⟨i, hi⟩ := exists_minimumCoordinate x.val
    exact ⟨i, by change (x.val.val i - minimumCoordinate x.val) / _ = 0
                 rw [← hi, sub_self, zero_div]⟩⟩

def radialRetraction : C(punctured I, boundary I) :=
  ⟨radialRetractionPoint, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)).sub
        (continuous_minimumCoordinate.comp continuous_subtype_val)).div
      (continuous_const.sub (continuous_const.mul
        (continuous_minimumCoordinate.comp continuous_subtype_val)))
      (fun x ↦ ne_of_gt (normalizationDenominator_pos x.val x.property))⟩


theorem radialRetraction_apply (x : punctured I) (i : I) :
    (radialRetraction x).val.val i = (x.val.val i - minimumCoordinate x.val) /
      (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val) := rfl


@[simp]
theorem radialRetraction_boundary (x : boundary I) :
    radialRetraction (boundaryInclusion x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (x.val.val i - minimumCoordinate x.val) /
    (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val) = x.val.val i
  rw [minimumCoordinate_eq_zero x.property, sub_zero, mul_zero, sub_zero, div_one]

private def radialHomotopyPoint (t : unitInterval) (x : punctured I) : punctured I :=
  ⟨⟨(1 - (t : ℝ)) • x.val.val + (t : ℝ) • (radialRetraction x).val.val,
    convex_stdSimplex ℝ I x.val.property (radialRetraction x).val.property
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel _ _)⟩, by
    obtain ⟨i, hi⟩ := exists_minimumCoordinate x.val
    have hq : (radialRetraction x).val.val i = 0 := by
      change (x.val.val i - minimumCoordinate x.val) / _ = 0
      rw [← hi, sub_self, zero_div]
    have hm := minimumCoordinate_lt_barycenter x.val x.property
    have htm : (1 - (t : ℝ)) * minimumCoordinate x.val ≤ minimumCoordinate x.val := by
      nlinarith [t.property.1, minimumCoordinate_nonneg x.val]
    intro he
    have hei := congrArg (fun y : stdSimplex ℝ I ↦ y.val i) he
    change (1 - (t : ℝ)) * x.val.val i + (t : ℝ) * (radialRetraction x).val.val i =
      (Fintype.card I : ℝ)⁻¹ at hei
    rw [← hi, hq, mul_zero, add_zero] at hei
    linarith⟩

def radialDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id (punctured I))
    (boundaryInclusion.comp radialRetraction) {x | x.val ∈ boundary I} where
  toFun tx := radialHomotopyPoint tx.1 tx.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp
          (radialRetraction.continuous.comp continuous_snd))))
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (0 : ℝ)) * x.val.val i + 0 * (radialRetraction x).val.val i = x.val.val i
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (1 : ℝ)) * x.val.val i + 1 * (radialRetraction x).val.val i =
      (radialRetraction x).val.val i
    ring
  prop' t := by
    intro x hx
    have hr : (radialRetraction x).val = x.val :=
      congrArg Subtype.val (radialRetraction_boundary (⟨x.val, hx⟩ : boundary I))
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (t : ℝ)) * x.val.val i + (t : ℝ) * (radialRetraction x).val.val i = x.val.val i
    rw [hr]
    ring

def radialHomotopyEquiv : ContinuousMap.HomotopyEquiv (punctured I) (boundary I) where
  toFun := radialRetraction
  invFun := boundaryInclusion
  left_inv := ⟨radialDeformation.toHomotopy.symm⟩
  right_inv := by
    have he : (radialRetraction (I := I)).comp boundaryInclusion = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact radialRetraction_boundary x
    rw [he]

end DifferentialGeometry.Simplex
