import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {ι : Type*} [Fintype ι]

open Classical in
private theorem linearMap_eq_sum_stdSimplex (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    ℓ x = ∑ i, x i * ℓ (Pi.single i 1) := by
  classical
  have heq : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [heq]
  simp only [map_sum, map_smul, smul_eq_mul]

open Classical in
private theorem exists_pos_coordinate_height_lt
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) {r : ℝ}
    (hxr : ℓ x ≤ r) (havoid : ∀ i, ℓ (Pi.single i 1) ≠ r) :
    ∃ i, 0 < x i ∧ ℓ (Pi.single i 1) < r := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [hx.2] at hsum
    norm_num at hsum
  have hgt : ∀ j, 0 < x j → r < ℓ (Pi.single j 1) :=
    fun j hj => lt_of_le_of_ne (hno j hj) (havoid j).symm
  have hsum : (∑ j, x j * r) < ∑ j, x j * ℓ (Pi.single j 1) := by
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases (hx.1 j).eq_or_lt with hj | hj
      · simp only [← hj, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hgt j hj).le (hx.1 j)
    · exact mul_lt_mul_of_pos_left (hgt i hi) hi
  rw [← Finset.sum_mul, hx.2, one_mul, ← linearMap_eq_sum_stdSimplex ℓ x] at hsum
  exact hsum.not_ge hxr

open Classical in
private theorem exists_stdSimplex_height_of_lt
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    {i : ι} (hi : 0 < x i) {r : ℝ} (hlo : ℓ (Pi.single i 1) < r) (hhi : r < ℓ x) :
    ∃ y ∈ stdSimplex ℝ ι, ℓ y = r ∧ ∀ j, y j = 0 ↔ x j = 0 := by
  classical
  let c := ℓ (Pi.single i 1)
  let t := (r - c) / (ℓ x - c)
  have hden : 0 < ℓ x - c := by dsimp [c]; linarith
  have ht : 0 < t := div_pos (by dsimp [c]; linarith) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hmul : t * (ℓ x - c) = r - c := div_mul_cancel₀ _ hden.ne'
  let y := t • x + (1 - t) • Pi.single i 1
  have hy : y ∈ stdSimplex ℝ ι := (convex_stdSimplex ℝ ι) hx (single_mem_stdSimplex ℝ i)
    ht.le (sub_nonneg.mpr ht1.le) (by ring)
  refine ⟨y, hy, ?_, ?_⟩
  · change ℓ (t • x + (1 - t) • Pi.single i 1) = r
    simp only [map_add, map_smul, smul_eq_mul]
    change t * ℓ x + (1 - t) * c = r
    nlinarith
  · intro j
    have hj : y j = t * x j + (1 - t) * (Pi.single i (1 : ℝ) : ι → ℝ) j := by
      simp only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro hyj
      have hnonneg : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := (single_mem_stdSimplex ℝ i).1 j
      have hxj := hx.1 j
      nlinarith
    · intro hxj
      have hji : j ≠ i := by intro heq; subst j; linarith
      rw [hj, hxj, Pi.single_eq_of_ne hji]
      ring

open Classical in
theorem exists_stdSimplex_same_support_height
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {a b : ℝ}
    (hvertices : ∀ i, ℓ (Pi.single i 1) < a ∨ b < ℓ (Pi.single i 1))
    {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hxa : a ≤ ℓ x) (hxb : ℓ x ≤ b)
    {r : ℝ} (hra : a ≤ r) (hrb : r ≤ b) :
    ∃ y ∈ stdSimplex ℝ ι, ℓ y = r ∧ ∀ j, y j = 0 ↔ x j = 0 := by
  classical
  rcases lt_trichotomy (ℓ x) r with hlt | heq | hgt
  · obtain ⟨i, hi, hlow⟩ := exists_pos_coordinate_height_lt (-ℓ) hx
      (by simpa using (neg_le_neg hxa)) (r := -a) (by
        intro i heq
        have hval : ℓ (Pi.single i 1) = a := by simpa only [LinearMap.neg_apply, neg_inj] using heq
        rcases hvertices i with h | h <;> linarith)
    have hlow' : (-ℓ) (Pi.single i 1) < -r := by
      simp only [LinearMap.neg_apply] at hlow ⊢
      rcases hvertices i with h | h <;> linarith
    obtain ⟨y, hy, hyr, hsupport⟩ := exists_stdSimplex_height_of_lt (-ℓ) hx hi hlow'
      (by simpa using (neg_lt_neg hlt))
    exact ⟨y, hy, by simpa only [LinearMap.neg_apply, neg_inj] using hyr, hsupport⟩
  · exact ⟨x, hx, heq, fun _ => Iff.rfl⟩
  · obtain ⟨i, hi, hlow⟩ := exists_pos_coordinate_height_lt ℓ hx hxb (by
      intro i heq
      rcases hvertices i with h | h <;> linarith)
    have hlow' : ℓ (Pi.single i 1) < r := by
      rcases hvertices i with h | h
      · linarith
      · linarith
    exact exists_stdSimplex_height_of_lt ℓ hx hi hlow' hgt

end DifferentialGeometry.Topology.PiecewiseLinear
