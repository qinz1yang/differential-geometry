import DifferentialGeometry.Geometry.Collapse.MetricRank.KLVertexImages

/-!
# The pointed half-plane obstruction (review 75, section C.5, S-X144 group G4)

A plain "no near-equilateral triangle in a half plane" is false. The obstruction needs that the
base point is close to the boundary line.

* Pure Euclidean part: three points `z i` of the closed upper half plane of `ℝ²` with
  `‖z i‖ ≤ R` and `‖z i - z j‖ > ρ` where `2 R² ≤ ρ²` do not exist (two of the three first
  coordinates have the same sign, so their inner product is `≥ 0`, hence
  `‖z i - z j‖² ≤ ‖z i‖² + ‖z j‖² ≤ 2 R²`). With `R = 551/100` and `ρ = 5 √3 - 19/25` this is
  the review's numerical contradiction `5 √3 - 19/25 > 551 √2 / 100` (`halfplane_numbers_SMR`).
* KL part: three vectors of norm `5` at `120°` (mutual distance `5 √3`) have KL witnesses in
  `B(p, 6)`; their `π`-images lie in the half plane with `‖z i‖ ≤ 5 + 3 β + ε_m + h ≤ 551/100` and
  `‖z i - z j‖ > 5 √3 - 5 β - ε_m ≥ 5 √3 - 19/25`.
The pointedness `π p = (0, h)`, `0 ≤ h ≤ 1/20` is used only through `‖π p‖ ≤ 1/20`
(`..._of_norm_le_SMR`); the verbatim form is `not_splitting_ge_two_at_halfplane_boundary_SMR`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

section Pure

theorem norm_sq_fin_two_SMR (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

theorem exists_pair_nonneg_mul_SMR (a : Fin 3 → ℝ) : ∃ i j : Fin 3, i ≠ j ∧ 0 ≤ a i * a j := by
  rcases le_total 0 (a 0) with h0 | h0 <;> rcases le_total 0 (a 1) with h1 | h1 <;>
    rcases le_total 0 (a 2) with h2 | h2 <;>
    first
      | exact ⟨0, 1, by decide, by nlinarith⟩
      | exact ⟨0, 2, by decide, by nlinarith⟩
      | exact ⟨1, 2, by decide, by nlinarith⟩

/-- **Three points of the closed upper half plane of `ℝ²`**, all of norm `≤ R`, cannot be
pairwise more than `ρ` apart when `2 R² ≤ ρ²`. -/
theorem not_three_in_upper_halfplane_SMR {R ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 2 * R ^ 2 ≤ ρ ^ 2)
    (z : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hz : ∀ i, 0 ≤ z i 1) (hR : ∀ i, ‖z i‖ ≤ R)
    (hfar : ∀ i j, i ≠ j → ρ < ‖z i - z j‖) : False := by
  obtain ⟨i, j, hij, hp⟩ := exists_pair_nonneg_mul_SMR (fun k => z k 0)
  have hdiff : ‖z i - z j‖ ^ 2 = ‖z i‖ ^ 2 + ‖z j‖ ^ 2 - 2 * (z i 0 * z j 0 + z i 1 * z j 1) := by
    rw [norm_sq_fin_two_SMR, norm_sq_fin_two_SMR, norm_sq_fin_two_SMR]
    simp only [PiLp.sub_apply]
    ring
  have hi := hR i
  have hj := hR j
  have hi0 := norm_nonneg (z i)
  have hj0 := norm_nonneg (z j)
  have hmul : 0 ≤ z i 1 * z j 1 := mul_nonneg (hz i) (hz j)
  have hf := hfar i j hij
  have hsq : ρ ^ 2 < ‖z i - z j‖ ^ 2 := by nlinarith
  simp only at hp
  nlinarith

/-- The numerical inequality of C.5: `5 √3 - 19/25 > 551 √2 / 100`. -/
theorem halfplane_numbers_SMR : 551 * Real.sqrt 2 / 100 < 5 * Real.sqrt 3 - 19 / 25 := by
  have h3 : (1732 / 1000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 2 < 14143 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- The squared form of `halfplane_numbers_SMR`: `2 R² ≤ ρ²` for `R = 551/100`,
`ρ = 5 √3 - 19/25`. -/
theorem halfplane_numbers_sq_SMR :
    2 * (551 / 100 : ℝ) ^ 2 ≤ (5 * Real.sqrt 3 - 19 / 25) ^ 2 := by
  have h := halfplane_numbers_SMR
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ 551 * Real.sqrt 2 / 100 := by positivity
  have := pow_le_pow_left₀ h0 h.le 2
  nlinarith

/-- **C.5, pure Euclidean form**: no three points of the closed upper half plane with norms
`≤ 551/100` and pairwise distances `> 5 √3 - 19/25`. -/
theorem not_three_in_halfplane_551_SMR (z : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (hz : ∀ i, 0 ≤ z i 1) (hR : ∀ i, ‖z i‖ ≤ 551 / 100)
    (hfar : ∀ i j, i ≠ j → 5 * Real.sqrt 3 - 19 / 25 < ‖z i - z j‖) : False := by
  have h3 : (1732 / 1000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  exact not_three_in_upper_halfplane_SMR (R := 551 / 100) (by linarith) halfplane_numbers_sq_SMR
    z hz hR hfar

theorem norm_sq_mk_SMR (a b : ℝ) : ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_fin_two_SMR]
  simp

/-- **Consumer (explicit numbers, half disc).** The points `(-11/2, 0)` and `(11/2, 0)` of the
half disc of radius `551/100` are `11 > 5 √3 - 19/25` apart, so every third point of the half
disc is within `5 √3 - 19/25` of one of them. -/
theorem halfdisc_third_point_close_SMR (c : EuclideanSpace ℝ (Fin 2)) (hc : 0 ≤ c 1)
    (hcR : ‖c‖ ≤ 551 / 100) :
    ‖c - !₂[-11 / 2, 0]‖ ≤ 5 * Real.sqrt 3 - 19 / 25 ∨
      ‖c - !₂[11 / 2, 0]‖ ≤ 5 * Real.sqrt 3 - 19 / 25 := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have h3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hA : ‖(!₂[-11 / 2, 0] : EuclideanSpace ℝ (Fin 2))‖ = 11 / 2 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [norm_sq_mk_SMR]; norm_num
  have hB : ‖(!₂[11 / 2, 0] : EuclideanSpace ℝ (Fin 2))‖ = 11 / 2 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [norm_sq_mk_SMR]; norm_num
  have hAB : ‖(!₂[-11 / 2, 0] : EuclideanSpace ℝ (Fin 2)) - !₂[11 / 2, 0]‖ = 11 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [norm_sq_fin_two_SMR]
    simp
    norm_num
  refine not_three_in_halfplane_551_SMR ![c, !₂[-11 / 2, 0], !₂[11 / 2, 0]] ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [hc]
  · intro i
    fin_cases i
    · simpa using hcR
    · show ‖(!₂[-11 / 2, 0] : EuclideanSpace ℝ (Fin 2))‖ ≤ 551 / 100
      rw [hA]; norm_num
    · show ‖(!₂[11 / 2, 0] : EuclideanSpace ℝ (Fin 2))‖ ≤ 551 / 100
      rw [hB]; norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using hcon.1
    · simpa using hcon.2
    · rw [norm_sub_rev]; simpa using hcon.1
    · exact absurd rfl hij
    · show 5 * Real.sqrt 3 - 19 / 25 <
        ‖(!₂[-11 / 2, 0] : EuclideanSpace ℝ (Fin 2)) - !₂[11 / 2, 0]‖
      rw [hAB]
      linarith
    · rw [norm_sub_rev]; simpa using hcon.2
    · show 5 * Real.sqrt 3 - 19 / 25 <
        ‖(!₂[11 / 2, 0] : EuclideanSpace ℝ (Fin 2)) - !₂[-11 / 2, 0]‖
      rw [norm_sub_rev, hAB]
      linarith
    · exact absurd rfl hij

end Pure

end GC.MetricGeometry
