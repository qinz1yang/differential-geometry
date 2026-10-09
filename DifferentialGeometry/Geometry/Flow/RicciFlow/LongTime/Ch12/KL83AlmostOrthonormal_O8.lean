import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# CH12-O8, package P3: almost orthonormal triples in a three-dimensional inner product space

For unit vectors `u 0, u 1, u 2` with `|⟪u j, u k⟫| ≤ η` (`j ≠ k`) the coordinate map
`v ↦ (⟪u j, v⟫)_j` is an almost isometry onto `ℝ³`:
`(1 - 2η) ‖v‖² ≤ ∑ ⟪u j, v⟫² ≤ (1 + 2η) ‖v‖²` (the lower bound and surjectivity use
`finrank = 3`).  This is the linear algebra behind the `(1 + τ)` strainer charts of KL 83.1.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

namespace GC.LongTime.Ch12

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Norm square of a combination of an almost orthonormal triple. -/
theorem norm_sq_combo_bounds_O8 (u : Fin 3 → F) (hu : ∀ j, ‖u j‖ = 1) {η : ℝ}
    (hoff : ∀ j k, j ≠ k → |(⟪u j, u k⟫_ℝ)| ≤ η) (β : Fin 3 → ℝ) :
    (1 - 2 * η) * ∑ j, β j ^ 2 ≤ ‖∑ j, β j • u j‖ ^ 2 ∧
      ‖∑ j, β j • u j‖ ^ 2 ≤ (1 + 2 * η) * ∑ j, β j ^ 2 := by
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hoff 0 1 (by decide))
  have hself : ∀ j, ⟪u j, u j⟫_ℝ = 1 := fun j => by
    rw [real_inner_self_eq_norm_sq, hu j]; norm_num
  have h01 := abs_le.mp (hoff 0 1 (by decide))
  have h02 := abs_le.mp (hoff 0 2 (by decide))
  have h12 := abs_le.mp (hoff 1 2 (by decide))
  have hsym : ∀ j k, ⟪u j, u k⟫_ℝ = ⟪u k, u j⟫_ℝ := fun j k => real_inner_comm _ _
  have hexp : ‖∑ j, β j • u j‖ ^ 2 =
      β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2 + 2 * β 0 * β 1 * ⟪u 0, u 1⟫_ℝ +
        2 * β 0 * β 2 * ⟪u 0, u 2⟫_ℝ + 2 * β 1 * β 2 * ⟪u 1, u 2⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Fin.sum_univ_three, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hself]
    rw [hsym 1 0, hsym 2 0, hsym 2 1]
    ring
  rw [hexp]
  simp only [Fin.sum_univ_three]
  -- `|2 b c x| ≤ η (b² + c²)` for `|x| ≤ η`
  have key : ∀ b c x : ℝ, -η ≤ x → x ≤ η →
      -(η * (b ^ 2 + c ^ 2)) ≤ 2 * b * c * x ∧ 2 * b * c * x ≤ η * (b ^ 2 + c ^ 2) := by
    intro b c x hx1 hx2
    have hbc : |2 * b * c| ≤ b ^ 2 + c ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (b + c), sq_nonneg (b - c)]
    have hx : |x| ≤ η := abs_le.mpr ⟨hx1, hx2⟩
    have hprod : |2 * b * c * x| ≤ (b ^ 2 + c ^ 2) * η := by
      rw [abs_mul]
      exact mul_le_mul hbc hx (abs_nonneg _) (by positivity)
    have := abs_le.mp hprod
    constructor <;> nlinarith [this.1, this.2]
  obtain ⟨a1, a2⟩ := key (β 0) (β 1) _ h01.1 h01.2
  obtain ⟨b1, b2⟩ := key (β 0) (β 2) _ h02.1 h02.2
  obtain ⟨c1, c2⟩ := key (β 1) (β 2) _ h12.1 h12.2
  constructor <;> nlinarith

/-- Upper Bessel-type bound for an almost orthonormal triple. -/
theorem sum_inner_sq_le_O8 (u : Fin 3 → F) (hu : ∀ j, ‖u j‖ = 1) {η : ℝ}
    (hoff : ∀ j k, j ≠ k → |(⟪u j, u k⟫_ℝ)| ≤ η) (v : F) :
    ∑ j, ⟪u j, v⟫_ℝ ^ 2 ≤ (1 + 2 * η) * ‖v‖ ^ 2 := by
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hoff 0 1 (by decide))
  set c : Fin 3 → ℝ := fun j => ⟪u j, v⟫_ℝ with hc
  set S := ∑ j, c j ^ 2 with hS
  set w := ∑ j, c j • u j with hw
  have hwv : ⟪w, v⟫_ℝ = S := by
    simp only [hw, hS, sum_inner, real_inner_smul_left, hc, sq]
  have hwn := (norm_sq_combo_bounds_O8 u hu hoff c).2
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hcs : S ≤ ‖w‖ * ‖v‖ := hwv ▸ real_inner_le_norm w v
  have h2 : S ^ 2 ≤ (1 + 2 * η) * S * ‖v‖ ^ 2 := by
    have : S ^ 2 ≤ ‖w‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hS0 hcs 2
    calc S ^ 2 ≤ ‖w‖ ^ 2 * ‖v‖ ^ 2 := this
      _ ≤ (1 + 2 * η) * S * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right hwn (sq_nonneg _)
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]; positivity
  · have := h2
    have h3 : S * S ≤ S * ((1 + 2 * η) * ‖v‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h3 hpos

variable [FiniteDimensional ℝ F]

/-- The combination map `β ↦ ∑ β j • u j` is onto when `finrank F = 3`. -/
theorem exists_combo_eq_O8 (u : Fin 3 → F) (hu : ∀ j, ‖u j‖ = 1) {η : ℝ}
    (hη : η < 1 / 2) (hoff : ∀ j k, j ≠ k → |(⟪u j, u k⟫_ℝ)| ≤ η)
    (hdim : Module.finrank ℝ F = 3) (v : F) : ∃ β : Fin 3 → ℝ, ∑ j, β j • u j = v := by
  let B : (Fin 3 → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ u
  have hB : ∀ β, B β = ∑ j, β j • u j := fun β => by
    simp [B, Fintype.linearCombination_apply]
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    have h := (norm_sq_combo_bounds_O8 u hu hoff β).1
    rw [← hB, hβ, norm_zero] at h
    have hpos : 0 < 1 - 2 * η := by linarith
    have hsum : ∑ j, β j ^ 2 = 0 := by
      have h0 : 0 ≤ ∑ j, β j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      nlinarith
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (β j))).mp hsum j
      (Finset.mem_univ _)
    simpa using this
  have hfr : Module.finrank ℝ (Fin 3 → ℝ) = Module.finrank ℝ F := by
    rw [hdim, Module.finrank_fin_fun]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
  obtain ⟨β, hβ⟩ := hsurj v
  exact ⟨β, (hB β).symm.trans hβ⟩

/-- Lower bound: `(1 - 2η) ‖v‖² ≤ ∑ ⟪u j, v⟫²` in dimension three. -/
theorem le_sum_inner_sq_O8 (u : Fin 3 → F) (hu : ∀ j, ‖u j‖ = 1) {η : ℝ}
    (hη : η < 1 / 2) (hoff : ∀ j k, j ≠ k → |(⟪u j, u k⟫_ℝ)| ≤ η)
    (hdim : Module.finrank ℝ F = 3) (v : F) :
    (1 - 2 * η) * ‖v‖ ^ 2 ≤ ∑ j, ⟪u j, v⟫_ℝ ^ 2 := by
  obtain ⟨β, hβ⟩ := exists_combo_eq_O8 u hu hη hoff hdim v
  set C := ∑ j, ⟪u j, v⟫_ℝ ^ 2 with hC
  set Bs := ∑ j, β j ^ 2 with hBs
  set N := ‖v‖ ^ 2 with hN
  have hlow : (1 - 2 * η) * Bs ≤ N := by
    have := (norm_sq_combo_bounds_O8 u hu hoff β).1; rwa [hβ] at this
  have hNeq : N = ∑ j, β j * ⟪u j, v⟫_ℝ := by
    rw [hN, ← real_inner_self_eq_norm_sq]
    conv_lhs => rw [← hβ]
    rw [sum_inner]
    simp only [real_inner_smul_left]
    congr 1; funext j; rw [← hβ]
  have hcs : (∑ j, β j * ⟪u j, v⟫_ℝ) ^ 2 ≤ Bs * C := by
    simpa only [hBs, hC] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ β (fun j => ⟪u j, v⟫_ℝ)
  have hpos : 0 < 1 - 2 * η := by linarith
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hN0 : 0 ≤ N := sq_nonneg _
  rw [← hNeq] at hcs
  -- `N² ≤ Bs C ≤ N C / (1 - 2η)`
  have h1 : (1 - 2 * η) * N ^ 2 ≤ N * C := by
    have : (1 - 2 * η) * (Bs * C) ≤ N * C := mul_le_mul_of_nonneg_right hlow hC0 |>.trans_eq' (by ring)
    nlinarith
  rcases eq_or_lt_of_le hN0 with h0 | hNpos
  · rw [← h0]; nlinarith
  · have : N * ((1 - 2 * η) * N) ≤ N * C := by nlinarith
    exact le_of_mul_le_mul_left this hNpos

/-- The coordinate map `v ↦ (⟪u j, v⟫)_j` is onto `ℝ³`, with a preimage of norm
`‖v‖² ≤ (1 - 2η)⁻¹ ∑ R j²`. -/
theorem exists_inner_eq_O8 (u : Fin 3 → F) (hu : ∀ j, ‖u j‖ = 1) {η : ℝ}
    (hη : η < 1 / 2) (hoff : ∀ j k, j ≠ k → |(⟪u j, u k⟫_ℝ)| ≤ η)
    (hdim : Module.finrank ℝ F = 3) (R : Fin 3 → ℝ) :
    ∃ v : F, (∀ j, ⟪u j, v⟫_ℝ = R j) ∧ (1 - 2 * η) * ‖v‖ ^ 2 ≤ ∑ j, R j ^ 2 := by
  let L : F →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun v j => ⟪u j, v⟫_ℝ
      map_add' := fun v w => by funext j; simp [inner_add_right]
      map_smul' := fun c v => by funext j; simp [real_inner_smul_right] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := le_sum_inner_sq_O8 u hu hη hoff hdim v
    have h0 : ∀ j, ⟪u j, v⟫_ℝ = 0 := fun j => congrFun hv j
    simp only [h0] at h
    norm_num at h
    have hpos : 0 < 1 - 2 * η := by linarith
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (Fin 3 → ℝ) := by
    rw [hdim, Module.finrank_fin_fun]
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj R
  have hvj : ∀ j, ⟪u j, v⟫_ℝ = R j := fun j => congrFun hv j
  refine ⟨v, hvj, ?_⟩
  have h := le_sum_inner_sq_O8 u hu hη hoff hdim v
  simpa only [hvj] using h

end GC.LongTime.Ch12
