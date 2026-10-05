import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinatePPCoframe

/-!
# Consumers of the (PP) coframe kernel (CGP06's retained-coordinate bound)

Concrete instances of `RetainedCoordinatePPCoframe.lean`:

* `exists_bounded_preimage_fst_BAS`: the first-coordinate surjection `ℝ × ℝ → ℝ` with the
  Euclidean bilinear form and `N(v) = |v.1| + |v.2|` (the lower bound holds on the orthogonal
  complement of the kernel `0 × ℝ`): every `y` has a preimage `w` with `N(w) ≤ 2|y|`.
* `retained_coordinate_tilted_line_BAS`: the tilted line `L = {(t, e t)}` in `ℝ × ℝ` (sup norm), the
  reference graph `T y = (y, 0)` with `π = fst`, the rough derivative `D w = (w, e w)` with error
  `e|w|`, `e = 1/16`, `Ω = 1`: CGP06's bound `‖v‖ ≤ 2‖π v‖` on `L`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

/-- The Euclidean bilinear form on `ℝ × ℝ`. -/
def euclidBilin_BAS : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => v.1 * w.1 + v.2 * w.2)
    (fun v v' w => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c v w => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun v w w' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c v w => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

/-- **Consumer of `exists_bounded_preimage_BAS`.** The first-coordinate projection of `ℝ × ℝ`
with the Euclidean form and `N(v) = |v.1| + |v.2|`: bounded preimages `N(w) ≤ 2|y|`. -/
theorem exists_bounded_preimage_fst_BAS (y : ℝ) :
    ∃ w : ℝ × ℝ, w.1 = y ∧ |w.1| + |w.2| ≤ 2 * ‖y‖ := by
  have hpos : ∀ v : ℝ × ℝ, v ≠ 0 → 0 < euclidBilin_BAS v v := by
    intro v hv
    simp only [euclidBilin_BAS, LinearMap.mk₂_apply]
    rcases v with ⟨a, b⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hv (by simp [h.1, h.2])
    rcases hab with ha | hb
    · have := mul_self_pos.mpr ha
      nlinarith [mul_self_nonneg b]
    · have := mul_self_pos.mpr hb
      nlinarith [mul_self_nonneg a]
  have hsurj : Function.Surjective (LinearMap.fst ℝ ℝ ℝ) := fun y => ⟨(y, 0), rfl⟩
  have hlow : ∀ v : ℝ × ℝ, (∀ k, LinearMap.fst ℝ ℝ ℝ k = 0 → euclidBilin_BAS v k = 0) →
      |v.1| + |v.2| ≤ 2 * ‖LinearMap.fst ℝ ℝ ℝ v‖ := by
    intro v hv
    have h := hv (0, 1) rfl
    simp only [euclidBilin_BAS, LinearMap.mk₂_apply, mul_zero, mul_one, zero_add] at h
    simp only [LinearMap.fst_apply, h, abs_zero, add_zero, Real.norm_eq_abs]
    linarith [abs_nonneg v.1]
  obtain ⟨w, hw, hN⟩ := exists_bounded_preimage_BAS euclidBilin_BAS hpos (LinearMap.fst ℝ ℝ ℝ)
    hsurj (fun v => |v.1| + |v.2|) hlow y
  exact ⟨w, hw, hN⟩

/-- **Consumer of `retained_coordinate_lower_bound_of_pp_BAS`.** The tilted line
`{(t, t/16)}` in `ℝ × ℝ`, reference graph `y ↦ (y, 0)`, rough derivative `w ↦ (w, w/16)`:
`‖v‖ ≤ 2‖v.1‖` on the line. -/
theorem retained_coordinate_tilted_line_BAS :
    ∀ v ∈ Set.range (fun t : ℝ => ((t, t / 16) : ℝ × ℝ)),
      ‖v‖ ≤ 2 * 1 * ‖ContinuousLinearMap.fst ℝ ℝ ℝ v‖ := by
  let D : ℝ →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun w => (w, w / 16)
      map_add' := fun w w' => by ext <;> simp; ring
      map_smul' := fun r w => by ext <;> simp; ring }
  have hD : ∀ w, D w = (w, w / 16) := fun w => rfl
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul, ContinuousLinearMap.coe_fst', Prod.norm_def]
      exact le_max_left _ _
  have hT : ∀ y : ℝ, ‖ContinuousLinearMap.inl ℝ ℝ ℝ y‖ ≤ 1 * ‖y‖ := by
    intro y
    simp [Prod.norm_def]
  have hπT : ∀ y : ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ (ContinuousLinearMap.inl ℝ ℝ ℝ y) = y :=
    fun y => rfl
  have hrough : ∀ w : ℝ,
      ‖D w - ContinuousLinearMap.inl ℝ ℝ ℝ ((LinearMap.id : ℝ →ₗ[ℝ] ℝ) w)‖ ≤ 1 / 16 * |w| := by
    intro w
    have h : D w - ContinuousLinearMap.inl ℝ ℝ ℝ ((LinearMap.id : ℝ →ₗ[ℝ] ℝ) w) =
        (0, w / 16) := by
      rw [hD, LinearMap.id_apply, ContinuousLinearMap.inl_apply, Prod.mk_sub_mk, sub_self,
        sub_zero]
    rw [h, Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_div,
      max_eq_right (by positivity)]
    norm_num
    linarith [abs_nonneg w]
  have hpre : ∀ v ∈ Set.range (fun t : ℝ => ((t, t / 16) : ℝ × ℝ)),
      ∃ w, ‖D w - v‖ ≤ 2 * (1 / 16) * ‖v‖ ∧ |w| ≤ 2 * ‖v‖ := by
    rintro v ⟨t, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hD, sub_self, norm_zero]
      positivity
    · have h1 : |t| ≤ ‖((t, t / 16) : ℝ × ℝ)‖ := by
        rw [Prod.norm_def, ← Real.norm_eq_abs]
        exact le_max_left _ _
      linarith [abs_nonneg t]
  exact retained_coordinate_lower_bound_of_pp_BAS (fun w : ℝ => |w|)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) hfst
    (ContinuousLinearMap.inl ℝ ℝ ℝ) hπT hT D LinearMap.id hrough _ hpre le_rfl (by norm_num)
    (by norm_num)

end DifferentialGeometry.Analysis
