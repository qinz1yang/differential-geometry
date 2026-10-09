import DifferentialGeometry.Geometry.Collapse.FiniteBlockMap
import DifferentialGeometry.Geometry.Collapse.BlockMapDerivative

/-!
# Consumers of FC01–FC04

The scale block `(0, ρ)` together with an `E'` block whose cutoff vanishes identically: FC01 makes
the map smooth for a smooth scale, FC02 bounds its derivative by `√2 Λ`, FC04 reads off the exact
scale. A single block with a full marker recovers its coordinate from image distance (FC03).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scale block and an empty `E'` block. -/
noncomputable def scaleBlockMap (ρ : E → ℝ) : E → BlockSpace (fun _ : Fin 2 => ℝ) :=
  blockMap (fun _ => ρ) (fun i _ => if i = 0 then 1 else 0) (fun _ _ => 0)

theorem contMDiff_scaleBlockMap {ρ : E → ℝ} {n : WithTop ℕ∞}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n ρ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, BlockSpace (fun _ : Fin 2 => ℝ)) n (scaleBlockMap ρ) :=
  contMDiff_blockMap (U := fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => contMDiffOn_const) (fun _ => contMDiff_const) (fun _ => hρ)
    (fun _ => subset_univ _)

theorem norm_fderiv_scaleBlockMap_le {ρ : E → ℝ} (hρd : Differentiable ℝ ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) {Λ : ℝ} (hΛ : ∀ y, ‖fderiv ℝ ρ y‖ ≤ Λ) (y : E) :
    ‖fderiv ℝ (scaleBlockMap ρ) y‖ ≤ Real.sqrt 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ y)
  have hz : tsupport (fun _ : E => if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = ∅ := by
    simp
  have h := norm_fderiv_blockMap_le (V := fun _ : Fin 2 => ℝ) (U := fun _ => univ) (ρ := ρ)
    (R := fun _ => ρ) (ζ := fun i _ => if i = 0 then 1 else 0) (η := fun _ _ => 0)
    0 1 (by decide) (fun _ => isOpen_univ) (fun _ => subset_univ _)
    (fun _ => differentiableOn_const 0) (fun _ => differentiable_const _)
    (fun i y => by by_cases hi : i = 0 <;> simp [hi]) hρd hρ0 hΛ rfl rfl rfl rfl
    (fun _ => 0) (fun _ => le_rfl) (fun i h0 h1 => by fin_cases i <;> simp_all) (N := 0)
    (fun y => by
      rw [Nat.le_zero, Set.ncard_eq_zero]
      ext i; fin_cases i <;> simp)
    (a := fun _ => 0) (b := fun _ => 0) (C := fun _ => 0) (B := 0)
    (fun i h0 h1 => by fin_cases i <;> simp_all) (fun i h0 h1 => by fin_cases i <;> simp_all)
    le_rfl le_rfl le_rfl (fun y hy => by rw [hz] at hy; exact absurd hy (notMem_empty y)) y
  have hval : Real.sqrt (Λ ^ 2 + ((0 : ℕ) : ℝ) * 0 ^ 2 + (0 + (0 + 1) * (0 + Λ)) ^ 2) =
      Real.sqrt 2 * Λ := by
    rw [show Λ ^ 2 + ((0 : ℕ) : ℝ) * 0 ^ 2 + (0 + (0 + 1) * (0 + Λ)) ^ 2 = 2 * Λ ^ 2 by
      push_cast; ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq hΛ0]
  exact h.trans hval.le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem scaleRadius_scaleBlockMap (ρ : E → ℝ) (σ : ℝ) (p : E) :
    scaleRadius 0 σ (scaleBlockMap ρ p) = σ * ρ p :=
  scaleRadius_blockMap (fun _ => rfl) (fun _ => rfl) σ p

theorem norm_coordinate_sub_lt_of_full_marker_blockMap {M W : Type*} [TopologicalSpace M]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (η₀ : M → W) {r e A : ℝ} (hr : 0 < r)
    (he : 0 < e) (he1 : e < 1) {p q : M} (hA : ‖η₀ p‖ ≤ A)
    (hq : ‖blockMap (V := fun _ : Fin 1 => W) (fun _ _ => r) (fun _ _ => 1) (fun _ => η₀) q -
      blockMap (V := fun _ : Fin 1 => W) (fun _ _ => r) (fun _ _ => 1) (fun _ => η₀) p‖ <
        e * r) :
    ‖η₀ q - η₀ p‖ < (1 + A) * e / (1 - e) := by
  have h := marker_recovery_of_blockMap_dist (κ := Fin 1) (V := fun _ => W)
    (R := fun _ _ => r) (ζ := fun _ _ => 1) (η := fun _ => η₀) (U := fun _ => univ) Finset.univ
    (Finset.mem_univ 0) hr (fun _ => rfl) (subset_univ _) rfl hA he he1
    (by rwa [blockRestrict_univ])
  exact h.2.2

end DifferentialGeometry.Geometry.Collapse
