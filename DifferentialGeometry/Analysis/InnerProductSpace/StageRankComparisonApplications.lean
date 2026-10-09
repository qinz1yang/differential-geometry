import DifferentialGeometry.Analysis.InnerProductSpace.StageRankComparison
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete consumers of the G6 rank kernels

* `finrank_le_range_of_pp_comparison_euclid_BASP`: (b1) on `ℝ²` with the whole plane, `D0 = B` the
  identity and `Q` the identity — the rank is `2`.
* `ne_zero_of_unit_pp_comparison_real_BASP`: (b2) on `ℝ` with the unit vector `1`.
-/

set_option autoImplicit false

noncomputable section

open Function

namespace DifferentialGeometry.Analysis

/-- (b1) on `ℝ²`: the identity has the full (PP) data for the whole plane, so the kernel gives
rank `2`. -/
theorem finrank_le_range_of_pp_comparison_euclid_BASP :
    2 ≤ Module.finrank ℝ (LinearMap.range
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
        LinearMap.id)) := by
  set L : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := ⊤
  have hπ : ∀ v : EuclideanSpace ℝ (Fin 2), (L.orthogonalProjectionOnto v : _) = v := fun v =>
    by rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_top]; rfl
  have hL : Module.finrank ℝ L = 2 := by
    rw [finrank_top, finrank_euclideanSpace_fin]
  have h := rank_ge_of_pp_comparison_BAS (V := EuclideanSpace ℝ (Fin 2)) L 0 (fun v => ‖v‖)
    (fun v hv => norm_pos_iff.mpr hv) LinearMap.id LinearMap.id
    (ContinuousLinearMap.id ℝ _) (e := 0) (δ := 0) (Ξ := 0) (Cu := 1)
    (fun y => ⟨y, Subtype.ext (hπ y)⟩)
    (fun v => by simp [hπ]) (fun v _ => by
      change 1 / 2 * ‖v‖ ≤ ‖(L.orthogonalProjectionOnto v : EuclideanSpace ℝ (Fin 2))‖
      rw [hπ]; linarith [norm_nonneg v])
    (fun v => by
      change ‖(L.orthogonalProjectionOnto v : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 * ‖v‖
      rw [hπ, one_mul])
    (fun v => by simp) (by rw [Submodule.starProjection_top, sub_self, norm_zero])
    le_rfl (by norm_num)
  rwa [hL] at h

/-- (b2) on `ℝ`: the unit vector `1` for the whole line. -/
theorem ne_zero_of_unit_pp_comparison_real_BASP :
    (ContinuousLinearMap.id ℝ ℝ) ((LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1) ≠ 0 := by
  set L : Submodule ℝ ℝ := ⊤
  have hπ : ∀ v : ℝ, L.starProjection v = v := fun v => by
    rw [Submodule.starProjection_top]; rfl
  exact ne_zero_of_unit_pp_comparison_BAS L LinearMap.id LinearMap.id
    (ContinuousLinearMap.id ℝ ℝ) (e := 1) (δ := 0) (Ξ := 0) (Cu := 1) 1
    (by rw [LinearMap.id_apply, hπ]; norm_num) (by rw [LinearMap.id_apply, hπ]; norm_num)
    (by rw [LinearMap.id_apply, hπ]; norm_num) (by simp)
    (by rw [Submodule.starProjection_top, sub_self, norm_zero]) le_rfl (by norm_num)

end DifferentialGeometry.Analysis
