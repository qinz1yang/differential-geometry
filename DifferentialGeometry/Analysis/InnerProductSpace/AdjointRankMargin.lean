import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped InnerProductSpace
namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem surjective_and_lower_bound_of_adjoint (P : E →L[ℝ] F) {a : ℝ}
    (ha : 0 < a) (hl : ∀ w, a * ‖w‖ ≤ ‖P.adjoint w‖) :
    Function.Surjective P ∧ ∀ v ∈ P.kerᗮ, a * ‖v‖ ≤ ‖P v‖ := by
  have hk : P.adjoint.ker = ⊥ := by
    ext w
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hw
      change P.adjoint w = 0 at hw
      have hh := hl w
      rw [hw, norm_zero] at hh
      have hz : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
      exact norm_eq_zero.mp hz
    · intro hw
      simp only [hw, map_zero]
  have hrange : P.range = ⊤ := Submodule.orthogonal_eq_bot_iff.mp (P.orthogonal_range.trans hk)
  refine ⟨LinearMap.range_eq_top.mp hrange, ?_⟩
  intro v hv
  have hker : P.kerᗮ = P.adjoint.range := by
    simpa only [P.adjoint_toLinearMap] using P.toLinearMap.orthogonal_ker
  rw [hker] at hv
  obtain ⟨w, rfl⟩ := hv
  change a * ‖P.adjoint w‖ ≤ ‖P (P.adjoint w)‖
  have hh := hl w
  have hi : ‖P.adjoint w‖ ^ 2 = ⟪P (P.adjoint w), w⟫_ℝ := by
    rw [← P.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hc := real_inner_le_norm (P (P.adjoint w)) w
  rw [← hi] at hc
  by_cases hz : ‖P.adjoint w‖ = 0
  · simp only [hz, mul_zero, norm_nonneg]
  have hp : 0 < ‖P.adjoint w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have h1 := mul_le_mul_of_nonneg_left hc ha.le
  have h2 := mul_le_mul_of_nonneg_left hh (norm_nonneg (P (P.adjoint w)))
  nlinarith

theorem adjoint_lower_bound_of_norm_sub_le (P A : E →L[ℝ] F) {a e : ℝ}
    (hA : ∀ w, a * ‖w‖ ≤ ‖A.adjoint w‖) (herror : ‖P - A‖ ≤ e) :
    ∀ w, (a - e) * ‖w‖ ≤ ‖P.adjoint w‖ := by
  intro w
  have hd := (P.adjoint - A.adjoint).le_opNorm w
  have hn : ‖P.adjoint - A.adjoint‖ = ‖P - A‖ := by
    rw [← map_sub]
    exact LinearIsometryEquiv.norm_map _ _
  rw [hn] at hd
  have he := mul_le_mul_of_nonneg_right herror (norm_nonneg w)
  have ht := norm_sub_le (P.adjoint w) ((P.adjoint - A.adjoint) w)
  have ht' : ‖A.adjoint w‖ ≤ ‖P.adjoint w‖ + ‖(P.adjoint - A.adjoint) w‖ := by
    simpa only [sub_apply, sub_sub_cancel] using ht
  nlinarith [hA w]

theorem surjective_of_adjoint_margin (P A : E →L[ℝ] F) {a e : ℝ}
    (hA : ∀ w, a * ‖w‖ ≤ ‖A.adjoint w‖) (herror : ‖P - A‖ ≤ e) (he : e < a) :
    Function.Surjective P ∧ ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ :=
  P.surjective_and_lower_bound_of_adjoint (sub_pos.mpr he)
    (P.adjoint_lower_bound_of_norm_sub_le A hA herror)

end ContinuousLinearMap
