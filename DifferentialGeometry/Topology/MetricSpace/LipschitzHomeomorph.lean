import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set
open scoped NNReal

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem exists_homeomorph_range_of_lipschitz_lower_bound {f : X → Y} {C ε : ℝ≥0}
    (hLip : LipschitzWith C f) (hε : 0 < ε)
    (hlower : ∀ x y, (ε : ℝ) * dist x y ≤ dist (f x) (f y)) :
    ∃ e : X ≃ₜ range f, (∀ x, (e x : Y) = f x) ∧
      LipschitzWith C e ∧ LipschitzWith ε⁻¹ e.symm := by
  have hεR : 0 < (ε : ℝ) := hε
  have ha : AntilipschitzWith ε⁻¹ f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have h := mul_le_mul_of_nonneg_left (hlower x y) (inv_nonneg.mpr hεR.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hεR.ne', one_mul, NNReal.coe_inv] using h
  let e := (ha.isEmbedding hLip.continuous).toHomeomorph
  have he (x : X) : (e x : Y) = f x := rfl
  refine ⟨e, he, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hLip.dist_le_mul x y
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    have hfu (w : range f) : f (e.symm w) = (w : Y) := by
      exact congrArg Subtype.val (e.apply_symm_apply w)
    have h := ha.le_mul_dist (e.symm u) (e.symm v)
    rw [hfu u, hfu v] at h
    exact h

end Metric
