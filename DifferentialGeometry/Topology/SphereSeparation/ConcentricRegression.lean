import Mathlib.Topology.Algebra.ConstMulAction
import DifferentialGeometry.Topology.SphereSeparation.Nesting
import DifferentialGeometry.Topology.SphereSeparation.Transport
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere

set_option autoImplicit false

open Set
open Metric

namespace DifferentialGeometry.Topology.SphereSeparation

theorem image_unitSphere_smulOfNeZero {r : ℝ} (hr : 0 < r) :
    (Homeomorph.smulOfNeZero r hr.ne' : EuclideanThree ≃ₜ EuclideanThree) ''
        sphere (0 : EuclideanThree) 1 =
      sphere (0 : EuclideanThree) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hy ⊢
    change ‖r • y‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hy, mul_one]
  · intro hx
    rw [mem_sphere_zero_iff_norm] at hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr), hx, inv_mul_cancel₀ hr.ne']
    · simp only [Homeomorph.smulOfNeZero_apply]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

noncomputable def roundSphereSides (r : ℝ) (hr : 0 < r) :
    SphereSides
      ((Homeomorph.smulOfNeZero r hr.ne' :
          EuclideanThree ≃ₜ EuclideanThree) ''
        sphere (0 : EuclideanThree) 1) :=
  standardUnitSphereSides.image (Homeomorph.smulOfNeZero r hr.ne')

@[simp] theorem roundSphereSides_compactSide {r : ℝ} (hr : 0 < r) :
    (roundSphereSides r hr).compactSide = ball (0 : EuclideanThree) r := by
  rw [roundSphereSides]
  change (Homeomorph.smulOfNeZero r hr.ne' :
      EuclideanThree ≃ₜ EuclideanThree) '' ball 0 1 = ball 0 r
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy ⊢
    change ‖r • y‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  · intro hx
    rw [mem_ball_zero_iff] at hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_lt_one₀ hr).2 hx
    · simp only [Homeomorph.smulOfNeZero_apply]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]


theorem concentric_roundSphere_strictlyNested
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    closure (roundSphereSides r hr).compactSide ⊂
      closure (roundSphereSides s (hr.trans hrs)).compactSide := by
  rw [roundSphereSides_compactSide hr,
    roundSphereSides_compactSide (hr.trans hrs),
    closure_ball 0 hr.ne', closure_ball 0 (hr.trans hrs).ne']
  refine Set.ssubset_iff_subset_ne.2 ⟨closedBall_subset_closedBall hrs.le, ?_⟩
  intro heq
  let x : EuclideanThree := EuclideanSpace.single 0 s
  have hxnorm : ‖x‖ = s := by
    simp [x, Real.norm_eq_abs, abs_of_pos (hr.trans hrs)]
  have hxs : x ∈ closedBall (0 : EuclideanThree) s := by
    rw [mem_closedBall_zero_iff, hxnorm]
  have hxr : x ∈ closedBall (0 : EuclideanThree) r := by
    rw [heq]
    exact hxs
  rw [mem_closedBall_zero_iff, hxnorm] at hxr
  exact (not_lt_of_ge hxr) hrs

theorem concentric_roundSphere_exclusiveNesting
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    let dᵣ := roundSphereSides r hr
    let dₛ := roundSphereSides s (hr.trans hrs)
    Xor
      (closure dᵣ.compactSide ⊂ dₛ.compactSide ∧
        dₛ.compactSide = interior (closure dₛ.compactSide) ∧
        closure dᵣ.compactSide ⊂ closure dₛ.compactSide)
      (closure dₛ.compactSide ⊂ dᵣ.compactSide ∧
        dᵣ.compactSide = interior (closure dᵣ.compactSide) ∧
        closure dₛ.compactSide ⊂ closure dᵣ.compactSide) := by
  let dᵣ := roundSphereSides r hr
  let dₛ := roundSphereSides s (hr.trans hrs)
  have hleft : closure dᵣ.compactSide ⊂ dₛ.compactSide := by
    rw [roundSphereSides_compactSide hr,
      roundSphereSides_compactSide (hr.trans hrs), closure_ball 0 hr.ne']
    refine Set.ssubset_iff_subset_ne.mpr ⟨closedBall_subset_ball hrs, ?_⟩
    intro heq
    let x : EuclideanThree := EuclideanSpace.single 0 ((r + s) / 2)
    have hxnorm : ‖x‖ = (r + s) / 2 := by
      simp [x, Real.norm_eq_abs]
      linarith
    have hxs : x ∈ ball (0 : EuclideanThree) s := by
      rw [mem_ball_zero_iff, hxnorm]
      linarith
    have hxr : x ∉ closedBall (0 : EuclideanThree) r := by
      rw [mem_closedBall_zero_iff, hxnorm]
      linarith
    exact hxr (heq ▸ hxs)
  have hinterior : dₛ.compactSide = interior (closure dₛ.compactSide) := by
    rw [roundSphereSides_compactSide (hr.trans hrs),
      closure_ball 0 (hr.trans hrs).ne', interior_closedBall 0 (hr.trans hrs).ne']
  have hclosure := concentric_roundSphere_strictlyNested hr hrs
  refine Or.inl ⟨⟨hleft, hinterior, hclosure⟩, ?_⟩
  rintro ⟨_, _, hreverse⟩
  exact lt_asymm hclosure hreverse

end DifferentialGeometry.Topology.SphereSeparation
