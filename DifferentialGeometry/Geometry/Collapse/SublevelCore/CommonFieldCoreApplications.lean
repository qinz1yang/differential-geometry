import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCore

/-!
# Consumer of LC47

The one-dimensional instance: on `M = ℝ` with `η = id`, the constant field `Y = 1` and the core
`D = (-∞, h₀]` with `a < h₀ < b` (defining function `x - h₀`), LC47 moves `D` onto `(-∞, ρ]` for any
`ρ ∈ (a, b)` by a smooth isotopy of `ℝ` supported in one compact subset of `(a, b)`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

theorem mvfderiv_real_sub_const (c x v : ℝ) :
    mvfderiv (I := 𝓘(ℝ, ℝ)) (fun y : ℝ => y - c) x v = v := by
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, fderiv_sub_const, fderiv_fun_id]
  rfl

/-- **Consumer of LC47.** Every half-line `(-∞, h₀]` with `a < h₀ < b` is carried onto `(-∞, ρ]`
by a smooth isotopy of `ℝ` that is the identity off a compact subset of `(a, b)`. -/
theorem real_halfLine_isotopic {a b h₀ ρ : ℝ} (hah : a < h₀) (hhb : h₀ < b) (hρ : ρ ∈ Ioo a b) :
    ∃ Hs : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      Hs 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞ ∧
      (∃ S : Set ℝ, IsCompact S ∧ S ⊆ Ioo a b ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' Iic h₀ = Iic ρ := by
  let Y : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun _ => (1 : ℝ)
  have hY : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) univ :=
    (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const).contMDiffOn
  have hid : ∀ x v : ℝ, mvfderiv (I := 𝓘(ℝ, ℝ)) (fun y : ℝ => y) x v = v := by
    intro x v
    simpa using mvfderiv_real_sub_const 0 x v
  obtain ⟨Hs, h0, -, -, hS, hD⟩ := exists_isotopy_of_common_outward_field (I := 𝓘(ℝ, ℝ))
    (η := fun x : ℝ => x) continuous_id isOpen_univ contMDiffOn_id hρ isCompact_Icc
    (subset_univ _) Y hY (fun x _ => by rw [hid]; exact one_pos) isClosed_Iic
    (fun x hx => by
      rw [interior_Iic]
      exact lt_of_le_of_lt (show x ≤ a from hx) hah)
    (fun x hx => lt_of_le_of_lt (show x ≤ h₀ from hx) hhb)
    (fun q hq => by
      rw [frontier_Iic, mem_singleton_iff] at hq
      refine ⟨univ, isOpen_univ, mem_univ _, fun y => y - h₀,
        (contMDiff_id.sub contMDiff_const).contMDiffOn, ?_, ?_⟩
      · ext y
        simp
      · rw [mvfderiv_real_sub_const]
        exact one_pos)
  exact ⟨Hs, h0, hS, hD⟩

end DifferentialGeometry.Geometry.Collapse
