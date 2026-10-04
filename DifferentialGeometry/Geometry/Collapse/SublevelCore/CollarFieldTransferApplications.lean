import DifferentialGeometry.Geometry.Collapse.SublevelCore.CollarFieldTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCoreApplications

/-!
# Consumer of the LC48 collar-field kernel

On `M = ℝ` with `η = id`, band field `Y₀ = 1`, core `D = (-∞, h₀]` and the collar field `Z = 2`
given only on the open collar `(h₀ - δ, h₀ + δ)`, the patched field of `exists_isotopy_of_collar_field`
carries `D` onto `(-∞, ρ]`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **Consumer of the LC48 kernel.** A collar field defined only near `h₀` and the band field
`1` together move `(-∞, h₀]` onto `(-∞, ρ]`. -/
theorem real_halfLine_isotopic_of_collar {a b h₀ ρ δ : ℝ} (hah : a < h₀) (hhb : h₀ < b)
    (hρ : ρ ∈ Ioo a b) (hδ : 0 < δ) :
    ∃ Hs : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      Hs 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞ ∧
      (∃ S : Set ℝ, IsCompact S ∧ S ⊆ Ioo a b ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' Iic h₀ = Iic ρ := by
  let Y₀ : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun _ => (1 : ℝ)
  let Z : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun _ => (2 : ℝ)
  have hid : ∀ x v : ℝ, mvfderiv (I := 𝓘(ℝ, ℝ)) (fun y : ℝ => y) x v = v := by
    intro x v
    simpa using mvfderiv_real_sub_const 0 x v
  obtain ⟨Hs, h0, -, -, hS, hD⟩ := exists_isotopy_of_collar_field (I := 𝓘(ℝ, ℝ))
    (η := fun x : ℝ => x) continuous_id isOpen_univ contMDiffOn_id hρ isCompact_Icc
    (subset_univ _) Y₀ (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const).contMDiffOn
    (fun x _ => by rw [hid]; exact one_pos) isClosed_Iic
    (fun x hx => by
      rw [interior_Iic]
      exact lt_of_le_of_lt (show x ≤ a from hx) hah)
    (fun x hx => lt_of_le_of_lt (show x ≤ h₀ from hx) hhb)
    (Wc := Ioo (h₀ - δ) (h₀ + δ)) isOpen_Ioo
    (fun q hq => by
      rw [frontier_Iic, mem_singleton_iff] at hq
      rw [hq]
      constructor <;> linarith)
    Z (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const).contMDiffOn
    (fun x _ => by rw [hid]; norm_num)
    (fun q hq => by
      refine ⟨univ, isOpen_univ, mem_univ _, fun y => y - h₀,
        (contMDiff_id.sub contMDiff_const).contMDiffOn, ?_, ?_⟩
      · ext y
        simp
      · rw [mvfderiv_real_sub_const]
        norm_num)
  exact ⟨Hs, h0, hS, hD⟩

end DifferentialGeometry.Geometry.Collapse
