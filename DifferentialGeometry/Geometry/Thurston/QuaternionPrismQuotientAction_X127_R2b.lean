import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismAxisSign_X127_R3b

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismAxisSignX127

namespace GC.Geometry.QuaternionPrismQuotientActionX127

local notation "UQ" => unitary (Quaternion ℝ)

def prismQuotientGroupMap_X127 (n : ℕ) [NeZero n] :
    QuaternionGroup n →* (spaceForm_X127 n).group := by
  let H : Subgroup UQ := (hom_X127 n).range
  letI : Finite H := inferInstance
  exact (quaternionLeftSpaceFormEquiv H).toMonoidHom.comp
    (hom_X127 n).rangeRestrict

theorem prismQuotientGroupMap_surjective_X127 (n : ℕ) [NeZero n] :
    Function.Surjective (prismQuotientGroupMap_X127 n) := by
  let H : Subgroup UQ := (hom_X127 n).range
  have : Finite H := inferInstance
  intro γ
  obtain ⟨h, hh⟩ := (quaternionLeftSpaceFormEquiv H).surjective γ
  obtain ⟨q, hq⟩ := (hom_X127 n).rangeRestrict_surjective h
  refine ⟨q, ?_⟩
  change (quaternionLeftSpaceFormEquiv H) ((hom_X127 n).rangeRestrict q) = γ
  rw [hq, hh]

theorem prismQuotientGroupMap_action_X127 (n : ℕ) [NeZero n]
    (q : QuaternionGroup n) :
    (prismQuotientGroupMap_X127 n q).val = quaternionLeftHom (value_X127 n q) := rfl

theorem prismQuotientGroupMap_axis_normalizer_X127 (n : ℕ) [NeZero n]
    (q : QuaternionGroup n) :
    star (value_X127 n q : Quaternion ℝ) * axisI_X127 *
        (value_X127 n q : Quaternion ℝ) = axisI_X127 ∨
      star (value_X127 n q : Quaternion ℝ) * axisI_X127 *
        (value_X127 n q : Quaternion ℝ) = -axisI_X127 :=
  value_normalizes_axisI_X127 n q

end GC.Geometry.QuaternionPrismQuotientActionX127
