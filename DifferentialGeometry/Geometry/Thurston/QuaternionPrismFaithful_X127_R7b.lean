import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open GC.Geometry.QuaternionPrismX127R3

namespace GC.Geometry.QuaternionPrismFaithfulX127

theorem characterComplex_injective_X127 (n : ℕ) [NeZero n] :
    Function.Injective (characterComplex_X127 n) := by
  intro i k h
  have hsub : characterSubgroup_X127 n i = characterSubgroup_X127 n k :=
    Subtype.ext h
  change Additive.toMul ((rootUnit_primitive_X127 n).zmodEquivZPowers i) =
    Additive.toMul ((rootUnit_primitive_X127 n).zmodEquivZPowers k) at hsub
  exact (rootUnit_primitive_X127 n).zmodEquivZPowers.injective
    (Additive.toMul.injective hsub)

theorem characterQ_injective_X127 (n : ℕ) [NeZero n] :
    Function.Injective (characterQ_X127 n) := by
  intro i k h
  have hv := congrArg Subtype.val h
  have hcomplex : characterComplex_X127 n i = characterComplex_X127 n k := by
    apply Units.ext
    apply Complex.ext
    · simpa [characterQ_X127, Quaternion.re_coeComplex] using
        congrArg (fun z : Quaternion ℝ => z.re) hv
    · simpa [characterQ_X127, Quaternion.imI_coeComplex] using
        congrArg (fun z : Quaternion ℝ => z.imI) hv
  exact characterComplex_injective_X127 n hcomplex

private theorem characterQ_ne_j_mul_character_X127 (n : ℕ) [NeZero n]
    (i k : ZMod (2 * n)) :
    characterQ_X127 n i ≠ jUnit_X127 * characterQ_X127 n k := by
  intro h
  have hjval : (jUnit_X127 : Quaternion ℝ) = (⟨0, 0, 1, 0⟩ : Quaternion ℝ) := rfl
  have hv := congrArg Subtype.val h
  change ((characterComplex_X127 n i : ℂˣ) : Quaternion ℝ) =
    (jUnit_X127 : Quaternion ℝ) *
      ((characterComplex_X127 n k : ℂˣ) : Quaternion ℝ) at hv
  rw [hjval] at hv
  have hre : (((characterComplex_X127 n i : ℂˣ) : ℂ).re) = 0 := by
    have hr := congrArg (fun z : Quaternion ℝ => z.re) hv
    simpa [Quaternion.coeComplex] using hr
  have him : (((characterComplex_X127 n i : ℂˣ) : ℂ).im) = 0 := by
    have hi := congrArg (fun z : Quaternion ℝ => z.imI) hv
    simpa [Quaternion.coeComplex] using hi
  have hzero : ((characterComplex_X127 n i : ℂˣ) : ℂ) = 0 := by
    apply Complex.ext
    · exact hre
    · exact him
  exact (Units.ne_zero (characterComplex_X127 n i)) hzero

theorem hom_injective_X127 (n : ℕ) [NeZero n] :
    Function.Injective (hom_X127 n) := by
  intro q r h
  change value_X127 n q = value_X127 n r at h
  cases q with
  | a i =>
      cases r with
      | a k =>
          exact congrArg QuaternionGroup.a
            (characterQ_injective_X127 n (by simpa [value_X127] using h))
      | xa k =>
          exact (characterQ_ne_j_mul_character_X127 n i k
            (by simpa [value_X127] using h)).elim
  | xa i =>
      cases r with
      | a k =>
          exact (characterQ_ne_j_mul_character_X127 n k i
            (by simpa [value_X127] using h.symm)).elim
      | xa k =>
          have hchar : characterQ_X127 n i = characterQ_X127 n k :=
            by simpa [value_X127] using h
          exact congrArg QuaternionGroup.xa (characterQ_injective_X127 n hchar)

end GC.Geometry.QuaternionPrismFaithfulX127
