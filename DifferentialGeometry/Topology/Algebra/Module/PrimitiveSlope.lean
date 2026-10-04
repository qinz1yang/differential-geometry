import DifferentialGeometry.Topology.Algebra.Module.UnimodularPair
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

open Matrix

namespace Int

abbrev PrimitivePair := {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1)}

instance primitivePairSetoid : Setoid PrimitivePair where
  r v w := v.val = w.val ∨ v.val = -w.val
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg])),
    fun h₁ h₂ => by
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inr (h₁.trans h₂)
      · exact Or.inr (by rw [h₁, h₂])
      · exact Or.inl (by rw [h₁, h₂, neg_neg])⟩

def PrimitiveSlope := Quotient primitivePairSetoid

namespace PrimitiveSlope

def mk (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) : PrimitiveSlope :=
  Quotient.mk _ ⟨v, hv⟩

theorem mk_eq_mk_iff (v w : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1))
    (hw : IsCoprime (w 0) (w 1)) :
    mk v hv = mk w hw ↔ v = w ∨ v = -w := Quotient.eq

theorem mk_eq_mk_iff_det_eq_zero (v w : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1))
    (hw : IsCoprime (w 0) (w 1)) :
    mk v hv = mk w hw ↔ v 0 * w 1 - v 1 * w 0 = 0 := by
  rw [mk_eq_mk_iff, Int.det_eq_zero_iff_eq_or_eq_neg hv hw]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨(congrFun h 0).symm, (congrFun h 1).symm⟩
    · right
      constructor
      · simpa using (congrArg Neg.neg (congrFun h 0)).symm
      · simpa using (congrArg Neg.neg (congrFun h 1)).symm
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    · left
      funext i
      fin_cases i <;> simp [h₀, h₁]
    · right
      funext i
      fin_cases i <;> simp [h₀, h₁]

def delta (s t : PrimitiveSlope) : ℤ :=
  Quotient.liftOn₂ s t (fun v w => |v.val 0 * w.val 1 - v.val 1 * w.val 0|)
    (by
      intro v w v' w' hv hw
      rcases hv with hv | hv <;> rcases hw with hw | hw
      · rw [hv, hw]
      · rw [hv, hw]
        simp only [Pi.neg_apply, mul_neg, neg_sub_neg]
        exact abs_sub_comm _ _
      · rw [hv, hw]
        simp only [Pi.neg_apply, neg_mul, neg_sub_neg]
        exact abs_sub_comm _ _
      · rw [hv, hw]
        simp)

theorem delta_mk (v w : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1))
    (hw : IsCoprime (w 0) (w 1)) :
    delta (mk v hv) (mk w hw) = |v 0 * w 1 - v 1 * w 0| := rfl

theorem delta_nonneg (s t : PrimitiveSlope) : 0 ≤ delta s t :=
  Quotient.inductionOn₂ s t (fun _ _ => abs_nonneg _)

theorem delta_comm (s t : PrimitiveSlope) : delta s t = delta t s := by
  refine Quotient.inductionOn₂ s t fun v w => ?_
  change |v.val 0 * w.val 1 - v.val 1 * w.val 0| =
    |w.val 0 * v.val 1 - w.val 1 * v.val 0|
  rw [mul_comm (w.val 0), mul_comm (w.val 1), abs_sub_comm]

theorem delta_eq_zero_iff (s t : PrimitiveSlope) : delta s t = 0 ↔ s = t := by
  refine Quotient.inductionOn₂ s t fun v w => ?_
  change |v.val 0 * w.val 1 - v.val 1 * w.val 0| = 0 ↔ mk v.val v.property = mk w.val w.property
  rw [abs_eq_zero, mk_eq_mk_iff_det_eq_zero]

def map (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) (s : PrimitiveSlope) : PrimitiveSlope :=
  Quotient.map (fun v => ⟨A.val *ᵥ v.val,
    Matrix.isCoprime_mulVec_of_isUnit_det A.val A.det.isUnit v.property⟩)
    (by
      intro v w h
      rcases h with h | h
      · exact Or.inl (congrArg (A.val *ᵥ ·) h)
      · apply Or.inr
        change A.val *ᵥ v.val = -(A.val *ᵥ w.val)
        rw [h, Matrix.mulVec_neg]) s

theorem map_mk (A : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    map A (mk v hv) = mk (A.val *ᵥ v)
      (Matrix.isCoprime_mulVec_of_isUnit_det A.val A.det.isUnit hv) := rfl

theorem delta_map (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) (s t : PrimitiveSlope) :
    delta (map A s) (map A t) = delta s t := by
  refine Quotient.inductionOn₂ s t fun v w => ?_
  exact Matrix.abs_det_pair_mulVec A.val A.det.isUnit v.val w.val

theorem map_one (s : PrimitiveSlope) : map 1 s = s := by
  refine Quotient.inductionOn s fun v => ?_
  apply Quotient.sound
  exact Or.inl (Matrix.one_mulVec v.val)

theorem map_mul (A B : Matrix.GeneralLinearGroup (Fin 2) ℤ) (s : PrimitiveSlope) :
    map (A * B) s = map A (map B s) := by
  refine Quotient.inductionOn s fun v => ?_
  apply Quotient.sound
  exact Or.inl (Matrix.mulVec_mulVec v.val A.val B.val).symm

def mapEquiv (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) : PrimitiveSlope ≃ PrimitiveSlope where
  toFun := map A
  invFun := map A⁻¹
  left_inv s := by rw [← map_mul, inv_mul_cancel, map_one]
  right_inv s := by rw [← map_mul, mul_inv_cancel, map_one]

end PrimitiveSlope

end Int
