import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
noncomputable section

def rootsOfUnityZPowEquiv (G : Type*) [CommGroup G] (n : ℤ) :
    rootsOfUnity n.natAbs G ≃ {z : G // z ^ n = 1} where
  toFun z := ⟨z.val.val, pow_natAbs_eq_one.mp ((mem_rootsOfUnity' _ _).mp z.property)⟩
  invFun z := ⟨_root_.toUnits z.val, (mem_rootsOfUnity' _ _).mpr (pow_natAbs_eq_one.mpr z.property)⟩
  left_inv z := by ext; rfl
  right_inv z := by rfl

namespace Circle

theorem finite_zpow_eq_one (n : ℤ) (hn : n ≠ 0) :
    ({z : Circle | z ^ n = 1}).Finite := by
  let : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hn⟩
  exact Finite.of_equiv (rootsOfUnity n.natAbs Circle) (rootsOfUnityZPowEquiv Circle n)

theorem natCard_zpow_eq_one (n : ℤ) (hn : n ≠ 0) :
    Nat.card {z : Circle // z ^ n = 1} = n.natAbs := by
  let : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hn⟩
  calc
    _ = Nat.card (rootsOfUnity n.natAbs Circle) :=
      Nat.card_congr (rootsOfUnityZPowEquiv Circle n).symm
    _ = _ := HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle n.natAbs

end Circle
