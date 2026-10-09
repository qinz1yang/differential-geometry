import DifferentialGeometry.Topology.Algebra.Group.TorusMatrix
import DifferentialGeometry.Topology.Algebra.Group.IntegerTorsion

set_option autoImplicit false
noncomputable section
open Matrix

namespace Circle

theorem mem_range_slopeMap_iff (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1))
    (p : Circle × Circle) :
    p ∈ Set.range (slopeMap v) ↔ p.1 ^ v 1 = p.2 ^ v 0 := by
  exact hv.mem_range_smul_pair_iff (M := Additive Circle) p.1 p.2

theorem slopeMap_mem_range_iff (v w : Fin 2 → ℤ) (hw : IsCoprime (w 0) (w 1))
    (z : Circle) :
    slopeMap v z ∈ Set.range (slopeMap w) ↔ z ^ (v 0 * w 1 - v 1 * w 0) = 1 := by
  rw [mem_range_slopeMap_iff w hw]
  simp only [slopeMap, ← zpow_mul, zpow_sub, mul_inv_eq_one]

private def rootsOfUnityEquivZPow (n : ℤ) :
    rootsOfUnity n.natAbs Circle ≃ {z : Circle // z ^ n = 1} :=
  rootsOfUnityZPowEquiv Circle n

private def slopeIntersectionEquiv (v w : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1))
    (hw : IsCoprime (w 0) (w 1)) :
    {z : Circle // z ^ (v 0 * w 1 - v 1 * w 0) = 1} ≃
      ↥(Set.range (slopeMap v) ∩ Set.range (slopeMap w)) :=
  Equiv.ofBijective
    (fun z => ⟨slopeMap v z.val, ⟨z.val, rfl⟩,
      (slopeMap_mem_range_iff v w hw z.val).mpr z.property⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (slopeMap_injective v hv (congrArg Subtype.val hxy))
    · rintro ⟨p, ⟨z, rfl⟩, hp⟩
      exact ⟨⟨z, (slopeMap_mem_range_iff v w hw z).mp hp⟩, rfl⟩)

theorem finite_slopeMap_intersection (v w : Fin 2 → ℤ)
    (hv : IsCoprime (v 0) (v 1)) (hw : IsCoprime (w 0) (w 1))
    (hd : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    (Set.range (slopeMap v) ∩ Set.range (slopeMap w)).Finite := by
  let n := v 0 * w 1 - v 1 * w 0
  have : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hd⟩
  let : Finite ↥(Set.range (slopeMap v) ∩ Set.range (slopeMap w)) :=
    Finite.of_equiv (rootsOfUnity n.natAbs Circle)
      ((rootsOfUnityEquivZPow n).trans (slopeIntersectionEquiv v w hv hw))
  exact Set.toFinite _

theorem card_slopeMap_intersection (v w : Fin 2 → ℤ)
    (hv : IsCoprime (v 0) (v 1)) (hw : IsCoprime (w 0) (w 1))
    (hd : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    Nat.card ↥(Set.range (slopeMap v) ∩ Set.range (slopeMap w)) =
      (v 0 * w 1 - v 1 * w 0).natAbs := by
  let n := v 0 * w 1 - v 1 * w 0
  have : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hd⟩
  calc
    _ = Nat.card (rootsOfUnity n.natAbs Circle) :=
      Nat.card_congr ((rootsOfUnityEquivZPow n).trans (slopeIntersectionEquiv v w hv hw)).symm
    _ = _ := HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle n.natAbs


theorem finite_slopeSet_intersection {s t : Int.PrimitiveSlope} (h : s ≠ t) :
    (slopeSet s ∩ slopeSet t).Finite := by
  revert h
  refine Quotient.inductionOn₂ s t fun v w h => ?_
  exact finite_slopeMap_intersection v.val w.val v.property w.property
    (fun hd => h ((Int.PrimitiveSlope.mk_eq_mk_iff_det_eq_zero _ _ _ _).mpr hd))

theorem card_slopeSet_intersection {s t : Int.PrimitiveSlope} (h : s ≠ t) :
    Nat.card ↥(slopeSet s ∩ slopeSet t) = (Int.PrimitiveSlope.delta s t).toNat := by
  revert h
  refine Quotient.inductionOn₂ s t fun v w h => ?_
  have hd : v.val 0 * w.val 1 - v.val 1 * w.val 0 ≠ 0 :=
    fun hd => h ((Int.PrimitiveSlope.mk_eq_mk_iff_det_eq_zero _ _ _ _).mpr hd)
  change Nat.card ↥(Set.range (slopeMap v.val) ∩ Set.range (slopeMap w.val)) =
    |v.val 0 * w.val 1 - v.val 1 * w.val 0|.toNat
  rw [← Int.natCast_natAbs, Int.toNat_natCast]
  exact card_slopeMap_intersection v.val w.val v.property w.property hd

end Circle
