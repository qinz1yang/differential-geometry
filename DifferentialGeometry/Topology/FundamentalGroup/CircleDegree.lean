import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.FundamentalGroup.CircleLoopGenerator

set_option autoImplicit false
noncomputable section
open AddSubgroup
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

private theorem intCast_eq_zero_unitAddCircle (k : ℤ) :
    (((k : ℝ) : loopCircle)) = 0 := by
  rw [show (k : ℝ) = k • (1 : ℝ) by simp,
    AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

def circleDegreePath (k : ℤ) : Path (0 : loopCircle) 0 where
  toFun t := (((k : ℝ) * (t : ℝ) : ℝ) : loopCircle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

def circleFiberInteger (k : ℤ) : ((↑) : ℝ → loopCircle) ⁻¹' {(0 : loopCircle)} :=
  ⟨k, intCast_eq_zero_unitAddCircle k⟩

theorem monodromy_circleDegreePath (k : ℤ) :
    circleQuotientCovering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (circleDegreePath k)) circleFiberZero =
        circleFiberInteger k := by
  exact circleQuotientCovering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (Path.segment 0 (k : ℝ))) (by
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      change ((AffineMap.lineMap (0 : ℝ) (k : ℝ) (t : ℝ) : ℝ) : loopCircle) =
        (((k : ℝ) * (t : ℝ) : ℝ) : loopCircle)
      simp only [AffineMap.lineMap_apply_ring, zero_mul, zero_add, mul_comm])

theorem fundamentalGroupToMulOpposite_circleDegreePath (k : ℤ) :
    circleQuotientCovering.fundamentalGroupToMulOpposite circleFiberZero
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleDegreePath k))) =
        MulOpposite.op (Multiplicative.ofAdd
          (⟨(k : ℝ), intCast_mem_zmultiples_one (R := ℝ) k⟩ : zmultiples (1 : ℝ))) := by
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff,
    monodromy_circleDegreePath]
  simp only [MulOpposite.unop_op, circleFiberZero, circleFiberInteger]
  exact add_zero (k : ℝ)

theorem fundamentalGroupUnitAddCircleEquivInt_circleDegreePath (k : ℤ) :
    fundamentalGroupUnitAddCircleEquivInt
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleDegreePath k))) =
        Multiplicative.ofAdd k := by
  apply intEquivZMultiplesOne.toMultiplicative.injective
  change intEquivZMultiplesOne.toMultiplicative
      (intEquivZMultiplesOne.toMultiplicative.symm
        (circleQuotientCovering.fundamentalGroupToMulOpposite circleFiberZero
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleDegreePath k)))).unop) = _
  rw [MulEquiv.apply_symm_apply, fundamentalGroupToMulOpposite_circleDegreePath]
  rfl

theorem circleDegreePath_one : circleDegreePath 1 = circleGeneratorPath := by
  ext t
  change (((((1 : ℤ) : ℝ) * (t : ℝ)) : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
  rw [Int.cast_one, one_mul]

theorem fundamentalGroupUnitAddCircleEquivInt_generator :
    fundamentalGroupUnitAddCircleEquivInt
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)) =
        Multiplicative.ofAdd (1 : ℤ) := by
  rw [← circleDegreePath_one]
  exact fundamentalGroupUnitAddCircleEquivInt_circleDegreePath 1

def unitAddCircleMultiply (k : ℤ) : C(loopCircle, loopCircle) :=
  ⟨fun z => k • z, by fun_prop⟩

@[simp] theorem unitAddCircleMultiply_zero (k : ℤ) : unitAddCircleMultiply k 0 = 0 := by
  simp [unitAddCircleMultiply]

theorem unitAddCircleMultiply_map_generator (k : ℤ) :
    FundamentalGroup.mapOfEq (unitAddCircleMultiply k) (unitAddCircleMultiply_zero k)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleDegreePath k)) := by
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    ((circleGeneratorPath.map (unitAddCircleMultiply k).continuous).cast _ _) =
      Path.Homotopic.Quotient.mk (circleDegreePath k)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  change k • ((t : ℝ) : loopCircle) = (((k : ℝ) * (t : ℝ) : ℝ) : loopCircle)
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem fundamentalGroupUnitAddCircleEquivInt_map_multiply (k : ℤ)
    (a : FundamentalGroup loopCircle 0) :
    fundamentalGroupUnitAddCircleEquivInt
      (FundamentalGroup.mapOfEq (unitAddCircleMultiply k) (unitAddCircleMultiply_zero k) a) =
        Multiplicative.ofAdd (k * (fundamentalGroupUnitAddCircleEquivInt a).toAdd) := by
  obtain ⟨m, rfl⟩ := exists_zpow_fundamentalGroup_loopCircle a
  rw [map_zpow, map_zpow, unitAddCircleMultiply_map_generator,
    fundamentalGroupUnitAddCircleEquivInt_circleDegreePath,
    map_zpow, fundamentalGroupUnitAddCircleEquivInt_generator]
  simp only [← ofAdd_zsmul, zsmul_eq_mul, mul_one,
    toAdd_ofAdd, mul_comm]

end DifferentialGeometry.Topology
