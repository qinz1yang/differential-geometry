import DifferentialGeometry.Topology.FundamentalGroup.CircleDegree

set_option autoImplicit false
noncomputable section
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

private theorem addCircleHomeomorph_zero :
    AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero) 0 = 1 := by
  rw [AddCircle.homeomorphCircle_apply]
  exact AddCircle.toCircle_zero

theorem fundamentalGroupCircleEquivInt_map_addCircle
    (a : FundamentalGroup loopCircle 0) :
    fundamentalGroupCircleEquivInt
      (FundamentalGroup.mapOfEq
        ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
        addCircleHomeomorph_zero a) = fundamentalGroupUnitAddCircleEquivInt a := by
  change fundamentalGroupUnitAddCircleEquivInt
    ((fundamentalGroupMulEquivOfHomotopyEquiv
      (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv 0 1
      addCircleHomeomorph_zero).symm
      ((fundamentalGroupMulEquivOfHomotopyEquiv
        (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv 0 1
        addCircleHomeomorph_zero) a)) = _
  rw [MulEquiv.symm_apply_apply]

def circlePowerMap (k : ℤ) : C(Circle, Circle) :=
  ⟨fun z => z ^ k, continuous_zpow k⟩

@[simp] theorem circlePowerMap_one (k : ℤ) : circlePowerMap k 1 = 1 := one_zpow k

private theorem circlePowerMap_naturality (k : ℤ)
    (a : FundamentalGroup loopCircle 0) :
    FundamentalGroup.mapOfEq (circlePowerMap k) (circlePowerMap_one k)
      (FundamentalGroup.mapOfEq
        ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
        addCircleHomeomorph_zero a) =
    FundamentalGroup.mapOfEq
      ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
      addCircleHomeomorph_zero
      (FundamentalGroup.mapOfEq (unitAddCircleMultiply k) (unitAddCircleMultiply_zero k) a) := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
    simp only [FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change (AddCircle.homeomorphCircle one_ne_zero (p t)) ^ k =
      AddCircle.homeomorphCircle one_ne_zero (k • p t)
    rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
    exact (AddCircle.toCircle_zsmul (p t) k).symm

theorem fundamentalGroupCircleEquivInt_map_power (k : ℤ)
    (a : FundamentalGroup Circle 1) :
    fundamentalGroupCircleEquivInt
      (FundamentalGroup.mapOfEq (circlePowerMap k) (circlePowerMap_one k) a) =
        Multiplicative.ofAdd (k * (fundamentalGroupCircleEquivInt a).toAdd) := by
  let e := fundamentalGroupMulEquivOfHomotopyEquiv
    (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv 0 1 addCircleHomeomorph_zero
  obtain ⟨b, rfl⟩ := e.surjective a
  change fundamentalGroupCircleEquivInt
    (FundamentalGroup.mapOfEq (circlePowerMap k) (circlePowerMap_one k)
      (FundamentalGroup.mapOfEq
        ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
        addCircleHomeomorph_zero b)) =
    Multiplicative.ofAdd (k * (fundamentalGroupCircleEquivInt
      (FundamentalGroup.mapOfEq
        ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
        addCircleHomeomorph_zero b)).toAdd)
  simp only [circlePowerMap_naturality, fundamentalGroupCircleEquivInt_map_addCircle,
    fundamentalGroupUnitAddCircleEquivInt_map_multiply]

end DifferentialGeometry.Topology
