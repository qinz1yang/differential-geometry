import DifferentialGeometry.Topology.FundamentalGroup.TorusMapDegree
import DifferentialGeometry.Topology.FundamentalGroup.TorusHomeomorphMatrix
import DifferentialGeometry.Topology.FundamentalGroup.MarkedMapComposition
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open scoped ContinuousMap Matrix

namespace GC.Topology

private theorem markedMap_constant_path {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) {y : Y} (h : f x = y) :
    markedMap f x ((Path.refl y).cast rfl h) = FundamentalGroup.mapOfEq f h := by
  subst y
  ext a
  change fundamentalGroupChangeBasepoint (Path.refl (f x))
    (FundamentalGroup.map f x a) = FundamentalGroup.mapOfEq f rfl a
  rw [fundamentalGroupChangeBasepoint_refl, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

theorem torusHomeomorphMatrix_matrixDiffeomorph
    (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    torusHomeomorphMatrix (Circle.matrixDiffeomorph A).toHomeomorph = A := by
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let a := torusFundamentalGroup.symm (Multiplicative.ofAdd (v 0), Multiplicative.ofAdd (v 1))
  have hv : ![v 0, v 1] = v := by
    funext i
    fin_cases i <;> rfl
  have ha : ![(torusFundamentalGroup a).1.toAdd, (torusFundamentalGroup a).2.toAdd] = v := by
    simpa only [a, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hv
  let β : Path (1 : Torus) ((Circle.matrixDiffeomorph A) 1) :=
    (Path.refl (1 : Torus)).cast rfl (Circle.matrixContinuousMap_one A.val)
  have h := torusHomeomorphMatrix_mulVec (Circle.matrixDiffeomorph A).toHomeomorph β a
  rw [ha] at h
  change (torusHomeomorphMatrix (Circle.matrixDiffeomorph A).toHomeomorph).val *ᵥ v = _ at h
  have hm : markedMap (Circle.matrixContinuousMap A.val) (1 : Torus) β =
      FundamentalGroup.mapOfEq (Circle.matrixContinuousMap A.val)
        (Circle.matrixContinuousMap_one A.val) :=
    markedMap_constant_path _ _ _
  change (torusHomeomorphMatrix (Circle.matrixDiffeomorph A).toHomeomorph).val *ᵥ v =
    ![(torusFundamentalGroup (markedMap (Circle.matrixContinuousMap A.val) (1 : Torus) β a)).1.toAdd,
      (torusFundamentalGroup (markedMap (Circle.matrixContinuousMap A.val) (1 : Torus) β a)).2.toAdd] at h
  rw [hm, torusFundamentalGroup_map_matrix, ha] at h
  exact h.trans (by
    funext i
    fin_cases i <;> rfl)

end GC.Topology
