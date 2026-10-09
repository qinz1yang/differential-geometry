import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open scoped ContinuousMap Matrix

namespace GC.Topology

private def torusVectorEquiv :
    FundamentalGroup Torus (1, 1) ≃* Multiplicative (Fin 2 → ℤ) :=
  (torusFundamentalGroup.trans (MulEquiv.prodMultiplicative ℤ ℤ).symm).trans
    (LinearEquiv.finTwoArrow ℤ ℤ).toAddEquiv.toMultiplicative.symm

private theorem torusVectorEquiv_apply (a : FundamentalGroup Torus (1, 1)) :
    (torusVectorEquiv a).toAdd =
      ![(torusFundamentalGroup a).1.toAdd, (torusFundamentalGroup a).2.toAdd] := rfl

private def torusMarkedHomeomorph (e : Torus ≃ₜ Torus)
    (β : Path (1, 1) (e (1, 1))) :
    FundamentalGroup Torus (1, 1) ≃* FundamentalGroup Torus (1, 1) :=
  (fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv (1, 1) (e (1, 1)) rfl).trans
    (fundamentalGroupChangeBasepoint β)

private theorem torusMarkedHomeomorph_apply (e : Torus ≃ₜ Torus)
    (β : Path (1, 1) (e (1, 1))) (a : FundamentalGroup Torus (1, 1)) :
    torusMarkedHomeomorph e β a = markedMap (e : C(Torus, Torus)) (1, 1) β a := by
  change fundamentalGroupChangeBasepoint β
    (FundamentalGroup.mapOfEq (e : C(Torus, Torus)) rfl a) =
      fundamentalGroupChangeBasepoint β (FundamentalGroup.map (e : C(Torus, Torus)) (1, 1) a)
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

private theorem torusMarkedHomeomorph_path_independent (e : Torus ≃ₜ Torus)
    (β γ : Path (1, 1) (e (1, 1))) :
    torusMarkedHomeomorph e β = torusMarkedHomeomorph e γ := by
  ext a
  apply torusFundamentalGroup.injective
  rw [torusMarkedHomeomorph_apply, torusMarkedHomeomorph_apply]
  change torusFundamentalGroup (fundamentalGroupChangeBasepoint β _) =
    torusFundamentalGroup (fundamentalGroupChangeBasepoint γ _)
  rw [fundamentalGroupChangeBasepoint_connector β γ, MulAut.conj_apply,
    map_mul, map_mul, map_inv]
  simp [mul_comm]

private def torusHomeomorphLinear (e : Torus ≃ₜ Torus)
    (β : Path (1, 1) (e (1, 1))) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (AddEquiv.toMultiplicative.symm
    ((torusVectorEquiv.symm.trans (torusMarkedHomeomorph e β)).trans
      torusVectorEquiv)).toIntLinearEquiv

def torusHomeomorphMatrix (e : Torus ≃ₜ Torus) : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (torusHomeomorphLinear e (PathConnectedSpace.somePath (1, 1) (e (1, 1)))))

theorem torusHomeomorphMatrix_mulVec (e : Torus ≃ₜ Torus)
    (β : Path (1, 1) (e (1, 1))) (a : FundamentalGroup Torus (1, 1)) :
    (torusHomeomorphMatrix e).val *ᵥ
      ![(torusFundamentalGroup a).1.toAdd, (torusFundamentalGroup a).2.toAdd] =
      ![(torusFundamentalGroup (markedMap (e : C(Torus, Torus)) (1, 1) β a)).1.toAdd,
        (torusFundamentalGroup (markedMap (e : C(Torus, Torus)) (1, 1) β a)).2.toAdd] := by
  rw [← torusVectorEquiv_apply]
  change (Matrix.GeneralLinearGroup.toLin (torusHomeomorphMatrix e) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) ((torusVectorEquiv a).toAdd) = _
  rw [torusHomeomorphMatrix, MulEquiv.apply_symm_apply]
  change (torusVectorEquiv
    (torusMarkedHomeomorph e (PathConnectedSpace.somePath (1, 1) (e (1, 1)))
      (torusVectorEquiv.symm (torusVectorEquiv a)))).toAdd = _
  rw [MulEquiv.symm_apply_apply,
    torusMarkedHomeomorph_path_independent e _ β,
    torusMarkedHomeomorph_apply, torusVectorEquiv_apply]

end GC.Topology
