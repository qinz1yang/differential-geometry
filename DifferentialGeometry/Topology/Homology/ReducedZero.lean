import DifferentialGeometry.Topology.Homology.ZeroAugmentation
import DifferentialGeometry.Topology.Homology.Homotopy
import Mathlib.Algebra.Module.Submodule.Equiv



noncomputable section

open CategoryTheory ContinuousMap

universe u

namespace DifferentialGeometry.Topology


abbrev integralReducedHomologyZero (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker (integralZeroAugmentation (X := X))

instance integralReducedHomologyZero_module (X : Type u) [TopologicalSpace X] :
    Module ℤ (integralReducedHomologyZero X) := (integralReducedHomologyZero X).module

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

instance integralZeroMapKernel_module (f : C(X, Y)) :
    Module ℤ (LinearMap.ker (integralSingularHomologyMap 0 f)) :=
  (LinearMap.ker (integralSingularHomologyMap 0 f)).module



theorem integralZeroMap_kernel_eq_reduced [PathConnectedSpace Y] (f : C(X, Y)) :
    LinearMap.ker (integralSingularHomologyMap 0 f) = integralReducedHomologyZero X := by
  have h := (integralConnectedZeroAugmentationEquiv (X := Y)).ker_comp
    (integralSingularHomologyMap 0 f)
  rw [integralConnectedZeroAugmentationEquiv_toLinearMap, integralZeroAugmentation_natural] at h
  exact h.symm


def integralZeroMapKernelReducedEquiv [PathConnectedSpace Y] (f : C(X, Y)) :
    LinearMap.ker (integralSingularHomologyMap 0 f) ≃ₗ[ℤ] integralReducedHomologyZero X :=
  LinearEquiv.ofEq _ _ (integralZeroMap_kernel_eq_reduced f)



def integralReducedZeroHomotopyEquiv (e : X ≃ₕ Y) :
    integralReducedHomologyZero X ≃ₗ[ℤ] integralReducedHomologyZero Y := by
  let h := integralSingularHomologyHomotopyEquiv 0 e
  have he : integralReducedHomologyZero X =
      (integralReducedHomologyZero Y).comap h.toLinearMap := by
    ext a
    change integralZeroAugmentation a = 0 ↔
      integralZeroAugmentation (integralSingularHomologyMap 0 e.toFun a) = 0
    have ha := LinearMap.congr_fun (integralZeroAugmentation_natural e.toFun) a
    exact (congrArg (fun b : ℤ => b = 0) ha.symm).to_iff
  exact (LinearEquiv.ofEq _ _ he).trans (h.ofSubmodule' (integralReducedHomologyZero Y))


theorem integralReducedZero_subsingleton [PathConnectedSpace X] :
    Subsingleton (integralReducedHomologyZero X) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  apply (integralConnectedZeroAugmentationEquiv (X := X)).injective
  exact a.property.trans b.property.symm

end DifferentialGeometry.Topology
