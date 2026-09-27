import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckContractReduction

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem cylinderAxialReflectionShift_trans_apply (c d : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d) y =
      cylinderAxialShift (d - c) y := by
  rw [PartialDiffeomorph.trans_apply, cylinderAxialReflectionShift_apply,
    cylinderAxialReflectionShift_apply]
  change (y.1, d - (c - y.2)) = (y.1, y.2 + (d - c))
  exact Prod.ext rfl (by ring)

theorem cylinderAxialReflectionShift_trans_self_apply (c : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift c) y = y := by
  rw [cylinderAxialReflectionShift_trans_apply]
  change (y.1, y.2 + (c - c)) = (y.1, y.2)
  exact Prod.ext rfl (by ring)

theorem cylinderAxialReflectionShift_trans_apply_fst (c d : ℝ) (y : Cylinder) :
    ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d) y).1 = y.1 := by
  rw [cylinderAxialReflectionShift_trans_apply]
  rfl

theorem cylinderAxialReflectionShift_target (c : ℝ) :
    (cylinderAxialReflectionShift c).target = Set.univ := by
  ext y
  simp [cylinderAxialReflectionShift, cylinderAxialShift, cylinderAxialReflection]

theorem cylinderAxialReflectionShift_trans_target (c d : ℝ) :
    ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d)).target =
      Set.univ := by
  rw [PartialDiffeomorph.trans_target, cylinderAxialReflectionShift_target,
    cylinderAxialReflectionShift_target]
  simp

theorem CylinderFiberPreserving.symm_of_apply_fst {Θ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}
    (hfst : ∀ z : Cylinder, (Θ z).1 = z.1) (htgt : ∀ y : Cylinder, y ∈ Θ.target) :
    CylinderFiberPreserving Θ.symm := by
  intro y a
  have h1 : (Θ.symm y).1 = y.1 := by
    have h := congrArg Prod.fst (Θ.right_inv' (htgt y))
    rwa [hfst] at h
  have h2 : (Θ.symm (y.1, a)).1 = y.1 := by
    have h := congrArg Prod.fst (Θ.right_inv' (htgt (y.1, a)))
    rwa [hfst] at h
  rw [h2, h1]

theorem cylinderAxialReflectionShift_trans_fiberPreserving (c d : ℝ) :
    CylinderFiberPreserving
      ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d)) :=
  CylinderFiberPreserving.trans (cylinderAxialReflectionShift_fiberPreserving c)
    (cylinderAxialReflectionShift_fiberPreserving d)

theorem cylinderAxialReflectionShift_trans_symm_fiberPreserving (c d : ℝ) :
    CylinderFiberPreserving
      ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d)).symm :=
  CylinderFiberPreserving.symm_of_apply_fst
    (cylinderAxialReflectionShift_trans_apply_fst c d)
    (fun y => by rw [cylinderAxialReflectionShift_trans_target]; exact Set.mem_univ y)

theorem cylinderAxialReflectionShift_trans_axial_fderiv (c d : ℝ) (y : Cylinder) :
    fderiv ℝ (fun a : ℝ =>
        (((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d))
          (y.1, a)).2) y.2 1 = 1 := by
  have hfun : (fun a : ℝ =>
        (((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d))
          (y.1, a)).2) = fun a : ℝ => a + (d - c) := by
    funext a
    rw [cylinderAxialReflectionShift_trans_apply]
    rfl
  rw [hfun]
  simp

theorem cylinderAxialReflectionShift_trans_coOriented (c d : ℝ) :
    CylinderCoOriented
      ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d)) :=
  ⟨cylinderAxialReflectionShift_trans_fiberPreserving c d,
    cylinderAxialReflectionShift_trans_symm_fiberPreserving c d,
    fun y _ => by
      rw [cylinderAxialReflectionShift_trans_axial_fderiv c d y]
      norm_num⟩

theorem CylinderCoOriented.trans_reflectionShift_trans {Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}
    (hΨ : CylinderCoOriented Ψ) (c d : ℝ) :
    CylinderCoOriented
      (Ψ.trans ((cylinderAxialReflectionShift c).trans (cylinderAxialReflectionShift d))) :=
  hΨ.trans (cylinderAxialReflectionShift_trans_coOriented c d)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
