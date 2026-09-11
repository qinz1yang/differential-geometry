import DifferentialGeometry.Topology.Homology.SphereTopHomology



noncomputable section

open ContinuousMap Metric Module
open scoped InnerProductSpace

universe u

namespace DifferentialGeometry.Topology


abbrev liftedSphereSpace (n : ℕ) := ULift.{u} (EuclideanSpace ℝ (Fin (n + 2)))



instance liftedSphereSpace_innerProductSpace (n : ℕ) :
    InnerProductSpace ℝ (liftedSphereSpace.{u} n) where
  inner x y := inner ℝ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r


theorem liftedSphereSpace_finrank (n : ℕ) : finrank ℝ (liftedSphereSpace.{u} n) = n + 2 :=
  (ULift.moduleEquiv : liftedSphereSpace.{u} n ≃ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n + 2))).finrank_eq.trans (by simp)

instance liftedSphereSpace_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (liftedSphereSpace.{u} n) :=
  FiniteDimensional.of_finrank_pos (by rw [liftedSphereSpace_finrank]; omega)


abbrev liftedHomotopySphere (n : ℕ) :=
  ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)



def liftedSphereHomeomorph (n : ℕ) :
    liftedHomotopySphere.{u} n ≃ₜ sphere (0 : liftedSphereSpace.{u} n) 1 where
  toFun x := ⟨ULift.up x.down.val, x.down.property⟩
  invFun x := ULift.up ⟨x.val.down, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((Homeomorph.ulift.symm.continuous).comp
    (continuous_subtype_val.comp Homeomorph.ulift.continuous)).subtype_mk _
  continuous_invFun := Homeomorph.ulift.symm.continuous.comp
    ((Homeomorph.ulift.continuous.comp continuous_subtype_val).subtype_mk _)




def integralLiftedSphereTopEquiv (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) ≃ₗ[ℤ] ℤ :=
  (integralSingularHomologyHomotopyEquiv (n + 1)
    (liftedSphereHomeomorph n).toHomotopyEquiv).trans
      (integralSphereTopHomologyEquiv n (liftedSphereSpace n) (liftedSphereSpace_finrank n))




def integralLiftedSphereGenerator (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) :=
  (integralLiftedSphereTopEquiv n).symm 1


theorem integralLiftedSphereGenerator_coordinate (n : ℕ) :
    integralLiftedSphereTopEquiv n (integralLiftedSphereGenerator.{u} n) = 1 :=
  (integralLiftedSphereTopEquiv n).apply_symm_apply 1

end DifferentialGeometry.Topology
