import DifferentialGeometry.Topology.Homology.CochainMaps

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def integralSingularCohomologyEquivOfHomeomorph (e : X ≃ₜ Y) (n : ℕ) :
    integralSingularCohomology n X ≃ₗ[ℤ] integralSingularCohomology n Y where
  toFun := ⇑(integralSingularCohomologyMap n (e.symm : C(Y, X)))
  invFun := ⇑(integralSingularCohomologyMap n (e : C(X, Y)))
  map_add' := (integralSingularCohomologyMap n (e.symm : C(Y, X))).map_add
  map_smul' := (integralSingularCohomologyMap n (e.symm : C(Y, X))).map_smul
  left_inv a := by
    have hcomp : (integralSingularCohomologyMap n (e : C(X, Y))).comp
        (integralSingularCohomologyMap n (e.symm : C(Y, X))) = LinearMap.id := by
      have h : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X :=
        ContinuousMap.ext fun x => e.left_inv x
      calc
        (integralSingularCohomologyMap n (e : C(X, Y))).comp
            (integralSingularCohomologyMap n (e.symm : C(Y, X)))
            = integralSingularCohomologyMap n ((e.symm : C(Y, X)).comp (e : C(X, Y))) :=
              (integralSingularCohomologyMap_comp n (e : C(X, Y)) (e.symm : C(Y, X))).symm
        _ = integralSingularCohomologyMap n (ContinuousMap.id X) := by rw [h]
        _ = LinearMap.id := integralSingularCohomologyMap_id n
    exact LinearMap.congr_fun hcomp a
  right_inv a := by
    have hcomp : (integralSingularCohomologyMap n (e.symm : C(Y, X))).comp
        (integralSingularCohomologyMap n (e : C(X, Y))) = LinearMap.id := by
      have h : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y :=
        ContinuousMap.ext fun y => e.right_inv y
      calc
        (integralSingularCohomologyMap n (e.symm : C(Y, X))).comp
            (integralSingularCohomologyMap n (e : C(X, Y)))
            = integralSingularCohomologyMap n ((e : C(X, Y)).comp (e.symm : C(Y, X))) :=
              (integralSingularCohomologyMap_comp n (e.symm : C(Y, X)) (e : C(X, Y))).symm
        _ = integralSingularCohomologyMap n (ContinuousMap.id Y) := by rw [h]
        _ = LinearMap.id := integralSingularCohomologyMap_id n
    exact LinearMap.congr_fun hcomp a

theorem subsingleton_integralSingularCohomology_of_homeomorph (e : X ≃ₜ Y) (n : ℕ)
    [Subsingleton (integralSingularCohomology n X)] :
    Subsingleton (integralSingularCohomology n Y) :=
  (integralSingularCohomologyEquivOfHomeomorph e n).surjective.subsingleton

end DifferentialGeometry.Topology
