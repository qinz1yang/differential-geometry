import DifferentialGeometry.Topology.Homology.TetrahedronSphereRelation

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularTetrahedronSpherePairing :
    (integralSingularChains X).X 3 →ₗ[ℤ] Additive (HomotopyGroup (Fin 3) X x) :=
  (integralSingularChainBasis 3 X).constr ℕ
    (fun σ => Additive.ofMul (integralSingularTetrahedronSphereClass x σ))

theorem integralSingularTetrahedronSpherePairing_simplex (σ : integralSingularSimplex 3 X) :
    integralSingularTetrahedronSpherePairing x (integralSimplexChain 3 σ) =
      Additive.ofMul (integralSingularTetrahedronSphereClass x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 3 X).constr_basis ℕ _ σ

theorem integralSingularTetrahedronSpherePairing_boundary (b : (integralSingularChains X).X 4) :
    integralSingularTetrahedronSpherePairing x ((integralSingularChains X).d 4 3 b) = 0 := by
  have heq : (integralSingularTetrahedronSpherePairing x).comp
      ((integralSingularChains X).d 4 3).hom = 0 := by
    apply (integralSingularChainBasis 4 X).ext
    intro τ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, LinearMap.zero_apply]
    rw [integralSimplexChain_boundary, map_sum]
    simp only [map_zsmul, integralSingularTetrahedronSpherePairing_simplex]
    rw [Fin.sum_univ_succ, Fin.sum_univ_four]
    norm_num
    have h := congrArg Additive.ofMul (integralSingularTetrahedronSphereClass_face_relation x τ)
    change Additive.ofMul (integralSingularTetrahedronSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)) +
      Additive.ofMul (integralSingularTetrahedronSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)) +
      Additive.ofMul (integralSingularTetrahedronSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 4 τ)) =
      Additive.ofMul (integralSingularTetrahedronSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)) +
      Additive.ofMul (integralSingularTetrahedronSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ)) at h
    have halg {A : Type u} [AddCommGroup A] (a b c d e : A)
        (heq : a + c + e = b + d) : a + (-b + c + -d + e) = 0 := by
      have hz := sub_eq_zero.mpr heq
      convert hz using 1
      abel
    exact halg _ _ _ _ _ h
  exact LinearMap.congr_fun heq b

private theorem integralSingularTetrahedronSpherePairing_range_le_ker :
    LinearMap.range (integralSingularBoundaryToCycles 2 X) ≤
      ((integralSingularTetrahedronSpherePairing x).comp
        (Submodule.subtype (integralSingularCycles 2 X))).ker := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    integralSingularBoundaryToCycles_coe, integralSingularTetrahedronSpherePairing_boundary x]

def integralSingularTetrahedronSphereHomologyPairing :
    integralSingularHomology 3 X →+ Additive (HomotopyGroup (Fin 3) X x) :=
  AddMonoidHom.mk' (fun y =>
    (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 2 X))
      ((integralSingularTetrahedronSpherePairing x).comp (integralSingularCycles 2 X).subtype)
      (integralSingularTetrahedronSpherePairing_range_le_ker x))
        ((integralSingularHomologyCycleEquiv 2 X) y)) (by
          intro y₁ y₂
          rw [map_add, map_add])

theorem integralSingularTetrahedronSphereHomologyPairing_cycle (z : integralSingularCycles 2 X) :
    integralSingularTetrahedronSphereHomologyPairing x (integralSingularCycleClass 2 X z) =
      integralSingularTetrahedronSpherePairing x z.val := by
  change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 2 X))
      ((integralSingularTetrahedronSpherePairing x).comp (integralSingularCycles 2 X).subtype)
      (integralSingularTetrahedronSpherePairing_range_le_ker x))
      ((integralSingularHomologyCycleEquiv 2 X) (integralSingularCycleClass 2 X z)) = _
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]

end DifferentialGeometry.Topology
