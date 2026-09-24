import DifferentialGeometry.Topology.Homology.TriangleSphereRelation

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularTriangleSpherePairing (x : X) :
    (integralSingularChains X).X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  (integralSingularChainBasis 2 X).constr ℕ
    (fun σ => Additive.ofMul (integralSingularTriangleSphereClass x σ))

theorem integralSingularTriangleSpherePairing_simplex (x : X) (σ : integralSingularSimplex 2 X) :
    integralSingularTriangleSpherePairing x (integralSimplexChain 2 σ) =
      Additive.ofMul (integralSingularTriangleSphereClass x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 2 X).constr_basis ℕ _ σ

variable (x : X)

theorem integralSingularTriangleSpherePairing_boundary (b : (integralSingularChains X).X 3) :
    integralSingularTriangleSpherePairing x ((integralSingularChains X).d 3 2 b) = 0 := by
  have heq : (integralSingularTriangleSpherePairing x).comp
      ((integralSingularChains X).d 3 2).hom = 0 := by
    apply (integralSingularChainBasis 3 X).ext
    intro τ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, LinearMap.zero_apply]
    rw [integralSimplexChain_boundary, map_sum]
    simp only [map_zsmul, integralSingularTriangleSpherePairing_simplex]
    rw [Fin.sum_univ_four]
    norm_num
    have h := congrArg Additive.ofMul (integralSingularTriangleSphereClass_face_relation x τ)
    change Additive.ofMul (integralSingularTriangleSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)) +
      Additive.ofMul (integralSingularTriangleSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)) =
      Additive.ofMul (integralSingularTriangleSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)) +
      Additive.ofMul (integralSingularTriangleSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ)) at h
    have hz := sub_eq_zero.mpr h
    convert hz using 1
    abel
  exact LinearMap.congr_fun heq b

private theorem integralSingularTriangleSpherePairing_range_le_ker :
    LinearMap.range (integralSingularBoundaryToCycles 1 X) ≤
      ((integralSingularTriangleSpherePairing x).comp
        (Submodule.subtype (integralSingularCycles 1 X))).ker := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    integralSingularBoundaryToCycles_coe, integralSingularTriangleSpherePairing_boundary x]

def integralSingularTriangleSphereHomologyPairing :
    integralSingularHomology 2 X →+ Additive (HomotopyGroup (Fin 2) X x) :=
  AddMonoidHom.mk' (fun y =>
    (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 1 X))
      ((integralSingularTriangleSpherePairing x).comp (integralSingularCycles 1 X).subtype)
      (integralSingularTriangleSpherePairing_range_le_ker x))
        ((integralSingularHomologyCycleEquiv 1 X) y)) (by
          intro y₁ y₂
          rw [map_add, map_add])

theorem integralSingularTriangleSphereHomologyPairing_cycle (z : integralSingularCycles 1 X) :
    integralSingularTriangleSphereHomologyPairing x (integralSingularCycleClass 1 X z) =
      integralSingularTriangleSpherePairing x z.val := by
  change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 1 X))
      ((integralSingularTriangleSpherePairing x).comp (integralSingularCycles 1 X).subtype)
      (integralSingularTriangleSpherePairing_range_le_ker x))
      ((integralSingularHomologyCycleEquiv 1 X) (integralSingularCycleClass 1 X z)) = _
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]

end DifferentialGeometry.Topology
