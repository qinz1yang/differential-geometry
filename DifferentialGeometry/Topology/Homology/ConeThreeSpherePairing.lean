import DifferentialGeometry.Topology.Homology.ThreeCycleRealization
import DifferentialGeometry.Topology.Homology.CubeSphereGenerator

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [hpi : Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularConeThreeSphereClass (σ : integralSingularSimplex 3 X) :
    HomotopyGroup (Fin 3) X x :=
  (homotopyGroupFreeSphereEquiv 2 x).symm
    (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ))

def integralSingularConeThreeSpherePairing :
    (integralSingularChains X).X 3 →ₗ[ℤ] Additive (HomotopyGroup (Fin 3) X x) :=
  (integralSingularChainBasis 3 X).constr ℕ
    (fun σ => Additive.ofMul (integralSingularConeThreeSphereClass x σ))

theorem integralSingularConeThreeSpherePairing_simplex (σ : integralSingularSimplex 3 X) :
    integralSingularConeThreeSpherePairing x (integralSimplexChain 3 σ) =
      Additive.ofMul (integralSingularConeThreeSphereClass x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 3 X).constr_basis ℕ _ σ

variable
    (hfaces : ∀ τ : integralSingularSimplex 4 X,
      integralSingularConeThreeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
        integralSingularConeThreeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) *
        integralSingularConeThreeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 4 τ) =
      integralSingularConeThreeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) *
        integralSingularConeThreeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ))

include hfaces

theorem integralSingularConeThreeSpherePairing_boundary (b : (integralSingularChains X).X 4) :
    integralSingularConeThreeSpherePairing x ((integralSingularChains X).d 4 3 b) = 0 := by
  have heq : (integralSingularConeThreeSpherePairing x).comp
      ((integralSingularChains X).d 4 3).hom = 0 := by
    apply (integralSingularChainBasis 4 X).ext
    intro τ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, LinearMap.zero_apply]
    rw [integralSimplexChain_boundary, map_sum]
    simp only [map_zsmul, integralSingularConeThreeSpherePairing_simplex]
    rw [Fin.sum_univ_succ, Fin.sum_univ_four]
    norm_num
    have h := congrArg Additive.ofMul (hfaces τ)
    change Additive.ofMul (integralSingularConeThreeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)) +
      Additive.ofMul (integralSingularConeThreeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)) +
      Additive.ofMul (integralSingularConeThreeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 4 τ)) =
      Additive.ofMul (integralSingularConeThreeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)) +
      Additive.ofMul (integralSingularConeThreeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ)) at h
    have halg {A : Type u} [AddCommGroup A] (a b c d e : A)
        (heq : a + c + e = b + d) : a + (-b + c + -d + e) = 0 := by
      have hz := sub_eq_zero.mpr heq
      convert hz using 1
      abel
    exact halg _ _ _ _ _ h
  exact LinearMap.congr_fun heq b

private theorem integralSingularConeThreeSpherePairing_range_le_ker :
    LinearMap.range (integralSingularBoundaryToCycles 2 X) ≤
      ((integralSingularConeThreeSpherePairing x).comp
        (Submodule.subtype (integralSingularCycles 2 X))).ker := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    integralSingularBoundaryToCycles_coe, integralSingularConeThreeSpherePairing_boundary x hfaces]

def integralSingularConeThreeSphereHomologyPairing :
    integralSingularHomology 3 X →+ Additive (HomotopyGroup (Fin 3) X x) :=
  AddMonoidHom.mk' (fun y =>
    (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 2 X))
      ((integralSingularConeThreeSpherePairing x).comp (integralSingularCycles 2 X).subtype)
      (integralSingularConeThreeSpherePairing_range_le_ker x hfaces))
        ((integralSingularHomologyCycleEquiv 2 X) y)) (by
          intro y₁ y₂
          rw [map_add, map_add])

theorem integralSingularConeThreeSphereHomologyPairing_cycle (z : integralSingularCycles 2 X) :
    integralSingularConeThreeSphereHomologyPairing x hfaces (integralSingularCycleClass 2 X z) =
      integralSingularConeThreeSpherePairing x z.val := by
  change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 2 X))
      ((integralSingularConeThreeSpherePairing x).comp (integralSingularCycles 2 X).subtype)
      (integralSingularConeThreeSpherePairing_range_le_ker x hfaces))
      ((integralSingularHomologyCycleEquiv 2 X) (integralSingularCycleClass 2 X z)) = _
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]

omit hfaces in
theorem sphereHurewicz_integralSingularConeThreeSphereClass (σ : integralSingularSimplex 3 X) :
    sphereHurewicz 2 x (simplexBoundarySphereClass.{u} 2)
      (integralSingularConeThreeSphereClass x σ) =
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) := by
  change freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
    ((homotopyGroupFreeSphereEquiv 2 x) ((homotopyGroupFreeSphereEquiv 2 x).symm
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)))) = _
  rw [Equiv.apply_symm_apply, integralSingularConeThreeSphereMap_simplexBoundarySphereClass]

omit hpi hfaces in
private def sphereHurewiczThreeLinearMap
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) :
    Additive (HomotopyGroup (Fin 3) X x) →ₗ[ℤ] integralSingularHomology 3 X where
  toFun a := sphereHurewicz 2 x c a.toMul
  map_add' a b := sphereHurewicz_three_mul x c a.toMul b.toMul
  map_smul' k a :=
    map_intCast_smul
      (AddMonoidHom.mk' (fun b : Additive (HomotopyGroup (Fin 3) X x) =>
        sphereHurewicz 2 x c b.toMul)
        (fun b d => sphereHurewicz_three_mul x c b.toMul d.toMul)) ℤ ℤ k a

omit hfaces in
private theorem sphereHurewicz_integralSingularConeThreeSpherePairing
    (b : (integralSingularChains X).X 3) :
    sphereHurewicz 2 x (simplexBoundarySphereClass.{u} 2)
      (integralSingularConeThreeSpherePairing x b).toMul =
        integralSingularCycleClass 2 X (integralSingularThreeCycleProjection x b) := by
  have heq : (sphereHurewiczThreeLinearMap x (simplexBoundarySphereClass.{u} 2)).comp
      (integralSingularConeThreeSpherePairing x) =
        (integralSingularCycleClassLinearMap 2 X).comp
          (integralSingularThreeCycleProjection x) := by
    apply (integralSingularChainBasis 3 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply,
      integralSingularConeThreeSpherePairing_simplex, integralSingularCycleClassLinearMap_apply]
    exact sphereHurewicz_integralSingularConeThreeSphereClass x σ
  exact LinearMap.congr_fun heq b

theorem sphereHurewicz_integralSingularConeThreeSphereHomologyPairing
    (y : integralSingularHomology 3 X) :
    sphereHurewicz 2 x (simplexBoundarySphereClass.{u} 2)
      (integralSingularConeThreeSphereHomologyPairing x hfaces y).toMul = y := by
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 2 X y
  rw [integralSingularConeThreeSphereHomologyPairing_cycle,
    sphereHurewicz_integralSingularConeThreeSpherePairing, integralSingularThreeCycleProjection_cycle]

end DifferentialGeometry.Topology
