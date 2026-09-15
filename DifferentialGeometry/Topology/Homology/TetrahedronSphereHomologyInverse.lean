import DifferentialGeometry.Topology.Homology.TetrahedronSphereHomologyPairing
import DifferentialGeometry.Topology.Homology.TetrahedronSphereHurewicz

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
variable [Subsingleton (HomotopyGroup (Fin 2) X x)]

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

private theorem sphereHurewicz_integralSingularTetrahedronSpherePairing
    (b : (integralSingularChains X).X 3) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (integralSingularTetrahedronSpherePairing x b).toMul =
        integralSingularCycleClass 2 X (integralSingularThreeCycleProjection x b) := by
  have heq : (sphereHurewiczThreeLinearMap x tetrahedronSphereFundamentalClass).comp
      (integralSingularTetrahedronSpherePairing x) =
        (integralSingularCycleClassLinearMap 2 X).comp
          (integralSingularThreeCycleProjection x) := by
    apply (integralSingularChainBasis 3 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply,
      integralSingularTetrahedronSpherePairing_simplex, integralSingularCycleClassLinearMap_apply]
    exact sphereHurewicz_integralSingularTetrahedronSphereClass x σ
  exact LinearMap.congr_fun heq b

theorem sphereHurewicz_integralSingularTetrahedronSphereHomologyPairing
    (y : integralSingularHomology 3 X) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (integralSingularTetrahedronSphereHomologyPairing x y).toMul = y := by
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 2 X y
  rw [integralSingularTetrahedronSphereHomologyPairing_cycle,
    sphereHurewicz_integralSingularTetrahedronSpherePairing, integralSingularThreeCycleProjection_cycle]


end DifferentialGeometry.Topology
