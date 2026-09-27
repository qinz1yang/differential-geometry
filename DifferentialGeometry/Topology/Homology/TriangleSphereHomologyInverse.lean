import DifferentialGeometry.Topology.Homology.TriangleSphereHomologyPairing
import DifferentialGeometry.Topology.Homology.TriangleSphereHurewicz

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)

private def sphereHurewiczTwoLinearMap
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1)) :
    Additive (HomotopyGroup (Fin 2) X x) →ₗ[ℤ] integralSingularHomology 2 X where
  toFun a := sphereHurewicz 1 x c a.toMul
  map_add' a b := sphereHurewicz_two_mul x c a.toMul b.toMul
  map_smul' k a :=
    map_intCast_smul
      (AddMonoidHom.mk' (fun b : Additive (HomotopyGroup (Fin 2) X x) =>
        sphereHurewicz 1 x c b.toMul)
        (fun b d => sphereHurewicz_two_mul x c b.toMul d.toMul)) ℤ ℤ k a

private theorem sphereHurewicz_integralSingularTriangleSpherePairing
    (b : (integralSingularChains X).X 2) :
    sphereHurewicz 1 x triangleSphereFundamentalClass
      (integralSingularTriangleSpherePairing x b).toMul =
        integralSingularCycleClass 1 X (integralSingularTwoCycleProjection x b) := by
  have heq : (sphereHurewiczTwoLinearMap x triangleSphereFundamentalClass).comp
      (integralSingularTriangleSpherePairing x) =
        (integralSingularCycleClassLinearMap 1 X).comp
          (integralSingularTwoCycleProjection x) := by
    apply (integralSingularChainBasis 2 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply,
      integralSingularTriangleSpherePairing_simplex, integralSingularCycleClassLinearMap_apply]
    exact sphereHurewicz_integralSingularTriangleSphereClass x σ
  exact LinearMap.congr_fun heq b

theorem sphereHurewicz_integralSingularTriangleSphereHomologyPairing
    (y : integralSingularHomology 2 X) :
    sphereHurewicz 1 x triangleSphereFundamentalClass
      (integralSingularTriangleSphereHomologyPairing x y).toMul = y := by
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 1 X y
  rw [integralSingularTriangleSphereHomologyPairing_cycle,
    sphereHurewicz_integralSingularTriangleSpherePairing, integralSingularTwoCycleProjection_cycle]


end DifferentialGeometry.Topology
