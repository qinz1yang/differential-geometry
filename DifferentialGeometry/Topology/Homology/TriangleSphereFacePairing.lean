import DifferentialGeometry.Topology.Homology.TriangleSphereHomologyInverse
import DifferentialGeometry.Topology.Homology.SphereFaceChains
import DifferentialGeometry.Topology.Homology.SphereConeNormalization

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularTriangleSphereHomologyPairing_freeSphereHomologyImage
    (x : X) (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) :
    integralSingularTriangleSphereHomologyPairing x
      (freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1) (ZerothHomotopy.mk f)) =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
          Additive.ofMul (integralSingularTriangleSphereClass x (integralSingularSphereFace f i)) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass, integralSingularCycleClass_map,
    integralSingularTriangleSphereHomologyPairing_cycle, integralSingularCycleMap_val,
    integralSingularChainMap_simplexBoundarySphereChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSingularTriangleSpherePairing_simplex]

theorem integralSingularTriangleSphereHomologyPairing_sphereHurewicz_mk
    (x : X) (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) :
    integralSingularTriangleSphereHomologyPairing x
      (sphereHurewicz 1 x triangleSphereFundamentalClass
        ((homotopyGroupFreeSphereEquiv 1 x).symm (ZerothHomotopy.mk f))) =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • Additive.ofMul
        (integralSingularTriangleSphereClass x
          (integralSingularSphereFace (f.comp Simplex.triangleSphereCollapse) i)) := by
  rw [triangleSphereFundamentalClass, sphereHurewicz_precompose]
  change integralSingularTriangleSphereHomologyPairing x
    (freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1)
      ((homotopyGroupFreeSphereEquiv 1 x)
        ((homotopyGroupFreeSphereEquiv 1 x).symm
          (freeSpherePrecompose 1 Simplex.triangleSphereCollapse
            ((homotopyGroupFreeSphereEquiv 1 x)
              ((homotopyGroupFreeSphereEquiv 1 x).symm (ZerothHomotopy.mk f))))))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, freeSpherePrecompose_mk,
    integralSingularTriangleSphereHomologyPairing_freeSphereHomologyImage]

theorem integralSingularTriangleSphereHomologyPairing_terminal_faces
    (x : X) (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X))
    (g : Fin 4 → C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ i, ∀ p ∈ Simplex.boundary (Fin 3), g i p = x)
    (hcones : ∀ i, (integralSingularConeSphereMap x (integralSingularSphereFace f i)).Homotopic
      (Simplex.triangleSphereMap (g i) x (hg i))) :
    integralSingularTriangleSphereHomologyPairing x
      (freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1) (ZerothHomotopy.mk f)) =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
          (Additive.ofMul ⟦Simplex.triangleGenLoop (g i) x (hg i)⟧ :
            Additive (HomotopyGroup (Fin 2) X x)) := by
  rw [integralSingularTriangleSphereHomologyPairing_freeSphereHomologyImage]
  apply Finset.sum_congr rfl
  intro i _
  rw [integralSingularTriangleSphereClass_eq_triangleGenLoop x _ (g i) (hg i) (hcones i)]

end DifferentialGeometry.Topology
