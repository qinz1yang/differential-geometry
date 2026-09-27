import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeSurjectivity
import DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_two_cycle_eq_sphere_image_add_boundary
    (s : integralSingularCycles 1 (liftedHomotopySphere.{u} 1))
    (hs : IsSphereHomologyGenerator 1
      (integralSingularCycleClass 1 (liftedHomotopySphere.{u} 1) s))
    (z : integralSingularCycles 1 X) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      ∃ b : (integralSingularChains X).X 3,
        z.val = (integralSingularChainMap
          (f.comp (liftedHomotopySphereDown 1))).f 2 s.val +
            (integralSingularChains X).d 3 2 b := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨f, hf⟩ := (surjective_sphereHurewicz_iff_forall_exists_map_eq 1 x
    (integralSingularCycleClass 1 (liftedHomotopySphere.{u} 1) s)).mp
      (surjective_sphereHurewicz_two x _ hs) (integralSingularCycleClass 1 X z)
  rw [freeSphereHomologyImage_mk, integralSingularCycleClass_map] at hf
  have hzero : integralSingularCycleClass 1 X
      (z - integralSingularCycleMap 1 (f.comp (liftedHomotopySphereDown 1)) s) = 0 := by
    change integralSingularCycleClassLinearMap 1 X
      (z - integralSingularCycleMap 1 (f.comp (liftedHomotopySphereDown 1)) s) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hf.symm
  obtain ⟨b, hb⟩ := (integralSingularCycleClass_eq_zero_iff 1 X
    (z - integralSingularCycleMap 1 (f.comp (liftedHomotopySphereDown 1)) s)).mp hzero
  refine ⟨f, b, ?_⟩
  have hboundary : (integralSingularChains X).d 3 2 b =
      z.val - (integralSingularChainMap
        (f.comp (liftedHomotopySphereDown 1))).f 2 s.val := congrArg Subtype.val hb
  rw [hboundary]
  abel

theorem exists_two_cycle_eq_simplexBoundarySphereChain_image_add_boundary
    (z : integralSingularCycles 1 X) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      ∃ b : (integralSingularChains X).X 3,
        z.val = (integralSingularChainMap
          (f.comp (liftedHomotopySphereDown 1))).f 2 (simplexBoundarySphereChain.{u} 1) +
            (integralSingularChains X).d 3 2 b :=
  exists_two_cycle_eq_sphere_image_add_boundary
    ⟨simplexBoundarySphereChain 1, simplexBoundarySphereChain_boundary 1⟩
    isSphereHomologyGenerator_simplexBoundarySphereClass z

end DifferentialGeometry.Topology
