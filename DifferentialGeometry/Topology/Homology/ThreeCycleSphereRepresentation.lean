import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeSurjectivity
import DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_three_cycle_eq_sphere_image_add_boundary
    (s : integralSingularCycles 2 (liftedHomotopySphere.{u} 2))
    (hs : IsSphereHomologyGenerator 2
      (integralSingularCycleClass 2 (liftedHomotopySphere.{u} 2) s))
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (z : integralSingularCycles 2 X) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      ∃ b : (integralSingularChains X).X 4,
        z.val = (integralSingularChainMap
          (f.comp (liftedHomotopySphereDown 2))).f 3 s.val +
            (integralSingularChains X).d 4 3 b := by
  obtain ⟨f, hf⟩ := (surjective_sphereHurewicz_iff_forall_exists_map_eq 2 x
    (integralSingularCycleClass 2 (liftedHomotopySphere.{u} 2) s)).mp
      (surjective_sphereHurewicz_three x _ hs) (integralSingularCycleClass 2 X z)
  rw [freeSphereHomologyImage_mk, integralSingularCycleClass_map] at hf
  have hzero : integralSingularCycleClass 2 X
      (z - integralSingularCycleMap 2 (f.comp (liftedHomotopySphereDown 2)) s) = 0 := by
    change integralSingularCycleClassLinearMap 2 X
      (z - integralSingularCycleMap 2 (f.comp (liftedHomotopySphereDown 2)) s) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hf.symm
  obtain ⟨b, hb⟩ := (integralSingularCycleClass_eq_zero_iff 2 X
    (z - integralSingularCycleMap 2 (f.comp (liftedHomotopySphereDown 2)) s)).mp hzero
  refine ⟨f, b, ?_⟩
  have hboundary : (integralSingularChains X).d 4 3 b =
      z.val - (integralSingularChainMap
        (f.comp (liftedHomotopySphereDown 2))).f 3 s.val := congrArg Subtype.val hb
  rw [hboundary]
  abel

theorem exists_three_cycle_eq_simplexBoundarySphereChain_image_add_boundary
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (z : integralSingularCycles 2 X) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      ∃ b : (integralSingularChains X).X 4,
        z.val = (integralSingularChainMap
          (f.comp (liftedHomotopySphereDown 2))).f 3 (simplexBoundarySphereChain.{u} 2) +
            (integralSingularChains X).d 4 3 b :=
  exists_three_cycle_eq_sphere_image_add_boundary
    ⟨simplexBoundarySphereChain 2, simplexBoundarySphereChain_boundary 2⟩
    isSphereHomologyGenerator_simplexBoundarySphereClass_three x z

end DifferentialGeometry.Topology
