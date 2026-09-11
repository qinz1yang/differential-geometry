import DifferentialGeometry.Topology.Homology.PathCones
import DifferentialGeometry.Topology.Homology.Cochains



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]



theorem integralSingularCocycle_one_primitive (a : X) (φ : integralSingularCochain 1 X)
    (hφ : integralSingularCoboundary X 1 2 φ = 0) :
    integralSingularCoboundary X 0 1 (φ.comp (integralSingularConeZero a)) = φ := by
  apply LinearMap.ext
  intro c
  have h := LinearMap.congr_fun (integralSingularConeOne_equation a) c
  change (integralSingularChains X).d 2 1 (integralSingularConeOne a c) =
    c - integralSingularConeZero a ((integralSingularChains X).d 1 0 c) at h
  have hz := LinearMap.congr_fun hφ (integralSingularConeOne a c)
  change φ ((integralSingularChains X).d 2 1 (integralSingularConeOne a c)) = 0 at hz
  rw [h, map_sub, sub_eq_zero] at hz
  exact hz.symm




theorem integralSingularCohomology_one_subsingleton :
    Subsingleton (integralSingularCohomology 1 X) := by
  apply (integralSingularCohomology_one_vanishing_iff X).mpr
  intro φ hφ
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨φ.comp (integralSingularConeZero a), integralSingularCocycle_one_primitive a φ hφ⟩

end DifferentialGeometry.Topology
