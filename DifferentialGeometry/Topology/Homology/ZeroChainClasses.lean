import DifferentialGeometry.Topology.Homology.ModuleHomologyMaps
import DifferentialGeometry.Topology.Homology.PathChains



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]


instance integralZeroCycles_module : Module ℤ (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) :=
  (LinearMap.ker ((integralSingularChains X).sc 0).g.hom).module


def integralZeroCycleInclusion : (integralSingularChains X).X 0 →ₗ[ℤ]
    LinearMap.ker ((integralSingularChains X).sc 0).g.hom :=
  (LinearMap.id : (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 0).codRestrict
    (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) (fun c => by
    change (integralSingularChains X).d 0 ((ComplexShape.down ℕ).next 0) c = 0
    rw [ChainComplex.next_nat_zero, (integralSingularChains X).shape 0 0 (by simp)]
    rfl)


def integralZeroChainClass : (integralSingularChains X).X 0 →ₗ[ℤ] integralSingularHomology 0 X :=
  (moduleHomologyClass ((integralSingularChains X).sc 0)).comp integralZeroCycleInclusion


theorem integralZeroChainClass_surjective : Function.Surjective (integralZeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc 0) a
  exact ⟨c.val, hc⟩


theorem integralZeroChainClass_eq_zero_iff (c : (integralSingularChains X).X 0) :
    integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c := by
  have h := moduleHomologyClass_eq_zero_iff ((integralSingularChains X).sc 0) (integralZeroCycleInclusion c)
  change (integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X ((ComplexShape.down ℕ).prev 0),
    (integralSingularChains X).d ((ComplexShape.down ℕ).prev 0) 0 b = c) at h
  exact h.trans (congrArg (fun i => ∃ b : (integralSingularChains X).X i,
    (integralSingularChains X).d i 0 b = c) (ChainComplex.prev ℕ 0)).to_iff


theorem integralZeroChainClass_eq_iff (c d : (integralSingularChains X).X 0) :
    integralZeroChainClass c = integralZeroChainClass d ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c - d := by
  rw [← sub_eq_zero, ← map_sub, integralZeroChainClass_eq_zero_iff]



theorem integralZeroChainClass_map (f : C(X, Y)) (c : (integralSingularChains X).X 0) :
    integralSingularHomologyMap 0 f (integralZeroChainClass c) =
      integralZeroChainClass ((integralSingularChainMap f).f 0 c) :=
  moduleHomologyClass_map
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0).map
      (integralSingularChainMap f)) (integralZeroCycleInclusion c)

end DifferentialGeometry.Topology
