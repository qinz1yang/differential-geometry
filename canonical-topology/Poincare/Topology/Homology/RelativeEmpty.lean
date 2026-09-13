import Poincare.Topology.Homology.SimplexBasis
import Poincare.Topology.Homology.RelativeMaps

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace Poincare.Topology

private theorem integralSingularChainMap_empty_eq_zero
    (X : Type u) [TopologicalSpace X] :
    integralSingularChainMap (singularSubspaceInclusion (∅ : Set X)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hc : c = 0 := by
    apply (integralSingularChainRepr n (∅ : Set X)).injective
    ext σ
    exact ((integralSingularSimplexEquiv n (∅ : Set X) σ)
      ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex ℝ 0⟩).2.elim
  subst c
  exact map_zero _

private theorem integralAbsoluteToRelative_empty_bijective
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (integralAbsoluteToRelative n (∅ : Set X)) := by
  let π := (integralRelativeChainSequence (∅ : Set X)).g
  have hπ : IsIso π := by
    change IsIso (cokernel.π (integralSingularChainMap (singularSubspaceInclusion (∅ : Set X))))
    rw [integralSingularChainMap_empty_eq_zero]
    infer_instance
  have hi : IsIso (HomologicalComplex.homologyMap π n) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

def integralAbsoluteToRelativeEmptyEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology n X ≃ₗ[ℤ] integralRelativeHomology n (∅ : Set X) :=
  LinearEquiv.ofBijective (integralAbsoluteToRelative n (∅ : Set X))
    (integralAbsoluteToRelative_empty_bijective X n)

theorem integralAbsoluteToRelativeEmptyEquiv_toLinearMap
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralAbsoluteToRelativeEmptyEquiv n X).toLinearMap =
      integralAbsoluteToRelative n (∅ : Set X) := rfl

end Poincare.Topology

end
