import DifferentialGeometry.Topology.Homology.Relative.Basic



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology


abbrev integralSingularCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom



instance integralSingularCycles_module (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module ℤ (integralSingularCycles n X) :=
  (LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom).module


def integralSingularBoundaryToCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X (n + 2) →ₗ[ℤ] integralSingularCycles n X :=
  ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatToCycles



def integralSingularHomologyCycleEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≃+
      (integralSingularCycles n X ⧸ LinearMap.range (integralSingularBoundaryToCycles n X)) :=
  (ShortComplex.homologyMapIso ((integralSingularChains X).isoSc'
      (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv




theorem integralSingularHomology_vanishing_iff (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Subsingleton (integralSingularHomology (n + 1) X) ↔
      ∀ c : (integralSingularChains X).X (n + 1),
        (integralSingularChains X).d (n + 1) n c = 0 →
          ∃ b : (integralSingularChains X).X (n + 2),
            (integralSingularChains X).d (n + 2) (n + 1) b = c := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

end DifferentialGeometry.Topology
