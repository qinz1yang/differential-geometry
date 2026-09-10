import DifferentialGeometry.Geometry.Comparison.Soul.Euclidean
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic

noncomputable section
open Manifold Topology
open scoped ContDiff

namespace Poincare.Geometry

open DifferentialGeometry

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SigmaCompactSpace M]
  [ConnectedSpace M] [NoncompactSpace M]
  {g : SmoothRiemannianMetric (𝓡 3) M}

theorem exists_euclidean_cover_of_cheegerGromoll
    (hCG : cheegerGromollSoulTheorem g)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : HasPositiveSectionalCurvature g) :
    (∃ p : EuclideanSpace ℝ (Fin 3) → M,
      IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∧
      ∀ x : M, Finite (FundamentalGroup M x) := by
  obtain ⟨d⟩ := diffeomorphic_euclidean_three_of_cheegerGromoll
    hCG hcomplete hsec (by simp)
  let _ : SimplyConnectedSpace M := d.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  have hp : IsCoveringMap (d.symm : EuclideanSpace ℝ (Fin 3) → M) := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    apply d.symm.toHomeomorph.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    · intro x _
      exact (Set.finite_singleton x).preimage d.symm.injective.injOn
    · exact d.symm.toHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn
  exact ⟨⟨d.symm, hp, d.symm.surjective, d.symm.isLocalDiffeomorph⟩,
    fun _ ↦ inferInstance⟩

end Poincare.Geometry
