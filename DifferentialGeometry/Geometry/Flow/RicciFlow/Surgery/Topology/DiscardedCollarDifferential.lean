import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem discardedCoreCollar_mfderiv_bijective
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b)
    (q : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :
    let : ChartedSpace (EuclideanHalfSpace 1)
        (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
      DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
        (cuttingCollarWidth_pos (G.delta_pos b.1))
    Function.Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel
      (G.discardedCoreCollar b hb) q) := by
  let : ChartedSpace (EuclideanHalfSpace 1)
      (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
    DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
      (cuttingCollarWidth_pos (G.delta_pos b.1))
  let T := (H.event i).transition
  let : ChartedSpace (EuclideanHalfSpace 3) T.trace.tubes.core := T.coreCharts
  let c := G.coreCollar b
  let j := T.trace.capping.coreInclusion
  let p := T.presentation
  have hc : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ c := G.coreCollar_contMDiff b
  have hj : ContMDiff (𝓡∂ 3) ThreeModel ∞ j := T.core_inclusion_smooth.contMDiff
  have hcB : Function.Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) c q) :=
    ((G.coreCollar_isLocalDiffeomorph b q).mfderivToContinuousLinearEquiv (by simp)).bijective
  have hjB : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel j (c q)) :=
    DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      (𝓡∂ 3) ThreeModel j (c q)
      (T.core_inclusion_smooth.isImmersion.isImmersionAt (c q)) (by simp [ThreeSpace])
  have hpB : Function.Bijective (mfderiv ThreeModel ThreeModel p (j (c q))) :=
    (p.mfderivToContinuousLinearEquiv (by simp) (j (c q))).bijective
  have heq : (Sum.inr : (H.event i).discarded.Carrier →
        (H.stage i.succ).Carrier ⊕ (H.event i).discarded.Carrier) ∘ G.discardedCoreCollar b hb =
      p ∘ j ∘ c := by
    funext z
    simp only [Function.comp_apply]
    rw [G.inr_discardedCoreCollar, T.presentation_eq]
  have hB : Function.Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel
      ((Sum.inr : (H.event i).discarded.Carrier →
        (H.stage i.succ).Carrier ⊕ (H.event i).discarded.Carrier) ∘
        G.discardedCoreCollar b hb) q) := by
    rw [heq, mfderiv_comp q (p.contMDiff.mdifferentiable (by simp) _)
      ((hj.comp hc).mdifferentiable (by simp) q),
      mfderiv_comp q (hj.mdifferentiable (by simp) _) (hc.mdifferentiable (by simp) q)]
    exact hpB.comp (hjB.comp hcB)
  rw [mfderiv_comp q ((ContMDiff.inr (n := ∞)).mdifferentiable (by simp) _)
    ((G.discardedCoreCollar_contMDiff b hb).mdifferentiable (by simp) q), mfderiv_sumInr] at hB
  exact hB

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
