import DifferentialGeometry.Geometry.Topology.UniversalCover.DeckAction
import DifferentialGeometry.Geometry.Topology.UniversalCover.Riemannian

set_option autoImplicit false

/-!
# Deck transformations preserve the lifted metric

In the preferred universal-cover charts, every deck transformation is the
identity on model-space coordinates.  Its manifold derivative is therefore the
identity, and the defining pullback formula for `liftedMetric` gives metric
preservation.
-/

open Set Function Manifold
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] in
/-- A deck transformation has identity differential in the preferred
universal-cover tangent coordinates. -/
theorem hasMFDerivAt_deck
    (a : FundamentalGroup M (default : M))
    (p : UniversalCover M) :
    HasMFDerivAt I I (fun q : UniversalCover M => a • q) p
      (ContinuousLinearMap.id ℝ E) := by
  let f : UniversalCover M → UniversalCover M := fun q => a • q
  have hproj : ∀ q, proj (f q) = proj q := fun q => proj_deckAct a q
  refine ⟨(deckAct_contMDiff (I := I) a).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I p f
        =ᶠ[𝓝[range I] (extChartAt I p p)] (id : E → E) := by
    have hmem : (extChartAt I p).target ∈
        𝓝[range I] (extChartAt I p p) :=
      extChartAt_target_mem_nhdsWithin p
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    show extChartAt I (f p) (f ((extChartAt I p).symm y)) = y
    rw [extChartAt_proj_eq (I := I) (M := M),
      hproj p, hproj ((extChartAt I p).symm y),
      ← extChartAt_proj_eq (I := I) (M := M)]
    exact (extChartAt I p).right_inv hy
  have hId : HasFDerivWithinAt (id : E → E)
      (ContinuousLinearMap.id ℝ E) (range I) (extChartAt I p p) :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I p f (extChartAt I p p) =
        (id : E → E) (extChartAt I p p) := by
    show extChartAt I (f p) (f ((extChartAt I p).symm (extChartAt I p p))) =
      extChartAt I p p
    rw [extChartAt_proj_eq (I := I) (M := M),
      hproj p, hproj ((extChartAt I p).symm (extChartAt I p p)),
      ← extChartAt_proj_eq (I := I) (M := M), extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0

/-- Deck transformations preserve the lifted pointwise metric. -/
theorem deck_inner
    (g : SmoothRiemannianMetric I M)
    (a : FundamentalGroup M (default : M))
    (p : UniversalCover M) (v w : TangentSpace I p) :
    (liftedMetric (I := I) g).inner (a • p)
        (mfderiv I I (fun q : UniversalCover M => a • q) p v)
        (mfderiv I I (fun q : UniversalCover M => a • q) p w) =
      (liftedMetric (I := I) g).inner p v w := by
  rw [(hasMFDerivAt_deck (I := I) a p).mfderiv]
  change g.inner (proj (a • p)) v w = g.inner (proj p) v w
  rw [proj_deckAct]

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
