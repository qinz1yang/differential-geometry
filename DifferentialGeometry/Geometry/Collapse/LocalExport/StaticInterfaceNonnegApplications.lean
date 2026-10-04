import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterfaceNonneg
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# Consumers of the LC90 nonnegative discharge: late cut families

* `GC.LongTime.LateCutFamily.exists_late_hyperbolicOrGraph_or_closedGeometric`: LC90's
  componentwise composition for the tree's late cut families with the static theorem as the ONLY
  explicit input: the common `A` (LC89) first, then `w₀` by the static theorem at `(K, A)`, then the
  late index `N`; every piece of every component of every late slice is hyperbolic or carries a raw
  graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean geometric structure.
* `GC.LongTime.LateCutFamily.exists_late_hyperbolicOrGraph_of_boundary_nonempty`: on the same tail,
  every late piece with nonempty boundary is hyperbolic or a raw graph.
No flow producer is used or proved.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime

universe u

/-- LC90 for a late cut family, with only the static theorem at order `K` as explicit input: in
the order `A` (LC89) → `w₀` (static theorem) → late index `N`, every late piece is hyperbolic or
carries a raw graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean geometric
structure. -/
theorem LateCutFamily.exists_late_hyperbolicOrGraph_or_closedGeometric
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ (C : ConnectedComponents (slices j).stage.Carrier)
        (i : Fin (L.decomposition j C).components.count),
        Nonempty (HyperbolicOrGraph (L.decomposition j C).carrier
          (L.decomposition j C).components i) ∨
        (((L.decomposition j C).component i).model.boundary
            ((L.decomposition j C).component i).Carrier = ∅ ∧
          ∃ G : GC.Geometry.GeometricStructure ((L.decomposition j C).component i).model
              ((L.decomposition j C).component i).Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds h
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A hA
  obtain ⟨N, hN⟩ := htests w₀ hw₀ hwc
  refine ⟨w₀, hw₀, hwc, N, fun j hj C i => ?_⟩
  obtain ⟨pieces⟩ := hN j hj C
  exact (pieces i).hyperbolicOrGraph_or_closedGeometric hstatic

/-- On the same late tail, every late piece with nonempty boundary is hyperbolic or carries a raw
graph presentation, with only the static theorem as explicit input. -/
theorem LateCutFamily.exists_late_hyperbolicOrGraph_of_boundary_nonempty
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ (C : ConnectedComponents (slices j).stage.Carrier)
        (i : Fin (L.decomposition j C).components.count),
        (((L.decomposition j C).component i).model.boundary
            ((L.decomposition j C).component i).Carrier).Nonempty →
        Nonempty (HyperbolicOrGraph (L.decomposition j C).carrier
          (L.decomposition j C).components i) := by
  obtain ⟨w₀, hw₀, hwc, N, hN⟩ := L.exists_late_hyperbolicOrGraph_or_closedGeometric h static
  exact ⟨w₀, hw₀, hwc, N, fun j hj C i hbd =>
    (hN j hj C i).resolve_right fun hc => hbd.ne_empty hc.1⟩

end GC.LongTime
