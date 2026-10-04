import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterfaceBoundary
import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterfaceApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# Consumers of the LC90 boundary interface

* `exists_threshold_fixed_family_rawGraph`: for a fixed finite list of connected compact carriers
  (closed or with nearly cuspidal boundary), the eventual derivative tests hold by compactness, so
  one threshold `w₀` from the static theorem serves the whole list, in both branches, with the
  boundary components matched to external tori.
* `GC.LongTime.LateCutFamily.exists_late_hyperbolicOrGraph`: LC90's componentwise composition for
  the tree's late cut families: the common `A` of
  `LateCutFamily.exists_late_tests_of_derivative_bounds` (LC89) is fixed first, then `w₀` by the
  static theorem at `(K, A)`, then the late index `N`; every piece of every late slice component
  is hyperbolic or has a raw graph presentation. The static theorem and the nonnegative branch
  are explicit inputs; no flow producer is used or proved.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC90's interface, both branches, for a fixed finite list of connected carriers: given the
static theorem at order `K`, one threshold `w₀` serves the whole list; each closed carrier volume
collapsed below `w₀` has a raw graph presentation, and each carrier with nearly cuspidal collar
data at `w₀` and interior volume collapse has one whose external tori match its labelled boundary
components. -/
theorem exists_threshold_fixed_family_rawGraph (K : ℕ) (ι : Type*) [Finite ι]
    (W : ι → CompactCarrier.{u}) [∀ i, ConnectedSpace (W i).Carrier]
    (g : (i : ι) → SmoothRiemannianMetric (W i).model (W i).Carrier)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      (∀ i : ι, (W i).model.boundary (W i).Carrier = ∅ →
        (∀ p, volumeCollapsedAtCurvatureScale (g i) w₀ p) →
        Nonempty (RawGraphPresentation (W i))) ∧
      (∀ (i : ι) (B : NearlyCuspidalBoundary (W i) (g i) K w₀),
        boundaryVolumeCollapsed (W i) (g i) w₀ →
        ∃ G : RawGraphPresentation (W i), ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ k, Set.range (G.external.torusMap (e k)) = B.component k) := by
  obtain ⟨w₀, hw₀, hwc, hclosed, hboundary⟩ := exists_threshold_components_rawGraph K
    (fun _ => ι) (fun _ i => W i) (fun _ i => g i) (eventual_bound_of_fixed_family K ι W g) static
  exact ⟨w₀, hw₀, hwc, fun i => hclosed 0 i, fun i => hboundary 0 i⟩

end DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime
universe u

/-- LC90's componentwise composition for a late cut family, interface form: with the static
theorem at order `K` and the nonnegative branch as explicit inputs, and the family's eventual
whole-ball derivative tests, the parameters are chosen in the order `A` (LC89) → `w₀` (static
theorem) → late index `N`, and every piece of every component of every late slice is hyperbolic
or carries a raw graph presentation. -/
theorem LateCutFamily.exists_late_hyperbolicOrGraph
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V))
    (nonneg : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      V.model.boundary V.Carrier = ∅ →
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow h 0 →
      Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ (C : ConnectedComponents (slices j).stage.Carrier)
        (i : Fin (L.decomposition j C).components.count),
        Nonempty (HyperbolicOrGraph (L.decomposition j C).carrier
          (L.decomposition j C).components i) := by
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds h
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A hA
  obtain ⟨N, hN⟩ := htests w₀ hw₀ hwc
  refine ⟨w₀, hw₀, hwc, N, fun j hj C i => ?_⟩
  obtain ⟨pieces⟩ := hN j hj C
  exact (pieces i).nonempty_hyperbolicOrGraph hstatic nonneg

end GC.LongTime
