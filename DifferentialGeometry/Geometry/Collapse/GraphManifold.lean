import DifferentialGeometry.Geometry.Thurston.NonnegativeClassification
import DifferentialGeometry.Geometry.Thurston.GraphPresentation
import DifferentialGeometry.Topology.Connected.FinitePartitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

def closedCollapseHypotheses (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) : Prop :=
  W.model.boundary W.Carrier = ∅ ∧
    (∀ p, volumeCollapsedAtCurvatureScale g w₀ p) ∧
    curvatureDerivativesControlled g K A w₀

def boundaryCollapseHypotheses (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) : Prop :=
  Nonempty (NearlyCuspidalBoundary W g K w₀) ∧
    boundaryVolumeCollapsed W g w₀ ∧ curvatureDerivativesControlled g K A w₀

def staticCollapseHypotheses (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) : Prop :=
  closedCollapseHypotheses W g K A w₀ ∨ boundaryCollapseHypotheses W g K A w₀

theorem volumeCollapsedAtCurvatureScale_mono
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    {w₁ w₂ : ℝ} (hw : w₁ ≤ w₂) (p : W.Carrier)
    (h : volumeCollapsedAtCurvatureScale g w₁ p) :
    volumeCollapsedAtCurvatureScale g w₂ p := by
  intro r hr hR
  exact (h r hr hR).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hw (pow_nonneg hr.le 3)))

theorem closedCollapseHypotheses_mono
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (K : ℕ) (A : ℝ → ℝ) {w₁ w₂ : ℝ} (hw : w₁ ≤ w₂)
    (h : closedCollapseHypotheses W g K A w₁) :
    closedCollapseHypotheses W g K A w₂ := by
  exact ⟨h.1, fun p => volumeCollapsedAtCurvatureScale_mono g hw p (h.2.1 p),
    curvatureDerivativesControlled_mono_threshold g K A hw h.2.2⟩

theorem boundaryCollapseHypotheses_mono
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (K : ℕ) (A : ℝ → ℝ) {w₁ w₂ : ℝ} (hw : w₁ ≤ w₂)
    (h : boundaryCollapseHypotheses W g K A w₁) :
    boundaryCollapseHypotheses W g K A w₂ := by
  obtain ⟨⟨B⟩, hvol, hder⟩ := h
  exact ⟨⟨B.weaken hw⟩, fun p hp => volumeCollapsedAtCurvatureScale_mono g hw p (hvol p hp),
    curvatureDerivativesControlled_mono_threshold g K A hw hder⟩

theorem not_boundaryCollapseHypotheses_of_boundary_empty (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ)
    (A : ℝ → ℝ) (w₀ : ℝ) (h : W.model.boundary W.Carrier = ∅) :
    ¬ boundaryCollapseHypotheses W g K A w₀ := by
  rintro ⟨⟨B⟩, -, -⟩
  have hi : B.component ⟨0, B.count_pos⟩ ⊆ W.model.boundary W.Carrier := by
    rw [← B.covers]
    exact Set.subset_iUnion _ _
  rw [h, Set.subset_empty_iff] at hi
  exact (B.connected ⟨0, B.count_pos⟩).nonempty.ne_empty hi

theorem staticCollapseHypotheses_exclusive (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) :
    ¬ (closedCollapseHypotheses W g K A w₀ ∧ boundaryCollapseHypotheses W g K A w₀) := by
  rintro ⟨hclosed, hboundary⟩
  exact not_boundaryCollapseHypotheses_of_boundary_empty W g K A w₀ hclosed.1 hboundary

theorem exists_rawGraphPresentation_of_nonnegative
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hboundary : W.model.boundary W.Carrier = ∅)
    (hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨G, hG⟩ := GC.Geometry.closed_nonnegative_sectional_classification W g hboundary hsec
  rcases hG with hG | hG | hG
  · exact rawGraphPresentation_of_sphericalSpaceForm W hboundary G hG
  · exact rawGraphPresentation_of_sphericalProduct W hboundary G hG
  · exact rawGraphPresentation_of_flat W hboundary G hG

theorem exists_closed_graph_threshold_of_finite_scales (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) →
        closedCollapseHypotheses W g K A w₀ → Nonempty (RawGraphPresentation W) := by
  sorry

theorem exists_closed_graph_threshold (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ → Nonempty (RawGraphPresentation W) := by
  obtain ⟨w₀, hw₀, hwupper, hfinite⟩ := exists_closed_graph_threshold_of_finite_scales K hK A hA
  refine ⟨w₀, hw₀, hwupper, ?_⟩
  intro W hconn g h
  by_cases hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0
  · exact exists_rawGraphPresentation_of_nonnegative W g h.1 hsec
  · exact hfinite W g (fun p hp => hsec ((curvatureRadius_eq_top_iff p).mp hp)) h

end DifferentialGeometry.Geometry.Collapse

namespace GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
universe u

theorem RawGraphPresentation.external_matching {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} (G : RawGraphPresentation W) (B : NearlyCuspidalBoundary W g K δ) :
    ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  have : ConnectedSpace Circle := (AddCircle.homeomorphCircle one_ne_zero).surjective.connectedSpace
    (AddCircle.homeomorphCircle one_ne_zero).continuous
  have hrange : ∀ i, Set.range (G.external.torusMap i) ⊆ (G.external.collar i).target := by
    intro i x hx
    obtain ⟨t, rfl⟩ := hx
    apply (G.external.collar i).map_source
    rw [G.external.source_eq]
    change (0 : ℝ) < 1
    norm_num
  obtain ⟨e, he⟩ := DifferentialGeometry.Topology.finite_connected_partitions_equiv B.component
    (fun i => Set.range (G.external.torusMap i)) B.connected
    (fun i => isConnected_range (G.external.torusMap_smooth i).continuous)
    B.closed (fun i => (isCompact_range (G.external.torusMap_smooth i).continuous).isClosed)
    B.disjoint (fun i j hij => (G.external.disjoint hij).mono (hrange i) (hrange j))
    (B.covers.trans G.external_exhausted)
  exact ⟨e, fun i => (he i).symm⟩

end GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse
universe u

theorem exists_boundary_graph_threshold (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  sorry

theorem exists_graph_threshold (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ → Nonempty (RawGraphPresentation W) := by
  obtain ⟨wc, hwc, hcupper, hc⟩ := exists_closed_graph_threshold K hK A hA
  obtain ⟨wb, hwb, hbupper, hb⟩ := exists_boundary_graph_threshold K hK A hA
  refine ⟨min wc wb, lt_min hwc hwb, (min_le_left wc wb).trans_lt hcupper, ?_⟩
  intro W hconn g h
  rcases h with h | h
  · exact hc W g (closedCollapseHypotheses_mono g K A (min_le_left wc wb) h)
  · obtain ⟨⟨B⟩, hvol, hder⟩ :=
      boundaryCollapseHypotheses_mono g K A (min_le_right wc wb) h
    obtain ⟨G, _, _⟩ := hb W g B hvol hder
    exact ⟨G⟩

end DifferentialGeometry.Geometry.Collapse
