import DifferentialGeometry.Geometry.Thurston.NonnegativeClassification
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



end DifferentialGeometry.Geometry.Collapse
