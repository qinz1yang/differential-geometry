import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

theorem continuous_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) :
    Continuous (indexedCapBoundary (ι := ι) hL) := by
  apply continuous_sigma
  intro b
  change Continuous (fun y : S2 => (⟨b, radialCapBoundary hL y⟩ : IndexedCaps ι L))
  have hr : Continuous (radialCapBoundary hL) :=
    (show Continuous (fun y : S2 => L • y.val) from
      (continuous_const : Continuous (fun _ : S2 => L)).fun_smul
        (continuous_subtype_val : Continuous (fun y : S2 => y.val))).subtype_mk _
  exact continuous_sigmaMk.comp hr

theorem isClosedEmbedding_indexedCapBoundary {ι : Type*} [Finite ι] {L : ℝ} (hL : 0 < L) :
    _root_.Topology.IsClosedEmbedding (indexedCapBoundary (ι := ι) hL) :=
  (continuous_indexedCapBoundary hL).isClosedEmbedding (injective_indexedCapBoundary hL)

variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}

theorem isClosedMap_finiteCapProjection (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    IsClosedMap (adjunctionMk (indexedCapBoundary hL)
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj)) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedMap_adjunctionMk _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

theorem finiteCapQuotient_t2Space (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    T2Space (FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact adjunction_t2Space _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

theorem isClosedEmbedding_finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    _root_.Topology.IsClosedEmbedding (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedEmbedding_adjunctionCell _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

theorem isClosedEmbedding_finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    _root_.Topology.IsClosedEmbedding (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedEmbedding_adjunctionLower _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous
end DifferentialGeometry.Topology.ThreeManifold.Surgery
