import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreCappedInterior
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreSmoothManifolds
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev FiniteEmbeddedE3 := EuclideanSpace ℝ (Fin 3)
private abbrev FiniteEmbeddedE2 := EuclideanSpace ℝ (Fin 2)
private abbrev FiniteEmbeddedIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev FiniteEmbeddedIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev FiniteEmbeddedIH := ModelProd FiniteEmbeddedE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FiniteEmbeddedIC I ∞ (f i))
local notation "FiniteEmbeddedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCoreInclusion_isSmoothEmbedding :
    let : ChartedSpace FiniteEmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace FiniteEmbeddedE3 FiniteEmbeddedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding FiniteEmbeddedIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  let : ChartedSpace FiniteEmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace FiniteEmbeddedE3 FiniteEmbeddedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  refine ⟨?_, (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding⟩
  suffices h : IsImmersionOfComplement Unit FiniteEmbeddedIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) from h.isImmersion
  intro p
  by_cases hp : p.val ∈ interior (cutCore f)
  · exact finiteCoreInclusion_isImmersionAt_interior I hdim hL hδ f hf hdisj hs ⟨p.val, hp⟩
  · have hfront : p ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    let q : _ × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    have hq : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q = p :=
      (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
    have h : IsImmersionAtOfComplement Unit FiniteEmbeddedIR (𝓡 3) ∞
        (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) :=
      finiteCoreInclusion_isImmersionAt_collar I hdim hL hδ f hf hdisj hs b q
    exact hq ▸ h

include hs in
theorem finiteRetainedCoreInclusion_isSmoothEmbedding (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FiniteEmbeddedIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace FiniteEmbeddedE3 FiniteEmbeddedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding FiniteEmbeddedIR (𝓡 3) ∞ (finiteRetainedCoreInclusion hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FiniteEmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold FiniteEmbeddedIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace FiniteEmbeddedIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace FiniteEmbeddedE3 FiniteEmbeddedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FiniteEmbeddedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  have h : IsSmoothEmbedding FiniteEmbeddedIR (𝓡 3) ∞
      (fun p : retainedCore f R => finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val) :=
    isSmoothEmbedding_restrictOpen FiniteEmbeddedIR (𝓡 3) _
      (finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs)
      (retainedCoreOpen I hdim hδ f hf hdisj R)
  exact isSmoothEmbedding_intoOpen FiniteEmbeddedIR (𝓡 3)
    (finiteCapRetained hL hδ f hf hdisj R) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) h

include hs in
theorem finiteDiscardedCoreInclusion_isSmoothEmbedding (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FiniteEmbeddedIH (discardedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    let : ChartedSpace FiniteEmbeddedE3 FiniteEmbeddedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding FiniteEmbeddedIR (𝓡 3) ∞
      (fun p : discardedCore f R => (finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ p : finiteCapDiscarded hL hδ f hf hdisj R)) :=
  finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs Rᶜ
end DifferentialGeometry.Topology.ThreeManifold.Surgery
