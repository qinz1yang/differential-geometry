import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentSelection
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeckManifold

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SelectedE3 := EuclideanSpace ℝ (Fin 3)
private abbrev SelectedIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ SelectedE3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M]

include I in
theorem originalModel_locallyPathConnected (hdim : Module.finrank ℝ E = 3) : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace H := (modelThreeHomeomorph I hdim).isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

variable {ι : Type*} [Finite ι] [T2Space M] [IsManifold I ∞ M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "CappedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem finiteCapSelected_isManifold
    (hs : ∀ i, IsLocalDiffeomorph SelectedIC I ∞ (f i)) (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧
      IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CappedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact ⟨inferInstance, inferInstance⟩

theorem finiteCapSelected_closedManifold_properties [CompactSpace M]
    (hs : ∀ i, IsLocalDiffeomorph SelectedIC I ∞ (f i)) (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧
      IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      CompactSpace (finiteCapRetained hL hδ f hf hdisj R) ∧
      CompactSpace (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      T2Space (finiteCapRetained hL hδ f hf hdisj R) ∧
      T2Space (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      SecondCountableTopology (finiteCapRetained hL hδ f hf hdisj R) ∧
      SecondCountableTopology (finiteCapDiscarded hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have htop := finiteCapQuotient_topological_properties I hdim hL hδ f hf hdisj
  let : T2Space CappedQ := htop.2.1
  let : SecondCountableTopology CappedQ := htop.2.2.1
  have hc := finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R
  have hs' := finiteCapSelected_isManifold I hdim hL hδ f hf hdisj hs R
  exact ⟨hs'.1, hs'.2, hc.1, hc.2, inferInstance, inferInstance, inferInstance, inferInstance⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
