import DifferentialGeometry.Topology.Manifold.ClopenDecomposition
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev DecompositionE3 := EuclideanSpace ℝ (Fin 3)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "DecompQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapSelectedDiffeomorph (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph (𝓡 3) (𝓡 3)
      (finiteCapRetained hL hδ f hf hdisj R ⊕ finiteCapDiscarded hL hδ f hf hdisj R) DecompQ ∞ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph (𝓡 3)
    (finiteCapRetained hL hδ f hf hdisj R)
    (isClopen_finiteCapRetained_discarded hL hδ f hf hdisj R).1.isClosed

theorem finiteCapSelectedDiffeomorph_inl (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    ∀ p : finiteCapRetained hL hδ f hf hdisj R,
      finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R (Sum.inl p) = p.val := by
  dsimp only
  intro p
  rfl

theorem finiteCapSelectedDiffeomorph_inr (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    ∀ p : finiteCapDiscarded hL hδ f hf hdisj R,
      finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R (Sum.inr p) = p.val := by
  dsimp only
  intro p
  rfl

theorem finiteCapSelectedDiffeomorph_symm_retained (R : Set (ConnectedComponents (cutCore f)))
    : let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
      let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
      ∀ (q : DecompQ) (hq : finiteCapComponentLabel hL hδ f hf hdisj q ∈ R),
    (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm q = Sum.inl ⟨q, hq⟩ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro q hq
  apply (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).injective
  exact (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).apply_symm_apply q

theorem finiteCapSelectedDiffeomorph_symm_discarded (R : Set (ConnectedComponents (cutCore f)))
    : let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
      let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
      ∀ (q : DecompQ) (hq : finiteCapComponentLabel hL hδ f hf hdisj q ∉ R),
    (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm q = Sum.inr ⟨q, hq⟩ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro q hq
  apply (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).injective
  exact (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).apply_symm_apply q
end DifferentialGeometry.Topology.ThreeManifold.Surgery
