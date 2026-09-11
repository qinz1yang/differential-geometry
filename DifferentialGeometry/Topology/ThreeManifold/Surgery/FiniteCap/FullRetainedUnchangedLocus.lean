import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCutCapGeometry
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
  (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
  (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
  (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f))) (U : Opens M)
  (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def FullRetainedUnchangedLocusGeometry : Prop :=
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
  ∃ K : Set (retainedCore f R), K = univ ∧ IsCompact K ∧
    IsSmoothEmbedding IR IR ∞ (id : retainedCore f R → retainedCore f R) ∧
    IsSmoothEmbedding IR I ∞ Ψ ∧ IsSmoothEmbedding IR (𝓡 3) ∞ Φ ∧
    MapsTo (fun p : retainedCore f R => p.val.val) K U ∧
    ((univ : Set (retainedCore f R)) \ (fun p => p.val.val) ⁻¹'
      (⋃ i, ν i '' {q : S2 × Icc (-2 : ℝ) 2 | q.2.val ∈ Ioo (-2 : ℝ) 2})) ⊆ K ∧
    (∀ q : finiteCapRetained hL hδ f hf hdisj R,
      ∃ p : retainedCore f R, p ∈ K ∧ Φ p ∈ connectedComponent q) ∧
    (IsEmpty (finiteCapRetained hL hδ f hf hdisj R) → K = ∅)

theorem fullRetainedUnchangedLocusGeometry [CompactSpace M] :
    FullRetainedUnchangedLocusGeometry I hdim hL hδ f hf hdisj hs hδ1 R U hRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : CompactSpace (retainedCore f R) := isCompact_iff_compactSpace.mp
    (isCompact_retained_discardedCore hδ f hf hdisj R).1
  refine ⟨univ, rfl, isCompact_univ, IsSmoothEmbedding.id, ?_, ?_, ?_, subset_univ _, ?_, ?_⟩
  · exact retainedCoreDomainMap_isSmoothEmbedding I hdim hδ f hf hdisj hs R U hRet
  · exact finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R
  · intro p _
    exact hRet p.property
  · intro q
    obtain ⟨p, hp⟩ := finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R q
    exact ⟨p, mem_univ _, hp⟩
  · intro hEmpty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p _
    exact hEmpty.false (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
