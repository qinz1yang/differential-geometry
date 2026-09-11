import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapFullInsertion
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPatchSelection
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev FullWE3 := EuclideanSpace ℝ (Fin 3)
private abbrev FullWIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev FullWAttachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)
private local instance {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : ChartedSpace FullWE3 (FullWAttachment hL hB) :=
  radialCapAttachmentChartedSpace hL hB
private local instance {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (FullWAttachment hL hB) :=
  radialCapAttachment_isManifold hL hB
private local instance {L B : ℝ} {hL : 0 < L} {hB : 0 < B} : T2Space (FullWAttachment hL hB) :=
  radialCapAttachment_t2Space hL hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullWIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c)
local notation "FullWQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "FullWRet" => finiteCapRetained hL hδ f hf hdisj R
local notation "FullWB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

def finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    FullWAttachment hL (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 → FullWRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) ∘
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm

theorem contMDiff_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_inclusion (n := ∞) (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹))).comp
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm.contMDiff

theorem finiteFullWitnessMap_mfderiv (b : FullWB) (q : FullWAttachment hL (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) q =
      mfderiv (𝓡 3) (𝓡 3) (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  change mfderiv (𝓡 3) (𝓡 3) (Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) ∘ D.symm) q = _
  rw [mfderiv_comp q ((contMDiff_inclusion (n := ∞) (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹))).mdifferentiable (by simp) (D.symm q))
    (D.symm.contMDiff.mdifferentiable (by simp) q), mfderiv_opens_incl]
  rfl

theorem injective_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Injective (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  dsimp only
  intro x y he
  apply D.symm.injective
  apply Subtype.ext
  exact congrArg (fun q : FullWRet => q.val) he

theorem isLocalDiffeomorph_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullWQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space FullWQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) _ rfl
  intro q
  rw [finiteFullWitnessMap_mfderiv]
  exact (D.symm.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) q).injective

theorem range_finiteFullWitnessMap (b : FullWB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b) =
      {q : FullWRet | q.val ∈ finiteCapRestrictedNeighborhood hL hδ f hf hdisj b.val ((c * precision b.val.1)⁻¹)} := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (D.symm p).property
  · intro hq
    refine ⟨D ⟨q.val, hq⟩, ?_⟩
    change Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property ((c * precision b.val.1)⁻¹)) (D.symm (D ⟨q.val, hq⟩)) = q
    rw [D.symm_apply_apply]
    rfl

theorem pairwise_disjoint_finiteFullWitnessMaps :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Pairwise (fun b d : FullWB => Disjoint
      (range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc b)) (range (finiteFullWitnessMap I hdim hL hδ f hf hdisj hs R c hc d))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace FullWE3 FullWQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro b d hbd
  apply Set.disjoint_left.mpr
  intro q hb hd
  rw [range_finiteFullWitnessMap] at hb hd
  have hval : b.val ≠ d.val := fun he => hbd (Subtype.ext he)
  exact Set.disjoint_left.mp (pairwise_disjoint_finiteCapRestrictedNeighborhoods hL hδ f hf hdisj
    (fun b => (c * precision b.1)⁻¹) hval) hb hd
end DifferentialGeometry.Topology.ThreeManifold.Surgery
