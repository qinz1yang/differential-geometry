import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SelectedCoreE2 := EuclideanSpace ℝ (Fin 2)
private abbrev SelectedCoreIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev SelectedCoreIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev SelectedCoreIH := ModelProd SelectedCoreE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (R : Set (ConnectedComponents (cutCore f)))

def retainedCoreOpen : Opens (cutCore f) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  exact ⟨retainedCore f R, (isClopen_retained_discardedCore hδ f hf hdisj R).1.isOpen⟩

@[instance_reducible] def retainedCoreChartedSpace : ChartedSpace SelectedCoreIH (retainedCore f R) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact inferInstanceAs (ChartedSpace SelectedCoreIH (retainedCoreOpen I hdim hδ f hf hdisj R))

variable (hs : ∀ i, IsLocalDiffeomorph SelectedCoreIC I ∞ (f i))

include hs in
theorem retainedCore_isManifold :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsManifold SelectedCoreIR ∞ (retainedCore f R) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold SelectedCoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact inferInstanceAs (IsManifold SelectedCoreIR ∞ (retainedCoreOpen I hdim hδ f hf hdisj R))

include hs in
theorem retainedCore_ambientInclusion_isSmoothEmbedding :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : retainedCore f R => p.val.val) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold SelectedCoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact isSmoothEmbedding_restrictOpen SelectedCoreIR I (Subtype.val : cutCore f → M)
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs)
    (retainedCoreOpen I hdim hδ f hf hdisj R)

include hs in
theorem retainedCore_boundary_eq_cuttingSpheres :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    SelectedCoreIR.boundary (retainedCore f R) = (Subtype.val : retainedCore f R → cutCore f) ⁻¹'
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  have hb : SelectedCoreIR.boundary (cutCore f) =
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) :=
    cutCore_boundary_eq_cuttingSpheres I hdim hδ f hf hdisj hs
  have hu := SelectedCoreIR.boundary_open (u := retainedCoreOpen I hdim hδ f hf hdisj R)
  exact hu.trans (congrArg ((Subtype.val : retainedCore f R → cutCore f) ⁻¹' ·) hb)

include hs in
theorem retained_discardedCore_smooth_embeddings :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace SelectedCoreIH (discardedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    IsManifold SelectedCoreIR ∞ (retainedCore f R) ∧
    IsManifold SelectedCoreIR ∞ (discardedCore f R) ∧
    IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : retainedCore f R => p.val.val) ∧
    IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : discardedCore f R => p.val.val) := by
  exact ⟨retainedCore_isManifold I hdim hδ f hf hdisj R hs,
    retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj Rᶜ hs⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
