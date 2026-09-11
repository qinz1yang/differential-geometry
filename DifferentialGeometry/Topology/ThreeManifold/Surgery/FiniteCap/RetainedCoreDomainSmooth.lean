import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreSmoothManifolds
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev DomainCoreE2 := EuclideanSpace ℝ (Fin 2)
private abbrev DomainCoreIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev DomainCoreIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev DomainCoreIH := ModelProd DomainCoreE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph DomainCoreIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (U : Opens M)
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)

include hs in
theorem retainedCoreDomainMap_isSmoothEmbedding :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsSmoothEmbedding DomainCoreIR I ∞ (retainedCoreDomainMap f R U hRet) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  exact isSmoothEmbedding_intoOpen DomainCoreIR I U (retainedCoreDomainMap f R U hRet)
    (retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs)

include hs in
theorem retainedCoreDomainMap_mfderiv (p : retainedCore f R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    mfderiv DomainCoreIR I (retainedCoreDomainMap f R U hRet) p =
      mfderiv DomainCoreIR I (fun q : retainedCore f R => q.val.val) p := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  have hF : ContMDiff DomainCoreIR I ∞ (retainedCoreDomainMap f R U hRet) :=
    (retainedCoreDomainMap_isSmoothEmbedding I hdim hδ f hf hdisj hs R U hRet).contMDiff
  have hd := mfderiv_comp p
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at hd
  dsimp only [TangentSpace] at hd ⊢
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun A : (DomainCoreE2 × EuclideanSpace ℝ (Fin 1)) →L[ℝ] E => A v) hd).symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
