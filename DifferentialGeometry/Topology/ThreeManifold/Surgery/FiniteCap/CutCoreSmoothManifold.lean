import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorToCollar

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreSmoothE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CoreSmoothIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CoreSmoothIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CoreSmoothIH := ModelProd CoreSmoothE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem cutCore_isManifold
    (hs : ∀ i, IsLocalDiffeomorph CoreSmoothIC I ∞ (f i)) :
    let : ChartedSpace CoreSmoothIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsManifold CoreSmoothIR ∞ (cutCore f) := by
  let : ChartedSpace CoreSmoothIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  apply isManifold_of_contDiffOn CoreSmoothIR ∞ (cutCore f)
  intro e e' he he'
  have hT : ContMDiffOn CoreSmoothIR CoreSmoothIR ∞ (e.symm.trans e') (e.symm.trans e').source := by
    change e ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj at he
    change e' ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj at he'
    rcases he with ⟨p, rfl⟩ | ⟨⟨b, q⟩, rfl⟩
    · rcases he' with ⟨p', rfl⟩ | ⟨⟨b', q'⟩, rfl⟩
      · exact cutCoreInteriorHalfChart_contMDiff_transition I hdim f p p'
      · exact cutCoreInteriorHalfChart_to_collar_contMDiff I hdim hδ f hf hdisj hs b' q' p
    · rcases he' with ⟨p', rfl⟩ | ⟨⟨b', q'⟩, rfl⟩
      · exact cutCoreCollarHalfChart_to_interior_contMDiff I hdim hδ f hf hdisj (fun i => (hs i).contMDiff) b q p'
      · exact cutCoreCollarHalfChart_contMDiff_transition hδ f hf hdisj b b' q q'
  have hcoord := hT.comp
    (CoreSmoothIR.contMDiffOn_symm.mono
      (inter_subset_right : CoreSmoothIR.symm ⁻¹' (e.symm.trans e').source ∩ range CoreSmoothIR ⊆ range CoreSmoothIR))
    (fun z hz => hz.1)
  exact (CoreSmoothIR.contMDiff.comp_contMDiffOn hcoord).contDiffOn
end DifferentialGeometry.Topology.ThreeManifold.Surgery
