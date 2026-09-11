import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

set_option autoImplicit false
noncomputable section
open IsManifold
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev AmbientE2 := EuclideanSpace ℝ (Fin 2)
private abbrev AmbientIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev AmbientIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev AmbientIH := ModelProd AmbientE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph AmbientIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_contMDiff :
    let : ChartedSpace AmbientIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    ContMDiff AmbientIR I ∞ (Subtype.val : cutCore f → M) := by
  let : ChartedSpace AmbientIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold AmbientIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  obtain ⟨e, he, hp⟩ := cutCoreBoundaryAtlas_covers I hdim hδ f hf hdisj p
  have ha : e ∈ maximalAtlas AmbientIR ∞ (cutCore f) :=
    subset_maximalAtlas he
  have hR : ContMDiffOn AmbientIR I ∞ (fun z : AmbientIH => (e.symm z).val) e.target := by
    rcases he with ⟨x, rfl⟩ | ⟨⟨b, q⟩, rfl⟩
    · exact cutCoreInteriorHalfChart_symm_ambient_contMDiffOn I hdim f x
    · exact cutCoreCollarHalfChart_symm_ambient_contMDiffOn I hδ f hdisj
        (fun i => (hs i).contMDiff) hf b q
  have hc : ContMDiffAt AmbientIR AmbientIR ∞ e p := contMDiffAt_of_mem_maximalAtlas ha hp
  have hcomp := (hR.contMDiffAt (e.open_target.mem_nhds (e.map_source hp))).comp p hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (congrArg Subtype.val (e.left_inv hq)).symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
