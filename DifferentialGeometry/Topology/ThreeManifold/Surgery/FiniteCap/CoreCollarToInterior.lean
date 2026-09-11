import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorCoordinates
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarSmooth

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ToInteriorE3 := EuclideanSpace ℝ (Fin 3)
private abbrev ToInteriorS2 := Metric.sphere (0 : ToInteriorE3) 1
private abbrev ToInteriorIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev ToInteriorIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {ι : Type*} {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem cutCoreCollarHalfChart_to_interior_contMDiff
    (hs : ∀ i, ContMDiff ToInteriorIC I ∞ (f i)) (b : ι × Bool)
    (q : ToInteriorS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)))
    (x : coreInteriorDomain f) :
    ContMDiffOn ToInteriorIR ToInteriorIR ∞
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreInteriorHalfChart I hdim f x))
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreInteriorHalfChart I hdim f x)).source := by
  intro z hz
  have hF := (cutCoreCollarHalfChart_symm_ambient_contMDiffOn I hδ f hdisj hs hf b q).contMDiffAt
    ((cutCoreCollarHalfChart hδ f hf hdisj b q).open_target.mem_nhds hz.1)
  exact (cutCoreInteriorHalfChart_comp_contMDiffAt I hdim f ToInteriorIR
    (cutCoreCollarHalfChart hδ f hf hdisj b q).symm x z hF hz.2).contMDiffWithinAt
end DifferentialGeometry.Topology.ThreeManifold.Surgery
