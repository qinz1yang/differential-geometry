import DifferentialGeometry.Topology.Manifold.LiftedChartLocalDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

set_option autoImplicit false
noncomputable section
open IsManifold
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev LocalCollarE3 := EuclideanSpace ℝ (Fin 3)
private abbrev LocalCollarE2 := EuclideanSpace ℝ (Fin 2)
private abbrev LocalCollarS2 := Metric.sphere (0 : LocalCollarE3) 1
private abbrev LocalCollarIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev LocalCollarIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev LocalCollarIH := ModelProd LocalCollarE2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ LocalCollarE3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph LocalCollarIC I ∞ (f i))

include hs in
theorem cuttingCollarMap_isLocalDiffeomorph (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace LocalCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsLocalDiffeomorph LocalCollarIR LocalCollarIR ∞
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace LocalCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold LocalCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  apply isLocalDiffeomorph_of_lifted_charts LocalCollarIR _ (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)
  intro q
  apply subset_maximalAtlas
  exact Or.inr ⟨⟨b, q⟩, rfl⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
