import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreOrientation
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

include hs in
theorem cuttingCollarMap_mfderiv_bijective (b : ι × Bool)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    Bijective (mfderiv IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) q) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact ((cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b q).mfderivToContinuousLinearEquiv
    (by simp)).bijective

def cuttingCollarSmoothOrientation (b : ι × Bool) (o : SmoothOrientation I M) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    SmoothOrientation IR (S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pullbackSmoothOrientation IR IR
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b)
    (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o)

theorem cuttingCollarSmoothOrientation_apply (b : ι × Bool) (o : SmoothOrientation I M)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q =
      tangentOrientationEquiv (differentialEquivOfBijective IR IR
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
        (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) q).symm.toLinearEquiv
          ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val
            (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) := rfl

theorem exists_radialOrientation_matching_cuttingCollar {L : ℝ} (hL : 0 < L)
    (b : ι × Bool) (o : SmoothOrientation I M) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    ∃ oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      (oE = (Module.finBasis ℝ E3).orientation ∨ oE = -(Module.finBasis ℝ E3).orientation) ∧
      ∀ q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
        (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
          (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  exact exists_radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1))
    (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
