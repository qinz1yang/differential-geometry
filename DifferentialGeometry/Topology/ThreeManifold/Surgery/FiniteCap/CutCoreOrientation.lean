import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInclusionDifferential

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CoreIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CoreIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CoreIH := ModelProd CoreE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CoreIC I ∞ (f i))

def cutCoreSmoothOrientation (o : SmoothOrientation I M) :
    let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation CoreIR (cutCore f) := by
  let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pullbackSmoothOrientation CoreIR I (Subtype.val : cutCore f → M)
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).contMDiff
    (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) o

theorem cutCoreSmoothOrientation_pushforward (o : SmoothOrientation I M) (p : cutCore f) :
    let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective CoreIR I (Subtype.val : cutCore f → M)
      (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) p).toLinearEquiv
        ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) = o.val p.val := by
  let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact tangentOrientationEquiv_symm
    (differentialEquivOfBijective CoreIR I (Subtype.val : cutCore f → M)
      (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) p).symm.toLinearEquiv
    (o.val p.val)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
