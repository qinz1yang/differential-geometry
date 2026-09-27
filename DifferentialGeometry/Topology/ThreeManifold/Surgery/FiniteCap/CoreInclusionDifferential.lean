import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallSmooth
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreDerE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CoreDerE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CoreDerIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CoreDerIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CoreDerIH := ModelProd CoreDerE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CoreDerIC I ∞ (f i))
local notation "CoreDerQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem cutCore_ambientInclusion_mfderiv_bijective (p : cutCore f) :
    let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    Bijective (mfderiv CoreDerIR I (Subtype.val : cutCore f → M) p) := by
  let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt CoreDerIR I _ p
    ((cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).isImmersion.isImmersionAt p)
    (by simpa using hdim.symm)

include hs in
theorem finiteCoreInclusion_mfderiv_bijective (p : cutCore f) :
    let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv CoreDerIR (𝓡 3) (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) p) := by
  let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt CoreDerIR (𝓡 3) _ p
    ((finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).isImmersion.isImmersionAt p) (by simp)

include hs in
theorem finiteCapInclusion_ball_mfderiv_bijective (b : ι × Bool)
    (x : {x : CoreDerE3 // ‖x‖ ≤ L}) :
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CoreDerE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (fun y : {x : CoreDerE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CoreDerE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) _ x
    ((finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).isImmersion.isImmersionAt x) rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
