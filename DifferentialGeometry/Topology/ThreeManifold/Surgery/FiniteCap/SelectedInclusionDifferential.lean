import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreOrientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "SelectedDerivativeQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteRetainedCoreInclusion_mfderiv_eq_original
    (R : Set (ConnectedComponents (cutCore f))) (p : retainedCore f R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv IR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p =
      mfderiv IR (𝓡 3) (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) p.val := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have ht := mfderiv_comp_open_val IR (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R)
    (finiteRetainedCoreInclusion hL hδ f hf hdisj R)
    (finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R).contMDiff p
  have hs' := DifferentialGeometry.mfderiv_restrict_open (I := IR) (J := 𝓡 3)
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
    (retainedCoreOpen I hdim hδ f hf hdisj R) p
  exact ht.symm.trans hs'

include hs in
theorem finiteRetainedCoreInclusion_mfderiv_bijective
    (R : Set (ConnectedComponents (cutCore f))) (p : retainedCore f R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv IR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  rw [finiteRetainedCoreInclusion_mfderiv_eq_original I hdim hL hδ f hf hdisj hs R p]
  exact finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs p.val

def retainedCoreSmoothOrientation (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation I M) :
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
    SmoothOrientation IR (retainedCore f R) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  exact restrictSmoothOrientation IR (retainedCoreOpen I hdim hδ f hf hdisj R)
    (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o)

theorem retainedCoreSmoothOrientation_apply (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation I M)
    (p : retainedCore f R) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
    (retainedCoreSmoothOrientation I hdim hδ f hf hdisj hs R o).val p =
      (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p.val := rfl

include hs in
theorem finiteRetainedCapInclusion_mfderiv_eq_original
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) (x : Ball L) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡∂ 3) (𝓡 3)
      (fun y : Ball L => (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩, hb⟩ :
        finiteCapRetained hL hδ f hf hdisj R)) x =
      mfderiv (𝓡∂ 3) (𝓡 3)
        (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) x := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (mfderiv_comp_open_val (𝓡∂ 3) (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R) _
    (finiteRetainedCapInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R b hb).contMDiff x).symm

include hs in
theorem finiteRetainedCapInclusion_mfderiv_bijective
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) (x : Ball L) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (fun y : Ball L => (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩, hb⟩ :
        finiteCapRetained hL hδ f hf hdisj R)) x) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let : ChartedSpace E3 SelectedDerivativeQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  rw [finiteRetainedCapInclusion_mfderiv_eq_original I hdim hL hδ f hf hdisj hs R b hb x]
  exact finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b x
end DifferentialGeometry.Topology.ThreeManifold.Surgery
