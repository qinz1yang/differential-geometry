import DifferentialGeometry.Topology.Manifold.ProductBoundaryMap
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingCollarOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Collar (B : ℝ) := S2 × Ico (0 : ℝ) B
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel
private local instance : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    ChartedSpace E2 (BoundaryManifold IR X) := BoundaryManifold.chartedSpace (I := IR)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold IR X) := BoundaryManifold.isManifold (I := IR)
private def sphereNativeCollar {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ BoundaryManifold IR (Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact (retainedFaceDiffeomorph hB).trans (retainedBoundaryFaceDiffeomorph hB).symm
private theorem sphereNativeCollar_apply {B : ℝ} (hB : 0 < B) (y : S2) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    (sphereNativeCollar hB y).val = (y, ⟨0, le_rfl, hB⟩) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact retainedBoundaryFaceDiffeomorph_symm_apply hB (retainedFaceDiffeomorph hB y)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

def nativeCuttingSphereMap (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    S2 → BoundaryManifold IR (cutCore f) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact productBoundaryMap (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) ∘ sphereNativeCollar hB

theorem nativeCuttingSphereMap_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y).val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b,y⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  change cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b (sphereNativeCollar hB y).val = _
  rw [sphereNativeCollar_apply]
  exact cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y

theorem nativeCuttingSphereMap_contMDiff (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ContMDiff (𝓡 2) (𝓡 2) ∞ (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact (productBoundaryMap_contMDiff _ (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b)).comp
    (sphereNativeCollar hB).contMDiff

theorem nativeCuttingSphereMap_mfderiv_bijective (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Bijective (mfderiv (𝓡 2) (𝓡 2) (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let hκ := cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b
  exact bijective_mfderiv_comp (𝓡 2) (𝓡 2) (𝓡 2) (sphereNativeCollar hB) (productBoundaryMap κ hκ)
    (sphereNativeCollar hB).contMDiff (productBoundaryMap_contMDiff κ hκ)
    (fun x => ((sphereNativeCollar hB).mfderivToContinuousLinearEquiv (by simp) x).bijective)
    (productBoundaryMap_mfderiv_bijective κ hκ) y

theorem nativeCuttingSphereMap_injective (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Injective (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro y z h
  have he := congrArg (fun p : BoundaryManifold IR (cutCore f) => p.val) h
  rw [nativeCuttingSphereMap_apply, nativeCuttingSphereMap_apply] at he
  have hp := (isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj).injective he
  exact congrArg (fun q : CuttingSpheres ι => q.2) hp

theorem nativeCuttingSphereMap_isLocalDiffeomorph (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact isLocalDiffeomorph_of_injective_mfderiv _ (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b)
    (fun y => (nativeCuttingSphereMap_mfderiv_bijective I hdim hδ f hf hdisj hs b y).injective) rfl

theorem nativeCuttingSphereMap_isOpenEmbedding (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    _root_.Topology.IsOpenEmbedding (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact _root_.Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨(nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous,
      nativeCuttingSphereMap_injective I hdim hδ f hf hdisj hs b,
      (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).isOpenMap⟩

theorem nativeCuttingSphereMap_range_isClosed (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    IsClosed (range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (isCompact_range (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous).isClosed

theorem nativeCuttingSphereMap_ranges_disjoint :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Pairwise (fun b c => Disjoint (range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b))
      (range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs c))) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro b c hbc
  rw [Set.disjoint_left]
  rintro p ⟨y, hy⟩ ⟨z, hz⟩
  have he := congrArg (fun q : BoundaryManifold IR (cutCore f) => q.val) (hy.trans hz.symm)
  rw [nativeCuttingSphereMap_apply, nativeCuttingSphereMap_apply] at he
  have hp := (isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj).injective he
  exact hbc (congrArg (fun q : CuttingSpheres ι => q.1) hp)

theorem nativeCuttingSphereMap_cover :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ p : BoundaryManifold IR (cutCore f),
      ∃ (b : ι × Bool) (y : S2), nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y = p := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  have hp := (Set.ext_iff.mp (cutCore_boundary_eq_cuttingSpheres I hdim hδ f hf hdisj hs) p.val).mp p.property
  obtain ⟨⟨b, y⟩, hby⟩ := hp
  refine ⟨b, y, Subtype.ext ?_⟩
  exact (nativeCuttingSphereMap_apply I hdim hδ f hf hdisj hs b y).trans hby
end DifferentialGeometry.Topology.ThreeManifold.Surgery
