import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCuttingSpheres
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.SetTheory.Cardinal.Finite

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
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

theorem nativeCuttingSphereMap_connectedComponent (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    connectedComponent (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) =
      range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  have hc := isConnected_range (nativeCuttingSphereMap_contMDiff I hdim hδ f hf hdisj hs b).continuous
  have ho : IsClopen (range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) :=
    ⟨nativeCuttingSphereMap_range_isClosed I hdim hδ f hf hdisj hs b, (nativeCuttingSphereMap_isOpenEmbedding I hdim hδ f hf hdisj hs b).isOpen_range⟩
  exact Subset.antisymm (ho.connectedComponent_subset ⟨y, rfl⟩) (hc.subset_connectedComponent ⟨y, rfl⟩)

def nativeCuttingSphereComponentsEquiv :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (ι × Bool) ≃ ConnectedComponents (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let β := nativeCuttingSphereMap I hdim hδ f hf hdisj hs
  apply Equiv.ofBijective (fun b : ι × Bool => ConnectedComponents.mk (β b spherePoint))
  constructor
  · intro b c he
    have hm : β b spherePoint ∈ connectedComponent (β c spherePoint) := ConnectedComponents.coe_eq_coe'.mp he
    have hc := nativeCuttingSphereMap_connectedComponent I hdim hδ f hf hdisj hs c spherePoint
    rw [hc] at hm
    by_contra hbc
    exact (Set.disjoint_left.mp (nativeCuttingSphereMap_ranges_disjoint I hdim hδ f hf hdisj hs hbc)) ⟨spherePoint, rfl⟩ hm
  · intro c
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨b, y, hp⟩ := nativeCuttingSphereMap_cover I hdim hδ f hf hdisj hs p
    refine ⟨b, ?_⟩
    apply ConnectedComponents.coe_eq_coe.mpr
    rw [← hp, nativeCuttingSphereMap_connectedComponent, nativeCuttingSphereMap_connectedComponent]

theorem nativeCuttingSphereComponentsEquiv_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs b =
      ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  change ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b spherePoint) = _
  apply ConnectedComponents.coe_eq_coe.mpr
  rw [nativeCuttingSphereMap_connectedComponent, nativeCuttingSphereMap_connectedComponent]

theorem nativeCuttingSphereComponents_card :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Nat.card (ConnectedComponents (BoundaryManifold IR (cutCore f))) = 2 * Nat.card ι := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  have h := (Nat.card_congr (nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs)).symm
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm] using h
end DifferentialGeometry.Topology.ThreeManifold.Surgery
