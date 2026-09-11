import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothManifold
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreBoundaryE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CoreBoundaryIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CoreBoundaryIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CoreBoundaryIH := ModelProd CoreBoundaryE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CoreBoundaryIC I ∞ (f i))

private theorem coreBoundary_model_interior (z : CoreBoundaryIH) :
    CoreBoundaryIR z ∈ interior (range CoreBoundaryIR) ↔ 0 < z.2.val 0 := by
  simp only [CoreBoundaryIR, ModelWithCorners.range_prod, interior_prod_eq,
    ModelWithCorners.Boundaryless.range_eq_univ, interior_univ,
    interior_range_modelWithCornersEuclideanHalfSpace, mem_prod, mem_univ, true_and]
  rfl

include hs in
private theorem coreBoundary_chart_interior
    (e : OpenPartialHomeomorph (cutCore f) CoreBoundaryIH)
    (he : e ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj)
    (p : cutCore f) (hp : p ∈ e.source) :
    let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    CoreBoundaryIR.IsInteriorPoint p ↔ 0 < (e p).2.val 0 := by
  let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CoreBoundaryIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  have ha : e ∈ atlas CoreBoundaryIH (cutCore f) := he
  rw [CoreBoundaryIR.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) ha hp]
  constructor
  · intro h
    exact (coreBoundary_model_interior (e p)).mp
      (e.interior_extend_target_subset_interior_range h)
  · intro h
    exact e.mem_interior_extend_target (e.map_source hp)
      ((coreBoundary_model_interior (e p)).mpr h)

include hs

theorem cutCore_isInteriorPoint_iff (p : cutCore f) :
    let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    CoreBoundaryIR.IsInteriorPoint p ↔ p.val ∈ interior (cutCore f) := by
  let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  constructor
  · intro h
    by_contra hp
    have hfront : p ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    let q : _ × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    have hq : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q = p :=
      (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
    have hmem := cutCoreCollarHalfChart_mem hδ f hf hdisj b q
    have hheight := cutCoreCollarHalfChart_height hδ f hf hdisj b q q
    rw [hq] at hmem hheight
    have hz := (coreBoundary_chart_interior I hdim hδ f hf hdisj hs
      (cutCoreCollarHalfChart hδ f hf hdisj b q) (Or.inr ⟨⟨b, q⟩, rfl⟩) p hmem).mp h
    rw [hheight] at hz
    exact (lt_irrefl (0 : ℝ)) hz
  · intro hp
    let x : coreInteriorDomain f := ⟨p.val, hp⟩
    have hx : coreInteriorInclusion f x = p := rfl
    have hmem := cutCoreInteriorHalfChart_mem I hdim f x
    have hheight := cutCoreInteriorHalfChart_base_height I hdim f x
    rw [hx] at hmem hheight
    apply (coreBoundary_chart_interior I hdim hδ f hf hdisj hs
      (cutCoreInteriorHalfChart I hdim f x) (Or.inl ⟨x, rfl⟩) p hmem).mpr
    rw [hheight]
    norm_num

theorem cutCore_boundary_eq_frontier :
    let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    CoreBoundaryIR.boundary (cutCore f) = (Subtype.val : cutCore f → M) ⁻¹' frontier (cutCore f) := by
  let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  ext p
  change CoreBoundaryIR.IsBoundaryPoint p ↔ p.val ∈ frontier (cutCore f)
  have hInt : CoreBoundaryIR.IsInteriorPoint p ↔ p.val ∈ interior (cutCore f) :=
    cutCore_isInteriorPoint_iff I hdim hδ f hf hdisj hs p
  rw [← not_iff_not, ← CoreBoundaryIR.isInteriorPoint_iff_not_isBoundaryPoint, hInt]
  exact mem_interior_iff_notMem_frontier p.property

theorem cutCore_boundary_eq_cuttingSpheres :
    let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    CoreBoundaryIR.boundary (cutCore f) =
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
  let : ChartedSpace CoreBoundaryIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  dsimp only
  exact (cutCore_boundary_eq_frontier I hdim hδ f hf hdisj hs).trans
    (range_cuttingSphereAttachment hδ f hf hdisj).symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
