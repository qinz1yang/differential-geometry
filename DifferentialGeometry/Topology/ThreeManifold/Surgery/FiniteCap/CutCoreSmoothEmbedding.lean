import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreCollarImmersion

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev EmbeddedE2 := EuclideanSpace ℝ (Fin 2)
private abbrev EmbeddedIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev EmbeddedIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev EmbeddedIH := ModelProd EmbeddedE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph EmbeddedIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_isSmoothEmbedding :
    let : ChartedSpace EmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsSmoothEmbedding EmbeddedIR I ∞ (Subtype.val : cutCore f → M) := by
  let : ChartedSpace EmbeddedIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  refine ⟨?_, _root_.Topology.IsEmbedding.subtypeVal⟩
  suffices h : IsImmersionOfComplement Unit EmbeddedIR I ∞ (Subtype.val : cutCore f → M) from h.isImmersion
  intro p
  by_cases hp : p.val ∈ interior (cutCore f)
  · exact cutCore_ambientInclusion_isImmersionAt_interior I hdim hδ f hf hdisj hs ⟨p.val, hp⟩
  · have hfront : p ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    let q : _ × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    have hq : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q = p :=
      (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
    have h : IsImmersionAtOfComplement Unit EmbeddedIR I ∞ (Subtype.val : cutCore f → M)
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) :=
      cutCore_ambientInclusion_isImmersionAt_collar I hdim hδ f hf hdisj hs b q
    exact hq ▸ h
end DifferentialGeometry.Topology.ThreeManifold.Surgery
