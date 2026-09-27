import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.ImmersionLiftSource
import DifferentialGeometry.Topology.Manifold.ImmersionEqualDimension
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarLocalDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CappedCollarE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CappedCollarE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CappedCollarS2 := Metric.sphere (0 : CappedCollarE3) 1
private abbrev CappedCollarIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CappedCollarIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CappedCollarIH := ModelProd CappedCollarE2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ CappedCollarE3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CappedCollarIC I ∞ (f i))
local notation "CoreCappedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCoreInclusion_collar_isSmoothEmbedding (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ∘
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CoreCappedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  let ρ := retainedRadialMap (B := cuttingCollarWidth (precision b.1)) hL
  have hρ : IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ ρ :=
    isSmoothEmbedding_retainedRadialMap hL (cuttingCollarWidth_pos (hδ b.1))
  have hN : IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ (D.symm ∘ ρ) :=
    isSmoothEmbedding_diffeomorph_comp CappedCollarIR (𝓡 3) ρ hρ D.symm
  have hQ : IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ (Subtype.val ∘ (D.symm ∘ ρ)) :=
    isSmoothEmbedding_fromOpen CappedCollarIR (𝓡 3) N (D.symm ∘ ρ) hN
  have heq : Subtype.val ∘ (D.symm ∘ ρ) =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ∘
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b := by
    funext q
    let p : N := ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), Or.inr ⟨q, rfl⟩⟩
    have hp : D p = ρ q := by
      apply Subtype.ext
      exact finiteCapNeighborhoodHomeomorph_collar hL hδ f hf hdisj b q
    change (D.symm (ρ q)).val = p.val
    rw [← hp, D.symm_apply_apply]
  exact heq ▸ hQ

include hs in
theorem finiteCoreInclusion_isImmersionAt_collar (b : ι × Bool)
    (q : CappedCollarS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    let : ChartedSpace CappedCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsImmersionAtOfComplement Unit CappedCollarIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace CappedCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CappedCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have h := (finiteCoreInclusion_collar_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).isImmersion.isImmersionAt q
  have hUnit := isImmersionAtOfComplement_unit_of_equalDimension CappedCollarIR (𝓡 3) _ q h (by simp)
  exact isImmersionAtOfComplement_lift_source CappedCollarIR (𝓡 3) _
    (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) _ q hUnit
end DifferentialGeometry.Topology.ThreeManifold.Surgery
