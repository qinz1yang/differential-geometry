import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import DifferentialGeometry.Topology.Manifold.ScaledClosedBall

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CapBallSmoothE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CapBallSmoothIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CapBallSmoothIC I ∞ (f i))
local notation "CapBallSmoothQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCapInclusion_ball_isSmoothEmbedding (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CapBallSmoothQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  let ρ : {x : CapBallSmoothE3 // ‖x‖ ≤ L} → V := fun x =>
    ⟨x.val, x.property.trans_lt (lt_add_of_pos_right L (cuttingCollarWidth_pos (hδ b.1)))⟩
  have hρ : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ρ :=
    isSmoothEmbedding_intoOpen (𝓡∂ 3) (𝓡 3) V ρ (isSmoothEmbedding_closedBall_inclusion hL)
  have hN : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (D.symm ∘ ρ) :=
    isSmoothEmbedding_diffeomorph_comp (𝓡∂ 3) (𝓡 3) ρ hρ D.symm
  have hQ : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val ∘ (D.symm ∘ ρ)) :=
    isSmoothEmbedding_fromOpen (𝓡∂ 3) (𝓡 3) N (D.symm ∘ ρ) hN
  have he : Subtype.val ∘ (D.symm ∘ ρ) =
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
    funext x
    let p : N := ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩
    have hp : D p = ρ x := Subtype.ext (finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b x)
    change (D.symm (ρ x)).val = p.val
    rw [← hp, D.symm_apply_apply]
  exact he ▸ hQ

include hs in
theorem finiteRetainedCapInclusion_isSmoothEmbedding
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} =>
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩ : finiteCapRetained hL hδ f hf hdisj R)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CapBallSmoothQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact isSmoothEmbedding_intoOpen (𝓡∂ 3) (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R) _
    (finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b)

include hs in
theorem finiteDiscardedCapInclusion_isSmoothEmbedding
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool)
    (hb : cuttingSphereComponent hδ f hf hdisj b ∉ R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CapBallSmoothE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CapBallSmoothE3 CapBallSmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (fun x : {x : CapBallSmoothE3 // ‖x‖ ≤ L} =>
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, hb⟩ : finiteCapDiscarded hL hδ f hf hdisj R)) :=
  finiteRetainedCapInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs Rᶜ b hb
end DifferentialGeometry.Topology.ThreeManifold.Surgery
