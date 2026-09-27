import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapForwardTransition
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapReverseTransition
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapHomogeneousTransitions

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SmoothE3 := EuclideanSpace ℝ (Fin 3)
private abbrev SmoothIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ SmoothE3 = 2 + 1) := ⟨by simp⟩
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "SmoothQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem finiteCapQuotient_isManifold
    (hs : ∀ i, IsLocalDiffeomorph SmoothIC I ∞ (f i)) :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ SmoothQ := by
  let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply isManifold_of_contDiffOn (𝓡 3) ∞ SmoothQ
  intro e e' he he'
  change e ∈ range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ range (finiteCapOpenChart hL hδ f hf hdisj) at he
  change e' ∈ range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ range (finiteCapOpenChart hL hδ f hf hdisj) at he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, comp_id, id_comp, preimage_id, range_id, inter_univ]
  rcases he with ⟨p, rfl⟩ | ⟨b, rfl⟩
  · rcases he' with ⟨q, rfl⟩ | ⟨c, rfl⟩
    · exact contDiffOn_finiteCoreThree_transition hdim hL hδ f hf hdisj p q
    · exact contDiffOn_coreThree_to_finiteCap hdim hL hδ f hf hdisj hs c p
  · rcases he' with ⟨q, rfl⟩ | ⟨c, rfl⟩
    · exact contDiffOn_finiteCap_to_coreThree hdim hL hδ f hf hdisj (fun i => (hs i).contMDiff) b q
    · exact contDiffOn_finiteCap_transition hL hδ f hf hdisj b c

omit [IsManifold I ∞ M] in
theorem finiteCapQuotient_boundary_eq_empty :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (𝓡 3).boundary SmoothQ = ∅ := by
  let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

theorem finiteCapQuotient_isManifold_of_immersion
    (hs : ∀ i, ContMDiff SmoothIC I ∞ (f i))
    (hi : ∀ i x, Injective (mfderiv SmoothIC I (f i) x)) :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ SmoothQ :=
  finiteCapQuotient_isManifold hdim hL hδ f hf hdisj (fun i =>
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv (f i) (hs i) (hi i)
      (by rw [hdim]; simp))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
