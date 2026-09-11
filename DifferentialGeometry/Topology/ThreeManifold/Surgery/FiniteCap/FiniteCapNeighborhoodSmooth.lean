import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SmoothE3 := EuclideanSpace ℝ (Fin 3)
private abbrev SmoothIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph SmoothIC I ∞ (f i)) (b : ι × Bool)
local notation "NeighborhoodQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapNeighborhoodOpens : Opens NeighborhoodQ :=
  ⟨finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b,
    isOpen_finiteCapNeighborhood hL hδ f hf hdisj b⟩

def finiteCapRadialBall : Opens SmoothE3 :=
  ⟨{x | ‖x‖ < L + cuttingCollarWidth (precision b.1)}, isOpen_lt continuous_norm continuous_const⟩

def finiteCapNeighborhoodDiffeomorph :
    let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph (𝓡 3) (𝓡 3) (finiteCapNeighborhoodOpens hL hδ f hf hdisj b)
      (finiteCapRadialBall (L := L) (precision := precision) b) ∞ := by
  let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ NeighborhoodQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let U := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let e : U ≃ₜ V := finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
  let c := finiteCapOpenChart hL hδ f hf hdisj b
  have hc : c ∈ maximalAtlas (𝓡 3) ∞ NeighborhoodQ :=
    StructureGroupoid.subset_maximalAtlas _ (show c ∈ @ChartedSpace.atlas SmoothE3 _ NeighborhoodQ _ (finiteCapChartedSpace I hdim hL hδ f hf hdisj) from Or.inr ⟨b, rfl⟩)
  have hsource (p : U) : p.val ∈ c.source := by
    rw [finiteCapOpenChart_source]
    exact p.property
  have htarget (x : V) : x.val ∈ c.target := by
    rw [finiteCapOpenChart_target]
    exact x.property
  have hforward (p : U) : c p.val = (e p).val := finiteCapOpenChart_apply hL hδ f hf hdisj b p
  have hinverse (x : V) : (e.symm x).val = c.symm x.val := by
    have he := c.left_inv (hsource (e.symm x))
    rw [hforward, e.apply_symm_apply] at he
    exact he.symm
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff V e).mp
    intro p
    have h := (contMDiffAt_of_mem_maximalAtlas hc (hsource p)).comp p
      (contMDiff_subtype_val (U := U)).contMDiffAt
    apply h.congr_of_eventuallyEq
    filter_upwards with q
    exact (hforward q).symm
  · apply (ContMDiff.subtypeVal_comp_iff U e.symm).mp
    intro x
    have h := (contMDiffAt_symm_of_mem_maximalAtlas hc (htarget x)).comp x
      (contMDiff_subtype_val (U := V)).contMDiffAt
    apply h.congr_of_eventuallyEq
    filter_upwards with y
    exact hinverse y

theorem finiteCapNeighborhoodDiffeomorph_apply (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b p =
      finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p := rfl

theorem finiteCapNeighborhoodDiffeomorph_symm_apply
    (x : finiteCapRadialBall (L := L) (precision := precision) b) :
    let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b).symm x =
      (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).symm x := rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
