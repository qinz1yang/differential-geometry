import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasOfImmersionBCF

/-!
# A graph atlas of the boundary slim base from the whole-fibre layer (lane B-BCF134)

Text v3 A4b asks for a graph atlas of `B₃` (the shared `K₃` kernel's input). From the whole-fibre layer
`WF : BoundaryWholeFiberSpecV2 C Bs`, every point of `B₃` carries a slim product chart whose base
parametrization `σ : ℝ¹ → H` is a smooth embedding with injective differential onto `B₃ ∩ O`; by
`exists_graphAtlas_of_immersions_BCF` this gives a graph atlas of `B₃` indexed by its points
(`BoundaryWholeFiberSpecV2.slimBase_graphAtlas_BCF`). Text v3's A4b (stated on `Bs` alone, finite index)
remains BAUG-Dd's; this is the `WF` route used by BCF01 G1.

Consumers: `BoundaryGaf02Chain.emptySlimBase_graphAtlas_BCF` (the empty family) and the non-vacuous generic
`exists_graphAtlas_euclidLine_BCF` (`ℝ¹` itself, `σ = id`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

section ProductChart

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace M] [ChartedSpace HM M] {IM : ModelWithCorners ℝ EM HM}
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  [TopologicalSpace F] [ChartedSpace HF F] {IF : ModelWithCorners ℝ EF HF}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The base parametrization of a product chart over a one-dimensional base. -/
theorem SmoothProductChartAt_BIFc.exists_base_immersion_BCF {f : M → H} {X : Set M} {Bs : Set H}
    {y : H} (h : SmoothProductChartAt_BIFc IM IF (F := F) 1 f X Bs y) :
    ∃ (σ : EuclideanSpace ℝ (Fin 1) → H) (O : Set H), σ 0 = y ∧ ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧
      (∀ x, Injective (fderiv ℝ σ x)) ∧ IsOpen O ∧ range σ = Bs ∩ O := by
  obtain ⟨σ, -, O, h0, hs, he, hi, hO, hr, -⟩ := h
  exact ⟨σ, O, h0, hs, he, hi, hO, hr⟩

end ProductChart

/-- **A graph atlas of the slim base** from the whole-fibre layer. -/
theorem BoundaryWholeFiberSpecV2.slimBase_graphAtlas_BCF {Φ : BoundaryInteriorSlots_BIF S}
    {D : BoundaryAugmentedData S Φ} {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (WF : BoundaryWholeFiberSpecV2 C Bs) :
    Nonempty (GraphAtlas1_BCF (Bs.base 2) (Bs.base 2)) := by
  refine exists_graphAtlas_of_immersions_BCF fun y hy => ?_
  rcases WF.slim_chart y hy with h | h
  · exact h.exists_base_immersion_BCF
  · exact h.exists_base_immersion_BCF

/-- **Consumer of the generic construction** (non-vacuous): `ℝ¹` has a graph atlas from `σ = id`. -/
theorem exists_graphAtlas_euclidLine_BCF :
    Nonempty (GraphAtlas1_BCF (univ : Set (EuclideanSpace ℝ (Fin 1)))
      (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  refine exists_graphAtlas_of_immersions_BCF fun y _ => ⟨fun x => x + y, univ, by simp, ?_, ?_, ?_,
    isOpen_univ, ?_⟩
  · exact contDiff_id.add contDiff_const
  · exact (Homeomorph.addRight y).isEmbedding
  · intro x
    rw [fderiv_add_const, fderiv_fun_id]
    exact injective_id
  · rw [univ_inter]
    exact (Equiv.addRight y).surjective.range_eq

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **Consumer**: the slim base of the empty v2 bases has a graph atlas from its whole-fibre layer. -/
theorem emptySlimBase_graphAtlas_BCF :
    Nonempty (GraphAtlas1_BCF ((C.emptyBasesV2_BIFc hc hF).base 2)
      ((C.emptyBasesV2_BIFc hc hF).base 2)) :=
  (C.emptyWholeFiberSpecV2_BIFc hc hF).slimBase_graphAtlas_BCF

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
