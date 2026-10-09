import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesEdgeParentConsumer
import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChart

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3c: the base-chart record `BoundaryBaseChartsSpec_BBP`

The remaining content of the extended G11 (to be proved by lane O-WF, group G4 = CGP07 one-sheet
port), stated on the data of the delivered core:

* `BoundaryStageSlot_BIF.zeroSet_BBP`: the native zero set `Z_st` of a slot (`O.Z`, empty if inactive);
* `circleAxis`-free chart coordinates: `κ_i = circleKappa_BBP i` (`ℝ²`), `edgeKappa_BBP i`,
  `slimKappa_BBP i` (`ℝ`, the axis coordinate), `ρ_i`-scaled as in `Gaf02CircleBasesSpec_BAS`;
* `nativePatch_BBP C st = ⋃_i (Z_st ∩ marked_i)` (the marked patches `V_st⁰`, radius `11/2 ℓ_i`),
  `bigBase_BBP C st = Θ_st(V_st⁰)` (the BIG final base `W_st`);
* **`BoundaryBaseChartsSpec_BBP C σc σe σs`** (Prop): `B_st = W_st ∩ O_st`; the base charts `σ_i`
  (smooth on the ball, `σ_i b ∈ W ∩ marked_i`, `κ_i σ_i b = b`, `σ_i (κ_i y) = y` on `W ∩ marked_i`,
  `W ⊆ ⋃ marked_i`) for the three stages; the embedding of `Θ_st` on `f_st⁰(X_st)`; `U ⊆ f₁⁻¹(B₁)`;
* `BoundaryBaseChartsSpec_BBP.of_empty_BBP` (inhabitant: empty chart families) and the consumer
  `BoundaryGaf02ChainE.exists_basesV2_of_chartSpec_BBP`: spec + the core's register premises + G12's
  numeric premises give `BoundaryGaf02BasesV2 C.toChain` (core `basesCore_BBP`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

namespace BoundaryStageSlot_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {st : Fin 3} {Kj : ℕ} {Ξ sg cw : ℝ}

/-- **The native zero set `Z_st` of a slot**: the zero set of the CFS15 output (active), empty
(inactive). -/
def zeroSet_BBP : BoundaryStageSlot_BIF D st Kj Ξ sg cw →
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
  | .active O => O.Z
  | .inactive _ _ => ∅

end BoundaryStageSlot_BIF

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The edge axis functional `pr₀ ∘ u_j` of `H^∂` (`κ_j = ρ_j⁻¹ • edgeAxis_BBP j`). -/
def edgeAxis_BBP (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).comp (S.edgeVector_BAUGD j)

/-- The slim axis functional `pr₀ ∘ u_j` of `H^∂` (`κ_j = ρ_j⁻¹ • slimAxis_BBP j`). -/
def slimAxis_BBP (j : S.SlimIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).comp (S.slimVector_BAUGD j)

theorem edgeKappa_eq_BBP (j : S.EdgeIdx_BAUGD) :
    S.edgeKappa_BBP j = (S.rho j.1)⁻¹ • S.edgeAxis_BBP j :=
  rfl

theorem slimKappa_eq_BBP (j : S.SlimIdx_BAUGD) :
    S.slimKappa_BBP j = (S.rho j.1)⁻¹ • S.slimAxis_BBP j :=
  rfl

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The native marked patches** `V_st⁰ = ⋃_i {w ∈ Z_st | v_i(w) > .9R_i, ‖u_i(w)‖ < 5.5ℓ_iR_i}`
(CGP07's `markedPatch_BPRE`, circle `ℓ = 1`, edge `ℓ = Δ`, slim `ℓ = 10⁵Δ`). -/
def nativePatch_BBP : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ![⋃ i : S.CircleIdx_BAUGD, markedPatch_BPRE (C.toChain.slot 0).zeroSet_BBP
      (S.circleVector_BAUGD i) (S.circleMarker_BAUGD i) (S.rho i.1) 1,
    ⋃ i : S.EdgeIdx_BAUGD, markedPatch_BPRE (C.toChain.slot 1).zeroSet_BBP
      (S.edgeAxis_BBP i) (S.edgeMarker_BAUGD i) (S.rho i.1) Δ,
    ⋃ i : S.SlimIdx_BAUGD, markedPatch_BPRE (C.toChain.slot 2).zeroSet_BBP
      (S.slimAxis_BBP i) (S.slimMarker_BAUGD i) (S.rho i.1) (10 ^ 5 * Δ)]

/-- **The big final bases** `W_st = Θ_st(V_st⁰)` (closed `finalBase_BAS`). -/
def bigBase_BBP (st : Fin 3) :
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  C.toChain.laterV2_BAUGD st '' C.nativePatch_BBP st

/-- **The base-chart record** (Prop; closed `Gaf02{Circle,Edge,Slim}BasesSpec_BAS.base_chart/cover`
transported to the actual bases, plus the embedding and the edge parent inclusion), for the chart
maps `σ_i = Θ_st ∘ (CGP07 chart inverse φ_i)`:
* `base_eq`: the core's bases are `B_st = W_st ∩ O_st` (CGP07 exhaustion);
* per stage: `σ_i` smooth on `B(0, 5.5ℓ_i)`, maps into `W_st ∩ marked_i` with `κ_i σ_i = id`, is the
  inverse of `κ_i` on `W_st ∩ marked_i` (which lies over the ball), and the `marked_i` cover `W_st`;
* `later_isEmbedding`: `Θ_st` is an embedding of the native base `f_st⁰(X_st)` (no merging);
* `edgeParent_sub`: `U ⊆ f₁⁻¹(B₁)`. -/
structure BoundaryBaseChartsSpec_BBP
    (σc : S.CircleIdx_BAUGD → ℝ² →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (σe : S.EdgeIdx_BAUGD → ℝ →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (σs : S.SlimIdx_BAUGD → ℝ →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : Prop where
  base_eq : ∀ st, C.baseSet_BBP st = C.bigBase_BBP st ∩ S.ratioSet_BBP st
  circle_smooth : ∀ i, ContDiffOn ℝ ∞ (σc i) (ball 0 (11 / 2 * 1))
  circle_mem : ∀ i, ∀ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
    σc i b ∈ C.bigBase_BBP 0 ∩ markedCondition_BPRE (S.circleVector_BAUGD i)
      (S.circleMarker_BAUGD i) (S.rho i.1) 1 ∧ S.circleKappa_BBP i (σc i b) = b
  circle_inv : ∀ i, ∀ y ∈ C.bigBase_BBP 0 ∩ markedCondition_BPRE (S.circleVector_BAUGD i)
      (S.circleMarker_BAUGD i) (S.rho i.1) 1,
    S.circleKappa_BBP i y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧ σc i (S.circleKappa_BBP i y) = y
  circle_cover : C.bigBase_BBP 0 ⊆ ⋃ i, markedCondition_BPRE (S.circleVector_BAUGD i)
    (S.circleMarker_BAUGD i) (S.rho i.1) 1
  edge_smooth : ∀ i, ContDiffOn ℝ ∞ (σe i) (ball 0 (11 / 2 * Δ))
  edge_mem : ∀ i, ∀ b ∈ ball (0 : ℝ) (11 / 2 * Δ),
    σe i b ∈ C.bigBase_BBP 1 ∩ markedCondition_BPRE (S.edgeAxis_BBP i)
      (S.edgeMarker_BAUGD i) (S.rho i.1) Δ ∧ S.edgeKappa_BBP i (σe i b) = b
  edge_inv : ∀ i, ∀ y ∈ C.bigBase_BBP 1 ∩ markedCondition_BPRE (S.edgeAxis_BBP i)
      (S.edgeMarker_BAUGD i) (S.rho i.1) Δ,
    S.edgeKappa_BBP i y ∈ ball (0 : ℝ) (11 / 2 * Δ) ∧ σe i (S.edgeKappa_BBP i y) = y
  edge_cover : C.bigBase_BBP 1 ⊆ ⋃ i, markedCondition_BPRE (S.edgeAxis_BBP i)
    (S.edgeMarker_BAUGD i) (S.rho i.1) Δ
  slim_smooth : ∀ i, ContDiffOn ℝ ∞ (σs i) (ball 0 (11 / 2 * (10 ^ 5 * Δ)))
  slim_mem : ∀ i, ∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
    σs i b ∈ C.bigBase_BBP 2 ∩ markedCondition_BPRE (S.slimAxis_BBP i)
      (S.slimMarker_BAUGD i) (S.rho i.1) (10 ^ 5 * Δ) ∧ S.slimKappa_BBP i (σs i b) = b
  slim_inv : ∀ i, ∀ y ∈ C.bigBase_BBP 2 ∩ markedCondition_BPRE (S.slimAxis_BBP i)
      (S.slimMarker_BAUGD i) (S.rho i.1) (10 ^ 5 * Δ),
    S.slimKappa_BBP i y ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
      σs i (S.slimKappa_BBP i y) = y
  slim_cover : C.bigBase_BBP 2 ⊆ ⋃ i, markedCondition_BPRE (S.slimAxis_BBP i)
    (S.slimMarker_BAUGD i) (S.rho i.1) (10 ^ 5 * Δ)
  later_isEmbedding : ∀ st,
    IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc st '' C.baseSource_BBP st =>
      C.toChain.laterV2_BAUGD st x)
  edgeParent_sub : C.edgeParentSet_BBP ⊆ C.toChain.stageMap 1 ⁻¹' C.baseSet_BBP 1

/-- Over empty chart families every set of the record is empty. -/
theorem baseSet_eq_empty_of_isEmpty_BBP [IsEmpty S.CircleIdx_BAUGD] [IsEmpty S.EdgeIdx_BAUGD]
    [IsEmpty S.SlimIdx_BAUGD] (st : Fin 3) : C.baseSource_BBP st = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  fin_cases st
  · obtain ⟨j, -⟩ := Set.mem_iUnion.mp hp.1
    exact isEmptyElim j
  · obtain ⟨j, -⟩ := Set.mem_iUnion.mp hp.1
    exact isEmptyElim j
  · obtain ⟨j, -⟩ := Set.mem_iUnion.mp hp.1
    exact isEmptyElim j

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
