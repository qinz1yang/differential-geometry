import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceInhabitants

/-!
# Boundary route interfaces, part 6: the direct corollaries (lane BIFACE, G3)

The rows of the frozen target text
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` that follow directly
from the definitions of the interfaces (no producer input):

* A3g `BoundaryGaf02Chain.Ψ_sub_mem_stageQ_BIF`: (ADJ) keeps the orthogonal coordinates,
  `Ψ_j z − z ∈ Q_j^∂` (closed twin `Gaf02Chain.keeps_orthogonal_coordinates`);
* F2 `BoundaryGaf02Chain.cuspFront_saturated_BIF`: (Sat) on ALL of `W` — every stage projection
  keeps the whole boundary block, so `π_j E q = π_j E p`, `p ∈ H_b` give `q ∈ H_b` (draft 61 §5.3);
* F4a `BoundaryInitialCoresSpec.isCompact_M₁_BIF`: `M₁` is compact (closed in compact `W`);
* G2 `BoundaryCompactSlimChoice.cover_BIF`: BCF01's `W = Z ∪ C_∂ ∪ S ∪ M₂`;
* G6 (part) `BoundaryCompactSlimChoice.M₂_eq_edgePiece_union_remainder_BIF`: `M₂ = P_e ∪ R_c`;
* helpers `relInterior_subset_BIF`, `relInterior_subset_left_BIF`,
  `BoundaryInteriorSlots_BIF.boundaryCoord_stageProj_BIF` (`J_b ∘ π_j = J_b`).

Consumer: the same statements on the empty-family inhabitants (`emptyDecomposition_BIF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The relative interior lies in the set. -/
theorem relInterior_subset_BIF {X : Type*} [TopologicalSpace X] (Y Z : Set X) :
    relInterior_BIF Y Z ⊆ Z := by
  rintro _ ⟨y, hy, rfl⟩
  exact (interior_subset hy : y ∈ Subtype.val ⁻¹' Z)

/-- The relative interior lies in the ambient piece. -/
theorem relInterior_subset_left_BIF {X : Type*} [TopologicalSpace X] (Y Z : Set X) :
    relInterior_BIF Y Z ⊆ Y := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
    W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- Every stage projection keeps the whole boundary block: `J_b ∘ π_j = J_b`. -/
theorem BoundaryInteriorSlots_BIF.boundaryCoord_stageProj_BIF (Φ : BoundaryInteriorSlots_BIF S)
    (st : Fin 3) (i : Fin S.packet.cusp.count)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    augmentedBoundaryCoord_BC7C i (Φ.stageProj st x) = augmentedBoundaryCoord_BC7C i x := by
  have hmem : (Sum.inr i : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈ Φ.stageTagsAug st := by
    simp [BoundaryInteriorSlots_BIF.stageTagsAug]
  have h : Φ.stageProj st x (Sum.inr i) = x (Sum.inr i) := by
    simp [BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hmem]
  simp only [augmentedBoundaryCoord_BC7C, h]

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S Φ} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **A3g, (ADJ) keeps the orthogonal coordinates**: `Ψ_j z − z ∈ Q_j^∂`. -/
theorem Ψ_sub_mem_stageQ_BIF (st : Fin 3)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    C.Ψ st z - z ∈ Φ.stageQ st := by
  simp only [BoundaryGaf02Chain.Ψ, BoundaryInteriorSlots_BIF.adjust, adjustmentMap_apply,
    add_sub_cancel_left]
  exact (Φ.stageQ st).smul_mem _ ((Φ.stageQ st).sub_mem
    ((Φ.stageQ st).starProjection_apply_mem _) ((Φ.stageQ st).starProjection_apply_mem _))

/-- **F2, (Sat) on all of `W`**: `p ∈ H_b` and `π_j E q = π_j E p` give `q ∈ H_b` (every `q ∈ W`;
no fibre connectedness). -/
theorem cuspFront_saturated_BIF (st : Fin 3) (i : Fin S.packet.cusp.count) {p q : W.Carrier}
    (hp : p ∈ C.cuspFront_BIF i) (hpq : C.stageMap st q = C.stageMap st p) :
    q ∈ C.cuspFront_BIF i := by
  have hJ : C.markerPair i q = C.markerPair i p := by
    have h := congrArg (augmentedBoundaryCoord_BC7C i) hpq
    simp only [BoundaryGaf02Chain.stageMap, Φ.boundaryCoord_stageProj_BIF] at h
    exact h
  change (9 / 10 : ℝ) ≤ (C.markerPair i q).2 ∧ (C.markerPair i q).1 = 40 * (C.markerPair i q).2
  rw [hJ]
  exact hp

end BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S Φ} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **F4a**: `M₁ = W \ int_W(Z ∪ C_∂)` is compact. -/
theorem BoundaryInitialCoresSpec.isCompact_M₁_BIF (ZC : BoundaryInitialCoresSpec C) :
    IsCompact ZC.M₁ :=
  isOpen_interior.isClosed_compl.isCompact

namespace BoundaryCompactSlimChoice

variable {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}
  (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- **G2, BCF01's cover**: `W = Z ∪ C_∂ ∪ S ∪ M₂`. -/
theorem cover_BIF : ZC.union ∪ C.cuspCores_BIF ∪ Kc.piece ∪ Kc.M₂ = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases h1 : x ∈ interior (ZC.union ∪ C.cuspCores_BIF)
  · exact Or.inl (Or.inl (interior_subset h1))
  · have hM₁ : x ∈ ZC.M₁ := h1
    by_cases h2 : x ∈ relInterior_BIF ZC.M₁ Kc.piece
    · exact Or.inl (Or.inr (relInterior_subset_BIF _ _ h2))
    · exact Or.inr ⟨hM₁, h2⟩

/-- **G6 (part), BCF02's cover**: `M₂ = P_e ∪ R_c`. -/
theorem M₂_eq_edgePiece_union_remainder_BIF : Kc.M₂ = Kc.edgePiece ∪ Kc.remainder := by
  refine Subset.antisymm (fun x hx => ?_) (union_subset (fun x hx => hx.1) fun x hx => hx.1)
  by_cases h : x ∈ relInterior_BIF Kc.M₂ Kc.edgePiece
  · exact Or.inl (relInterior_subset_BIF _ _ h)
  · exact Or.inr ⟨hx, h⟩

end BoundaryCompactSlimChoice

/-- **Consumer**: the corollaries on the empty-family decomposition of a supply (empty stage and
zero centres, `F_∂` continuous): the cover `W = Z ∪ C_∂ ∪ S ∪ M₂`, compact `M₁`,
`M₂ = P_e ∪ R_c`. -/
theorem emptyDecomposition_corollaries_BIF {D : BoundaryAugmentedData S S.emptySlots_BIF}
    (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    (C.emptyDecomposition_BIF hc hF hz0).zero.union ∪ C.cuspCores_BIF ∪
        (C.emptyDecomposition_BIF hc hF hz0).slim.piece ∪
        (C.emptyDecomposition_BIF hc hF hz0).slim.M₂ = univ ∧
      IsCompact (C.emptyDecomposition_BIF hc hF hz0).zero.M₁ ∧
      (C.emptyDecomposition_BIF hc hF hz0).slim.M₂ =
        (C.emptyDecomposition_BIF hc hF hz0).slim.edgePiece ∪
          (C.emptyDecomposition_BIF hc hF hz0).slim.remainder :=
  ⟨(C.emptyDecomposition_BIF hc hF hz0).slim.cover_BIF,
    (C.emptyDecomposition_BIF hc hF hz0).zero.isCompact_M₁_BIF,
    (C.emptyDecomposition_BIF hc hF hz0).slim.M₂_eq_edgePiece_union_remainder_BIF⟩

end DifferentialGeometry.Geometry.Collapse
