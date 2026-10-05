import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlot
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageNativeOutput

/-!
# BCG03: the ACTUAL slot of the boundary chain, v2 — closed stage tags (lane BAUG-D, A0 v2)

Lead decision (B) (2026-10-05, on review 69 D69-5 / D69-6): the stage subspaces follow the CLOSED
pattern verbatim (`gafStageTags`: `Q₁ = all`, `Q₂ = cgpQ2Tags`, `Q₃ = cgpQ3Tags`), i.e. the scale
block is a tag of stage `0` only; the later two adjustments then keep the scale slot (and the `E'`
slot and the circle blocks), so `s = ℓ_ρ(E) = ℓ_ρ(g₁)` is the first blend (A3f with `c₀`, EDP01's
early scale exit). Supersedes the stage tags of `actualSlots_BAUGD` (v1, `BoundaryActualSlot.lean`,
which had the scale tag in every stage); the stage cores, enlargements and cutoffs are the SAME
definitions.

* `stageTagsV2_BAUGD`: `Q₁^∂` = all interior tags; `Q₂^∂` = slim, `edgeB`, zero; `Q₃^∂` = slim,
  zero (`inQ2V2_BAUGD`, `inQ3V2_BAUGD` = closed `cgpInQ2`, `cgpInQ3`).
* **`actualSlotsV2_BAUGD S`** (THE entry): stage tags `stageTagsV2_BAUGD`, cores
  `⋃ markerCore7_BAUGC`, enlargements `⋃ markerCore8_BAUGD`, cutoffs `cutoffZero/One/Two_BAUGD`.
* Read-offs (A0a and the slot contract of D69-6): `actualSlotsV2_stageCore_BAUGD` (A0a, `rfl`),
  `…_stageEnlargement_…`, `…_cutoff_…`, `…_cloud_subset_…`, `actualSlotsV2_scale_kept_BAUGD`
  (stage `0` only), the membership lemmas, the empty-family lemmas; the NESTING / preservation
  contract: `stageTagsV2_two_subset_one_BAUGD` (`Q₃ ⊆ Q₂`), `scaleTag_notMem_stageTagsV2_BAUGD`,
  `edgeTag_notMem_stageTagsV2_BAUGD`, `circleTag_notMem_stageTagsV2_BAUGD` (`st ≠ 0`),
  `edgeBTag_notMem_stageTagsV2_two_BAUGD`, `slimTag_mem_stageTagsV2_BAUGD`, and the actual cutoff's
  coordinate dependence `cutoffTwo_stageProj_BAUGD` (`ψ₂ ∘ π_j = ψ₂`, `j = 1, 2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- Membership of an interior tag in `Q₂^∂ = H₀ ⊕ H_s ⊕ H_e` (closed `cgpInQ2`): slim, `edgeB` and
zero blocks. -/
def inQ2V2_BAUGD : S.IntTag_BAUGA → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- Membership of an interior tag in `Q₃^∂ = H₀ ⊕ H_s` (closed `cgpInQ3`): slim and zero blocks. -/
def inQ3V2_BAUGD : S.IntTag_BAUGA → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- **The interior stage tags, closed pattern** `Q₁^∂ = all`, `Q₂^∂`, `Q₃^∂`. -/
def stageTagsV2_BAUGD : Fin 3 → Finset S.IntTag_BAUGA :=
  ![Finset.univ, Finset.univ.filter fun t => S.inQ2V2_BAUGD t = true,
    Finset.univ.filter fun t => S.inQ3V2_BAUGD t = true]

variable {S} in
/-- Membership in the stage-`1` tags. -/
theorem mem_stageTagsV2_one_BAUGD {t : S.IntTag_BAUGA} :
    t ∈ S.stageTagsV2_BAUGD 1 ↔ S.inQ2V2_BAUGD t = true := by
  change t ∈ Finset.univ.filter _ ↔ _
  simp

variable {S} in
/-- Membership in the stage-`2` tags. -/
theorem mem_stageTagsV2_two_BAUGD {t : S.IntTag_BAUGA} :
    t ∈ S.stageTagsV2_BAUGD 2 ↔ S.inQ3V2_BAUGD t = true := by
  change t ∈ Finset.univ.filter _ ↔ _
  simp

/-- **Nesting** `Q₃^∂ ⊆ Q₂^∂ ⊆ Q₁^∂` on the interior tags. -/
theorem stageTagsV2_two_subset_one_BAUGD : S.stageTagsV2_BAUGD 2 ⊆ S.stageTagsV2_BAUGD 1 := by
  intro t ht
  have ht' := mem_stageTagsV2_two_BAUGD.mp ht
  refine mem_stageTagsV2_one_BAUGD.mpr ?_
  rcases t with t | t | t | t | t <;> simp_all [inQ2V2_BAUGD, inQ3V2_BAUGD]

/-- The scale tag is a tag of stage `0` only. -/
theorem scaleTag_notMem_stageTagsV2_BAUGD {st : Fin 3} (hst : st ≠ 0) :
    S.scaleTag_BAUGA ∉ S.stageTagsV2_BAUGD st := by
  fin_cases st
  · exact absurd rfl hst
  · exact fun h => absurd (mem_stageTagsV2_one_BAUGD.mp h) (by simp [inQ2V2_BAUGD])
  · exact fun h => absurd (mem_stageTagsV2_two_BAUGD.mp h) (by simp [inQ3V2_BAUGD])

/-- The `E'` tag is a tag of stage `0` only. -/
theorem edgeTag_notMem_stageTagsV2_BAUGD {st : Fin 3} (hst : st ≠ 0) :
    S.edgeTag_BAUGA ∉ S.stageTagsV2_BAUGD st := by
  fin_cases st
  · exact absurd rfl hst
  · exact fun h => absurd (mem_stageTagsV2_one_BAUGD.mp h) (by simp [inQ2V2_BAUGD])
  · exact fun h => absurd (mem_stageTagsV2_two_BAUGD.mp h) (by simp [inQ3V2_BAUGD])

/-- The circle tags are tags of stage `0` only. -/
theorem circleTag_notMem_stageTagsV2_BAUGD {st : Fin 3} (hst : st ≠ 0)
    (j : S.CircleIdx_BAUGD) : (.inl j : S.IntTag_BAUGA) ∉ S.stageTagsV2_BAUGD st := by
  fin_cases st
  · exact absurd rfl hst
  · exact fun h => absurd (mem_stageTagsV2_one_BAUGD.mp h) (by simp [inQ2V2_BAUGD])
  · exact fun h => absurd (mem_stageTagsV2_two_BAUGD.mp h) (by simp [inQ3V2_BAUGD])

/-- The `edgeB` tags are not tags of stage `2`. -/
theorem edgeBTag_notMem_stageTagsV2_two_BAUGD (j : S.EdgeIdx_BAUGD) :
    (.inr (.inr (.inl j)) : S.IntTag_BAUGA) ∉ S.stageTagsV2_BAUGD 2 :=
  fun h => absurd (mem_stageTagsV2_two_BAUGD.mp h) (by simp [inQ3V2_BAUGD])

/-- The slim tags are tags of every stage. -/
theorem slimTag_mem_stageTagsV2_BAUGD (st : Fin 3) (j : S.SlimIdx_BAUGD) :
    (.inr (.inl j) : S.IntTag_BAUGA) ∈ S.stageTagsV2_BAUGD st := by
  fin_cases st
  · exact Finset.mem_univ _
  · exact mem_stageTagsV2_one_BAUGD.mpr rfl
  · exact mem_stageTagsV2_two_BAUGD.mpr rfl

end BoundarySupplyCore

/-- **A0 v2: the ACTUAL slot of the boundary chain** (closed stage tags; decision (B)): stage tags
`stageTagsV2_BAUGD`, stage cores = threshold-`7` cores of the stage's marker charts, enlargements =
their threshold-`8` cores, cutoffs `ψ₀, ψ₁, ψ₂` = CFS31's formulas on `H^∂` (the same definitions as
`actualSlots_BAUGD`). -/
def actualSlotsV2_BAUGD (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr
    e T V vs ζ Λz θ W g δn n B oM) : BoundaryInteriorSlots_BIF S where
  stageTags := S.stageTagsV2_BAUGD
  stageCore := fun st =>
    ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore7_BAUGC m
  stageEnlargement := fun st =>
    ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore8_BAUGD m
  cutoff := ![S.cutoffZero_BAUGD, S.cutoffOne_BAUGD, S.cutoffTwo_BAUGD]

section Slot

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **A0a** on the v2 slot: the stage cores are the threshold-`7` cores of the stage's marker
charts. -/
theorem actualSlotsV2_stageCore_BAUGD (st : Fin 3) :
    (actualSlotsV2_BAUGD S).stageCore st =
      ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore7_BAUGC m :=
  rfl

/-- The enlargements are the threshold-`8` cores of the stage's marker charts. -/
theorem actualSlotsV2_stageEnlargement_BAUGD (st : Fin 3) :
    (actualSlotsV2_BAUGD S).stageEnlargement st =
      ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore8_BAUGD m :=
  rfl

/-- The stage tags of the v2 slot. -/
theorem actualSlotsV2_stageTags_BAUGD : (actualSlotsV2_BAUGD S).stageTags = S.stageTagsV2_BAUGD :=
  rfl

/-- The cutoffs of the v2 slot: `ψ₀`, `ψ₁`, `ψ₂` (CFS31's formulas). -/
theorem actualSlotsV2_cutoff_BAUGD :
    (actualSlotsV2_BAUGD S).cutoff 0 = S.cutoffZero_BAUGD ∧
      (actualSlotsV2_BAUGD S).cutoff 1 = S.cutoffOne_BAUGD ∧
      (actualSlotsV2_BAUGD S).cutoff 2 = S.cutoffTwo_BAUGD :=
  ⟨rfl, rfl, rfl⟩

/-- The v2 slot has the same cores, enlargements and cutoffs as `actualSlots_BAUGD`. -/
theorem actualSlotsV2_eq_cores_BAUGD :
    (actualSlotsV2_BAUGD S).stageCore = (actualSlots_BAUGD S).stageCore ∧
      (actualSlotsV2_BAUGD S).stageEnlargement = (actualSlots_BAUGD S).stageEnlargement ∧
      (actualSlotsV2_BAUGD S).cutoff = (actualSlots_BAUGD S).cutoff :=
  ⟨rfl, rfl, rfl⟩

/-- `A_j ⊆ Ã_j` on the v2 slot (BAUG-C's `cloud_subset`). -/
theorem actualSlotsV2_cloud_subset_BAUGD (hΔ : 0 ≤ Δ) (st : Fin 3) :
    (actualSlotsV2_BAUGD S).stageCore st ⊆ (actualSlotsV2_BAUGD S).stageEnlargement st :=
  actualSlots_cloud_subset_BAUGD S hΔ st

/-- The actual stage cloud lies in the enlarged one. -/
theorem actualSlotsV2_stageCloud_subset_BAUGD (hΔ : 0 ≤ Δ) (st : Fin 3) :
    (actualSlotsV2_BAUGD S).stageCloud st ⊆ (actualSlotsV2_BAUGD S).stageCloudEnlarged st :=
  Set.image_mono (actualSlotsV2_cloud_subset_BAUGD S hΔ st)

/-- The scale block is kept in `Q₁^∂` (stage `0`; BAUG-C's `scale_kept` at `st = 0`). -/
theorem actualSlotsV2_scale_kept_BAUGD :
    S.scaleTag_BAUGA ∈ (actualSlotsV2_BAUGD S).stageTags 0 :=
  Finset.mem_univ _

/-- **Circle stage**: an original point in a threshold-`7` set of a circle centre lies in `A₀`. -/
theorem mem_actualSlotsV2_stageCore_circle_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 0)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 200 * S.rho j)
    (hη : ‖S.circleEta_BIF j q‖ ≤ 7) : q ∈ (actualSlotsV2_BAUGD S).stageCore 0 :=
  mem_actualSlots_stageCore_circle_BAUGD S hj hd hη

/-- **Edge stage**: an original point in a threshold-`7` set of an `edgeB` centre lies in `A₁`. -/
theorem mem_actualSlotsV2_stageCore_edge_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 1)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 100 * Δ * S.rho j)
    (hη : |S.edgeEta_BIF j q| ≤ 7 * Δ) (ht : S.edgeHeightRaw q ≤ 7 * Δ) :
    q ∈ (actualSlotsV2_BAUGD S).stageCore 1 :=
  mem_actualSlots_stageCore_edge_BAUGD S hj hd hη ht

/-- **Slim stage**: an original point in a threshold-`7` set of a slim centre lies in `A₂`. -/
theorem mem_actualSlotsV2_stageCore_slim_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 2)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 1000000 * Δ * S.rho j)
    (hη : |S.slimEta_BIF j q| ≤ 7 * (100000 * Δ)) : q ∈ (actualSlotsV2_BAUGD S).stageCore 2 :=
  mem_actualSlots_stageCore_slim_BAUGD S hj hd hη

/-- An empty stage family has an empty stage core and enlargement on the v2 slot. -/
theorem actualSlotsV2_eq_empty_of_stageCentres_BAUGD {st : Fin 3}
    (h : S.stageCentres_BIF st = ∅) :
    (actualSlotsV2_BAUGD S).stageCore st = ∅ ∧
      (actualSlotsV2_BAUGD S).stageEnlargement st = ∅ :=
  actualSlots_eq_empty_of_stageCentres_BAUGD S h

/-- The inactive slot of an empty stage family on any augmented data over the v2 slot. -/
def actualSlotsV2_inactiveSlot_BAUGD {D : BoundaryAugmentedData S (actualSlotsV2_BAUGD S)}
    {st : Fin 3} (h : S.stageCentres_BIF st = ∅) (Kj : ℕ) (Ξ sg cw : ℝ) :
    BoundaryStageSlot_BIF D st Kj Ξ sg cw :=
  .inactive (actualSlotsV2_eq_empty_of_stageCentres_BAUGD S h).1
    (actualSlotsV2_eq_empty_of_stageCentres_BAUGD S h).2

/-- A kept slim block: the slim vector of `π_st y` is that of `y`. -/
theorem slimVector_stageProj_BAUGD (st : Fin 3) (j : S.SlimIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.slimVector_BAUGD j ((actualSlotsV2_BAUGD S).stageProj st y) = S.slimVector_BAUGD j y := by
  have hmem : (Sum.inl (.inr (.inl j)) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug st :=
    Finset.inl_mem_disjSum.mpr (S.slimTag_mem_stageTagsV2_BAUGD st j)
  simp only [BoundarySupplyCore.slimVector_BAUGD, blockVectorCLM_apply,
    BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hmem, ite_true]

/-- A kept slim block: the slim marker of `π_st y` is that of `y`. -/
theorem slimMarker_stageProj_BAUGD (st : Fin 3) (j : S.SlimIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj st y) = S.slimMarker_BAUGD j y := by
  have hmem : (Sum.inl (.inr (.inl j)) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug st :=
    Finset.inl_mem_disjSum.mpr (S.slimTag_mem_stageTagsV2_BAUGD st j)
  exact blockMarkerCLM_blockRestrict_BAUGC _ hmem y

/-- **The actual third cutoff reads only slim blocks**: `ψ₂ ∘ π_st = ψ₂` for every stage
(closed `ActualStageChainLater`: from the cutoff's coordinate dependence, not from `Q₃ ⊆ Q₂`). -/
theorem cutoffTwo_stageProj_BAUGD (st : Fin 3)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.cutoffTwo_BAUGD ((actualSlotsV2_BAUGD S).stageProj st y) = S.cutoffTwo_BAUGD y := by
  simp only [BoundarySupplyCore.cutoffTwo_BAUGD, cfsUniformAxisCutoff, cfsAxisGate,
    slimVector_stageProj_BAUGD, slimMarker_stageProj_BAUGD]

end Slot

end DifferentialGeometry.Geometry.Collapse
