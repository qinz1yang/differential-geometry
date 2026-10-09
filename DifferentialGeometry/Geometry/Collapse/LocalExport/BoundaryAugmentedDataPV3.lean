import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpecV3

/-!
# BCG03: the augmented data with the V3 enhanced plane specs, `BoundaryAugmentedDataPV3` (BAUG-D)

Target A1 (text v3; lead decision (B)): `BoundaryAugmentedData S Φ` together with BAUG-C's V3 spec
(`BoundaryEnhancedPlaneSpecV3 R Γ sg eg`: no `scale_kept`; `radius_mcb` and `preimage_comparable`
for every stage) of each of the three stored stage tables, per-stage qualities `Γ j`, radius factors
`Sg j`, normal errors `eg j`. Supersedes `BoundaryAugmentedDataP` (BAUG-D G2', on the AGZ spec with
`scale_kept` at every stage — uninhabitable over the closed-tag slot `actualSlotsV2_BAUGD` once a
later stage is involved).

* `BoundaryAugmentedDataPV3 S Φ Γ Sg eg`, `BoundaryAugmentedDataPV3.spec` (the stage-indexed form
  `D.EnhancedPlaneSpecV3 Γ Sg eg st`, the input of `boundaryStage_output_V3_BAUGC`), the uniform
  accessors `preimage_comparable_BAUGD`, `cloud_subset_BAUGD`;
* inhabitant on the ACTUAL v2 slot: `exists_boundaryStageTableV3_of_empty_BAUGD`,
  `exists_boundaryAugmentedDataPV3_of_empty_BAUGD`.
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

/-- **A1 v2: the augmented data with the enhanced plane specs** (draft 61 §1.4 `plane_spec`,
D61-6): `BoundaryAugmentedData S Φ` and, for each stored stage table, BAUG-C's
`BoundaryEnhancedPlaneSpec` on its OWN (PDEF) plane at quality `Γ j`, radius factor `Sg j` and
normal error `eg j`. -/
structure BoundaryAugmentedDataPV3 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (Φ : BoundaryInteriorSlots_BIF S)
    (Γ Sg eg : Fin 3 → ℝ) extends BoundaryAugmentedData S Φ where
  /-- The circle table's spec. -/
  circle_spec : BoundaryEnhancedPlaneSpecV3 circle (Γ 0) (Sg 0) (eg 0)
  /-- The revised-edge table's spec. -/
  edge_spec : BoundaryEnhancedPlaneSpecV3 edge (Γ 1) (Sg 1) (eg 1)
  /-- The slim table's spec. -/
  slim_spec : BoundaryEnhancedPlaneSpecV3 slim (Γ 2) (Sg 2) (eg 2)

namespace BoundaryAugmentedDataPV3

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}

/-- The three specs in BAUG-C's stage-indexed form (the input of `boundaryStage_output_BAUGC`). -/
theorem spec (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    DP.toBoundaryAugmentedData.EnhancedPlaneSpecV3 Γ Sg eg st := by
  fin_cases st
  · exact DP.circle_spec
  · exact DP.edge_spec
  · exact DP.slim_spec

/-- **Two preimages of one enlarged-cloud point have comparable scales** (every stage; the V3
field `preimage_comparable`). -/
theorem preimage_comparable_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    ∀ x ∈ Φ.stageCloudEnlarged st, ∀ q₁ q₂ : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q₁.val) = x →
      Φ.stageProj st (S.boundaryOriginalMap q₂.val) = x → S.rho q₁ ≤ 5 / 3 * S.rho q₂ := by
  fin_cases st
  · exact DP.circle_spec.preimage_comparable
  · exact DP.edge_spec.preimage_comparable
  · exact DP.slim_spec.preimage_comparable

/-- `A_j ⊆ Ã_j` (every stage; the V3 field `cloud_subset`). -/
theorem cloud_subset_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    Φ.stageCore st ⊆ Φ.stageEnlargement st := by
  fin_cases st
  · exact DP.circle_spec.cloud_subset
  · exact DP.edge_spec.cloud_subset
  · exact DP.slim_spec.cloud_subset

end BoundaryAugmentedDataPV3

section Inhabitant

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **A stage table with the V3 enhanced plane spec on a slot with an empty stage**: if the stage
core and enlargement of `Φ` at `st` are empty, every coordinate / row family
has a stage table (the augmented (BM) model of the rows, `K_a = id`) with the spec at every
`Γ, sg, eg` (all cloud clauses vacuous). -/
theorem exists_boundaryStageTableV3_of_empty_BAUGD (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (hc : Φ.stageCore st = ∅) (he : Φ.stageEnlargement st = ∅)
    {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) (Γ sg eg : ℝ) :
    ∃ R : BoundaryStageReferences_BIF Φ st E eta row, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  have hE : ∀ x, x ∉ Φ.stageCloud st := fun x ⟨p, hp, _⟩ => by
    rw [hc] at hp; exact Set.notMem_empty p hp
  have hE' : ∀ x, x ∉ Φ.stageCloudEnlarged st := fun x ⟨p, hp, _⟩ => by
    rw [he] at hp; exact Set.notMem_empty p hp
  let R₀ : BoundaryStageReferences_BIF Φ st E eta row :=
    { planes :=
        { rpre := fun x => (hE' x.1 x.2).elim
          pre := fun x => (hE x.1 x.2).elim
          ref := fun x => (hE x.1 x.2).elim
          model := fun a => augmentedModel_BAUGC 0 (S.boundaryList_BIF st a)
            (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a))
          prune := fun _ => ContinuousLinearMap.id ℝ _
          coord := eta }
      ref_mem := fun x => (hE x.1 x.2).elim
      coord_eq := fun _ _ => rfl
      rpre_spec := fun x => (hE' x.1 x.2).elim
      pre_spec := fun x => (hE x.1 x.2).elim
      model_listed := fun a _ i hi z => by
        simp only [augmentedModel_apply_inr_BAUGC, augmentedBlocks_of_mem_BAUGC _ hi]
        rfl
      model_unlisted := fun a _ i hi z => by
        simp only [augmentedModel_apply_inr_BAUGC, augmentedBlocks_of_notMem_BAUGC _ hi,
          Pi.zero_apply, map_zero]
      prune_boundary := fun _ _ _ => rfl }
  refine ⟨R₀, ?_⟩
  exact
    { prune_slot := fun _ _ _ => rfl
      cloud_subset := by rw [hc]; exact Set.empty_subset _
      radius_mcb := fun _ _ _ _ _ x hx => (hE' x hx).elim
      preimage_comparable := fun x hx => (hE' x hx).elim
      dimension := fun x hx => (hE x hx).elim
      cloudy := fun _ _ x hx => (hE x hx).elim
      normal := fun x hx => (hE x hx).elim
      small_pp := fun x hx => (hE x hx).elim
      scale_zero := fun _ x hx => (hE x hx).elim
      small_block := fun x hx => (hE x hx).elim
      full_marker := fun _ _ _ _ _ _ _ _ _ _ y hy => (hE y hy).elim
      zero_block := fun _ _ _ _ _ _ _ hx => (hE _ hx).elim }

/-- **Inhabitant of A1 (V3) on the ACTUAL v2 slot**: a separated supply whose circle, `edgeB` and
slim families are empty has augmented data with the enhanced plane specs over
`actualSlotsV2_BAUGD S`, at every `Γ`, `Sg`, `eg` (stored rows / coordinates of `S`). -/
theorem exists_boundaryAugmentedDataPV3_of_empty_BAUGD (hsep : S.SeparatedCollarZero_BIF)
    (hempty : ∀ st, S.stageCentres_BIF st = ∅) (Γ Sg eg : Fin 3 → ℝ) :
    Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) := by
  have h0 := actualSlotsV2_eq_empty_of_stageCentres_BAUGD S (hempty 0)
  have h1 := actualSlotsV2_eq_empty_of_stageCentres_BAUGD S (hempty 1)
  have h2 := actualSlotsV2_eq_empty_of_stageCentres_BAUGD S (hempty 2)
  obtain ⟨Rc, hRc⟩ := exists_boundaryStageTableV3_of_empty_BAUGD S (actualSlotsV2_BAUGD S) 0
    h0.1 h0.2 S.circleEta_BIF S.circleRow_BIF (Γ 0) (Sg 0) (eg 0)
  obtain ⟨Re, hRe⟩ := exists_boundaryStageTableV3_of_empty_BAUGD S (actualSlotsV2_BAUGD S) 1
    h1.1 h1.2 S.edgeEta_BIF S.edgeRow_BIF (Γ 1) (Sg 1) (eg 1)
  obtain ⟨Rs, hRs⟩ := exists_boundaryStageTableV3_of_empty_BAUGD S (actualSlotsV2_BAUGD S) 2
    h2.1 h2.2 S.slimEta_BIF S.slimRow_BIF (Γ 2) (Sg 2) (eg 2)
  exact ⟨{ separated := hsep
           circle := Rc
           edge := Re
           slim := Rs
           circle_spec := hRc
           edge_spec := hRe
           slim_spec := hRs }⟩

end Inhabitant

end DifferentialGeometry.Geometry.Collapse
