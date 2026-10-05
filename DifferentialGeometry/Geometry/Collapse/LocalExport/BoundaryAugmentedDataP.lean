import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlot

/-!
# BCG03: the augmented data with the enhanced plane specs, `BoundaryAugmentedDataP` (BAUG-D, A1 v2)

Target A1 of `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary-A-v2.lean.txt`
(supersedes v1's A1, which was never in production): the augmented data `BoundaryAugmentedData S Φ`
together with BAUG-C's enhanced plane spec (G2', `BoundaryEnhancedPlaneSpec R Γ sg eg`, with the
normal clause) of each of the three stored stage tables, at qualities `Γ j`, radius factors `Sg j`
and normal errors `eg j` PER STAGE (D61-6: the plane is the (PDEF) plane of the SAME table). One
quality for all three stages is inconsistent with GAF01's CHOICE (`Ξ₀ b_der < c₀ ≤ 3Σ₁/10`,
`Σ₁ < Γ/200`, `Γ ≤ δ₀(Ξ₀) ≤ Ξ₀`), as on the closed side (`Γ j`).

* `BoundaryAugmentedDataP S Φ Γ Sg eg` (frozen structure; `Γ Sg eg : Fin 3 → ℝ`),
  `BoundaryAugmentedDataP.spec` (the three specs in BAUG-C's stage-indexed form
  `D.EnhancedPlaneSpec Γ Sg eg st`, the input of `boundaryStage_output_BAUGC`).
* Inhabitant on the ACTUAL slot: `exists_boundaryStageTable_of_empty_BAUGD` (a stage table with the
  spec on any slot whose stage core and enlargement are empty, the scale tag kept) and
  `exists_boundaryAugmentedDataP_of_empty_BAUGD` (every separated supply whose three stage families
  are empty has a `DP` over `actualSlots_BAUGD S`, at every `Γ Sg eg`).
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
structure BoundaryAugmentedDataP (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (Φ : BoundaryInteriorSlots_BIF S)
    (Γ Sg eg : Fin 3 → ℝ) extends BoundaryAugmentedData S Φ where
  /-- The circle table's spec. -/
  circle_spec : BoundaryEnhancedPlaneSpec circle (Γ 0) (Sg 0) (eg 0)
  /-- The revised-edge table's spec. -/
  edge_spec : BoundaryEnhancedPlaneSpec edge (Γ 1) (Sg 1) (eg 1)
  /-- The slim table's spec. -/
  slim_spec : BoundaryEnhancedPlaneSpec slim (Γ 2) (Sg 2) (eg 2)

namespace BoundaryAugmentedDataP

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}

/-- The three specs in BAUG-C's stage-indexed form (the input of `boundaryStage_output_BAUGC`). -/
theorem spec (DP : BoundaryAugmentedDataP S Φ Γ Sg eg) (st : Fin 3) :
    DP.toBoundaryAugmentedData.EnhancedPlaneSpec Γ Sg eg st := by
  fin_cases st
  · exact DP.circle_spec
  · exact DP.edge_spec
  · exact DP.slim_spec

end BoundaryAugmentedDataP

section Inhabitant

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **A stage table with the enhanced plane spec on a slot with an empty stage**: if the stage core
and enlargement of `Φ` at `st` are empty and the scale tag is kept, every coordinate / row family
has a stage table (the augmented (BM) model of the rows, `K_a = id`) with the spec at every
`Γ, sg, eg` (all cloud clauses vacuous). -/
theorem exists_boundaryStageTable_of_empty_BAUGD (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (hc : Φ.stageCore st = ∅) (he : Φ.stageEnlargement st = ∅)
    (hsc : S.scaleTag_BAUGA ∈ Φ.stageTags st) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) (Γ sg eg : ℝ) :
    ∃ R : BoundaryStageReferences_BIF Φ st E eta row, BoundaryEnhancedPlaneSpec R Γ sg eg := by
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
      scale_kept := hsc
      dimension := fun x hx => (hE x hx).elim
      cloudy := fun _ _ x hx => (hE x hx).elim
      normal := fun x hx => (hE x hx).elim
      small_pp := fun x hx => (hE x hx).elim
      scale_zero := fun _ x hx => (hE x hx).elim
      small_block := fun x hx => (hE x hx).elim
      full_marker := fun _ _ _ _ _ _ _ _ _ _ y hy => (hE y hy).elim
      zero_block := fun _ _ _ _ _ _ _ hx => (hE _ hx).elim }

/-- **Inhabitant of A1 v2 on the ACTUAL slot**: a separated supply whose circle, `edgeB` and slim
families are empty has augmented data with the enhanced plane specs over `actualSlots_BAUGD S`, at
every `Γ`, `Sg`, `eg` (stored rows / coordinates of `S`). -/
theorem exists_boundaryAugmentedDataP_of_empty_BAUGD (hsep : S.SeparatedCollarZero_BIF)
    (hempty : ∀ st, S.stageCentres_BIF st = ∅) (Γ Sg eg : Fin 3 → ℝ) :
    Nonempty (BoundaryAugmentedDataP S (actualSlots_BAUGD S) Γ Sg eg) := by
  have h0 := actualSlots_eq_empty_of_stageCentres_BAUGD S (hempty 0)
  have h1 := actualSlots_eq_empty_of_stageCentres_BAUGD S (hempty 1)
  have h2 := actualSlots_eq_empty_of_stageCentres_BAUGD S (hempty 2)
  obtain ⟨Rc, hRc⟩ := exists_boundaryStageTable_of_empty_BAUGD S (actualSlots_BAUGD S) 0 h0.1 h0.2
    (actualSlots_scale_kept_BAUGD S 0) S.circleEta_BIF S.circleRow_BIF (Γ 0) (Sg 0) (eg 0)
  obtain ⟨Re, hRe⟩ := exists_boundaryStageTable_of_empty_BAUGD S (actualSlots_BAUGD S) 1 h1.1 h1.2
    (actualSlots_scale_kept_BAUGD S 1) S.edgeEta_BIF S.edgeRow_BIF (Γ 1) (Sg 1) (eg 1)
  obtain ⟨Rs, hRs⟩ := exists_boundaryStageTable_of_empty_BAUGD S (actualSlots_BAUGD S) 2 h2.1 h2.2
    (actualSlots_scale_kept_BAUGD S 2) S.slimEta_BIF S.slimRow_BIF (Γ 2) (Sg 2) (eg 2)
  exact ⟨{ separated := hsep
           circle := Rc
           edge := Re
           slim := Rs
           circle_spec := hRc
           edge_spec := hRe
           slim_spec := hRs }⟩

end Inhabitant

end DifferentialGeometry.Geometry.Collapse
