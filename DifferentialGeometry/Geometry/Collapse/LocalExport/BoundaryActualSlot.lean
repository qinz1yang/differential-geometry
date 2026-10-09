import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceChain
import DifferentialGeometry.Analysis.Calculus.Cutoff.MarkerLocalitySourceCutoff
import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff
import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoff

/-!
# BCG03: the ACTUAL parameter slot of the boundary chain (lane BAUG-D, target A0 / A0a)

Frozen target text `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`
§A, A0 (`actualSlots_BAUGD`, "BAUG-C/D: the DEFINITION") and A0a (`actualSlots_stageCore_BAUGD`).
Every field of `actualSlots_BAUGD S : BoundaryInteriorSlots_BIF S` is a DEFINITION of the supply
`S` (draft 61 §2, §3.2, D61-4/6; closed pattern `gafStageTags`, `gafStageCore`,
`gafStageEnlargement`, `markerLocalitySourceCutoff`, `gafStageTwoCutoff`, `gafStageThreeCutoff`):

* `stageTags`: `Q₁^∂` = all interior tags; `Q₂^∂` = slim, `edgeB`, zero and scale tags;
  `Q₃^∂` = slim, zero and scale tags (`stageTags_BAUGD`). The closed pattern (`cgpQ2Tags`,
  `cgpQ3Tags`) plus the scale tag in every stage: BAUG-C's `BoundaryEnhancedPlaneSpec.scale_kept`
  (the (MCb) input of the native output) requires it.
* `stageCore st` = the union of the threshold-`7` cores `markerCore7_BAUGC m` of the marker charts
  of stage `st` (A0a holds by `rfl`); `stageEnlargement st` = the same union of the threshold-`8`
  cores `markerCore8_BAUGD m` (same balls).
* `cutoff`: CFS31's three formulas on `H^∂` read off the marker blocks of the active family —
  `ψ₀` the source cutoff (`markerLocalitySourceCutoff`, circle blocks), `ψ₁` CFS23's buffered edge
  cutoff (`cfsBufferedEdgeCutoff`, `edgeB` blocks, the scale marker, the `E'` block), `ψ₂` CFS22's
  uniform one-axis cutoff (`cfsUniformAxisCutoff`, slim blocks, `ℓ = 10⁵Δ`).

Read-offs: `actualSlots_stageCore_BAUGD` (A0a), `actualSlots_cloud_subset_BAUGD` (`A_j ⊆ Ã_j`),
`actualSlots_scale_kept_BAUGD`, the three membership lemmas `mem_actualSlots_stageCore_*_BAUGD`
(an original point in a threshold-`7` set of a stage centre lies in the stage core), and the
cutoff formulas `actualSlots_cutoff_*_BAUGD`.
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

/-- Membership of an interior tag in `Q₂^∂`: slim, `edgeB`, zero and scale blocks (closed
`cgpInQ2` plus the scale block). -/
def inQ2_BAUGD : S.IntTag_BAUGA → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr t))) => !t

/-- Membership of an interior tag in `Q₃^∂`: slim, zero and scale blocks (closed `cgpInQ3` plus
the scale block). -/
def inQ3_BAUGD : S.IntTag_BAUGA → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr t))) => !t

/-- **The interior stage tags** `Q₁^∂ = all`, `Q₂^∂`, `Q₃^∂`. -/
def stageTags_BAUGD : Fin 3 → Finset S.IntTag_BAUGA :=
  ![Finset.univ, Finset.univ.filter fun t => S.inQ2_BAUGD t = true,
    Finset.univ.filter fun t => S.inQ3_BAUGD t = true]

/-- The scale tag is a tag of every stage. -/
theorem scaleTag_mem_stageTags_BAUGD (st : Fin 3) : S.scaleTag_BAUGA ∈ S.stageTags_BAUGD st := by
  fin_cases st
  · exact Finset.mem_univ _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- **The threshold-`8` core of a marker chart** (the enlargement `Ã`; the same balls as
`markerCore7_BAUGC`): circle `B(i, 200ρ_i) ∩ {‖η_i‖ ≤ 8}`, slim `B(i, 10⁶Δρ_i) ∩ {|η_i| ≤ 8·10⁵Δ}`,
`edgeB` `B(i, 100Δρ_i) ∩ {|η_i| ≤ 8Δ} ∩ {t_B ≤ 8Δ}`. -/
def markerCore8_BAUGD (m : S.MarkerIdx_BAUGC) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  match m with
  | .inl j => {p | dist p j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 p‖ ≤ 8}
  | .inr (.inl j) => {p | dist p j.1 < 1000000 * Δ * S.rho j.1 ∧
      |S.slimEta_BIF j.1 p| ≤ 8 * (100000 * Δ)}
  | .inr (.inr j) => {p | dist p j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 p| ≤ 8 * Δ ∧
      S.edgeHeightRaw p ≤ 8 * Δ}

/-- `Core⁷ ⊆ Core⁸` (for `0 ≤ Δ`). -/
theorem markerCore7_subset_markerCore8_BAUGD (hΔ : 0 ≤ Δ) (m : S.MarkerIdx_BAUGC) :
    S.markerCore7_BAUGC m ⊆ S.markerCore8_BAUGD m := by
  rcases m with j | j | j
  · rintro p ⟨h1, h2⟩
    exact ⟨h1, h2.trans (by norm_num)⟩
  · rintro p ⟨h1, h2⟩
    exact ⟨h1, h2.trans (by nlinarith)⟩
  · rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, h2.trans (by nlinarith), h3.trans (by nlinarith)⟩

/-- The circle centre index of the active family. -/
abbrev CircleIdx_BAUGD : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.circle.finite_centres.toFinset

/-- The slim centre index of the active family. -/
abbrev SlimIdx_BAUGD : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.slim.finite_centres.toFinset

/-- The `edgeB` centre index of the active family. -/
abbrev EdgeIdx_BAUGD : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.edgeB.finite_centres.toFinset

/-- The circle vector block `u_j` on `H^∂`. -/
def circleVector_BAUGD (j : S.CircleIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inl (.inl j))

/-- The circle marker `v_j` on `H^∂`. -/
def circleMarker_BAUGD (j : S.CircleIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inl (.inl j))

/-- The `edgeB` vector block `u_j` on `H^∂`. -/
def edgeVector_BAUGD (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (.inr (.inr (.inl j))))

/-- The `edgeB` marker `v_j` on `H^∂`. -/
def edgeMarker_BAUGD (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (.inr (.inr (.inl j))))

/-- The slim vector block `u_j` on `H^∂`. -/
def slimVector_BAUGD (j : S.SlimIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (.inr (.inl j)))

/-- The slim marker `v_j` on `H^∂`. -/
def slimMarker_BAUGD (j : S.SlimIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (.inr (.inl j)))

/-- The vector of the `E'` block on `H^∂` (`ρ t_B z_{E'}` on the axis). -/
def heightVector_BAUGD :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl S.edgeTag_BAUGA)

/-- The marker of the `E'` block on `H^∂` (`ρ z_{E'}`). -/
def heightMarker_BAUGD :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl S.edgeTag_BAUGA)

/-- **`ψ₀`, CFS31's source cutoff** on `H^∂` (circle blocks of the active family). -/
def cutoffZero_BAUGD : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
  markerLocalitySourceCutoff lc87EdgeTransition
    (fun j : S.CircleIdx_BAUGD => S.rho j.1) S.circleVector_BAUGD
    S.circleMarker_BAUGD

/-- **`ψ₁`, CFS23's buffered edge cutoff** on `H^∂` (`edgeB` blocks, the scale marker, the `E'`
block). -/
def cutoffOne_BAUGD : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
  cfsBufferedEdgeCutoff lc87EdgeTransition Δ
    (fun j : S.EdgeIdx_BAUGD => S.rho j.1) S.edgeVector_BAUGD
    S.edgeMarker_BAUGD S.scaleMarker_BIF S.heightVector_BAUGD S.heightMarker_BAUGD

/-- **`ψ₂`, CFS22's uniform one-axis cutoff** on `H^∂` (slim blocks, `ℓ = 10⁵Δ`). -/
def cutoffTwo_BAUGD : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
  cfsUniformAxisCutoff lc87EdgeTransition (10 ^ 5 * Δ)
    (fun j : S.SlimIdx_BAUGD => S.rho j.1) S.slimVector_BAUGD
    S.slimMarker_BAUGD

end BoundarySupplyCore

/-- **A0: the ACTUAL slot of the boundary chain** (every field a definition of `S`): stage tags
`Q₁^∂ = all`, `Q₂^∂`, `Q₃^∂` (`stageTags_BAUGD`), stage cores = the threshold-`7` cores of the
stage's marker charts, enlargements = their threshold-`8` cores, cutoffs `ψ₀, ψ₁, ψ₂` = CFS31's
formulas on `H^∂`. -/
def actualSlots_BAUGD (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz θ W g δn n B oM) : BoundaryInteriorSlots_BIF S where
  stageTags := S.stageTags_BAUGD
  stageCore := fun st =>
    ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore7_BAUGC m
  stageEnlargement := fun st =>
    ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore8_BAUGD m
  cutoff := ![S.cutoffZero_BAUGD, S.cutoffOne_BAUGD, S.cutoffTwo_BAUGD]

section Slot

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **A0a** (frozen): the stage cores of the actual slot are the threshold-`7` cores of the stage's
marker charts. -/
theorem actualSlots_stageCore_BAUGD (st : Fin 3) :
    (actualSlots_BAUGD S).stageCore st =
      ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore7_BAUGC m :=
  rfl

/-- The enlargements of the actual slot are the threshold-`8` cores of the stage's marker charts. -/
theorem actualSlots_stageEnlargement_BAUGD (st : Fin 3) :
    (actualSlots_BAUGD S).stageEnlargement st =
      ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st}, S.markerCore8_BAUGD m :=
  rfl

/-- The stage tags of the actual slot. -/
theorem actualSlots_stageTags_BAUGD : (actualSlots_BAUGD S).stageTags = S.stageTags_BAUGD :=
  rfl

/-- The cutoffs of the actual slot: `ψ₀`, `ψ₁`, `ψ₂`. -/
theorem actualSlots_cutoff_BAUGD :
    (actualSlots_BAUGD S).cutoff 0 = S.cutoffZero_BAUGD ∧
      (actualSlots_BAUGD S).cutoff 1 = S.cutoffOne_BAUGD ∧
      (actualSlots_BAUGD S).cutoff 2 = S.cutoffTwo_BAUGD :=
  ⟨rfl, rfl, rfl⟩

/-- `A_j ⊆ Ã_j` on the actual slot (BAUG-C's `cloud_subset`). -/
theorem actualSlots_cloud_subset_BAUGD (hΔ : 0 ≤ Δ) (st : Fin 3) :
    (actualSlots_BAUGD S).stageCore st ⊆ (actualSlots_BAUGD S).stageEnlargement st :=
  biUnion_mono subset_rfl fun m _ => S.markerCore7_subset_markerCore8_BAUGD hΔ m

/-- The scale block is kept in every `Q_j^∂` of the actual slot (BAUG-C's `scale_kept`). -/
theorem actualSlots_scale_kept_BAUGD (st : Fin 3) :
    S.scaleTag_BAUGA ∈ (actualSlots_BAUGD S).stageTags st :=
  S.scaleTag_mem_stageTags_BAUGD st

/-- A marker-chart threshold-`7` core lies in the core of its stage. -/
theorem markerCore7_subset_actualSlots_stageCore_BAUGD (m : S.MarkerIdx_BAUGC) :
    S.markerCore7_BAUGC m ⊆ (actualSlots_BAUGD S).stageCore (S.markerStage_BAUGC m) :=
  subset_biUnion_of_mem (u := S.markerCore7_BAUGC) (show m ∈ {m' : S.MarkerIdx_BAUGC |
    S.markerStage_BAUGC m' = S.markerStage_BAUGC m} from rfl)

/-- **Circle stage**: an original point in a threshold-`7` set of a circle centre lies in the
stage core `A₀`. -/
theorem mem_actualSlots_stageCore_circle_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 0)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 200 * S.rho j)
    (hη : ‖S.circleEta_BIF j q‖ ≤ 7) : q ∈ (actualSlots_BAUGD S).stageCore 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.circle.centres := hj
  exact markerCore7_subset_actualSlots_stageCore_BAUGD S
    (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) ⟨hd, hη⟩

/-- **Edge stage**: an original point in a threshold-`7` set of an `edgeB` centre lies in the
stage core `A₁`. -/
theorem mem_actualSlots_stageCore_edge_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 1)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 100 * Δ * S.rho j)
    (hη : |S.edgeEta_BIF j q| ≤ 7 * Δ) (ht : S.edgeHeightRaw q ≤ 7 * Δ) :
    q ∈ (actualSlots_BAUGD S).stageCore 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  exact markerCore7_subset_actualSlots_stageCore_BAUGD S
    (.inr (.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩)) ⟨hd, hη, ht⟩

/-- **Slim stage**: an original point in a threshold-`7` set of a slim centre lies in the stage
core `A₂`. -/
theorem mem_actualSlots_stageCore_slim_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 2)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 1000000 * Δ * S.rho j)
    (hη : |S.slimEta_BIF j q| ≤ 7 * (100000 * Δ)) : q ∈ (actualSlots_BAUGD S).stageCore 2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.slim.centres := hj
  exact markerCore7_subset_actualSlots_stageCore_BAUGD S
    (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩)) ⟨hd, hη⟩

/-- **Consumer**: an original point of a threshold-`7` set of a stage centre gives a point of the
actual stage cloud `S_j = π_j F_∂(A_j)` (circle stage). -/
theorem stageProj_mem_actualSlots_stageCloud_circle_BAUGD {j q : W.pieceInterior ⊤}
    (hj : j ∈ S.stageCentres_BIF 0)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j < 200 * S.rho j)
    (hη : ‖S.circleEta_BIF j q‖ ≤ 7) :
    (actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
      (actualSlots_BAUGD S).stageCloud 0 :=
  ⟨q, mem_actualSlots_stageCore_circle_BAUGD S hj hd hη, rfl⟩

/-- The centre of a marker chart is a centre of its stage family. -/
theorem markerCentre_mem_stageCentres_BAUGD (m : S.MarkerIdx_BAUGC) :
    S.markerCentre_BAUGC m ∈ S.stageCentres_BIF (S.markerStage_BAUGC m) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  rcases m with j | j | j
  · exact (Set.Finite.mem_toFinset _).mp j.2
  · exact (Set.Finite.mem_toFinset _).mp j.2
  · exact (Set.Finite.mem_toFinset _).mp j.2

/-- **An empty stage family has an empty stage core and enlargement** on the actual slot (the
hypotheses of `BoundaryStageSlot_BIF.inactive`). -/
theorem actualSlots_eq_empty_of_stageCentres_BAUGD {st : Fin 3} (h : S.stageCentres_BIF st = ∅) :
    (actualSlots_BAUGD S).stageCore st = ∅ ∧ (actualSlots_BAUGD S).stageEnlargement st = ∅ := by
  have hm : ∀ m : S.MarkerIdx_BAUGC, S.markerStage_BAUGC m ≠ st := by
    intro m hm
    have := markerCentre_mem_stageCentres_BAUGD S m
    rw [hm, h] at this
    exact this
  refine ⟨Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_,
    Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_⟩
  · obtain ⟨m, hmst, -⟩ := Set.mem_iUnion₂.mp hp
    exact hm m hmst
  · obtain ⟨m, hmst, -⟩ := Set.mem_iUnion₂.mp hp
    exact hm m hmst

/-- **Consumer: the inactive slot of an empty stage family** on any augmented data over the actual
slot (`Ψ_j = id`, BIFACE's `Ψ_eq_id_of_inactive`). -/
def actualSlots_inactiveSlot_BAUGD {D : BoundaryAugmentedData S (actualSlots_BAUGD S)} {st : Fin 3}
    (h : S.stageCentres_BIF st = ∅) (Kj : ℕ) (Ξ sg cw : ℝ) : BoundaryStageSlot_BIF D st Kj Ξ sg cw :=
  .inactive (actualSlots_eq_empty_of_stageCentres_BAUGD S h).1
    (actualSlots_eq_empty_of_stageCentres_BAUGD S h).2

/-- The actual stage cloud lies in the enlarged one (`S_j ⊆ S̃_j`). -/
theorem actualSlots_stageCloud_subset_BAUGD (hΔ : 0 ≤ Δ) (st : Fin 3) :
    (actualSlots_BAUGD S).stageCloud st ⊆ (actualSlots_BAUGD S).stageCloudEnlarged st :=
  Set.image_mono (actualSlots_cloud_subset_BAUGD S hΔ st)

end Slot

end DifferentialGeometry.Geometry.Collapse
