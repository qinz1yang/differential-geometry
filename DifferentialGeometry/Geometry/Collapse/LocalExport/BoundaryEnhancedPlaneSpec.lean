import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedSupplyRows

/-!
# BCG03: the enhanced stage-plane specification on the augmented tables (lane BAUG-C, G2)

Draft 61 §1.4 (`plane_spec`), D61-6: `BoundaryEnhancedPlaneSpec` is the closed `EnhancedStagePlanes`
(draft 59 §1.3–1.5, D59-2; Lean: the `Prop` fields of `FirstStagePlanes_PLN` / `EdgeStagePlanes_PLN`
/ `SlimStagePlanes_PLN` and the derived (FM*) / (ZB*) / whole-small-block contracts of
`ActualStagePlaneFullMarker.lean` / `ActualStagePlaneZeroBlock.lean`) over the AUGMENTED reference
table of BIFACE (`BoundaryStageReferences_BIF Φ st E eta row`): every clause is about the SAME plane
`R.planes.plane` = (P) `im D(K^∂_a Φ^∂_a)(η_a(q))` in `H^∂`, with the interior tags of BAUG-A G3
(`S.IntTag_BAUGA`) for the interior markers. The boundary blocks need no clause: their contributor
properties are THEOREMS of the table (BCG04 / BCG05 halves, `…_BAUGC` below and in G3).

Interior data of the active family used by the clauses (definitions, never choices):
`S.MarkerIdx_BAUGC` (circle ⊕ slim ⊕ `edgeB` centres), `S.markerTag_BAUGC`, `S.markerCentre_BAUGC`,
`S.markerStage_BAUGC` (`0` circle, `1` edge, `2` slim), `S.markerCore7_BAUGC` (the threshold-`7`
cores: circle `B(i, 200ρ_i) ∩ {‖η_i‖ ≤ 7}`, edge `B(i, 100Δρ_i) ∩ {|η_i| ≤ 7Δ, t_B ≤ 7Δ}`, slim
`B(i, 10⁶Δρ_i) ∩ {|η_i| ≤ 7·10⁵Δ}`), `S.ZeroIdx_BAUGC`, `S.zeroTag_BAUGC`, `S.zeroRadius_BAUGC`,
`smallBlockFactor_BAUGC = (1/2, .99, .99)`.

Fields of `BoundaryEnhancedPlaneSpec R Γ sg eg`:
* `prune_slot` — `K_a` never writes into `H_∂` (with BIFACE's `prune_boundary`: `K_a = K^∂(K_int)`);
* `cloud_subset`, `scale_kept` — the two slot facts CFS15 reads (`A_j ⊆ Ã_j`; the scale block is kept
  in `Q_j^∂`); see state-BAUG-C.md "FOR BIFACEb";
* `dimension` (`dim L_x = k_j`, `L_x ≤ Q_j^∂`), `cloudy` (FC27's (CS) for every selection of
  preimages in `W°`, radius `Σρ(sel x)`, quality `Γ`), `normal` (TCP06 / EGP07 / SGP05's normal
  error `‖L_xᗮ π_j DF_∂(q) v‖ ≤ e‖v‖_g` at every preimage `q ∈ W°`, original metric), `small_pp` ((PP), every preimage), `scale_zero`
  (stage `0`), `small_block` (CGP04's whole small block), `full_marker` ((FM*)), `zero_block` ((ZB*)).

Derived: `gaf03_input_BAUGC` (GAF03's contributor input from (FM*)), `zsp01_input_BAUGC` (ZSP01's
from (ZB*)), `prune_eq_augmented_BAUGC` (`K_a = augmentedPrune_BAUGC (pr_int K_a ι_int)`),
`plane_eq_augmented_BAUGC` (the plane is G1's augmented derivative image).
The data level: `BoundaryAugmentedData.EnhancedPlaneSpec D Γ sg eg st` (the three stored tables).
Inhabitant: `exists_boundaryEnhancedPlaneSpec_BAUGC` (every supply, every stage: a slot and a stage
table with the stored rows / (BM) blocks and the spec; empty clouds), double cusp in
`BoundaryEnhancedPlaneSpecDoubleCusp.lean`.
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

/-- `ContinuousSMul` on one block `WithLp 2 (ℝ² × ℝ)`, as a named local instance (the default
search times out; protocol pitfall, lane C14-KA6). -/
local instance instContinuousSMulPlaneBlock_BAUGCs :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- CGP04's whole-small-block ratio per stage: `ρ(c) ≤ ρ(a)/2` at the first stage (CFS27's
pruning), `ρ(c) ≤ .99ρ(a)` at the edge and slim stages (the actual lists). -/
def smallBlockFactor_BAUGC : Fin 3 → ℝ :=
  ![1 / 2, 99 / 100, 99 / 100]

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The marker index of the active family: circle, slim and `edgeB` centres (the constant-radius
marker charts; tags `.inl`, `.inr .inl`, `.inr .inr .inl` of `S.IntTag_BAUGA`). -/
abbrev MarkerIdx_BAUGC : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.circle.finite_centres.toFinset ⊕ S.family.slim.finite_centres.toFinset ⊕
    S.family.edgeB.finite_centres.toFinset

/-- The interior tag of a marker chart. -/
def markerTag_BAUGC : S.MarkerIdx_BAUGC → S.IntTag_BAUGA
  | .inl j => .inl j
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr j) => .inr (.inr (.inl j))

/-- The centre of a marker chart. -/
def markerCentre_BAUGC : S.MarkerIdx_BAUGC → W.pieceInterior ⊤
  | .inl j => j.1
  | .inr (.inl j) => j.1
  | .inr (.inr j) => j.1

/-- The stage of a marker chart: circle `0`, `edgeB` `1`, slim `2`. -/
def markerStage_BAUGC : S.MarkerIdx_BAUGC → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

/-- **The threshold-`7` core of a marker chart** (draft 59 §1.4 `Core⁷`, on the active family):
circle `B(i, 200ρ_i) ∩ {‖η_i‖ ≤ 7}`, slim `B(i, 10⁶Δρ_i) ∩ {|η_i| ≤ 7·10⁵Δ}`, `edgeB`
`B(i, 100Δρ_i) ∩ {|η_i| ≤ 7Δ} ∩ {t_B ≤ 7Δ}` (`t_B = edgeB.smoothing/ρ`, the SAME global height). -/
def markerCore7_BAUGC (m : S.MarkerIdx_BAUGC) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  match m with
  | .inl j => {p | dist p j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 p‖ ≤ 7}
  | .inr (.inl j) => {p | dist p j.1 < 1000000 * Δ * S.rho j.1 ∧
      |S.slimEta_BIF j.1 p| ≤ 7 * (100000 * Δ)}
  | .inr (.inr j) => {p | dist p j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 p| ≤ 7 * Δ ∧
      S.edgeHeightRaw p ≤ 7 * Δ}

/-- The zero index of the active family (zero centres; tags `.inr .inr .inr .inl`). -/
abbrev ZeroIdx_BAUGC : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  S.family.zero.finite_centres.toFinset

/-- The interior tag of a zero centre. -/
def zeroTag_BAUGC (k : S.ZeroIdx_BAUGC) : S.IntTag_BAUGA :=
  .inr (.inr (.inr (.inl k)))

/-- The radius `R_k` of a zero centre (the block radius of its tag). -/
def zeroRadius_BAUGC (k : S.ZeroIdx_BAUGC) : ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius

/-- The marker functional `v_c = (·)_{c}.snd` of a marker chart on `H^∂`. -/
def markerCLM_BAUGC (m : S.MarkerIdx_BAUGC) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (S.markerTag_BAUGC m))

/-- The whole-block projection `J_c` of a marker chart on `H^∂`. -/
def markerBlockCLM_BAUGC (m : S.MarkerIdx_BAUGC) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
  blockProjCLM_PLN (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (S.markerTag_BAUGC m))

/-- The whole-block projection `J_k` of a zero centre on `H^∂`. -/
def zeroBlockCLM_BAUGC (k : S.ZeroIdx_BAUGC) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
  blockProjCLM_PLN (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (S.zeroTag_BAUGC k))

/-- The scale marker `v_scale` on `H^∂`. -/
def scaleCLM_BAUGC : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl S.scaleTag_BAUGA)

/-- The whole boundary block `J_b` of a boundary component on `H^∂`. -/
def boundaryBlockCLM_BAUGC (i : Fin S.packet.cusp.count) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
  blockProjCLM_PLN (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)

/-- The boundary marker `v_b = (·)_b.snd` of a boundary component on `H^∂`. -/
def boundaryMarkerCLM_BAUGC (i : Fin S.packet.cusp.count) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)

end BoundarySupplyCore

section Spec

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}

/-- **`BoundaryEnhancedPlaneSpec`** (draft 61 §1.4 `plane_spec`, D61-6): the closed enhanced-plane
contract (draft 59 §1.3–1.5) on the SAME plane `R.planes.plane` of an augmented stage table, at
quality `Γ` and radius factor `sg`, with the interior markers of the active family. `Prop` fields
only; the data (models, pruning, coordinates, preimages, references) are the table's. -/
structure BoundaryEnhancedPlaneSpec (R : BoundaryStageReferences_BIF Φ st E eta row)
    (Γ sg eg : ℝ) : Prop where
  /-- The pruning never writes into `H_∂`: every boundary slot of `K_a v` is that of `v`. -/
  prune_slot : ∀ a v (i : Fin S.packet.cusp.count),
    R.planes.prune a v (Sum.inr i) = v (Sum.inr i)
  /-- `A_j ⊆ Ã_j` (hence `S_j ⊆ S̃_j`). -/
  cloud_subset : Φ.stageCore st ⊆ Φ.stageEnlargement st
  /-- The scale block is kept in `Q_j^∂`. -/
  scale_kept : S.scaleTag_BAUGA ∈ Φ.stageTags st
  /-- `dim L_x = k_j` and `L_x ≤ Q_j^∂`. -/
  dimension : ∀ x ∈ Φ.stageCloud st,
    Module.finrank ℝ (R.planes.plane x) = gafStageDim st ∧ R.planes.plane x ≤ Φ.stageQ st
  /-- FC27's (CS) for every selection of preimages in `W°`, radius `Σρ(sel x)`, quality `Γ`. -/
  cloudy : ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      W.pieceInterior ⊤,
    (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
    ∀ x ∈ Φ.stageCloud st,
      hausdorffEDist (Φ.stageCloudEnlarged st ∩ ball x (sg * S.rho (sel x) / Γ))
        ((AffineSubspace.mk' x (R.planes.plane x) :
            Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) ∩
          ball x (sg * S.rho (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * S.rho (sel x)))
  /-- TCP06 / EGP07 / SGP05's normal estimate (the error part of `normal` on the closed side), in the
  ORIGINAL metric `g` of `W`: at every preimage `q ∈ W°` of a cloud point `x`, the component of
  `π_j DF_∂(q) v` normal to the plane `L_x` is at most `e‖v‖_g`. -/
  normal : ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
    Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
    ∀ v : TangentSpace W.model q.val,
      ‖(R.planes.plane x)ᗮ.starProjection (Φ.stageProj st
          (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
        eg * Real.sqrt (g.inner q.val v v)
  /-- (PP): every preimage `q ∈ W°`, every marker chart with `ρ(c) < ρ(q)/5`: `L_x ≤ ker v_c`. -/
  small_pp : ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
    Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
    ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
      R.planes.plane x ≤ LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ))
  /-- EDP01's scale clause at the first stage: `L_x ≤ ker v_scale`. -/
  scale_zero : st = 0 → ∀ x ∈ Φ.stageCloud st,
    R.planes.plane x ≤ LinearMap.ker ((S.scaleCLM_BAUGC :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ))
  /-- CGP04's whole small block: a marker chart with `ρ(c) ≤ f_j ρ(a(x))` has its WHOLE block in the
  kernel of the plane. -/
  small_block : ∀ x (hx : x ∈ Φ.stageCloud st) (m : S.MarkerIdx_BAUGC),
    S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC st * S.rho (R.planes.ref ⟨x, hx⟩) →
      R.planes.plane x ≤ LinearMap.ker ((S.markerBlockCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)))
  /-- (FM*): a marker chart `m` of the stage, a threshold-`7` core point `p`, `x = π_j F_∂(p)`, a
  cloud point `y` in the contributor window of the radius `σρ ∘ q̂` (`0 ≤ σ ≤ ε_c/10000`): the
  marker of `m` is full at `y` and the plane at `y` lies in its kernel. -/
  full_marker : ∀ εc σ : ℝ, 0 < εc → 0 ≤ σ → σ ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
    (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = st → ∀ p ∈ S.markerCore7_BAUGC m,
    ∀ y ∈ Φ.stageCloud st,
      (closedBall y (80 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
        ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q)
            (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
      S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
        R.planes.plane y ≤ LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ))
  /-- (ZB*): a zero centre `k`, a preimage `p` of a cloud point with `ρ(p) > 200R_k/T`, a cloud
  point `y` in the contributor window: the WHOLE `k`-block of `y` vanishes and the plane at `y` lies
  in its kernel. -/
  zero_block : ∀ εc σ : ℝ, 0 < εc → σ ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
    (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
    Φ.stageProj st (S.boundaryOriginalMap p.val) ∈ Φ.stageCloud st →
    200 * S.zeroRadius_BAUGC k / T < S.rho p →
    ∀ y ∈ Φ.stageCloud st,
      (closedBall y (80 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
        ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q)
            (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
      S.zeroBlockCLM_BAUGC k y = 0 ∧
        R.planes.plane y ≤ LinearMap.ker ((S.zeroBlockCLM_BAUGC k :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)))

/-- **`K = K^∂(K_int)`, generically**: a continuous linear map of `H^∂` that is the identity on
`H_∂` and never writes into `H_∂` is the augmented pruning of its interior part
`pr_int K ι_int`. -/
theorem eq_augmentedPrune_of_slots_BAUGC {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Kp : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (hbd : ∀ v ∈ (augmentedBoundarySubmodule_BC7C :
      Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²))), Kp v = v)
    (hslot : ∀ v i, Kp v (Sum.inr i) = v (Sum.inr i)) :
    Kp = augmentedPrune_BAUGC (augIntProjCLM_BAUGC.comp (Kp.comp augIntInclCLM_BAUGC)) := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun t => ?_
  rcases t with t | i
  · rw [augmentedPrune_apply_inl_BAUGC]
    have hmem : x - augIntInclCLM_BAUGC (augIntProjCLM_BAUGC x) ∈
        (augmentedBoundarySubmodule_BC7C : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) := by
      intro i
      change x (Sum.inl i) - (augIntInclCLM_BAUGC (augIntProjCLM_BAUGC x)) (Sum.inl i) = 0
      rw [augIntInclCLM_apply_inl_BAUGC, augIntProjCLM_apply_BAUGC, sub_self]
    have h2 : Kp x = Kp (augIntInclCLM_BAUGC (augIntProjCLM_BAUGC x)) +
        (x - augIntInclCLM_BAUGC (augIntProjCLM_BAUGC x)) := by
      rw [← hbd _ hmem, ← map_add, add_sub_cancel]
    rw [h2, PiLp.add_apply, PiLp.sub_apply, augIntInclCLM_apply_inl_BAUGC,
      augIntProjCLM_apply_BAUGC, sub_self, add_zero]
    rfl
  · rw [hslot, augmentedPrune_apply_inr_BAUGC]

namespace BoundaryEnhancedPlaneSpec

variable {R : BoundaryStageReferences_BIF Φ st E eta row} {Γ sg eg : ℝ}

/-- **`K_a = K^∂(K_int)`**: with BIFACE's `prune_boundary` (`K_a = id` on `H_∂`) and `prune_slot`,
the stored pruning is G1's augmented pruning of its interior part `pr_int K_a ι_int`. -/
theorem prune_eq_augmented_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) (a : W.pieceInterior ⊤) :
    R.planes.prune a = augmentedPrune_BAUGC
      (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp augIntInclCLM_BAUGC)) :=
  eq_augmentedPrune_of_slots_BAUGC _ (R.prune_boundary a) (hR.prune_slot a)

/-- The stored pruned model is G1's augmented model of the pruned interior part:
`K_a ∘ Φ_a = K^∂(K_int) ∘ Φ^∂[pr_int Φ_a]` at every centre. -/
theorem prune_comp_model_eq_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF st) :
    ⇑(R.planes.prune a) ∘ R.planes.model a =
      ⇑(augmentedPrune_BAUGC (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp
          augIntInclCLM_BAUGC))) ∘
        augmentedModel_BAUGC (augIntProjCLM_BAUGC ∘ R.planes.model a) (S.boundaryList_BIF st a)
          (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a)) :=
  (congrArg (fun f : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) => ⇑f ∘ R.planes.model a)
      (hR.prune_eq_augmented_BAUGC a)).trans
    (congrArg (fun m => ⇑(augmentedPrune_BAUGC (augIntProjCLM_BAUGC.comp
      ((R.planes.prune a).comp augIntInclCLM_BAUGC))) ∘ m) (R.model_eq_augmented_BAUGC ha))

/-- **The plane is G1's augmented derivative image** (draft 61 (P)): at a cloud point `x` with
reference `a` and model preimage `q`, if the pruned interior model is differentiable at `η_a(q)`,
`L_x = im (ι_int D(K_int Φ_int) + Σ_{b ∈ J_∂(a)} slot_b DΦ^∂_{a,b})`. -/
theorem plane_eq_augmented_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) {x : _}
    (hx : x ∈ Φ.stageCloud st)
    (hd : DifferentiableAt ℝ (⇑(augIntProjCLM_BAUGC.comp ((R.planes.prune (R.planes.ref ⟨x, hx⟩)).comp
        augIntInclCLM_BAUGC)) ∘ (augIntProjCLM_BAUGC ∘ R.planes.model (R.planes.ref ⟨x, hx⟩)))
      (eta (R.planes.ref ⟨x, hx⟩) (R.planes.pre ⟨x, hx⟩))) :
    R.planes.plane x = LinearMap.range (augDeriv_BAUGC
      (fderiv ℝ (⇑(augIntProjCLM_BAUGC.comp ((R.planes.prune (R.planes.ref ⟨x, hx⟩)).comp
        augIntInclCLM_BAUGC)) ∘ (augIntProjCLM_BAUGC ∘ R.planes.model (R.planes.ref ⟨x, hx⟩)))
        (eta (R.planes.ref ⟨x, hx⟩) (R.planes.pre ⟨x, hx⟩)))
      (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st (R.planes.ref ⟨x, hx⟩)) fun i =>
        fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i (R.planes.ref ⟨x, hx⟩))
          (S.rho (R.planes.ref ⟨x, hx⟩)) (row (R.planes.ref ⟨x, hx⟩))
          (eta (R.planes.ref ⟨x, hx⟩) (R.planes.ref ⟨x, hx⟩)) i)
          (eta (R.planes.ref ⟨x, hx⟩) (R.planes.pre ⟨x, hx⟩))) :
        E →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) := by
  have ha := R.ref_mem ⟨x, hx⟩
  have hF := fderiv_augmented_pruned_BAUGC (J := S.boundaryList_BIF st (R.planes.ref ⟨x, hx⟩))
    (Φb := bmBlocks_BAUGC (fun i => S.packet.height i (R.planes.ref ⟨x, hx⟩))
      (S.rho (R.planes.ref ⟨x, hx⟩)) (row (R.planes.ref ⟨x, hx⟩))
      (eta (R.planes.ref ⟨x, hx⟩) (R.planes.ref ⟨x, hx⟩)))
    _ hd fun i _ => differentiableAt_bmBlocks_BAUGC _ (S.rho_pos _).ne' _ _ _ i
  have hK := hR.prune_comp_model_eq_BAUGC ha
  have hc := R.coord_eq _ ha
  rw [R.planes.plane_of_mem hx]
  simp only [hK, hc]
  exact congrArg (fun T : E →L[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
    LinearMap.range (T : E →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) hF

/-- **GAF03's contributor input from (FM\*)** (`markerLine_input_PLN`, `c = K.starProjection x`, the
full-marker vector of `x = π_j F_∂(p)`): every window contributor `y` has the same marker-line
projection as `x` and `L_y ≤ Kᗮ`, provided the marker of `m` is full at `x` as well. -/
theorem gaf03_input_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : W.pieceInterior ⊤) (m : S.MarkerIdx_BAUGC)
    (hm : S.markerStage_BAUGC m = st) {p : W.pieceInterior ⊤} (hp : p ∈ S.markerCore7_BAUGC m)
    (hvx : S.markerCLM_BAUGC m (Φ.stageProj st (S.boundaryOriginalMap p.val)) =
      S.rho (S.markerCentre_BAUGC m)) :
    ∀ y ∈ Φ.stageCloud st,
      (closedBall y (80 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
        ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q)
            (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
      (LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)))ᗮ.starProjection
          y =
        (LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)))ᗮ.starProjection
          (Φ.stageProj st (S.boundaryOriginalMap p.val)) ∧
      R.planes.plane y ≤ (LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hF := hR.full_marker εc σ hε hσ hσε x₀ m hm p hp y hy ⟨z, hz1, hz2⟩
  have hv2 := hF.1.trans hvx.symm
  exact markerLine_input_PLN (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    _ _ hv2 hF.2

/-- **ZSP01's contributor input from (ZB\*)** (`zeroBlock_input_PLN`, `c = 0`): every window
contributor `y` has `K.starProjection y = 0` and `L_y ≤ Kᗮ` for the whole zero-block line
`K = (ker J_k)ᗮ`. -/
theorem zsp01_input_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) {εc σ : ℝ} (hε : 0 < εc)
    (hσε : σ ≤ εc / 10000) (x₀ : W.pieceInterior ⊤) (k : S.ZeroIdx_BAUGC) {p : W.pieceInterior ⊤}
    (hx : Φ.stageProj st (S.boundaryOriginalMap p.val) ∈ Φ.stageCloud st)
    (hρp : 200 * S.zeroRadius_BAUGC k / T < S.rho p) :
    ∀ y ∈ Φ.stageCloud st,
      (closedBall y (80 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
        ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
          R.planes.radius x₀ σ (fun q : W.pieceInterior ⊤ => S.rho q)
            (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
      (LinearMap.ker ((S.zeroBlockCLM_BAUGC k :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))))ᗮ.starProjection y = 0 ∧
      R.planes.plane y ≤ (LinearMap.ker ((S.zeroBlockCLM_BAUGC k :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hZ := hR.zero_block εc σ hε hσε x₀ k p hx hρp y hy ⟨z, hz1, hz2⟩
  exact zeroBlock_input_PLN (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    _ _ hZ.1 hZ.2

end BoundaryEnhancedPlaneSpec

/-- **The plane spec of the stored tables** (draft 61 §1.4 `plane_spec : ∀ st, BoundaryEnhancedPlaneSpec
…`): at stage `st` the spec of the circle / edge / slim table of `D`, at quality `Γ st` and radius
factor `sg st`. -/
def BoundaryAugmentedData.EnhancedPlaneSpec (D : BoundaryAugmentedData S Φ) (Γ sg eg : Fin 3 → ℝ) :
    Fin 3 → Prop :=
  ![BoundaryEnhancedPlaneSpec D.circle (Γ 0) (sg 0) (eg 0),
    BoundaryEnhancedPlaneSpec D.edge (Γ 1) (sg 1) (eg 1),
    BoundaryEnhancedPlaneSpec D.slim (Γ 2) (sg 2) (eg 2)]

end Spec

section Inhabitant

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **Inhabitant** (every supply, every stage, every coordinate and row family — in particular the
stored ones of `S`): a parameter slot (scale tag kept, empty stage cores) and a stage table whose
stored model is the augmented (BM) model of the rows on the whole lists, with the enhanced-plane
spec. The global clauses (`prune_slot`, `cloud_subset`, `scale_kept`) hold with `K_a = id`; the
cloud clauses are vacuous on the empty clouds. -/
theorem exists_boundaryEnhancedPlaneSpec_BAUGC (st : Fin 3) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) (Γ sg eg : ℝ) :
    ∃ (Φ : BoundaryInteriorSlots_BIF S) (R : BoundaryStageReferences_BIF Φ st E eta row),
      BoundaryEnhancedPlaneSpec R Γ sg eg ∧ ∀ a, R.planes.model a =
        augmentedModel_BAUGC 0 (S.boundaryList_BIF st a)
          (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a)) := by
  let Φ₀ : BoundaryInteriorSlots_BIF S :=
    { stageTags := fun _ => {S.scaleTag_BAUGA}
      stageCore := fun _ => ∅
      stageEnlargement := fun _ => ∅
      cutoff := fun _ _ => 0 }
  have hE : ∀ x, x ∉ Φ₀.stageCloud st := fun x ⟨p, hp, _⟩ => Set.notMem_empty p hp
  have hE' : ∀ x, x ∉ Φ₀.stageCloudEnlarged st := fun x ⟨p, hp, _⟩ => Set.notMem_empty p hp
  let R₀ : BoundaryStageReferences_BIF Φ₀ st E eta row :=
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
  refine ⟨Φ₀, R₀, ?_, fun _ => rfl⟩
  exact
    { prune_slot := fun _ _ _ => rfl
      cloud_subset := subset_refl _
      scale_kept := Finset.mem_singleton_self _
      dimension := fun x hx => (hE x hx).elim
      cloudy := fun _ _ x hx => (hE x hx).elim
      normal := fun x hx => (hE x hx).elim
      small_pp := fun x hx => (hE x hx).elim
      scale_zero := fun _ x hx => (hE x hx).elim
      small_block := fun x hx => (hE x hx).elim
      full_marker := fun _ _ _ _ _ _ _ _ _ _ y hy => (hE y hy).elim
      zero_block := fun _ _ _ _ _ _ _ hx => (hE _ hx).elim }

/-- **Inhabitant on the stored rows, three stages at once**: for every supply there are a slot and
the circle (`ℝ²`, `S.circleEta_BIF`, `S.circleRow_BIF`), revised-edge and slim stage tables with the
stored rows of `S.ba_spec`, each with the enhanced-plane spec. -/
theorem exists_boundaryEnhancedPlaneSpec_stored_BAUGC (Γ sg eg : Fin 3 → ℝ) :
    (∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 0 ℝ² S.circleEta_BIF S.circleRow_BIF),
        BoundaryEnhancedPlaneSpec R (Γ 0) (sg 0) (eg 0)) ∧
    (∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 1 ℝ S.edgeEta_BIF S.edgeRow_BIF),
        BoundaryEnhancedPlaneSpec R (Γ 1) (sg 1) (eg 1)) ∧
    ∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 2 ℝ S.slimEta_BIF S.slimRow_BIF),
        BoundaryEnhancedPlaneSpec R (Γ 2) (sg 2) (eg 2) := by
  obtain ⟨Φc, Rc, hc, -⟩ := exists_boundaryEnhancedPlaneSpec_BAUGC S 0 S.circleEta_BIF
    S.circleRow_BIF (Γ 0) (sg 0) (eg 0)
  obtain ⟨Φe, Re, he, -⟩ := exists_boundaryEnhancedPlaneSpec_BAUGC S 1 S.edgeEta_BIF
    S.edgeRow_BIF (Γ 1) (sg 1) (eg 1)
  obtain ⟨Φs, Rs, hs, -⟩ := exists_boundaryEnhancedPlaneSpec_BAUGC S 2 S.slimEta_BIF
    S.slimRow_BIF (Γ 2) (sg 2) (eg 2)
  exact ⟨⟨Φc, Rc, hc⟩, ⟨Φe, Re, he⟩, ⟨Φs, Rs, hs⟩⟩

end Inhabitant

end DifferentialGeometry.Geometry.Collapse
