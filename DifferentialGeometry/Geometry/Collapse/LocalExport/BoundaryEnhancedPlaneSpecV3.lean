import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlotV2

/-!
# `BoundaryEnhancedPlaneSpecV3`: the enhanced stage-plane spec after lead decision (B) (lane BAUG-C)

New module (the accepted `BoundaryEnhancedPlaneSpec`, AGZ 438bccb9a, stays unchanged). Lead decision
(B) (review 69 D69-5 / A3f): the scale block is in `Q₁^∂` only (BAUG-D slot v2
`actualSlotsV2_BAUGD`: `Q₂^∂` = slim + edgeB + zero, `Q₃^∂` = slim + zero). Hence the field
`scale_kept` (scale block in every `Q_j^∂`) of the accepted spec is replaced by
`radius_mcb` — CFS15's (MCb) for every selection of preimages at every buffer `L'` with `L'Σ ≤ 1/5`
(closed `gafCloud_mcb_GAF2`; stage `0` from the scale block of `Q₁^∂`, stages `1, 2` from the port
lanes' (MCb) clause), and the field `preimage_comparable` (two preimages of the same point of `S̃_j`
have `ρ q₁ ≤ 5/3·ρ q₂`; closed `gafCloud_preimage_ratio_two_GAF5`) is added. All other fields, the derived theorems and the inhabitants are those of the
accepted module, re-stated for `BoundaryEnhancedPlaneSpecV3`; the interior data (`MarkerIdx_BAUGC`,
`markerCore7_BAUGC`, the CLM defs, `smallBlockFactor_BAUGC`) and the generic
`eq_augmentedPrune_of_slots_BAUGC` are imported from the accepted module.

* `BoundaryEnhancedPlaneSpecV3 R Γ sg eg : Prop`; `BoundaryAugmentedData.EnhancedPlaneSpecV3 D Γ sg eg st`;
* `BoundaryEnhancedPlaneSpecV3.prune_eq_augmented_BAUGC`, `.prune_comp_model_eq_BAUGC`,
  `.plane_eq_augmented_BAUGC`, `.gaf03_input_BAUGC`, `.zsp01_input_BAUGC`;
* inhabitants `exists_boundaryEnhancedPlaneSpecV3_BAUGC`, `exists_boundaryEnhancedPlaneSpecV3_stored_BAUGC`.
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
local instance instContinuousSMulPlaneBlock_BAUGCv3 :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}


section Spec

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}

/-- **`BoundaryEnhancedPlaneSpec`** (draft 61 §1.4 `plane_spec`, D61-6): the closed enhanced-plane
contract (draft 59 §1.3–1.5) on the SAME plane `R.planes.plane` of an augmented stage table, at
quality `Γ` and radius factor `sg`, with the interior markers of the active family. `Prop` fields
only; the data (models, pruning, coordinates, preimages, references) are the table's. -/
structure BoundaryEnhancedPlaneSpecV3 (R : BoundaryStageReferences_BIF Φ st E eta row)
    (Γ sg eg : ℝ) : Prop where
  /-- The pruning never writes into `H_∂`: every boundary slot of `K_a v` is that of `v`. -/
  prune_slot : ∀ a v (i : Fin S.packet.cusp.count),
    R.planes.prune a v (Sum.inr i) = v (Sum.inr i)
  /-- `A_j ⊆ Ã_j` (hence `S_j ⊆ S̃_j`). -/
  cloud_subset : Φ.stageCore st ⊆ Φ.stageEnlargement st
  /-- (MCb) on the enlarged cloud for every selection of preimages in `W°`, at every buffer `L'` with
  `L'Σ ≤ 1/5` (closed `gafCloud_mcb_GAF2`; stage `0` from the scale block, stages `1, 2` by the marker
  route). -/
  radius_mcb : ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      W.pieceInterior ⊤,
    (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
    ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
    ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
      dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
      sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
        sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))
  /-- Two preimages in `W°` of the SAME point of the enlarged cloud have comparable scales
  (closed `gafCloud_preimage_ratio_two_GAF5`; stage `0` from the scale block of `Q₁^∂`, stages
  `1, 2` from the ports). Needed because (MCb) compares only points of ONE selection. -/
  preimage_comparable : ∀ x ∈ Φ.stageCloudEnlarged st, ∀ q₁ q₂ : W.pieceInterior ⊤,
    Φ.stageProj st (S.boundaryOriginalMap q₁.val) = x →
    Φ.stageProj st (S.boundaryOriginalMap q₂.val) = x → S.rho q₁ ≤ 5 / 3 * S.rho q₂
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

namespace BoundaryEnhancedPlaneSpecV3

variable {R : BoundaryStageReferences_BIF Φ st E eta row} {Γ sg eg : ℝ}

/-- **`K_a = K^∂(K_int)`**: with BIFACE's `prune_boundary` (`K_a = id` on `H_∂`) and `prune_slot`,
the stored pruning is G1's augmented pruning of its interior part `pr_int K_a ι_int`. -/
theorem prune_eq_augmented_BAUGC (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) (a : W.pieceInterior ⊤) :
    R.planes.prune a = augmentedPrune_BAUGC
      (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp augIntInclCLM_BAUGC)) :=
  eq_augmentedPrune_of_slots_BAUGC _ (R.prune_boundary a) (hR.prune_slot a)

/-- The stored pruned model is G1's augmented model of the pruned interior part:
`K_a ∘ Φ_a = K^∂(K_int) ∘ Φ^∂[pr_int Φ_a]` at every centre. -/
theorem prune_comp_model_eq_BAUGC (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) {a : W.pieceInterior ⊤}
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
theorem plane_eq_augmented_BAUGC (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) {x : _}
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
theorem gaf03_input_BAUGC (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) {εc σ : ℝ} (hε : 0 < εc)
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
theorem zsp01_input_BAUGC (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) {εc σ : ℝ} (hε : 0 < εc)
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

end BoundaryEnhancedPlaneSpecV3

/-- **The plane spec of the stored tables** (draft 61 §1.4 `plane_spec : ∀ st, BoundaryEnhancedPlaneSpec
…`): at stage `st` the spec of the circle / edge / slim table of `D`, at quality `Γ st` and radius
factor `sg st`. -/
def BoundaryAugmentedData.EnhancedPlaneSpecV3 (D : BoundaryAugmentedData S Φ) (Γ sg eg : Fin 3 → ℝ) :
    Fin 3 → Prop :=
  ![BoundaryEnhancedPlaneSpecV3 D.circle (Γ 0) (sg 0) (eg 0),
    BoundaryEnhancedPlaneSpecV3 D.edge (Γ 1) (sg 1) (eg 1),
    BoundaryEnhancedPlaneSpecV3 D.slim (Γ 2) (sg 2) (eg 2)]

end Spec

section Inhabitant

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **Inhabitant** (every supply, every stage, every coordinate and row family — in particular the
stored ones of `S`): a parameter slot (scale tag kept, empty stage cores) and a stage table whose
stored model is the augmented (BM) model of the rows on the whole lists, with the enhanced-plane
spec. The global clauses (`prune_slot`, `cloud_subset`) hold with `K_a = id`; the
cloud clauses are vacuous on the empty clouds. -/
theorem exists_boundaryEnhancedPlaneSpecV3_BAUGC (st : Fin 3) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) (Γ sg eg : ℝ) :
    ∃ (Φ : BoundaryInteriorSlots_BIF S) (R : BoundaryStageReferences_BIF Φ st E eta row),
      BoundaryEnhancedPlaneSpecV3 R Γ sg eg ∧ ∀ a, R.planes.model a =
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

/-- **Inhabitant on the stored rows, three stages at once**: for every supply there are a slot and
the circle (`ℝ²`, `S.circleEta_BIF`, `S.circleRow_BIF`), revised-edge and slim stage tables with the
stored rows of `S.ba_spec`, each with the enhanced-plane spec. -/
theorem exists_boundaryEnhancedPlaneSpecV3_stored_BAUGC (Γ sg eg : Fin 3 → ℝ) :
    (∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 0 ℝ² S.circleEta_BIF S.circleRow_BIF),
        BoundaryEnhancedPlaneSpecV3 R (Γ 0) (sg 0) (eg 0)) ∧
    (∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 1 ℝ S.edgeEta_BIF S.edgeRow_BIF),
        BoundaryEnhancedPlaneSpecV3 R (Γ 1) (sg 1) (eg 1)) ∧
    ∃ (Φ : BoundaryInteriorSlots_BIF S)
      (R : BoundaryStageReferences_BIF Φ 2 ℝ S.slimEta_BIF S.slimRow_BIF),
        BoundaryEnhancedPlaneSpecV3 R (Γ 2) (sg 2) (eg 2) := by
  obtain ⟨Φc, Rc, hc, -⟩ := exists_boundaryEnhancedPlaneSpecV3_BAUGC S 0 S.circleEta_BIF
    S.circleRow_BIF (Γ 0) (sg 0) (eg 0)
  obtain ⟨Φe, Re, he, -⟩ := exists_boundaryEnhancedPlaneSpecV3_BAUGC S 1 S.edgeEta_BIF
    S.edgeRow_BIF (Γ 1) (sg 1) (eg 1)
  obtain ⟨Φs, Rs, hs, -⟩ := exists_boundaryEnhancedPlaneSpecV3_BAUGC S 2 S.slimEta_BIF
    S.slimRow_BIF (Γ 2) (sg 2) (eg 2)
  exact ⟨⟨Φc, Rc, hc⟩, ⟨Φe, Re, he⟩, ⟨Φs, Rs, hs⟩⟩

end Inhabitant

end DifferentialGeometry.Geometry.Collapse
