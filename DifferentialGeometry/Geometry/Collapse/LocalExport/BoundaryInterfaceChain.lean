import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreDefs
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization

/-!
# Boundary route interfaces, part 2: the adjustment chain `BoundaryGaf02Chain` (lane BIFACE)

External draft 61 §3.2–§3.5, §4.1 and dispositions D61-6, D61-7, D61-8, D61-9; closed template
`Fibration/ActualStageChain.lean` (`Gaf02StageSlot`, `Gaf02Chain`, D59-4).

* `BoundaryStageSlot_BIF D st Kj Ξ sg cw`: `active` — ONE native CFS15 stage output
  `Cfs15StageOutput` in the ambient `H^∂` on the stage cloud, radius `Σ_j ρ(q̂_j x)`, plane slot the
  stored (PDEF) plane of `D`; `inactive` — the original stage core and enlargement are empty. The
  smoothing map `a_j` is the output's own ambient nearest map `ι ∘ p` (`id` when inactive).
* `BoundaryInteriorSlots_BIF.adjust`: (ADJ) `Ψ = adjustmentMap Q_j^∂ (π_{Q_j} ∘ a) ψ_j`.
* `BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ`: FIELDS = GAF01's CHOICE inequalities of the
  chain's numbers (closed shape, the early constants `b_cut`, `L₀`, `κ` explicit), the three
  smoothing
  slots and the CFS31 cutoff bindings of the slot cutoffs `ψ_j` at the chain's own stage inputs
  (value range, threshold-6 plateau, threshold-7 closed-support localization in the ORIGINAL
  coordinates of the active family, derivative budget along `[F_∂ p, g_{j−1} p]`). Models and planes
  live in `D`; nothing is copied.
* DEFINITIONS (CHAIN): `Ψ st`, `g₁ = Ψ₀ ∘ F_∂`, `g₂ = Ψ₁ ∘ g₁`, `E = g₃ = Ψ₂ ∘ g₂`, `stage`
  (`g₀ = F_∂`), the scale `s = ℓ_ρ(E)`, the height `A = u_{E'}(E)`, `T = A/s`, the boundary pair
  `(u_b, v_b) = J_b(E)` (BCG7-COLLAR's `J_b`), and the GLOBAL cusp core / front of BCG6-K at that
  pair (`cuspCore_BIF`, `cuspFront_BIF`, `cuspCores_BIF = C_∂`). The conclusions (`stage_smooth`,
  `stage_error_lt`, `prefix_am0`, `segment_am0`, `keeps_orthogonal_coordinates`,
  `keeps_earlier_family_blocks`, `scale_pos`, (BI), (BFM), BCG06) are THEOREMS frozen in
  `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`.
* Exits proved here: `stage_zero`, `E_eq`, `Ψ_eq_id_of_inactive` (an inactive stage is the
  identity), `scaleMarker_boundaryOriginalMap_BIF` (`ℓ_ρ(F_∂) = ρ`),
  `markerPair_eq`.
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

namespace BoundarySupplyCore

/-- The scale marker `ℓ_ρ` of `H^∂` (the marker of the scale block). -/
def scaleMarker_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz W g δn n B oM) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl S.scaleTag_BAUGA)

/-- The height coordinate `u_{E'}` of `H^∂` (first axis coordinate of the weak-edge block). -/
def heightCoord_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz W g δn n B oM)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : ℝ :=
  (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl S.edgeTag_BAUGA) z) 0

/-- The scale marker of `F_∂` is the original scale: `ℓ_ρ(F_∂ p) = ρ(p)` (BAUG-A's scale slot
`(0, ρ)`). -/
theorem scaleMarker_boundaryOriginalMap_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) (p : W.Carrier) :
    S.scaleMarker_BIF (S.boundaryOriginalMap p) = S.rho p := by
  simp [scaleMarker_BIF, blockMarkerCLM, BoundarySupplyCore.boundaryOriginalMap,
    boundaryOriginalMap_BAUGA, boundaryAugmentedMap_BAUGA, interiorMapW_BAUGA, intSlotW_BAUGA]

end BoundarySupplyCore

namespace BoundaryInteriorSlots_BIF

/-- (ADJ) the stage adjustment `Ψ = adjustmentMap Q_j^∂ (π_{Q_j} ∘ a) ψ_j` of a smoothing map
`a`. -/
def adjust (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (a y)) (Φ.cutoff st)

/-- An identity smoothing map gives the identity stage (`π_Q (π_Q x) = π_Q x`). -/
theorem adjust_id (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) :
    Φ.adjust st (fun y => y) = id := by
  funext x
  have h : (Φ.stageQ st).starProjection ((Φ.stageQ st).starProjection x) =
      (Φ.stageQ st).starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.coe_mem _)
  simp [adjust, adjustmentMap, h]

end BoundaryInteriorSlots_BIF

/-- **The boundary per-stage smoothing slot** (draft 61 §3.2–§3.3, D61-6, D61-7): `active` — CFS15's
native stage output in `H^∂` (model dimension `k_st`, jet order `Kj`, accuracy `Ξ`, weight
constant `c_w`, clouds `S_st ⊆ S̃_st`, radius `Σρ ∘ q̂`, plane slot the stored (PDEF) plane);
`inactive` — the original stage core and enlargement are empty (empty family: `Ψ_j = id`, empty
source domain and marked base). -/
inductive BoundaryStageSlot_BIF (D : BoundaryAugmentedData S Φ) (st : Fin 3) (Kj : ℕ)
    (Ξ sg cw : ℝ) : Type
  | active (O : Cfs15StageOutput (gafStageDim st) Kj Ξ cw (Φ.stageCloud st)
        (Φ.stageCloudEnlarged st) (D.stageRadius st sg) (D.stagePlane st)) :
      BoundaryStageSlot_BIF D st Kj Ξ sg cw
  | inactive (hcore : Φ.stageCore st = ∅) (henl : Φ.stageEnlargement st = ∅) :
      BoundaryStageSlot_BIF D st Kj Ξ sg cw

namespace BoundaryStageSlot_BIF

variable {D : BoundaryAugmentedData S Φ} {st : Fin 3} {Kj : ℕ} {Ξ sg cw : ℝ}

/-- The smoothing map `a_j` of a slot: the output's ambient nearest map `ι ∘ p` (active), the
identity (inactive). -/
def map : BoundaryStageSlot_BIF D st Kj Ξ sg cw →
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  | .active O => O.ambient
  | .inactive _ _ => fun y => y

/-- An inactive stage has empty stage clouds. -/
theorem stageCloud_eq_empty_of_inactive (hc : Φ.stageCore st = ∅)
    (he : Φ.stageEnlargement st = ∅) :
    Φ.stageCloud st = ∅ ∧ Φ.stageCloudEnlarged st = ∅ := by
  refine ⟨?_, ?_⟩
  · simp [BoundaryInteriorSlots_BIF.stageCloud, hc]
  · simp [BoundaryInteriorSlots_BIF.stageCloudEnlarged, he]

end BoundaryStageSlot_BIF

/-- **The boundary GAF02 chain** (draft 61 §3.3, D61-7): on the augmented data `D`, with jet order
`Kj`, per-stage numbers `Ξ_j, Σ_j, e_j, c_j, c_w` and GAF01's early constants `b_cut`, `L₀`, `κ`
(the augmented ones, `N_int + 1`):

* `numbers`: GAF01's CHOICE inequalities in the kernel's form (closed shape) and EDP01's
  `Σ_j ≤ ε_j/10000` (BCG05's register request), `0 ≤ c_w`;
* `slot`: the three smoothing slots;
* `cutoff_bindings`: the CFS31 bindings of the slot cutoffs `ψ_j` at the chain's own stage inputs
  `F_∂ p`, `g₁ p`, `g₂ p` (`g₁ = Ψ₀ ∘ F_∂`, `g₂ = Ψ₁ ∘ g₁`): smoothness, values in `[0, 1]`, the
  threshold-6 plateau and the threshold-7 closed-support localization in the original
  coordinates of the active family (circle `‖η_j‖`, `edgeB` `|η_j|` and `t_B = edgeB.smoothing/ρ`,
  slim `|η_j|`), and `‖Dψ_j‖ ≤ b_cut/ρ` along `[F_∂ p, g_{j−1} p]` (with a positive scale for
  `ψ₁`). -/
structure BoundaryGaf02Chain (D : BoundaryAugmentedData S Φ) (Kj : ℕ) (Ξ Sg eg c cw : Fin 3 → ℝ)
    (bcut bder κ : ℝ) : Type where
  /-- GAF01's CHOICE inequalities (closed shape with explicit early constants). -/
  numbers : (∀ j, 0 < Ξ j ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 ≤ eg j ∧
      Sg j ≤ Ξ j / 10000 ∧ 0 ≤ cw j) ∧
    5 / 3 * Ξ 0 * Sg 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * Sg 0 * bcut * bder + Ξ 0 * bder + eg 0) < c 0 ∧
    c 0 ≤ 4 * κ / 5 ∧ c 0 ≤ 3 * Sg 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (bder + c 0) +
        Ξ 1 * (bder + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * κ / 5 ∧ c 1 ≤ 3 * Sg 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) +
        Ξ 2 * (bder + c 1) + eg 2 + 2 * c 1) < c 2
  /-- The three smoothing slots. -/
  slot : ∀ st, BoundaryStageSlot_BIF D st Kj (Ξ st) (Sg st) (cw st)
  /-- The CFS31 bindings of `ψ₀` (source cutoff), `ψ₁` (CFS23) and `ψ₂` (CFS22). -/
  cutoff_bindings :
    letI := inducedMetricSpace S.completion.metric
    (ContDiff ℝ ∞ (Φ.cutoff 0) ∧ (∀ z, Φ.cutoff 0 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 0, dist p j < 200 * S.rho j ∧
          ‖S.circleEta_BIF j p‖ < 6) → Φ.cutoff 0 (S.boundaryOriginalMap p.val) = 1) ∧
      (∀ p : W.Carrier, S.boundaryOriginalMap p ∈ tsupport (Φ.cutoff 0) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
          dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ ≤ 13 / 2) ∧
      ∀ p : W.Carrier, ‖fderiv ℝ (Φ.cutoff 0) (S.boundaryOriginalMap p)‖ ≤ bcut / S.rho p) ∧
    (ContDiffOn ℝ ∞ (Φ.cutoff 1) {z | 0 < S.scaleMarker_BIF z} ∧
      (∀ z, Φ.cutoff 1 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 1, dist p j < 100 * Δ * S.rho j ∧
          |S.edgeEta_BIF j p| < 6 * Δ ∧ S.edgeHeightRaw p < 6 * Δ) →
        Φ.cutoff 1 (Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p.val)) = 1) ∧
      (∀ p : W.Carrier, Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p) ∈ tsupport (Φ.cutoff 1) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 1,
          dist q j < 100 * Δ * S.rho j ∧ |S.edgeEta_BIF j q| < 7 * Δ ∧
            S.edgeHeightRaw q < 7 * Δ) ∧
      ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < S.scaleMarker_BIF ((1 - t) • S.boundaryOriginalMap p +
          t • Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p)) ∧
        ‖fderiv ℝ (Φ.cutoff 1) ((1 - t) • S.boundaryOriginalMap p +
          t • Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p))‖ ≤ bcut / S.rho p) ∧
    (ContDiff ℝ ∞ (Φ.cutoff 2) ∧ (∀ z, Φ.cutoff 2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 2,
          dist p j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j p| < 6 * (10 ^ 5 * Δ)) →
        Φ.cutoff 2 (Φ.adjust 1 (slot 1).map (Φ.adjust 0 (slot 0).map
          (S.boundaryOriginalMap p.val))) = 1) ∧
      (∀ p : W.Carrier,
        Φ.adjust 1 (slot 1).map (Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p)) ∈
          tsupport (Φ.cutoff 2) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 2,
          dist q j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j q| < 7 * (10 ^ 5 * Δ)) ∧
      ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (Φ.cutoff 2) ((1 - t) • S.boundaryOriginalMap p +
          t • Φ.adjust 1 (slot 1).map (Φ.adjust 0 (slot 0).map (S.boundaryOriginalMap p)))‖ ≤
          bcut / S.rho p)

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S Φ} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- (ADJ) the stage adjustments `Ψ_j` of the chain. -/
def Ψ (st : Fin 3) : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  Φ.adjust st (C.slot st).map

/-- (CHAIN) `g₁ = Ψ₀ ∘ F_∂`. -/
def g₁ : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  C.Ψ 0 ∘ S.boundaryOriginalMap

/-- (CHAIN) `g₂ = Ψ₁ ∘ g₁`. -/
def g₂ : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  C.Ψ 1 ∘ C.g₁

/-- (CHAIN) the final map `E = g₃ = Ψ₂ ∘ g₂`. -/
def E : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  C.Ψ 2 ∘ C.g₂

/-- The stage outputs `g₀ = F_∂, g₁, g₂, g₃ = E`. -/
def stage : Fin 4 → W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  ![S.boundaryOriginalMap, C.g₁, C.g₂, C.E]

/-- The scale `s = ℓ_ρ(E)`. -/
def scale (p : W.Carrier) : ℝ :=
  S.scaleMarker_BIF (C.E p)

/-- The height `A = u_{E'}(E)`. -/
def height (p : W.Carrier) : ℝ :=
  S.heightCoord_BIF (C.E p)

/-- `T = A/s`. -/
def heightRatio (p : W.Carrier) : ℝ :=
  C.height p / C.scale p

/-- The boundary pair `(u_b, v_b) = J_b(E)` (BCG7-COLLAR's `J_b`). -/
def markerPair (i : Fin S.packet.cusp.count) (p : W.Carrier) : ℝ × ℝ :=
  augmentedBoundaryCoord_BC7C i (C.E p)

/-- **The global cusp core** `C_b = N₃₅(∂_b W) ∪ {v_b ≥ .9 ∧ u_b ≤ 40 v_b}` at `(u_b, v_b) = J_b(E)`
(BCG6-K's `cuspCore_BCG6K`, D61-9). -/
def cuspCore_BIF (i : Fin S.packet.cusp.count) : Set W.Carrier :=
  S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i (fun k p => (C.markerPair k p).1)
    (fun k p => (C.markerPair k p).2)

/-- **The global cusp front** `H_b = {v_b ≥ .9 ∧ u_b = 40 v_b}` at `(u_b, v_b) = J_b(E)`. -/
def cuspFront_BIF (i : Fin S.packet.cusp.count) : Set W.Carrier :=
  S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i (fun k p => (C.markerPair k p).1)
    (fun k p => (C.markerPair k p).2)

/-- The union of the cusp cores `C_∂ = ⋃_b C_b`. -/
def cuspCores_BIF : Set W.Carrier :=
  ⋃ i, C.cuspCore_BIF i

/-- `g₀ = F_∂`. -/
theorem stage_zero : C.stage 0 = S.boundaryOriginalMap :=
  rfl

/-- (CHAIN) unfolded: `E = Ψ₂ ∘ Ψ₁ ∘ Ψ₀ ∘ F_∂`. -/
theorem E_eq : C.E = C.Ψ 2 ∘ C.Ψ 1 ∘ C.Ψ 0 ∘ S.boundaryOriginalMap :=
  rfl

/-- An inactive stage is the identity. -/
theorem Ψ_eq_id_of_inactive (st : Fin 3) {hc : Φ.stageCore st = ∅}
    {he : Φ.stageEnlargement st = ∅} (h : C.slot st = .inactive hc he) : C.Ψ st = id := by
  rw [Ψ, h]
  exact Φ.adjust_id st

/-- The front in BCG7-COLLAR's set form: `H_b = {x | J_b(E x) ∈ {v ≥ .9 ∧ u = 40 v}}`. -/
theorem markerPair_eq (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    C.markerPair i p = ((C.E p (Sum.inr i)).fst 0, (C.E p (Sum.inr i)).snd) :=
  rfl

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
