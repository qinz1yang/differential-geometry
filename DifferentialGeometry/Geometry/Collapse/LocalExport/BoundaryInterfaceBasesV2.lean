import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCoresSat
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.Handle.Manifold

/-!
# Boundary route interfaces v2, part 1: BASES with native / final bases and the edge parent
(lane BIFACEc, re-freeze after review 69)

External review 69 §1.2, §1.3, §1.5 and lead dispositions D69-1, D69-2, D69-7 (binding). The v1
objects of `LE/BoundaryInterfaceBases.lean` stay in the tree unchanged; this file adds the v2
objects with NEW names and the projections between them.

* `BoundaryGaf02Chain.nativeStageMap_BIFc st`: the NATIVE stage map `f_j⁰ = π_j ∘ g_{j+1}`
  (`g_{j+1} = C.stage st.succ`); `C.stageMap st = π_j ∘ C.E` is the FINAL map.
* `BoundaryGaf02BasesV2 C` (D69-2, D69-7): v1's correct fields with the SAME names (`source`,
  `isOpen_source`, `base`, `image_eq`, `*_source_eq`, `*_original_subset`, `edge_entry`,
  `heightRatio_continuous`, `*_localization`, `proper`, `rank_eq`, `inactive_empty`); v1's wrong
  `base_subset_zeroSet` (the FINAL base inside the NATIVE zero set) is REPLACED by the native /
  final split: `nativeBase`, `later` (the later embeddings `Θ_j`), `native_image_eq`
  (`f_j⁰(X_j) = B_j⁰`), `native_scope` (`B_j⁰ ⊆ Z_j⁰` on an active slot), `base_eq`
  (`B_j = Θ_j(B_j⁰)`), `final_factor` (`f_j = Θ_j ∘ f_j⁰` at EVERY point), `later_last`
  (`Θ₃ = id`), and the later-embedding contract on the marked patches only (never a global
  diffeomorphism): `later_isEmbedding` (topological embedding of `B_j⁰`; no merging),
  `later_contDiffAt` (smooth at the native base points), `later_retains` (chart transport: the
  marker blocks of the stage's own charts are kept). D69-7: the OPEN edge parent domain
  `edgeParent = U₂^amb` with `X₂ = U₂^amb ∩ {T ≤ 4Δ}` (`edgeParent_cut`), `U₂^amb ⊆ f₂⁻¹(B₂)`,
  smoothness of `f₂` and `T` on it, `rank df₂ = 1` on it and `rank d(f₂, T) = 2` at `T = 4Δ`.
  Closed twins: `Gaf02Chain.Θ_BAS`, `final_factor_BAS`, `finalBase_BAS`, `theta_retains_*_BAS`,
  `contDiffAt_theta_BAS` (`Fibration/ActualStageChainLater.lean`); `gafStageDomain5_BAS`
  (`ActualStageChainPatches.lean`); FDC: `Gaf02Chain.ratio_localization_FDC` (EDP02 (ELoc)),
  `Gaf02Chain.vertical_eq_FDC` (`V = {T ≤ 4Δ}`), `Gaf02Chain.stageTwo_mem_finalBase_FDC`
  (`π₂E(q) ∈ W₂ = finalBase_BAS 1` on the threshold-5 edge domain).
* Derived: `base_subset_zeroSet_last_BIFc` (the last stage keeps v1's inclusion),
  `later_injOn_BIFc` (no merging), the conditional projection `toV1_BIFc` (v1's object, given v1's
  inclusion — e.g. when every `Θ_j` is the identity) and `ofV1_BIFc` (v1's object with `Θ = id`,
  given the final factorization through the native map and an edge parent).
* Inhabitant: `BoundaryGaf02Chain.emptyBasesV2_BIFc` (the empty-family chain of BIFACE's
  inhabitants: every stage output is `F_∂`, `Θ_j = id`, empty bases and parent).
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

/-- The NATIVE stage map `f_j⁰ = π_j ∘ g_{j+1}` (`g₁, g₂, g₃ = E`); the final stage map is
`C.stageMap st = π_j ∘ C.E`. -/
def nativeStageMap_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (st : Fin 3) :
    W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  fun p => Φ.stageProj st (C.stage st.succ p)

/-- At the last stage the native map is the final map (`g₃ = E`). -/
theorem nativeStageMap_two_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    C.nativeStageMap_BIFc 2 = C.stageMap 2 :=
  rfl

/-- The rank of the final stage map `f_j = π_j ∘ C.E` at `p` (`dim range df_j`). -/
def stageRank_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (st : Fin 3)
    (p : W.Carrier) : ℕ :=
  Module.finrank ℝ (LinearMap.range
    ((mvfderiv W.model (C.stageMap st) p :
        TangentSpace W.model p →L[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
      TangentSpace W.model p →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))

/-- The rank of the pair `(f₂, T)` at `p` (`dim range d(f₂, T)`). -/
def edgePairRank_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (p : W.Carrier) : ℕ :=
  Module.finrank ℝ (LinearMap.range
    ((mvfderiv W.model (fun q => (C.stageMap 1 q, C.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) :
      TangentSpace W.model p →ₗ[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ))

end BoundaryGaf02Chain

/-- **The common core of the BASES exits v1 and v2**: v1's fields WITHOUT v1's
`base_subset_zeroSet` (same names; review 69 confirms them). -/
structure BoundaryGaf02BasesCore_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  /-- The source domains `X_j`. -/
  source : Fin 3 → Set W.Carrier
  /-- The circle and slim source domains are open (the edge source is not). -/
  isOpen_source : ∀ st, st ≠ 1 → IsOpen (source st)
  /-- The FINAL marked bases `B_j ⊆ H^∂`. -/
  base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
  /-- `f_j(X_j) = B_j` for the final map `f_j = π_j ∘ C.E`. -/
  image_eq : ∀ st, C.stageMap st '' source st = base st
  /-- The circle source domain is the WHOLE preimage of its base (GAF07). -/
  circle_source_eq : source 0 = C.stageMap 0 ⁻¹' base 0
  /-- EDP02 (ED): `X₂ = f₂⁻¹(B₂) ∩ {T ≤ 4Δ}` (not open). -/
  edge_source_eq : source 1 = C.stageMap 1 ⁻¹' base 1 ∩ {p | C.heightRatio p ≤ 4 * Δ}
  /-- The slim source domain is the WHOLE preimage of its base (GAF07). -/
  slim_source_eq : source 2 = C.stageMap 2 ⁻¹' base 2
  /-- GAF07: the original closed circle sets `{‖η_j‖ ≤ 3.5}` lie in `X₁`. -/
  circle_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 0, dist q j < 200 * S.rho j →
      ‖S.circleEta_BIF j q‖ ≤ 7 / 2 → q.val ∈ source 0
  /-- EDP02: the original closed edge sets lie in the ambient interior of `X₂`. -/
  edge_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 1, dist q j < 100 * Δ * S.rho j →
      |S.edgeEta_BIF j q| ≤ 7 / 2 * Δ → S.edgeHeightRaw q ≤ 7 / 2 * Δ → q.val ∈ interior (source 1)
  /-- GAF07: the original closed slim slabs lie in `X₃`. -/
  slim_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 2, dist q j < 1000000 * Δ * S.rho j →
      |S.slimEta_BIF j q| ≤ 350000 * Δ → q.val ∈ source 2
  /-- EDP02's threshold-5 ENTRY into `X₂` (review 68 A5; kept from v1). -/
  edge_entry :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 1, dist q j < 100 * Δ * S.rho j →
      |S.edgeEta_BIF j q| ≤ 7 / 2 * Δ → S.edgeHeightRaw q < 5 * Δ →
      C.heightRatio q.val ≤ 4 * Δ → q.val ∈ source 1
  /-- `T = A/s` is continuous on `W` (kept from v1; later an accessor of the enhanced chain). -/
  heightRatio_continuous : Continuous C.heightRatio
  /-- GAF06 localization of `X₁` in original `{‖η_j‖ < 4.01}` domains. -/
  circle_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 0, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
      dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ < 401 / 100
  /-- EDP02 (ELoc) localization of `X₂`. -/
  edge_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 1, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 1,
      dist q j < 100 * Δ * S.rho j ∧ |S.edgeEta_BIF j q| < 401 / 100 * Δ ∧
        S.edgeHeightRaw q < 401 / 100 * Δ
  /-- GAF06 localization of `X₃`. -/
  slim_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 2, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 2,
      dist q j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j q| < 401 / 100 * (10 ^ 5 * Δ)
  /-- Properness of `f_j|X_j`. -/
  proper : ∀ st, ∀ Kc ⊆ base st, IsCompact Kc → IsCompact (source st ∩ C.stageMap st ⁻¹' Kc)
  /-- The submersion rank on `X_j` is `k_j = (2, 1, 1)`. -/
  rank_eq : ∀ st, ∀ p ∈ source st, Module.finrank ℝ (LinearMap.range
    ((mvfderiv W.model (C.stageMap st) p :
        TangentSpace W.model p →L[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
      TangentSpace W.model p →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) =
    gafStageDim st
  /-- Inactive stages have empty source domain and base. -/
  inactive_empty : ∀ st (hc : Φ.stageCore st = ∅) (he : Φ.stageEnlargement st = ∅),
    C.slot st = .inactive hc he → source st = ∅ ∧ base st = ∅

/-- **The native / final split of a BASES exit** (review 69 §1.3, D69-2) on the source domains
`source` and the FINAL bases `base` of the chain `C`: native bases `B_j⁰ = f_j⁰(X_j)` inside the
native zero sets, later embeddings `Θ_j` with `B_j = Θ_j(B_j⁰)`, `f_j = Θ_j ∘ f_j⁰` at EVERY point,
`Θ₃ = id`, and the later-embedding contract on the marked patches only (topological embedding of
`B_j⁰`, smooth at its points, keeping the stage's own marker blocks). Closed twins:
`Gaf02Chain.Θ_BAS`, `final_factor_BAS`, `finalBase_BAS`, `theta_retains_*_BAS`,
`contDiffAt_theta_BAS`. -/
structure BoundaryLaterSplit_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (source : Fin 3 → Set W.Carrier) (base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) : Type where
  /-- (D69-2) the NATIVE marked bases `B_j⁰` (inside the native zero sets). -/
  nativeBase : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
  /-- (D69-2) the later embeddings `Θ_j` (`Θ₁ = Ψ₃ ∘ Ψ₂`, `Θ₂ = Ψ₃₂`, `Θ₃ = id`). -/
  later : Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  /-- (D69-2) `f_j⁰(X_j) = B_j⁰`. -/
  native_image_eq : ∀ st, C.nativeStageMap_BIFc st '' source st = nativeBase st
  /-- (D69-2) native-patch scope: on an active slot `B_j⁰ ⊆ Z_j⁰` (the native zero set). -/
  native_scope : ∀ st (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (Φ.stageCloud st) (Φ.stageCloudEnlarged st) (D.stageRadius st (Sg st)) (D.stagePlane st)),
    C.slot st = .active O →
      nativeBase st ⊆ cfs15ZeroSet_C15 (Ξ st) (D.stageRadius st (Sg st)) (D.stagePlane st) O.hI
  /-- (D69-2) `B_j = Θ_j(B_j⁰)`. -/
  base_eq : ∀ st, base st = later st '' nativeBase st
  /-- (D69-2) the final factorization `f_j = Θ_j ∘ f_j⁰` at EVERY point (never `f_j = f_j⁰`). -/
  final_factor : ∀ st p, C.stageMap st p = later st (C.nativeStageMap_BIFc st p)
  /-- (D69-2) the last stage: `Θ₃ = id`. -/
  later_last : later 2 = id
  /-- (D69-2) `Θ_j` is a topological embedding of the native base (no merging of patches). -/
  later_isEmbedding : ∀ st, IsEmbedding (fun x : nativeBase st => later st x)
  /-- (D69-2) `Θ_j` is smooth at the native base points (image-neighbourhood smoothness). -/
  later_contDiffAt : ∀ st, ∀ y ∈ nativeBase st, ContDiffAt ℝ ∞ (later st) y
  /-- (D69-2) chart transport: `Θ_j` keeps the blocks of the stage's own marker charts. -/
  later_retains : ∀ st (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = st →
    ∀ x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
      later st x (Sum.inl (S.markerTag_BAUGC m)) = x (Sum.inl (S.markerTag_BAUGC m))

/-- **The OPEN edge parent domain** (review 69 §1.2, D69-7) of a BASES exit with sources
`source` and final bases `base`: `U₂^amb` open, `X₂ = U₂^amb ∩ {T ≤ 4Δ}`, `f₂(U₂^amb) ⊆ B₂`, `f₂` and
`T` smooth on `U₂^amb`, `rank df₂ = 1` there and `rank d(f₂, T) = 2` on `T = 4Δ` (FC39's
`EdgeBundle.source` / `rank_two`; closed twin `Gaf02Chain.vertical_eq_FDC`). -/
structure BoundaryEdgeParent_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (source : Fin 3 → Set W.Carrier) (base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) : Type where
  /-- (D69-7) the OPEN edge parent domain `U₂^amb`. -/
  edgeParent : Set W.Carrier
  /-- (D69-7) `U₂^amb` is open. -/
  isOpen_edgeParent : IsOpen edgeParent
  /-- (D69-7) `X₂ = U₂^amb ∩ {T ≤ 4Δ}`. -/
  edgeParent_cut : source 1 = edgeParent ∩ {p | C.heightRatio p ≤ 4 * Δ}
  /-- (D69-7) the parent projects into the edge base: `f₂(U₂^amb) ⊆ B₂`. -/
  edgeParent_subset : edgeParent ⊆ C.stageMap 1 ⁻¹' base 1
  /-- (D69-7) `f₂` and `T` are smooth on `U₂^amb`. -/
  edgeParent_smooth : ∀ p ∈ edgeParent,
    ContMDiffAt W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      (C.stageMap 1) p ∧ ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ C.heightRatio p
  /-- (D69-7) `f₂` is a submersion onto the one-dimensional base on `U₂^amb`. -/
  edgeParent_rank : ∀ p ∈ edgeParent, C.stageRank_BIFc 1 p = 1
  /-- (D69-7) `rank d(f₂, T) = 2` on the vertical level `T = 4Δ` (hence near it). -/
  edgeParent_rank_two : ∀ p ∈ edgeParent, C.heightRatio p = 4 * Δ → C.edgePairRank_BIFc p = 2


/-- **The BASES exit of the boundary chain, v2** (review 69 §1.3, §1.2; D69-2, D69-7): the
common core (v1's correct fields, same names), the native / final split replacing v1's
`base_subset_zeroSet`, and the open edge parent domain. -/
structure BoundaryGaf02BasesV2 (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) : Type
    extends BoundaryGaf02BasesCore_BIFc C where
  /-- (D69-2) the native / final split. -/
  split : BoundaryLaterSplit_BIFc C source base
  /-- (D69-7) the open edge parent domain. -/
  parent : BoundaryEdgeParent_BIFc C source base

namespace BoundaryGaf02BasesV2

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} (Bs : BoundaryGaf02BasesV2 C)

/-- The native bases `B_j⁰` of the split. -/
abbrev nativeBase : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  Bs.split.nativeBase

/-- The later embeddings `Θ_j` of the split. -/
abbrev later : Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  Bs.split.later

/-- The open edge parent domain `U₂^amb`. -/
abbrev edgeParent : Set W.Carrier :=
  Bs.parent.edgeParent

/-- The whole fibre `X_j ∩ f_j⁻¹{y}` of the FINAL stage map. -/
def fibre (st : Fin 3) (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    Set W.Carrier :=
  Bs.source st ∩ C.stageMap st ⁻¹' {y}

/-- At the last stage the final base is the native base. -/
theorem base_two_eq_nativeBase_BIFc : Bs.base 2 = Bs.nativeBase 2 := by
  rw [Bs.split.base_eq, Bs.split.later_last, image_id]

/-- **v1's inclusion survives at the last stage**: an active last slot has its (final = native)
base in the native zero set. -/
theorem base_subset_zeroSet_last_BIFc (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2)
    (Φ.stageCloud 2) (Φ.stageCloudEnlarged 2) (D.stageRadius 2 (Sg 2)) (D.stagePlane 2))
    (h : C.slot 2 = .active O) :
    Bs.base 2 ⊆ cfs15ZeroSet_C15 (Ξ 2) (D.stageRadius 2 (Sg 2)) (D.stagePlane 2) O.hI := by
  rw [Bs.base_two_eq_nativeBase_BIFc]
  exact Bs.split.native_scope 2 O h

/-- No merging: `Θ_j` is injective on the native base. -/
theorem later_injOn_BIFc (st : Fin 3) : InjOn (Bs.later st) (Bs.nativeBase st) := by
  intro x hx y hy hxy
  have h := (Bs.split.later_isEmbedding st).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val h

/-- The final base is the image of the source under the final factorization. -/
theorem image_later_native_BIFc (st : Fin 3) :
    Bs.later st '' (C.nativeStageMap_BIFc st '' Bs.source st) = Bs.base st := by
  rw [Bs.split.native_image_eq, Bs.split.base_eq]

/-- `X₂ ⊆ U₂^amb`. -/
theorem source_one_subset_edgeParent_BIFc : Bs.source 1 ⊆ Bs.edgeParent := by
  rw [Bs.parent.edgeParent_cut]
  exact inter_subset_left

/-- **Conditional projection to v1** (`toV1_BIFc`): v1's object with the same sources and bases,
given v1's native-scope inclusion of the FINAL bases (true when every `Θ_j` is the identity, e.g.
on the empty family; false in general — that is review 69's P0 item). -/
def toV1_BIFc (h : ∀ st (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (Φ.stageCloud st) (Φ.stageCloudEnlarged st) (D.stageRadius st (Sg st)) (D.stagePlane st)),
    C.slot st = .active O →
      Bs.base st ⊆ cfs15ZeroSet_C15 (Ξ st) (D.stageRadius st (Sg st)) (D.stagePlane st) O.hI) :
    BoundaryGaf02Bases C where
  source := Bs.source
  isOpen_source := Bs.isOpen_source
  base := Bs.base
  image_eq := Bs.image_eq
  circle_source_eq := Bs.circle_source_eq
  edge_source_eq := Bs.edge_source_eq
  slim_source_eq := Bs.slim_source_eq
  circle_original_subset := Bs.circle_original_subset
  edge_original_subset := Bs.edge_original_subset
  slim_original_subset := Bs.slim_original_subset
  edge_entry := Bs.edge_entry
  heightRatio_continuous := Bs.heightRatio_continuous
  circle_localization := Bs.circle_localization
  edge_localization := Bs.edge_localization
  slim_localization := Bs.slim_localization
  proper := Bs.proper
  rank_eq := Bs.rank_eq
  base_subset_zeroSet := h
  inactive_empty := Bs.inactive_empty

/-- `toV1_BIFc` keeps the sources. -/
theorem toV1_source_BIFc (h : ∀ st (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (Φ.stageCloud st) (Φ.stageCloudEnlarged st) (D.stageRadius st (Sg st)) (D.stagePlane st)),
    C.slot st = .active O →
      Bs.base st ⊆ cfs15ZeroSet_C15 (Ξ st) (D.stageRadius st (Sg st)) (D.stagePlane st) O.hI) :
    (Bs.toV1_BIFc h).source = Bs.source ∧ (Bs.toV1_BIFc h).base = Bs.base :=
  ⟨rfl, rfl⟩

/-- When every later embedding is the identity, v1's inclusion holds (`B_j = B_j⁰ ⊆ Z_j⁰`). -/
theorem base_subset_zeroSet_of_later_id_BIFc (hid : ∀ st, Bs.later st = id) (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (Φ.stageCloud st) (Φ.stageCloudEnlarged st) (D.stageRadius st (Sg st)) (D.stagePlane st))
    (h : C.slot st = .active O) :
    Bs.base st ⊆ cfs15ZeroSet_C15 (Ξ st) (D.stageRadius st (Sg st)) (D.stagePlane st) O.hI := by
  rw [Bs.split.base_eq, show Bs.split.later st = id from hid st, image_id]
  exact Bs.split.native_scope st O h

end BoundaryGaf02BasesV2

namespace BoundaryGaf02Bases

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **v1 → v2 with `Θ = id`** (`ofV1_BIFc`): a v1 object whose final map factors through the
native map at every point (`f_j = f_j⁰`, i.e. the later adjustments do not move the stage
coordinates) and an open edge parent with the v2 parent clauses. -/
def ofV1_BIFc (Bs : BoundaryGaf02Bases C)
    (hfac : ∀ st p, C.stageMap st p = C.nativeStageMap_BIFc st p)
    (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : Bs.source 1 = U ∩ {p | C.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.stageMap 1 ⁻¹' Bs.base 1)
    (hsm : ∀ p ∈ U,
      ContMDiffAt W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
        (C.stageMap 1) p ∧ ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ C.heightRatio p)
    (hrk : ∀ p ∈ U, C.stageRank_BIFc 1 p = 1)
    (hrk2 : ∀ p ∈ U, C.heightRatio p = 4 * Δ → C.edgePairRank_BIFc p = 2) :
    BoundaryGaf02BasesV2 C where
  toBoundaryGaf02BasesCore_BIFc :=
    { source := Bs.source
      isOpen_source := Bs.isOpen_source
      base := Bs.base
      image_eq := Bs.image_eq
      circle_source_eq := Bs.circle_source_eq
      edge_source_eq := Bs.edge_source_eq
      slim_source_eq := Bs.slim_source_eq
      circle_original_subset := Bs.circle_original_subset
      edge_original_subset := Bs.edge_original_subset
      slim_original_subset := Bs.slim_original_subset
      edge_entry := Bs.edge_entry
      heightRatio_continuous := Bs.heightRatio_continuous
      circle_localization := Bs.circle_localization
      edge_localization := Bs.edge_localization
      slim_localization := Bs.slim_localization
      proper := Bs.proper
      rank_eq := Bs.rank_eq
      inactive_empty := Bs.inactive_empty }
  split :=
    { nativeBase := Bs.base
      later := fun _ => id
      native_image_eq := fun st => by
        rw [← Bs.image_eq st]
        exact image_congr fun p _ => (hfac st p).symm
      native_scope := Bs.base_subset_zeroSet
      base_eq := fun st => (image_id _).symm
      final_factor := hfac
      later_last := rfl
      later_isEmbedding := fun _ => IsEmbedding.subtypeVal
      later_contDiffAt := fun _ _ _ => contDiffAt_id
      later_retains := fun _ _ _ _ => rfl }
  parent :=
    { edgeParent := U
      isOpen_edgeParent := hU
      edgeParent_cut := hcut
      edgeParent_subset := hsub
      edgeParent_smooth := hsm
      edgeParent_rank := hrk
      edgeParent_rank_two := hrk2 }

end BoundaryGaf02Bases

/-! ## Inhabitant: the empty-family chain -/

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- Over the empty slot every stage output is the original map `F_∂`. -/
theorem stage_eq_of_emptySlots_BIFc (k : Fin 4) : C.stage k = S.boundaryOriginalMap := by
  fin_cases k <;>
    simp [BoundaryGaf02Chain.stage, BoundaryGaf02Chain.g₁, BoundaryGaf02Chain.g₂,
      BoundaryGaf02Chain.E, BoundaryGaf02Chain.Ψ, BoundarySupply.emptySlots_adjust_BIF]

/-- Over the empty slot the final and the native stage maps agree. -/
theorem stageMap_eq_native_of_emptySlots_BIFc (st : Fin 3) (p : W.Carrier) :
    C.stageMap st p = C.nativeStageMap_BIFc st p := by
  simp only [BoundaryGaf02Chain.stageMap, BoundaryGaf02Chain.nativeStageMap_BIFc,
    C.stage_eq_of_emptySlots_BIFc, C.E_eq_of_emptySlots_BIF]

/-- **Empty v2 bases** on a chain over the empty slot of a supply with empty stage centres
(`Θ_j = id`, empty sources, bases and edge parent): v1's `emptyBases_BIF` through `ofV1_BIFc`. -/
def emptyBasesV2_BIFc (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap) :
    BoundaryGaf02BasesV2 C :=
  (C.emptyBases_BIF hc hF).ofV1_BIFc C.stageMap_eq_native_of_emptySlots_BIFc ∅ isOpen_empty
    (by simp [emptyBases_BIF]) (empty_subset _) (fun p hp => (notMem_empty p hp).elim)
    (fun p hp => (notMem_empty p hp).elim) (fun p hp => (notMem_empty p hp).elim)

/-- The empty v2 bases have empty sources, bases, native bases and edge parent. -/
theorem emptyBasesV2_eq_BIFc (hc : ∀ st, S.stageCentres_BIF st = ∅)
    (hF : Continuous S.boundaryOriginalMap) (st : Fin 3) :
    (C.emptyBasesV2_BIFc hc hF).source st = ∅ ∧ (C.emptyBasesV2_BIFc hc hF).base st = ∅ ∧
      (C.emptyBasesV2_BIFc hc hF).nativeBase st = ∅ ∧ (C.emptyBasesV2_BIFc hc hF).edgeParent = ∅ :=
  ⟨rfl, rfl, rfl, rfl⟩

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
