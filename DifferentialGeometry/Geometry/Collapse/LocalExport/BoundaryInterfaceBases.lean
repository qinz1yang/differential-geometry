import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceChain
import DifferentialGeometry.Topology.Attachment.Defs

/-!
# Boundary route interfaces, part 3: bases, whole fibres, zero cores (lane BIFACE)

External draft 61 §3.6, §5.1, §5.4, §6.1 and dispositions D61-7, D61-10. All objects are attached
to ONE chain `C` and read `C.E` only through the stage maps `f_j = π_j ∘ C.E`; no second map, no
re-chosen family.

* `BoundaryGaf02Bases C`: the consumer-facing BASES exit (draft §3.6 table) — per stage the
  source domain `X_j ⊆ W` (open for circle and slim) and the marked base `B_j ⊆ H^∂` (inside the
  native zero set of
  the active slot), `f_j(X_j) = B_j`, the WHOLE preimage `f_j⁻¹(B_j) ∩ X_j`-properness, the
  submersion rank `k_j = (2, 1, 1)` on `X_j`, the WHOLE-preimage source domains
  `X₁ = f₁⁻¹(B₁)`, `X₃ = f₃⁻¹(B₃)`, `X₂ = f₂⁻¹(B₂) ∩ {T ≤ 4Δ}` (GAF07, EDP02 (ED)), the original
  closed threshold-3.5 sets inside them, EDP02's threshold-5 entry into `X₂`, the continuity of
  `T = C.heightRatio`, and the localization of every source point in an original
  threshold-4.01 domain (GAF06, (ELoc)), empty source and base on inactive stages, and the
  native-patch scope (`B_j` lies in the native zero set, never `p_j(Ω_j)`). The internal BASES
  content (marked-patch single-sheetedness, `5.5ℓ` coordinates, threshold-6 exhaustion, the later
  embedding `Θ₂` with its factorization; never `π₂ g₂ = π₂ E`) is BAUG-D's, mirroring the closed
  `Gaf02Bases` of lane C14-BASES.
* `BoundaryGaf02Bases.fibre`: the whole fibre `X_j ∩ f_j⁻¹{y}`.
* `BoundaryWholeFiberSpec C Bs` (D61-10): whole circle fibres (`≃ₜ Circle`), whole slim fibres
  (`≃ₜ Circle × Circle`), whole edge disk fibres (`≃ₜ ClosedCell 2` with the unit circle onto
  `fibre ∩ {C.heightRatio = 4Δ}`: the disk route's height IS `C.T`), and the buffered source
  domains (`D > 10`). Fibre types are TOPOLOGICAL here; the smooth types are theorems through the
  smooth-type bridge (never read a homeomorphism as a diffeomorphism).
* The edge source domain is NOT open: `edge_source_eq : X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}` (EDP02
  (ED)); only the circle and slim source domains are open (an open submersion domain cannot have
  closed-disk fibres).
* `BoundaryInitialCoresSpec C` (draft §6.1 `ZC`): the actual zero cores `Z_k` of `C.E` — finitely
  many compact sets, each inside the original selected zero ball of its centre of the stored
  family, every selected zero centre covered (ZSP02: `B(z, .38 r_z) ⊆ int Z_k`), pairwise
  disjoint, with smooth whole boundary faces `S²` or `T²` (topological type).
  TODO(BAUG-F/ZSP transplant): `core k` becomes the DEFINITION by the zero-block sublevel of
  `C.E` once the boundary zero tags are in the slot; the fields stay.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

/-- The stage map `f_j = π_j ∘ C.E` (never `π_j ∘ g_j`). -/
def stageMap (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (st : Fin 3) :
    W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  fun p => Φ.stageProj st (C.E p)

end BoundaryGaf02Chain

/-- **The BASES exit of the boundary chain** (draft 61 §3.6, D61-7), consumer-facing part: per
stage `j` (circle, edge, slim) the source domain `X_j`, the marked base `B_j`, `f_j(X_j) = B_j`
for `f_j = π_j ∘ C.E`, properness of `f_j|X_j : X_j → B_j`, the submersion rank `k_j` on `X_j`, the
native-patch scope and empty data on inactive stages. -/
structure BoundaryGaf02Bases (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) : Type where
  /-- The source domains `X_j`. -/
  source : Fin 3 → Set W.Carrier
  /-- The circle and slim source domains are open. -/
  isOpen_source : ∀ st, st ≠ 1 → IsOpen (source st)
  /-- The marked bases `B_j ⊆ H^∂`. -/
  base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
  /-- `f_j(X_j) = B_j`. -/
  image_eq : ∀ st, C.stageMap st '' source st = base st
  /-- The circle source domain is the WHOLE preimage of its base (GAF07). -/
  circle_source_eq : source 0 = C.stageMap 0 ⁻¹' base 0
  /-- The edge source domain (EDP02 (ED), with its proved equality): the WHOLE preimage of the
  edge base cut at the height level, `X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`; it is not open (its manifold
  boundary is `X₂ ∩ {T = 4Δ}`). -/
  edge_source_eq : source 1 = C.stageMap 1 ⁻¹' base 1 ∩ {p | C.heightRatio p ≤ 4 * Δ}
  /-- The slim source domain is the WHOLE preimage of its base (GAF07). -/
  slim_source_eq : source 2 = C.stageMap 2 ⁻¹' base 2
  /-- GAF07: the original closed circle sets `{‖η_j‖ ≤ 3.5}` lie in `X₁`. -/
  circle_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 0, dist q j < 200 * S.rho j →
      ‖S.circleEta_BIF j q‖ ≤ 7 / 2 → q.val ∈ source 0
  /-- EDP02: the original closed edge sets `{|η_j| ≤ 3.5Δ, t_B ≤ 3.5Δ}` lie in the ambient
  interior of `X₂`. -/
  edge_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 1, dist q j < 100 * Δ * S.rho j →
      |S.edgeEta_BIF j q| ≤ 7 / 2 * Δ → S.edgeHeightRaw q ≤ 7 / 2 * Δ → q.val ∈ interior (source 1)
  /-- GAF07: the original closed slim slabs `{|η_j| ≤ 3.5·10⁵Δ}` lie in `X₃`. -/
  slim_original_subset :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 2, dist q j < 1000000 * Δ * S.rho j →
      |S.slimEta_BIF j q| ≤ 350000 * Δ → q.val ∈ source 2
  /-- EDP02's threshold-5 ENTRY (review 68 A5, D68-6): an original edge point with
  `|η_j| ≤ 3.5Δ`, `t_B < 5Δ` (`t_B = edgeB.smoothing/ρ`) and `T ≤ 4Δ` lies in `X₂` (its image is in
  the marked base through the actual factorization; never `q ∈ X₂` as a premise). -/
  edge_entry :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 1, dist q j < 100 * Δ * S.rho j →
      |S.edgeEta_BIF j q| ≤ 7 / 2 * Δ → S.edgeHeightRaw q < 5 * Δ →
      C.heightRatio q.val ≤ 4 * Δ → q.val ∈ source 1
  /-- `T = A/s` is continuous on `W` (from the chain's smoothness and `s > 0`; makes the edge cut
  `{T ≤ 4Δ}` closed). -/
  heightRatio_continuous : Continuous C.heightRatio
  /-- GAF06 localization: every point of `X₁` lies in an original `{‖η_j‖ < 4.01}` domain. -/
  circle_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 0, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
      dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ < 401 / 100
  /-- EDP02 (ELoc): every point of `X₂` lies in an original `{|η_j| < 4.01Δ, t_B < 4.01Δ}`
  domain. -/
  edge_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 1, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 1,
      dist q j < 100 * Δ * S.rho j ∧ |S.edgeEta_BIF j q| < 401 / 100 * Δ ∧
        S.edgeHeightRaw q < 401 / 100 * Δ
  /-- GAF06 localization: every point of `X₃` lies in an original `{|η_j| < 4.01·10⁵Δ}`
  domain. -/
  slim_localization :
    letI := inducedMetricSpace S.completion.metric
    ∀ p ∈ source 2, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 2,
      dist q j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j q| < 401 / 100 * (10 ^ 5 * Δ)
  /-- Properness of `f_j|X_j`: compact subsets of `B_j` have compact preimages in `X_j`. -/
  proper : ∀ st, ∀ Kc ⊆ base st, IsCompact Kc → IsCompact (source st ∩ C.stageMap st ⁻¹' Kc)
  /-- The submersion rank on `X_j` is the base dimension `k_j = (2, 1, 1)`. -/
  rank_eq : ∀ st, ∀ p ∈ source st, Module.finrank ℝ (LinearMap.range
    ((mvfderiv W.model (C.stageMap st) p :
        TangentSpace W.model p →L[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
      TangentSpace W.model p →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) =
    gafStageDim st
  /-- Native-patch scope: an active stage's base lies in its native zero set `Z_j⁰`. -/
  base_subset_zeroSet : ∀ st (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (Φ.stageCloud st) (Φ.stageCloudEnlarged st) (D.stageRadius st (Sg st)) (D.stagePlane st)),
    C.slot st = .active O →
      base st ⊆ cfs15ZeroSet_C15 (Ξ st) (D.stageRadius st (Sg st)) (D.stagePlane st) O.hI
  /-- Inactive stages have empty source domain and base. -/
  inactive_empty : ∀ st (hc : Φ.stageCore st = ∅) (he : Φ.stageEnlargement st = ∅),
    C.slot st = .inactive hc he → source st = ∅ ∧ base st = ∅

namespace BoundaryGaf02Bases

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- The whole fibre `X_j ∩ f_j⁻¹{y}`. -/
def fibre (Bs : BoundaryGaf02Bases C) (st : Fin 3)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : Set W.Carrier :=
  Bs.source st ∩ C.stageMap st ⁻¹' {y}

end BoundaryGaf02Bases

/-- **The whole-fibre layer** (draft 61 §5.1, D61-10) on ONE chain `C` and ONE BASES exit `Bs`:
whole circle fibres, whole slim torus fibres, whole edge disk fibres whose boundary circles are the
vertical part `{T = 4Δ}` of the SAME chain's `T = C.heightRatio` (the disk route's height IS
`C.T` by definition, not by a stored equation), and the buffered source domains. Topological fibre
types (the smooth types are theorems). -/
structure BoundaryWholeFiberSpec (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (Bs : BoundaryGaf02Bases C) : Prop where
  /-- Whole circle fibres. -/
  circle_fibre : ∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)
  /-- Whole slim torus fibres. -/
  slim_fibre : ∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)
  /-- Whole edge disk fibres (EDP03 (EV)): the unit circle goes onto the vertical part
  `fibre ∩ {T = 4Δ}` of the SAME chain's height ratio `T = C.heightRatio`. -/
  edge_fibre : ∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
    Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
      Bs.fibre 1 y ∩ {p | C.heightRatio p = 4 * Δ}
  /-- The whole source domains lie in the buffered interior domain `{D > 10}`. -/
  source_buffered : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}

/-- **The actual zero cores of `C.E`** (draft 61 §6.1 `ZC`, §5.4): finitely many compact cores,
each inside the original selected zero ball of a centre of the stored family, pairwise disjoint,
with whole boundary faces of type `S²` or `T²` (frontier components, topological type). -/
structure BoundaryInitialCoresSpec (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  /-- The number of zero cores. -/
  count : ℕ
  /-- The zero cores `Z_k`. -/
  core : Fin count → Set W.Carrier
  /-- The zero centre of `Z_k`. -/
  centre : Fin count → W.pieceInterior ⊤
  centre_mem : ∀ k,
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    centre k ∈ S.family.zero.centres
  /-- `Z_k` lies in the original selected zero ball of its centre. -/
  core_subset_ball : ∀ k,
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∃ hk : centre k ∈ S.family.zero.centres,
      core k ⊆ riemannianBallOf g (centre k).val (S.family.zero.zero (centre k) hk).radius
  /-- ZSP02 at `a = 2/5` (the direction consumed by BCF02's zero exclusion): every selected zero
  centre `z` has a core containing the `ĝ`-ball `B(z, .38 r_z)` in its interior. -/
  zero_cover :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ z (hz : z ∈ S.family.zero.centres), ∃ k, centre k = z ∧
      ∀ q : W.pieceInterior ⊤, dist q z < 38 / 100 * (S.family.zero.zero z hz).radius →
        q.val ∈ interior (core k)
  isCompact_core : ∀ k, IsCompact (core k)
  pairwise_disjoint : Pairwise (Disjoint on core)
  /-- The face type of `Z_k`: its frontier is a whole `S²` or a whole `T²`. -/
  face_type : ∀ k, Nonempty (frontier (core k) ≃ₜ Metric.sphere (0 : E3) 1) ∨
    Nonempty (frontier (core k) ≃ₜ Circle × Circle)

namespace BoundaryInitialCoresSpec

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- The union `Z = ⋃_k Z_k` of the actual zero cores. -/
def union (ZC : BoundaryInitialCoresSpec C) : Set W.Carrier :=
  ⋃ k, ZC.core k

end BoundaryInitialCoresSpec

end DifferentialGeometry.Geometry.Collapse
