import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsLandingLND
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b

/-!
# The boundary decomposition on the whole-fibre layer v2b and the §R records on it (lane O-BD1)

Named revision for text v3.2 (lead decision 2026-10-05 21:2x, the same revision as the 20:4x V2b
decision of lane O-WF, not a new contract): `BoundaryActualDecompositionV2.fibres` is a
`BoundaryWholeFiberSpecV2`, whose buffer `sources ⊆ {D > 10}` is not provable for the actual bases
(the chart centres lie in `{D > 10}`, the sources only in `{D > 5}`); the A4 production gives
`BoundaryWholeFiberSpecV2b`. So the decomposition and the records of text v3.1 §R are restated on
the v2b layer, VERBATIM otherwise (no field of the records uses the buffer):

* `BoundaryActualDecompositionV2b C` (the five fields of `BoundaryActualDecompositionV2`, with
  `fibres : BoundaryWholeFiberSpecV2b C bases`);
* projections: `BoundaryActualDecompositionV2.toV2b_OBD` (always, `{D > 10} ⊆ {D > 5}`) and
  `BoundaryActualDecompositionV2b.toV2_OBD` (ONLY given `h10 : ∀ st, sources ⊆ {D > 10}`);
* **`BoundaryGeometricExports74b C dec`** and **`BoundaryRowsLink74b C dec Et Rw`**: the records
  `BoundaryGeometricExports74` / `BoundaryRowsLink` (S-LANDING G3, = text v3.1 §R token for token)
  with `dec : BoundaryActualDecompositionV2b C`; transfer along both projections
  (`BoundaryGeometricExports74.toV2b_OBD`, `BoundaryGeometricExports74b.toV2_OBD`,
  `BoundaryRowsLink.toV2b_OBD`, `BoundaryRowsLink74b.toV2_OBD`);
* inhabitant: `BoundaryGaf02Chain.emptyDecompositionV2b_OBD` (the empty v2 decomposition).

NEVER `∀ dec, Nonempty (BoundaryGeometricExports74b C dec)`: the producer chooses `dec` and the
exports together (`exists_boundaryGeometricExports74b_OBD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

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

section Rows

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The actual decomposition data of the boundary branch on the v2b layer** (named revision for
text v3.2): the five fields of `BoundaryActualDecompositionV2` on ONE chain `C`, the whole-fibre
layer being `BoundaryWholeFiberSpecV2b` (sources in `{D > 5}`). -/
structure BoundaryActualDecompositionV2b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  bases : BoundaryGaf02BasesV2 C
  fibres : BoundaryWholeFiberSpecV2b C bases
  zero : BoundaryActualZeroDomains_BIFc C bases
  slim : BoundaryCompactSlimChoiceV2 bases
  edge : BoundaryRelativeEdgeRestrictionV2 slim

/-- **v2 gives v2b** (the buffer `{D > 10} ⊆ {D > 5}`; all other fields unchanged). -/
def BoundaryActualDecompositionV2.toV2b_OBD {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (dec : BoundaryActualDecompositionV2 C) : BoundaryActualDecompositionV2b C where
  bases := dec.bases
  fibres := dec.fibres.toV2b_OWF
  zero := dec.zero
  slim := dec.slim
  edge := dec.edge

/-- **v2b gives v2 ONLY when the sources lie in `{D > 10}`**. -/
def BoundaryActualDecompositionV2b.toV2_OBD {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (dec : BoundaryActualDecompositionV2b C)
    (h10 : ∀ st, dec.bases.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}) :
    BoundaryActualDecompositionV2 C where
  bases := dec.bases
  fibres := dec.fibres.toV2_OWF h10
  zero := dec.zero
  slim := dec.slim
  edge := dec.edge

/-- **`BoundaryGeometricExports74b C dec`** (text v3.1 §R `BoundaryGeometricExports74`, D69-10,
D74-16, VERBATIM on `dec : BoundaryActualDecompositionV2b C`; named revision for text v3.2): the
outputs of the E–G rows on the SAME chain `C` and the SAME decomposition `dec`. Four groups: (1) the
actual smooth stage restrictions ARE `dec` plus G4s; (2) the same-chain ZSP02 zero cores ARE
`dec.zero` plus F5z; (3) the same-product BCG06 cusp cores: E4b, E4c and the collar shrink; (4)
smooth `K₃`, whole fibres, EDP–BCF faces and corners: F1, F4b, F4c, F5, G3, G6, G6c, G7. -/
structure BoundaryGeometricExports74b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2b C) : Prop where
  /-- (1) G4s: the descended edge face functions are smooth on an open set around each zero. -/
  edgeFacesSmooth : ∀ ℓ, ∀ y ∈ dec.bases.base 1, dec.edge.faceFun ℓ y = 0 →
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧
      ContDiffOn ℝ ∞ (dec.edge.faceFun ℓ) O
  /-- (2) F5z: a zero face meeting `X₃` is ONE whole slim fibre. -/
  zeroSlim : ∀ k : S.ZeroIdx_BAUGC, (C.actualZeroFace_BIFc k ∩ dec.bases.source 2).Nonempty →
    ∃ y ∈ dec.bases.base 2, C.actualZeroFace_BIFc k = dec.bases.fibre 2 y
  /-- (3) E4b: BCG06's bare spec at `J_b(C.E)` (labelled smooth product `T² × [0, 1]`, end `0` =
  the boundary component, end `1` = the front, regular defining function, `v = 1` near the front).
  -/
  cusp : BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
    (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) S.zeroBall_BCG6K
  /-- (3) E4c: the SAME whole-core product as a smooth embedding into `W` (end `0` = the boundary
  component, end `1` = the front). -/
  cuspProduct : ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
    IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧ range Φ = C.cuspCore_BIF i ∧
    (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
    (range fun t => Φ (t, iccEnd true)) = C.cuspFront_BIF i
  /-- (3) the collar shrink: an open neighbourhood of the boundary component inside the core whose
  closure misses the front (FC39 `collar_owned` / `collar_closure_off`). -/
  cuspCollar : ∀ i : Fin S.packet.cusp.count, ∃ U : Set W.Carrier, IsOpen U ∧
    S.packet.cusp.component i ⊆ U ∧ U ⊆ C.cuspCore_BIF i ∧ Disjoint (closure U) (C.cuspFront_BIF i)
  /-- (4) F1: the rim of every whole edge disk is ONE whole circle fibre of the same final map. -/
  diskRim : ∀ y ∈ dec.bases.base 1, ∀ p ∈ dec.bases.fibre 1 y, C.heightRatio p = 4 * Δ →
    p ∈ dec.bases.source 0 ∧ dec.bases.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} =
      dec.bases.fibre 0 (C.stageMap 0 p)
  /-- (4) F4b: `M₁ ⊆ {D ≥ 35}`. -/
  buffer : C.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p}
  /-- (4) F4c: the faces of `M₁` are the actual zero faces and the cusp fronts. -/
  frontierM₁ : frontier C.M₁_BIFc = (⋃ k, C.actualZeroFace_BIFc k) ∪ ⋃ i, C.cuspFront_BIF i
  /-- (4) F5: a cusp front meeting `X₃` is ONE whole slim fibre. -/
  frontSlim : ∀ i : Fin S.packet.cusp.count, (C.cuspFront_BIF i ∩ dec.bases.source 2).Nonempty →
    ∃ y ∈ dec.bases.base 2, C.cuspFront_BIF i = dec.bases.fibre 2 y
  /-- (4) G3 at `K₃ = dec.slim.K₃`: the three face identities of BCF01. -/
  faces : dec.slim.piece ∩ dec.slim.M₂ = frontier dec.slim.piece \ frontier C.M₁_BIFc ∧
    frontier dec.slim.M₂ = (frontier C.M₁_BIFc \ dec.slim.piece) ∪
      (frontier dec.slim.piece \ frontier C.M₁_BIFc) ∧
    Disjoint (frontier C.M₁_BIFc \ dec.slim.piece) (frontier dec.slim.piece \ frontier C.M₁_BIFc)
  /-- (4) G6: BCF02's pieces, `R_c` a union of WHOLE circle fibres, one active label at corners. -/
  pieces : IsCompact dec.slim.edgePiece ∧ IsCompact dec.slim.remainder ∧
    dec.slim.M₂ = dec.slim.edgePiece ∪ dec.slim.remainder ∧ dec.slim.remainder ⊆ dec.bases.source 0
        ∧
    dec.slim.edgePiece ∩ dec.slim.remainder = dec.slim.verticalFace ∧
    dec.slim.remainder ∩ frontier dec.slim.M₂ =
      frontier dec.slim.M₂ \ relInterior_BIF (frontier dec.slim.M₂) dec.slim.horizontalFace ∧
    dec.slim.remainder =
      dec.bases.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' dec.slim.remainder) ∧
    ∀ p ∈ dec.slim.verticalFace ∩ dec.slim.horizontalFace,
      ∃! ℓ, dec.edge.faceFun ℓ (C.stageMap 1 p) = 0
  /-- (4) G6c: the corner model of the circle base `C₁ = f₁(R_c)`. -/
  circleCorners : CircleBaseCorners74 dec.slim
  /-- (4) G7: the embedded face partition of every face component of `∂M₂` (disks = whole edge
  fibres over `f₂(H_e)`, pieces = `R_c`). -/
  partition : ∀ x ∈ frontier dec.slim.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
      (connectedComponentIn (frontier dec.slim.M₂) x),
    (∀ i, ∃ y ∈ C.stageMap 1 '' dec.slim.horizontalFace,
      Subtype.val '' P.disk i = connectedComponentIn (frontier dec.slim.M₂) x ∩ dec.bases.fibre 1 y)
          ∧
    Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier dec.slim.M₂) x ∩
        dec.slim.remainder
  /-- (4) G7, cusp branch: a front is ONE whole slim fibre inside `S`, or a whole boundary
  component of `R_c` disjoint from `P_e`. -/
  cuspFace : ∀ i : Fin S.packet.cusp.count,
    (∃ y ∈ dec.bases.base 2, C.cuspFront_BIF i = dec.bases.fibre 2 y ∧
      C.cuspFront_BIF i ⊆ dec.slim.piece) ∨
    (∃ x ∈ dec.slim.remainder, C.cuspFront_BIF i =
        connectedComponentIn (frontier dec.slim.remainder) x ∧
      Disjoint (C.cuspFront_BIF i) dec.slim.edgePiece)


/-- **`BoundaryRowsLink74b C dec Et Rw`** (text v3.1 §R `BoundaryRowsLink`, D69-10, D74-5, VERBATIM
on `dec : BoundaryActualDecompositionV2b C`; named revision for text v3.2): the rows ARE the
decomposition of the SAME chain — zero equivalence and global ratio, cusp ranges / fronts /
defining function, slim components = whole `f₃`-preimages, edge / circle base embeddings with the
FINAL maps, height, level, whole disks / fibres, regions `M₁ / M₂ / M₃`. -/
structure BoundaryRowsLink74b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2b C) (Et : BoundaryTori W S.packet.cusp.count)
    (Rw : FC39P0.FC39RowsV2 W Et) : Prop where
  zero : ∃ σ : Fin Rw.zero.count ≃ S.ZeroIdx_BAUGC, ∀ k,
    range (Rw.zero.piece k).map = C.actualZeroDomain_BIFc (σ k) ∧
      Rw.zero.ratio k = dec.zero.defFn (σ k)
  cusp : ∀ i, range (Rw.cusp.piece i).map = C.cuspCore_BIF i ∧
    (range fun t => (Rw.cusp.piece i).map (Rw.cusp.product i (t, iccEnd true))) = C.cuspFront_BIF i
        ∧
    ∀ x ∈ Rw.cusp.near i,
      Rw.cusp.cuspFn i x = chainBoundaryU_BCG6K C.E i x - 40 * chainBoundaryV_BCG6K C.E i x
  slim : Rw.slim.union = dec.slim.piece ∧
    ∃ σ : Fin Rw.slim.count ≃ FC39P0.ActualComponent (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc),
      ∀ j, range (Rw.slim.piece j).map = dec.bases.source 2 ∩ C.stageMap 2 ⁻¹' (σ j).1
  edge : ∃ ι : Rw.edge.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
    IsEmbedding ι ∧ range ι ⊆ dec.bases.base 1 ∧
    ι '' Rw.edge.cbase = C.stageMap 1 '' dec.slim.edgePiece ∧
    (∀ x : Rw.edge.source, x.1 ∈ dec.bases.edgeParent ∧ ι (Rw.edge.proj x) = C.stageMap 1 x.1 ∧
      Rw.edge.height x = C.heightRatio x.1) ∧
    Rw.edge.level = 4 * Δ ∧ (∀ c', Rw.edge.disk c' = dec.bases.fibre 1 (ι c')) ∧
    Rw.edge.edgePiece = dec.slim.edgePiece
  circle : ∃ ι : Rw.circle.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
    IsEmbedding ι ∧ range ι ⊆ dec.bases.base 0 ∧
    ι '' Rw.circle.cbase = C.stageMap 0 '' dec.slim.remainder ∧
    (∀ x : Rw.circle.domain, x.1 ∈ dec.bases.source 0 ∧ ι (Rw.circle.proj x) = C.stageMap 0 x.1) ∧
    (∀ c', Rw.circle.fibre c' = dec.bases.fibre 0 (ι c')) ∧
    Rw.circle.region = dec.slim.remainder
  regions : FC39P0.regionM1 Rw.zero Rw.cusp = C.M₁_BIFc ∧ FC39P0.regionM2 Rw.slim = dec.slim.M₂ ∧
    FC39P0.regionM3 Rw.slim Rw.edge = dec.slim.remainder


variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- The v3.1 exports of a v2 decomposition are the v2b exports of its v2b projection. -/
theorem BoundaryGeometricExports74.toV2b_OBD {dec : BoundaryActualDecompositionV2 C}
    (geom : BoundaryGeometricExports74 C dec) : BoundaryGeometricExports74b C dec.toV2b_OBD where
  edgeFacesSmooth := geom.edgeFacesSmooth
  zeroSlim := geom.zeroSlim
  cusp := geom.cusp
  cuspProduct := geom.cuspProduct
  cuspCollar := geom.cuspCollar
  diskRim := geom.diskRim
  buffer := geom.buffer
  frontierM₁ := geom.frontierM₁
  frontSlim := geom.frontSlim
  faces := geom.faces
  pieces := geom.pieces
  circleCorners := geom.circleCorners
  partition := geom.partition
  cuspFace := geom.cuspFace

/-- The v2b exports are the v3.1 exports of the v2 projection (when it exists, `h10`). -/
theorem BoundaryGeometricExports74b.toV2_OBD {dec : BoundaryActualDecompositionV2b C}
    (h10 : ∀ st, dec.bases.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p})
    (geom : BoundaryGeometricExports74b C dec) :
    BoundaryGeometricExports74 C (dec.toV2_OBD h10) where
  edgeFacesSmooth := geom.edgeFacesSmooth
  zeroSlim := geom.zeroSlim
  cusp := geom.cusp
  cuspProduct := geom.cuspProduct
  cuspCollar := geom.cuspCollar
  diskRim := geom.diskRim
  buffer := geom.buffer
  frontierM₁ := geom.frontierM₁
  frontSlim := geom.frontSlim
  faces := geom.faces
  pieces := geom.pieces
  circleCorners := geom.circleCorners
  partition := geom.partition
  cuspFace := geom.cuspFace

/-- The v3.1 rows link of a v2 decomposition is the v2b link of its v2b projection. -/
theorem BoundaryRowsLink.toV2b_OBD {dec : BoundaryActualDecompositionV2 C}
    {Et : BoundaryTori W S.packet.cusp.count} {Rw : FC39P0.FC39RowsV2 W Et}
    (L : BoundaryRowsLink C dec Et Rw) : BoundaryRowsLink74b C dec.toV2b_OBD Et Rw where
  zero := L.zero
  cusp := L.cusp
  slim := L.slim
  edge := L.edge
  circle := L.circle
  regions := L.regions

/-- The v2b rows link is the v3.1 link of the v2 projection (when it exists, `h10`). -/
theorem BoundaryRowsLink74b.toV2_OBD {dec : BoundaryActualDecompositionV2b C}
    (h10 : ∀ st, dec.bases.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p})
    {Et : BoundaryTori W S.packet.cusp.count} {Rw : FC39P0.FC39RowsV2 W Et}
    (L : BoundaryRowsLink74b C dec Et Rw) : BoundaryRowsLink C (dec.toV2_OBD h10) Et Rw where
  zero := L.zero
  cusp := L.cusp
  slim := L.slim
  edge := L.edge
  circle := L.circle
  regions := L.regions

end Rows

/-! ## Inhabitant: the empty-family chain -/

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {D : BoundaryAugmentedData S S.emptySlots_BIF}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **The empty decomposition on the v2b layer** (the v2b projection of `emptyDecompositionV2_BIFc`;
empty stage and zero centres). -/
def emptyDecompositionV2b_OBD
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) : BoundaryActualDecompositionV2b C :=
  (C.emptyDecompositionV2_BIFc hc hF hz0).toV2b_OBD

/-- The empty v2b decomposition has the empty bases (no slim, edge or circle source). -/
theorem emptyDecompositionV2b_source_OBD
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) (st : Fin 3) :
    (C.emptyDecompositionV2b_OBD hc hF hz0).bases.source st = ∅ :=
  rfl

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
