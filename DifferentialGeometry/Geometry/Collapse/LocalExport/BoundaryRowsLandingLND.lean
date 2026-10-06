import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecompositionV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlotV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedDataPV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCorollaries
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSupply
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationRowsBCF
import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceSlimCutV2
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRoughData
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransfer

/-!
# The boundary rows' landing records (D69-10, D74-16, D74-5): `BoundaryGeometricExports74` and
`BoundaryRowsLink`

Lane S-LANDING (`_LND74`), G3. The frozen records of text v3.1 §R (`TargetsBoundary-v3.1.lean.txt`,
sections "Labels of the circle-base faces" and "R. The last link"), taken VERBATIM into the
production namespace `DifferentialGeometry.Geometry.Collapse`:

* `CircleFaceLabel74`, `circleFaceSet74`, `CircleBaseCorners74` (G6c's corner model of the circle
  base `C₁ = f₁(R_c)`, the labels of its faces);
* **`BoundaryGeometricExports74 C dec`** (Prop): the outputs of the E–G rows on the SAME chain `C`
and
  the SAME decomposition `dec`; no `FC39RowsV2` / `StrongCertificate` / `ZeroDomains` / ... field;
* **`BoundaryRowsLink C dec Et Rw`** (Prop): the equality table of D74-5 adapted to the boundary
  (rows directly on `W`, no carrier transport).
NEVER `∀ dec, Nonempty (BoundaryGeometricExports74 C dec)`: the producer chooses `dec` and `geom`
together.
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

section Labels

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- The labels of the faces of the circle base `C₁ = f₁(R_c)` (FC39 `CircleFaceLabel`): a horizontal
face (a zero face, a cusp front, a NEW slim end — the edge labels of `Kc`) or the vertical edge face
`V_e = P_e ∩ {T = 4Δ}`. -/
abbrev CircleFaceLabel74 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Kc : BoundaryCompactSlimChoiceV2 Bs) : Type :=
  Kc.EdgeFaceLabel_BIFc ⊕ Unit

/-- The ACTUAL ambient face of a circle-base label. -/
def circleFaceSet74 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    CircleFaceLabel74 Kc → Set W.Carrier
  | .inl ℓ => Kc.edgeFaceSet_BIFc ℓ
  | .inr _ => Kc.verticalFace

/-- **The corner model of the circle base** (G6c's conclusion; FC39 `JunctionsV2.local_faces`, draft
74
§3.6 "`C₁` corners"): at every point `y` of `C₁ = f₁(R_c)` off its relative interior in `B₀`, one or
two
labelled smooth face functions `φ_f` of the base near `y` with `φ_f y = 0`, zero set in `C₁` = the
base
points whose WHOLE circle fibre lies in the face, INDEPENDENT differentials (through `f₁`, at every
point of the fibre) and `C₁ = {φ_f ≤ 0 ∀ f}` near `y`. -/
def CircleBaseCorners74 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Kc : BoundaryCompactSlimChoiceV2 Bs) : Prop :=
  ∀ y ∈ C.stageMap 0 '' Kc.remainder,
    y ∉ relInterior_BIF (Bs.base 0) (C.stageMap 0 '' Kc.remainder) →
    ∃ (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
      (L : Finset (CircleFaceLabel74 Kc))
      (φ : CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
      IsOpen O ∧ y ∈ O ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
      (∀ f ∈ L, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0 ∧
        {y' | y' ∈ O ∧ y' ∈ C.stageMap 0 '' Kc.remainder ∧ φ f y' = 0} =
          {y' | y' ∈ O ∧ y' ∈ C.stageMap 0 '' Kc.remainder ∧ Bs.fibre 0 y' ⊆ circleFaceSet74 Kc f})
              ∧
      (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
        fun f : L => mvfderiv W.model (fun q => φ f (C.stageMap 0 q)) p v) ∧
      (C.stageMap 0 '' Kc.remainder) ∩ O = {y' | y' ∈ O ∩ Bs.base 0 ∧ ∀ f ∈ L, φ f y' ≤ 0}

end Labels

section Rows

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **`BoundaryGeometricExports74 C dec`** (D69-10, D74-16; draft 74 §4.3): the outputs of the E–G
rows on
the SAME chain `C` and the SAME decomposition `dec` — each field is the conclusion of the named row
(NOT a
wish list; no `FC39RowsV2` / `StrongCertificate` / `ZeroDomains` / … field, D74-4). Four groups:
(1) the actual smooth stage restrictions ARE `dec` (`dec.bases`, `dec.fibres` of the same final maps
`f_j = C.stageMap j`; good open base neighbourhoods are not needed: `dec.fibres` has a whole chart
at
EVERY base point) plus G4s; (2) the same-chain ZSP02 zero cores ARE `dec.zero` plus F5z; (3) the
same-product BCG06 cusp cores: E4b, E4c (the product as a smooth embedding into `W`) and the collar
shrink; (4) smooth `K₃` (`dec.slim`), whole fibres
(`dec.fibres`), EDP–BCF faces and corners: F1, F4b, F4c, F5, G3, G6, G6c, G7. -/
structure BoundaryGeometricExports74 (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2 C) : Prop where
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

/-- **`BoundaryRowsLink C dec Et Rw`** (D69-10, D74-5's equality table adapted to the boundary: rows
directly on `W`, no carrier transport): the rows ARE the decomposition of the SAME chain. Zero: an
EQUIVALENCE of indices (every actual zero domain is listed), ranges `Z_k`, the rows' ratio = `dec`'s
GLOBAL defining function (hence `= u_k/v_k − 2/5` near the face, `dec.zero.ratio_near`). Cusp:
ranges
`C_b`, internal ends = fronts `H_b`, `cuspFn = u_b − 40 v_b` on `near` (the external end = `Et`'s
torus
pointwise is the rows' own `external_end`). Slim: an equivalence with the actual components of
`K₃ ∩ D₃`, each piece the WHOLE `f₃`-preimage. Edge / circle: a topological embedding of the rows'
base
into `B₂` / `B₀` with the FINAL maps `f_j = C.stageMap j`, sources inside `U₂^amb` / `X₁`, height
`T = C.heightRatio`, level `4Δ`, compact bases = `f₂(P_e)` / `f₁(R_c)`, WHOLE disks / fibres, pieces
`P_e` / `R_c`. Regions: `M₁ / M₂ / M₃` of the rows = `C.M₁_BIFc`, `dec.slim.M₂`, `R_c`. -/
structure BoundaryRowsLink (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2 C) (Et : BoundaryTori W S.packet.cusp.count)
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

end Rows

end DifferentialGeometry.Geometry.Collapse
