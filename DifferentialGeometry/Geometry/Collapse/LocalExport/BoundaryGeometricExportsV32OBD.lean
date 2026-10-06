import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD

/-!
# The v3.2 corner model `CircleBaseCornersV32` and the exports `BoundaryGeometricExports74V32`

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G4 (review 77 D77-2 / D77-10: "V32 exports saved, G7
and landing consume; old → new exports only forgetful"; owner O-BD2b). The two records of the
frozen text v3.2 (`evidence/boundary/TargetsBoundary-v3.2.lean.txt`, section "Labels of the
circle-base faces and the corner model V32 (R9)" and §R), VERBATIM:

* `CircleBaseCornersV32 Kc` = `CircleBaseCorners74 Kc` (S-LANDING G3) plus the label completeness
  clause `∀ f, whole circle fibre of y ⊆ face f → f ∈ L` (R9); `CircleBaseCornersV32.toCorners74`;
* `BoundaryGeometricExports74V32 C dec` = `BoundaryGeometricExports74b C dec` (O-BD1 G1) with
  `circleCorners : CircleBaseCornersV32 dec.slim`; `.toExports74b` (forgetful), and
  `BoundaryGeometricExports74V32.ofExports74b_OBD` (the v2b exports AND a V32 corner proof — the
  only way up, never from the old corners alone);
* `circleBaseCornersV32_of_remainder_empty_OBD`: compiled inhabitant of the corner record (empty
  remaining circle piece).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

/-- **The corner model of the circle base, v3.2** (R9, CANDIDATE; G6c's conclusion; FC39
`JunctionsV2.local_faces`, draft 74 §3.6 "`C₁` corners"): `CircleBaseCorners74` (production,
`LE/BoundaryRowsLandingLND.lean`; labels `CircleFaceLabel74`, faces `circleFaceSet74`) PLUS the
clause `∀ f, whole circle fibre of `y` ⊆ face `f` → `f ∈ L``: the labels at `y` contain every face
that contains the whole circle fibre of `y` ("the horizontal label is forced at a vertical
meeting"). -/
def CircleBaseCornersV32 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Kc : BoundaryCompactSlimChoiceV2 Bs) : Prop :=
  ∀ y ∈ C.stageMap 0 '' Kc.remainder,
    y ∉ relInterior_BIF (Bs.base 0) (C.stageMap 0 '' Kc.remainder) →
    ∃ (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
      (L : Finset (CircleFaceLabel74 Kc))
      (φ : CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
      IsOpen O ∧ y ∈ O ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
      (∀ f ∈ L, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0 ∧
        {y' | y' ∈ O ∧ y' ∈ C.stageMap 0 '' Kc.remainder ∧ φ f y' = 0} =
          {y' | y' ∈ O ∧ y' ∈ C.stageMap 0 '' Kc.remainder ∧
            Bs.fibre 0 y' ⊆ circleFaceSet74 Kc f}) ∧
      (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
        fun f : L => mvfderiv W.model (fun q => φ f (C.stageMap 0 q)) p v) ∧
      (C.stageMap 0 '' Kc.remainder) ∩ O = {y' | y' ∈ O ∩ Bs.base 0 ∧ ∀ f ∈ L, φ f y' ≤ 0} ∧
      (∀ f : CircleFaceLabel74 Kc, Bs.fibre 0 y ⊆ circleFaceSet74 Kc f → f ∈ L)

/-- V32 corners are the production corners with one more clause (so the delivered records keep
working). -/
theorem CircleBaseCornersV32.toCorners74 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (h : CircleBaseCornersV32 Kc) : CircleBaseCorners74 Kc := by
  intro y hy hyr
  obtain ⟨O, L, φ, hO, hyO, h1, h2, hf, hs, hc, -⟩ := h y hy hyr
  exact ⟨O, L, φ, hO, hyO, h1, h2, hf, hs, hc⟩

/-- **`BoundaryGeometricExports74V32 C dec`** (R2, R9): `BoundaryGeometricExports74b` (production,
O-BD1 G1: the §R record of v3.1 on `dec : BoundaryActualDecompositionV2b C`) with `circleCorners :
CircleBaseCornersV32 dec.slim`. Four groups: (1) the actual smooth stage restrictions ARE `dec` plus
G4s; (2) the same-chain ZSP02 zero cores ARE `dec.zero` plus F5z; (3) the same-product BCG06 cusp
cores: E4b, E4c and the collar shrink; (4) smooth `K₃`, whole fibres, EDP–BCF faces and corners: F1,
F4b, F4c, F5, G3, G6, G6c, G7. NEVER `∀ dec, Nonempty (BoundaryGeometricExports74V32 C dec)`: the
producer chooses `dec` and `geom` together (`exists_boundaryGeometricExports74b_OBD` is the
delivered conditional form). -/
structure BoundaryGeometricExports74V32 (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2b C) : Prop where
  edgeFacesSmooth : ∀ ℓ, ∀ y ∈ dec.bases.base 1, dec.edge.faceFun ℓ y = 0 →
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧
      ContDiffOn ℝ ∞ (dec.edge.faceFun ℓ) O
  zeroSlim : ∀ k : S.ZeroIdx_BAUGC, (C.actualZeroFace_BIFc k ∩ dec.bases.source 2).Nonempty →
    ∃ y ∈ dec.bases.base 2, C.actualZeroFace_BIFc k = dec.bases.fibre 2 y
  cusp : BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
    (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) S.zeroBall_BCG6K
  cuspProduct : ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
    IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧ range Φ = C.cuspCore_BIF i ∧
    (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
    (range fun t => Φ (t, iccEnd true)) = C.cuspFront_BIF i
  cuspCollar : ∀ i : Fin S.packet.cusp.count, ∃ U : Set W.Carrier, IsOpen U ∧
    S.packet.cusp.component i ⊆ U ∧ U ⊆ C.cuspCore_BIF i ∧ Disjoint (closure U) (C.cuspFront_BIF i)
  diskRim : ∀ y ∈ dec.bases.base 1, ∀ p ∈ dec.bases.fibre 1 y, C.heightRatio p = 4 * Δ →
    p ∈ dec.bases.source 0 ∧ dec.bases.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} =
      dec.bases.fibre 0 (C.stageMap 0 p)
  buffer : C.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p}
  frontierM₁ : frontier C.M₁_BIFc = (⋃ k, C.actualZeroFace_BIFc k) ∪ ⋃ i, C.cuspFront_BIF i
  frontSlim : ∀ i : Fin S.packet.cusp.count, (C.cuspFront_BIF i ∩ dec.bases.source 2).Nonempty →
    ∃ y ∈ dec.bases.base 2, C.cuspFront_BIF i = dec.bases.fibre 2 y
  faces : dec.slim.piece ∩ dec.slim.M₂ = frontier dec.slim.piece \ frontier C.M₁_BIFc ∧
    frontier dec.slim.M₂ = (frontier C.M₁_BIFc \ dec.slim.piece) ∪
      (frontier dec.slim.piece \ frontier C.M₁_BIFc) ∧
    Disjoint (frontier C.M₁_BIFc \ dec.slim.piece) (frontier dec.slim.piece \ frontier C.M₁_BIFc)
  pieces : IsCompact dec.slim.edgePiece ∧ IsCompact dec.slim.remainder ∧
    dec.slim.M₂ = dec.slim.edgePiece ∪ dec.slim.remainder ∧
    dec.slim.remainder ⊆ dec.bases.source 0 ∧
    dec.slim.edgePiece ∩ dec.slim.remainder = dec.slim.verticalFace ∧
    dec.slim.remainder ∩ frontier dec.slim.M₂ =
      frontier dec.slim.M₂ \ relInterior_BIF (frontier dec.slim.M₂) dec.slim.horizontalFace ∧
    dec.slim.remainder =
      dec.bases.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' dec.slim.remainder) ∧
    ∀ p ∈ dec.slim.verticalFace ∩ dec.slim.horizontalFace,
      ∃! ℓ, dec.edge.faceFun ℓ (C.stageMap 1 p) = 0
  circleCorners : CircleBaseCornersV32 dec.slim
  partition : ∀ x ∈ frontier dec.slim.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
      (connectedComponentIn (frontier dec.slim.M₂) x),
    (∀ i, ∃ y ∈ C.stageMap 1 '' dec.slim.horizontalFace,
      Subtype.val '' P.disk i =
        connectedComponentIn (frontier dec.slim.M₂) x ∩ dec.bases.fibre 1 y) ∧
    Subtype.val '' (⋃ j, P.piece j) =
      connectedComponentIn (frontier dec.slim.M₂) x ∩ dec.slim.remainder
  cuspFace : ∀ i : Fin S.packet.cusp.count,
    (∃ y ∈ dec.bases.base 2, C.cuspFront_BIF i = dec.bases.fibre 2 y ∧
      C.cuspFront_BIF i ⊆ dec.slim.piece) ∨
    (∃ x ∈ dec.slim.remainder, C.cuspFront_BIF i =
        connectedComponentIn (frontier dec.slim.remainder) x ∧
      Disjoint (C.cuspFront_BIF i) dec.slim.edgePiece)

/-- The V32 exports give the delivered v2b exports (forget the corner clause). -/
theorem BoundaryGeometricExports74V32.toExports74b
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {dec : BoundaryActualDecompositionV2b C}
    (geom : BoundaryGeometricExports74V32 C dec) : BoundaryGeometricExports74b C dec where
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
  circleCorners := geom.circleCorners.toCorners74
  partition := geom.partition
  cuspFace := geom.cuspFace

/-- **Constructor** (the only way from the v2b exports up to V32): the v2b exports and a proof of
the V32 corner model of the SAME slim choice. -/
theorem BoundaryGeometricExports74V32.ofExports74b_OBD
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {dec : BoundaryActualDecompositionV2b C}
    (geom : BoundaryGeometricExports74b C dec) (hV32 : CircleBaseCornersV32 dec.slim) :
    BoundaryGeometricExports74V32 C dec where
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
  circleCorners := hV32
  partition := geom.partition
  cuspFace := geom.cuspFace

/-- **Inhabitant of the V32 corner record**: with an empty remaining circle piece the corner model
holds vacuously. -/
theorem circleBaseCornersV32_of_remainder_empty_OBD
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} (h : Kc.remainder = ∅) : CircleBaseCornersV32 Kc := by
  intro y hy
  rw [h, image_empty] at hy
  exact absurd hy (notMem_empty y)

end Labels

end DifferentialGeometry.Geometry.Collapse
