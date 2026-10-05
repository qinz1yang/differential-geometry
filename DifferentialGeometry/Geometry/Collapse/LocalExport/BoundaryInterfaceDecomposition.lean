import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBases

/-!
# Boundary route interfaces, part 4: the actual decomposition (lane BIFACE)

External draft 61 §5.4, §6.1–§6.4 and disposition D61-10, D68-6. Everything is attached to ONE
chain `C`, ONE BASES exit `Bs`, the actual zero cores `ZC` and the cusp cores `C.cuspCores_BIF` of
the SAME `C.E`; the pieces are DEFINITIONS, the choices are the post-chosen `K₃` (BCF01) and the
descended face functions of the edge base (BCF02).

* `relInterior_BIF Y Z`: the interior of `Z` relative to `Y` (as a subset of the ambient space).
* `BoundaryInitialCoresSpec.M₁`: `M₁ = W \ int_W(Z ∪ C_∂)` (§5.4).
* `BoundaryGaf02Bases.slimBaseDomain_BIF`: `D₃ = f₃(M₁ ∩ X₃)` (§6.1).
* `BoundarySupplyCore.slimSlabs_BIF`: the original closed slim slabs `{|η_j| ≤ 3.5·10⁵Δ}`.
* `BoundaryCompactSlimChoice Bs ZC` (BCF01 (K)): `K₃ ⊆ B₃` a finite disjoint union of embedded
  arcs with `f₃(all original closed slabs) ⊆ int_{B₃} K₃` and `f₃(∂M₁ ∩ X₃) ⊆ int_{B₃} K₃`; defs
  `K₃`, `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)` (`piece`), `M₂ = M₁ \ int_{M₁} S`.
* `BoundaryRelativeEdgeRestriction Bs ZC K` (BCF02, draft §6.2 "relative edge restriction",
  D68-6): the descended face functions `h_k` of the edge base, saturation
  `M₂ ∩ X₂ = X₂ ∩ f₂⁻¹(f₂(M₂ ∩ X₂))`, the edge base domain
  `f₂(M₂ ∩ X₂) = {y ∈ B₂ | ∀ k, h_k y ≥ 0}`,
  continuity of `h_k ∘ f₂` on `X₂`, smoothness and a nonzero differential at the face points, and
  the independence of `d(h_k ∘ f₂)` and `dT` at the vertical face `T = 4Δ` (quadrant charts are
  theorems). Defs `edgePiece` (`P_e = M₂ ∩ X₂`), `remainder` (`R_c = M₂ \ int_{M₂} P_e`),
  `verticalFace` (`V_e = M₂ ∩ X₂ ∩ {T = 4Δ}`), `horizontalFace` (`H_e = ∂M₂ ∩ X₂`).
* `BoundaryActualDecomposition C`: bases, whole fibres, zero cores, `K₃`, edge restriction. NO
  coverage or face-identity fields: `W = Z ∪ C_∂ ∪ S ∪ M₂`, `P_e ∩ R_c = V_e`, compactness of
  `P_e`, the face partition and the Euler count are the THEOREMS BCF01–BCF03 (frozen in
  `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`); the rounding data of
  BCF04 are FC41's explicit inputs there.
* `BoundaryGeometricOutput S Φ …`: T3B's labelled whole product (no cores) OR the separated branch
  with `D`, `C`, `dec` (draft §4.5).
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

/-- The interior of `Z` relative to `Y`, as a subset of the ambient space:
`int_Y Z = ι_Y(int(ι_Y⁻¹ Z))`. -/
def relInterior_BIF {X : Type*} [TopologicalSpace X] (Y Z : Set X) : Set X :=
  Subtype.val '' interior (Subtype.val ⁻¹' Z : Set Y)

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- The original closed slim slabs `⋃_j {d(q, j) < 10⁶Δρ_j, |η_j(q)| ≤ 3.5·10⁵Δ}` of the stored
family (BCF01 (K) reads ALL of them, not their intersection with `M₁`). -/
def BoundarySupplyCore.slimSlabs_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {q | ∃ j ∈ S.stageCentres_BIF 2, dist q j < 1000000 * Δ * S.rho j ∧
    |S.slimEta_BIF j q| ≤ 350000 * Δ}

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- `M₁ = W \ int_W(Z ∪ C_∂)` for the actual zero cores `Z` and the cusp cores `C_∂` of the SAME
chain (draft 61 §5.4). -/
def BoundaryInitialCoresSpec.M₁ (ZC : BoundaryInitialCoresSpec C) : Set W.Carrier :=
  (interior (ZC.union ∪ C.cuspCores_BIF))ᶜ

/-- `D₃ = f₃(M₁ ∩ X₃)`: the slim base domain of `M₁` (draft 61 §6.1). -/
def BoundaryGaf02Bases.slimBaseDomain_BIF (Bs : BoundaryGaf02Bases C)
    (ZC : BoundaryInitialCoresSpec C) :
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  C.stageMap 2 '' (ZC.M₁ ∩ Bs.source 2)

/-- **BCF01's post-chosen compact slim base `K₃`** (draft 61 §6.1 (K), D61-10): a finite disjoint
union of embedded arcs in the slim base `B₃` whose relative interior contains the images of ALL
original closed slim slabs and of all old face points `f₃(∂M₁ ∩ X₃)` (= `∂D₃`). Chosen after `E`
and the actual faces; no early tolerance. -/
structure BoundaryCompactSlimChoice (Bs : BoundaryGaf02Bases C) (ZC : BoundaryInitialCoresSpec C) :
    Type where
  /-- The number of arcs. -/
  arcCount : ℕ
  /-- The arcs of `K₃`. -/
  arc : Fin arcCount → Icc (0 : ℝ) 1 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  arc_isEmbedding : ∀ k, Topology.IsEmbedding (arc k)
  arc_disjoint : Pairwise (Disjoint on fun k => range (arc k))
  arc_subset_base : ∀ k, range (arc k) ⊆ Bs.base 2
  /-- (K), slabs: `f₃(⋃ original closed slabs) ⊆ int_{B₃} K₃`. -/
  slabs_subset : C.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ⊆
    relInterior_BIF (Bs.base 2) (⋃ k, range (arc k))
  /-- (K), old faces: `f₃(∂M₁ ∩ X₃) ⊆ int_{B₃} K₃`. -/
  faces_subset : C.stageMap 2 '' (frontier ZC.M₁ ∩ Bs.source 2) ⊆
    relInterior_BIF (Bs.base 2) (⋃ k, range (arc k))

namespace BoundaryCompactSlimChoice

variable {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}
  (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- `K₃ = ⋃ arcs`. -/
def K₃ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ k, range (Kc.arc k)

/-- The slim piece `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`. -/
def piece : Set W.Carrier :=
  Bs.source 2 ∩ C.stageMap 2 ⁻¹' (Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC)

/-- `M₂ = M₁ \ int_{M₁} S`. -/
def M₂ : Set W.Carrier :=
  ZC.M₁ \ relInterior_BIF ZC.M₁ Kc.piece

/-- `K₃` is compact (a finite union of arcs). -/
theorem isCompact_K₃ : IsCompact Kc.K₃ :=
  isCompact_iUnion fun k => isCompact_range (Kc.arc_isEmbedding k).continuous

end BoundaryCompactSlimChoice

/-- **The relative edge restriction** (draft 61 §6.2, D61-10, D68-6; consumed by BCF02): on the
edge source `X₂ = f₂⁻¹(B₂) ∩ {T ≤ 4Δ}` of the SAME chain, the descended face functions `h_k` of
the edge base (zero face: kept zero-block ratio; cusp face: `u_b/v_b − 40` of `J_b(E)`; new slim
endpoint: the endpoint coordinate of `π₃E` through the `π₂,₃` factorization), saturation of
`M₂ ∩ X₂`, the edge base domain as the sublevel `{h_k ≥ 0}`, continuity of `h_k ∘ f₂` on `X₂`,
smoothness and a nonzero differential of `h_k ∘ f₂` at its zeros, and the independence of
`d(h_k ∘ f₂)` and `dT` on the vertical face `T = 4Δ`. Compactness of `P_e` is NOT claimed here. -/
structure BoundaryRelativeEdgeRestriction (Bs : BoundaryGaf02Bases C)
    (ZC : BoundaryInitialCoresSpec C) (Kc : BoundaryCompactSlimChoice Bs ZC) : Type where
  /-- The number of horizontal face functions. -/
  faceCount : ℕ
  /-- The descended face functions `h_k` of the edge base. -/
  faceFun : Fin faceCount → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ
  /-- Saturation: `M₂ ∩ X₂ = X₂ ∩ f₂⁻¹(f₂(M₂ ∩ X₂))`. -/
  saturated : Kc.M₂ ∩ Bs.source 1 =
    Bs.source 1 ∩ C.stageMap 1 ⁻¹' (C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1))
  /-- The edge base domain is the sublevel of the face functions. -/
  base_eq : C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1) = {y ∈ Bs.base 1 | ∀ k, 0 ≤ faceFun k y}
  /-- `h_k ∘ f₂` is continuous on `X₂`. -/
  face_continuousOn : ∀ k, ContinuousOn (fun p => faceFun k (C.stageMap 1 p)) (Bs.source 1)
  /-- `h_k ∘ f₂` is smooth at its zeros in `X₂`. -/
  face_smooth : ∀ k, ∀ p ∈ Bs.source 1, faceFun k (C.stageMap 1 p) = 0 →
    ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => faceFun k (C.stageMap 1 q)) p
  /-- Regularity: `d(h_k ∘ f₂) ≠ 0` at its zeros in `X₂`. -/
  regular : ∀ k, ∀ p ∈ Bs.source 1, faceFun k (C.stageMap 1 p) = 0 →
    mvfderiv W.model (fun q => faceFun k (C.stageMap 1 q)) p ≠ 0
  /-- Horizontal–vertical independence on the vertical face `T = 4Δ`: `(d(h_k ∘ f₂), dT)` is
  onto `ℝ²` (EDP04's `(dg_i, dT)` independence pushed through `h_k = b(g_i)`, `b' ≠ 0`). -/
  transverse : ∀ k, ∀ p ∈ Bs.source 1, faceFun k (C.stageMap 1 p) = 0 →
    C.heightRatio p = 4 * Δ →
    Surjective (fun v : TangentSpace W.model p =>
      (mvfderiv W.model (fun q => faceFun k (C.stageMap 1 q)) p v,
        mvfderiv W.model C.heightRatio p v))

namespace BoundaryCompactSlimChoice

variable {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}
  (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- The edge piece `P_e = M₂ ∩ X₂` (draft 61 §6.2). -/
def edgePiece : Set W.Carrier :=
  Kc.M₂ ∩ Bs.source 1

/-- The circle remainder `R_c = M₂ \ int_{M₂} P_e`. -/
def remainder : Set W.Carrier :=
  Kc.M₂ \ relInterior_BIF Kc.M₂ Kc.edgePiece

/-- The vertical edge face `V_e = M₂ ∩ ∂X₂ = M₂ ∩ X₂ ∩ {T = 4Δ}` (EDP03 (EV)). -/
def verticalFace : Set W.Carrier :=
  Kc.edgePiece ∩ {p | C.heightRatio p = 4 * Δ}

/-- The horizontal edge face `H_e = ∂M₂ ∩ X₂`. -/
def horizontalFace : Set W.Carrier :=
  frontier Kc.M₂ ∩ Bs.source 1

end BoundaryCompactSlimChoice

/-- **The actual decomposition data of the boundary branch** (draft 61 §6, D61-10) on ONE chain
`C`: the BASES exit, the whole fibres, the actual zero cores, BCF01's `K₃` and BCF02's relative edge
restriction. The pieces `Z`, `C_∂`, `S`, `M₂`, `P_e`, `R_c` are definitions; their set identities,
compactness, face partition and Euler count are the theorems BCF01–BCF03. -/
structure BoundaryActualDecomposition (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  /-- The BASES exit of `C`. -/
  bases : BoundaryGaf02Bases C
  /-- The whole circle / slim / edge-disk fibres. -/
  fibres : BoundaryWholeFiberSpec C bases
  /-- The actual zero cores of `C.E`. -/
  zero : BoundaryInitialCoresSpec C
  /-- BCF01's compact slim base `K₃`. -/
  slim : BoundaryCompactSlimChoice bases zero
  /-- BCF02's relative edge restriction. -/
  edge : BoundaryRelativeEdgeRestriction bases zero slim

/-- **The geometric output of the boundary route** (draft 61 §4.5, D61-9): T3B's labelled whole
product of the stored supply (no cores are constructed), OR the separated branch with the augmented
data `D`, ONE chain `C` on it and the actual decomposition of `C`. -/
inductive BoundaryGeometricOutput (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (Φ : BoundaryInteriorSlots_BIF S) (Kj : ℕ)
    (Ξ Sg eg c cw : Fin 3 → ℝ) (bcut bder κ : ℝ) : Type
  | product (cert : S.LabelledWholeProduct_BIF) :
      BoundaryGeometricOutput S Φ Kj Ξ Sg eg c cw bcut bder κ
  | separated (D : BoundaryAugmentedData S Φ) (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
      (dec : BoundaryActualDecomposition C) :
      BoundaryGeometricOutput S Φ Kj Ξ Sg eg c cw bcut bder κ

end DifferentialGeometry.Geometry.Collapse
