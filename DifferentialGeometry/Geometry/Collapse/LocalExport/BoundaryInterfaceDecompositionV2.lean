import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceV2Applications

/-!
# Boundary route interfaces v2, part 4: the actual decomposition on the v2 objects (lane BIFACEc)

External review 69 §2.4 and lead disposition D69-9 (specification of the re-frozen sections F–G).
Everything is attached to ONE chain `C`, ONE v2 BASES exit `Bs` and the ACTUAL zero domains of the
same `C.E` (definitions, so `M₁` is a definition of `C`).

* `BoundaryGaf02Chain.M₁_BIFc C = W \ int_W(⋃ Z_k ∪ C_∂)` (`Z_k = C.actualZeroDomain_BIFc k`);
  `BoundaryGaf02BasesV2.slimBaseDomain_BIFc Bs = f₃(M₁ ∩ X₃)` (`D₃`).
* `BoundaryCompactSlimChoiceV2 Bs` (BCF01 (K), D69-9 G1; lane B-BCF134's kernel output form): finitely
  many SMOOTH arcs `arc k : ℝ → H` on `[0, 1]` (`ContDiffOn`, `InjOn`, nonzero derivative), pairwise
  disjoint, inside `B₃`, whose union `K₃` has the images of ALL original closed slim slabs and of
  `∂M₁ ∩ X₃` in its relative interior, and whose slim piece `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)` is regular
  (`closure (interior S) = S`). Circle components are excluded by the theorem
  `no_closed_base_component_BCF` (lane B-BCF134), not by a field. Defs `K₃`, `piece`, `M₂`,
  `edgePiece`, `remainder`, `verticalFace`, `horizontalFace` (v1's formulas on the v2 objects).
* `BoundaryEdgeFaceLabel_BIFc Kc` (D69-9 G3/G4): the labels of the horizontal faces of the edge base:
  a zero face `Z_k` (`.inl k`), a cusp front `H_b` (`.inr (.inl b)`), a NEW slim end `(arc j, end e)`
  (`.inr (.inr (j, e))`); `edgeFaceSet_BIFc` their ACTUAL ambient faces (`C.actualZeroFace_BIFc k`,
  `C.cuspFront_BIF b`, the whole slim fibre `X₃ ∩ f₃⁻¹{arc j (end e)}`).
* `BoundaryRelativeEdgeRestrictionV2 Bs Kc` (BCF02, D69-9 G4, D68-6): labelled descended face
  functions `h_ℓ` of the edge base, v1's saturation / sublevel / smoothness / regularity /
  transversality clauses, plus the COMPLETE labels (`face_label`: the zero of `h_ℓ ∘ f₂` on
  `M₂ ∩ X₂` is the actual labelled face; `face_complete`: every horizontal face point is labelled)
  and the LOCAL MODEL (`local_single`: near every base point at most ONE label is active — excludes
  the pinching `h₁ = t, h₂ = −t`; with `transverse` this is the quadrant model
  `{T ≤ 4Δ} ∩ {h_ℓ ≥ 0}` at the corners).
* `BoundaryActualDecompositionV2 C`: v2 bases, v2 whole fibres, actual zero domains, `K₃`, edge
  restriction. Inhabitant `BoundaryGaf02Chain.emptyDecompositionV2_BIFc` (empty family).
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

/-- `M₁ = W \ int_W(⋃ Z_k ∪ C_∂)` for the ACTUAL zero domains and the cusp cores of the SAME
chain (a definition of `C`). -/
def BoundaryGaf02Chain.M₁_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Set W.Carrier :=
  (interior ((⋃ k, C.actualZeroDomain_BIFc k) ∪ C.cuspCores_BIF))ᶜ

/-- `D₃ = f₃(M₁ ∩ X₃)` on the v2 bases. -/
def BoundaryGaf02BasesV2.slimBaseDomain_BIFc {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (Bs : BoundaryGaf02BasesV2 C) :
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  C.stageMap 2 '' (C.M₁_BIFc ∩ Bs.source 2)

/-- **BCF01's compact slim base `K₃`, v2** (D69-9 G1; the K₃ kernel's output form): finitely many
SMOOTH pairwise disjoint arcs `arc k : ℝ → H` on `[0, 1]` (smooth, injective, nonzero derivative)
inside `B₃`, whose union has the images of ALL original closed slim slabs and of `∂M₁ ∩ X₃` in its
relative interior, with a REGULAR slim piece `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`. -/
structure BoundaryCompactSlimChoiceV2 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (Bs : BoundaryGaf02BasesV2 C) : Type where
  /-- The number of arcs. -/
  arcCount : ℕ
  /-- The arcs (parametrized on `[0, 1]`). -/
  arc : Fin arcCount → ℝ → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  arc_smooth : ∀ k, ContDiffOn ℝ ∞ (arc k) (Icc 0 1)
  arc_injOn : ∀ k, InjOn (arc k) (Icc 0 1)
  arc_deriv : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (arc k) (Icc 0 1) t ≠ 0
  arc_disjoint : Pairwise (Disjoint on fun k => arc k '' Icc 0 1)
  arc_subset_base : ∀ k, arc k '' Icc 0 1 ⊆ Bs.base 2
  /-- (K), slabs: `f₃(⋃ original closed slabs) ⊆ int_{B₃} K₃`. -/
  slabs_subset : C.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ⊆
    relInterior_BIF (Bs.base 2) (⋃ k, arc k '' Icc 0 1)
  /-- (K), old faces: `f₃(∂M₁ ∩ X₃) ⊆ int_{B₃} K₃`. -/
  faces_subset : C.stageMap 2 '' (frontier C.M₁_BIFc ∩ Bs.source 2) ⊆
    relInterior_BIF (Bs.base 2) (⋃ k, arc k '' Icc 0 1)
  /-- The slim piece is regular: `cl(int S) = S`. -/
  piece_regular : closure (interior (Bs.source 2 ∩
      C.stageMap 2 ⁻¹' ((⋃ k, arc k '' Icc 0 1) ∩ Bs.slimBaseDomain_BIFc))) =
    Bs.source 2 ∩ C.stageMap 2 ⁻¹' ((⋃ k, arc k '' Icc 0 1) ∩ Bs.slimBaseDomain_BIFc)

namespace BoundaryCompactSlimChoiceV2

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (Kc : BoundaryCompactSlimChoiceV2 Bs)

/-- `K₃ = ⋃ arcs`. -/
def K₃ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ k, Kc.arc k '' Icc 0 1

/-- The slim piece `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`. -/
def piece : Set W.Carrier :=
  Bs.source 2 ∩ C.stageMap 2 ⁻¹' (Kc.K₃ ∩ Bs.slimBaseDomain_BIFc)

/-- `M₂ = M₁ \ int_{M₁} S`. -/
def M₂ : Set W.Carrier :=
  C.M₁_BIFc \ relInterior_BIF C.M₁_BIFc Kc.piece

/-- The edge piece `P_e = M₂ ∩ X₂`. -/
def edgePiece : Set W.Carrier :=
  Kc.M₂ ∩ Bs.source 1

/-- The circle remainder `R_c = M₂ \ int_{M₂} P_e`. -/
def remainder : Set W.Carrier :=
  Kc.M₂ \ relInterior_BIF Kc.M₂ Kc.edgePiece

/-- The vertical edge face `V_e = P_e ∩ {T = 4Δ}`. -/
def verticalFace : Set W.Carrier :=
  Kc.edgePiece ∩ {p | C.heightRatio p = 4 * Δ}

/-- The horizontal edge face `H_e = ∂M₂ ∩ X₂`. -/
def horizontalFace : Set W.Carrier :=
  frontier Kc.M₂ ∩ Bs.source 1

/-- `K₃` is compact (finitely many images of `[0, 1]` under continuous maps). -/
theorem isCompact_K₃_BIFc : IsCompact Kc.K₃ :=
  isCompact_iUnion fun k => isCompact_Icc.image_of_continuousOn (Kc.arc_smooth k).continuousOn

/-- The slim piece is regular. -/
theorem closure_interior_piece_BIFc : closure (interior Kc.piece) = Kc.piece :=
  Kc.piece_regular

/-- **The labels of the horizontal faces of the edge base** (D69-9 G3/G4): a zero domain, a cusp
front, or a NEW slim end `(arc j, end e)`. -/
abbrev EdgeFaceLabel_BIFc : Type :=
  S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count ⊕ (Fin Kc.arcCount × Bool)

/-- The end parameter of an arc (`false ↦ 0`, `true ↦ 1`). -/
def arcEnd_BIFc (e : Bool) : ℝ :=
  if e then 1 else 0

/-- The ACTUAL ambient face of a label: the zero face of `Z_k`, the cusp front `H_b`, the whole
slim fibre over the arc end. -/
def edgeFaceSet_BIFc : Kc.EdgeFaceLabel_BIFc → Set W.Carrier
  | .inl k => C.actualZeroFace_BIFc k
  | .inr (.inl i) => C.cuspFront_BIF i
  | .inr (.inr je) => Bs.fibre 2 (Kc.arc je.1 (arcEnd_BIFc je.2))

end BoundaryCompactSlimChoiceV2

/-- **The relative edge restriction, v2** (BCF02; D69-9 G3/G4, D68-6): on the edge source of the
SAME chain, LABELLED descended face functions `h_ℓ` of the edge base, v1's clauses (saturation,
sublevel, continuity, smoothness and regularity at zeros, transversality with `T` on `T = 4Δ`),
the COMPLETE labels and the local model (at most one active label near every base point). -/
structure BoundaryRelativeEdgeRestrictionV2 {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (Kc : BoundaryCompactSlimChoiceV2 Bs) : Type where
  /-- The labelled descended face functions `h_ℓ` of the edge base. -/
  faceFun : Kc.EdgeFaceLabel_BIFc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ
  /-- Saturation: `M₂ ∩ X₂ = X₂ ∩ f₂⁻¹(f₂(M₂ ∩ X₂))`. -/
  saturated : Kc.M₂ ∩ Bs.source 1 =
    Bs.source 1 ∩ C.stageMap 1 ⁻¹' (C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1))
  /-- The edge base domain is the sublevel of the face functions. -/
  base_eq : C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1) = {y ∈ Bs.base 1 | ∀ ℓ, 0 ≤ faceFun ℓ y}
  /-- `h_ℓ ∘ f₂` is continuous on `X₂`. -/
  face_continuousOn : ∀ ℓ, ContinuousOn (fun p => faceFun ℓ (C.stageMap 1 p)) (Bs.source 1)
  /-- `h_ℓ ∘ f₂` is smooth at its zeros in `X₂`. -/
  face_smooth : ∀ ℓ, ∀ p ∈ Bs.source 1, faceFun ℓ (C.stageMap 1 p) = 0 →
    ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => faceFun ℓ (C.stageMap 1 q)) p
  /-- Regularity: `d(h_ℓ ∘ f₂) ≠ 0` at its zeros in `X₂`. -/
  regular : ∀ ℓ, ∀ p ∈ Bs.source 1, faceFun ℓ (C.stageMap 1 p) = 0 →
    mvfderiv W.model (fun q => faceFun ℓ (C.stageMap 1 q)) p ≠ 0
  /-- `(d(h_ℓ ∘ f₂), dT)` is onto `ℝ²` on the vertical face. -/
  transverse : ∀ ℓ, ∀ p ∈ Bs.source 1, faceFun ℓ (C.stageMap 1 p) = 0 →
    C.heightRatio p = 4 * Δ →
    Surjective (fun v : TangentSpace W.model p =>
      (mvfderiv W.model (fun q => faceFun ℓ (C.stageMap 1 q)) p v,
        mvfderiv W.model C.heightRatio p v))
  /-- COMPLETE labels: on `M₂ ∩ X₂` the zero of `h_ℓ ∘ f₂` is the actual labelled face. -/
  face_label : ∀ ℓ, ∀ p ∈ Kc.M₂ ∩ Bs.source 1, faceFun ℓ (C.stageMap 1 p) = 0 →
    p ∈ Kc.edgeFaceSet_BIFc ℓ
  /-- Every horizontal face point carries a label. -/
  face_complete : ∀ p ∈ Kc.horizontalFace, ∃ ℓ, faceFun ℓ (C.stageMap 1 p) = 0
  /-- LOCAL MODEL: near every point of the edge base domain at most ONE label is active. -/
  local_single : ∀ y ∈ C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1), ∀ ℓ, faceFun ℓ y = 0 →
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧
      ∀ ℓ', ℓ' ≠ ℓ → ∀ y' ∈ O ∩ Bs.base 1, 0 < faceFun ℓ' y'

/-- **The actual decomposition data of the boundary branch, v2** (D69-1, D69-2, D69-4, D69-9) on ONE
chain `C`: the v2 BASES exit, its whole-fibre layer, the ACTUAL zero domains of `C.E`, BCF01's
`K₃` and BCF02's labelled relative edge restriction. -/
structure BoundaryActualDecompositionV2 (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  bases : BoundaryGaf02BasesV2 C
  fibres : BoundaryWholeFiberSpecV2 C bases
  zero : BoundaryActualZeroDomains_BIFc C bases
  slim : BoundaryCompactSlimChoiceV2 bases
  edge : BoundaryRelativeEdgeRestrictionV2 slim

/-! ## Inhabitant: the empty-family chain -/

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- `K₃ = ∅` on the empty v2 bases (no slab, no slim source). -/
def emptySlimChoiceV2_BIFc : BoundaryCompactSlimChoiceV2 (C.emptyBasesV2_BIFc hc hF) where
  arcCount := 0
  arc := fun k => k.elim0
  arc_smooth := fun k => k.elim0
  arc_injOn := fun k => k.elim0
  arc_deriv := fun k => k.elim0
  arc_disjoint := fun k => k.elim0
  arc_subset_base := fun k => k.elim0
  slabs_subset := by
    rw [S.slimSlabs_eq_empty_BIF (hc 2)]
    simp
  faces_subset := by
    change C.stageMap 2 '' (frontier _ ∩ ∅) ⊆ _
    simp
  piece_regular := by
    change closure (interior ((∅ : Set W.Carrier) ∩ _)) = (∅ : Set W.Carrier) ∩ _
    simp

/-- The labelled edge restriction on the empty v2 bases (no base point; face functions `0`). -/
def emptyEdgeRestrictionV2_BIFc :
    BoundaryRelativeEdgeRestrictionV2 (C.emptySlimChoiceV2_BIFc hc hF) where
  faceFun := fun _ _ => 0
  saturated := by
    change _ ∩ (∅ : Set W.Carrier) = (∅ : Set W.Carrier) ∩ _
    simp
  base_eq := by
    change C.stageMap 1 '' (_ ∩ (∅ : Set W.Carrier)) = {y | y ∈ (∅ : Set _) ∧ _}
    simp
  face_continuousOn := fun _ => by
    change ContinuousOn _ (∅ : Set W.Carrier)
    exact continuousOn_empty _
  face_smooth := fun _ p hp => (notMem_empty p hp).elim
  regular := fun _ p hp => (notMem_empty p hp).elim
  transverse := fun _ p hp => (notMem_empty p hp).elim
  face_label := fun _ p hp => (notMem_empty p hp.2).elim
  face_complete := fun p hp => (notMem_empty p hp.2).elim
  local_single := fun y hy => by
    obtain ⟨p, hp, -⟩ := hy
    exact (notMem_empty p hp.2).elim

/-- **The empty decomposition v2** of a chain over the empty slot (empty stage and zero centres). -/
def emptyDecompositionV2_BIFc
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) : BoundaryActualDecompositionV2 C where
  bases := C.emptyBasesV2_BIFc hc hF
  fibres := C.emptyWholeFiberSpecV2_BIFc hc hF
  zero := C.emptyActualZeroDomains_BIFc hc hF hz0
  slim := C.emptySlimChoiceV2_BIFc hc hF
  edge := C.emptyEdgeRestrictionV2_BIFc hc hF

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
