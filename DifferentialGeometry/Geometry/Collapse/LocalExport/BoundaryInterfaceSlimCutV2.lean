import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecompositionV2
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF

/-!
# Boundary route interfaces v2, part 5: the slim cut at set level and the chart-interval `K₃`
(lane BIFACEc, G1c; lane B-BCF134's decoupling proposal)

BCF01's compact slim base `K₃` in two forms, so that BCF01 (G1 / G3) does not wait for the arc
merging (K-b):

* set level: `BoundaryGaf02BasesV2.slimPieceOf_BIFc Bs K = X₃ ∩ f₃⁻¹(K ∩ D₃)`,
  `M₂Of_BIFc Bs K = M₁ \ int_{M₁} S`, and the predicate `BoundarySlimCut_BIFc Bs K` (BCF01 (K)):
  `K ⊆ B₃` compact, the images of ALL original closed slim slabs and of `∂M₁ ∩ X₃` in the relative
  interior of `K` in `B₃`, and the regular slim piece `cl(int S) = S`;
* `BoundarySlimChartIntervals_BIFc Bs At` (the K₃ kernel's (K-a) output): finitely many closed
  intervals of the charts of a graph atlas `At : GraphAtlas1_BCF ι (Bs.base 2)` (v3 target A4b) with
  pairwise distinct endpoints, their union `K₃`, (K) and the regular piece;
  `BoundarySlimChartIntervals_BIFc.slimCut_BIFc` (its `K₃` is a cut);
* the delivered arc form: `BoundaryCompactSlimChoiceV2.slimCut_BIFc` (its `K₃` is a cut) and
  `piece_eq_slimPieceOf_BIFc`, `M₂_eq_M₂Of_BIFc` (definitional).

Inhabitants: `BoundaryGaf02Chain.emptySlimCut_BIFc` (the empty cut on the empty v2 bases),
`BoundaryGaf02Chain.emptySlimChartIntervals_BIFc` (no interval, any atlas) and
`BoundaryGaf02Chain.emptySlimAtlas_BIFc` (the atlas with no chart of the empty slim base).
Consumer: `BoundaryGaf02Chain.emptyDecomposition_slimCut_BIFc` (both forms of `K₃` on the empty-family
chain are slim cuts, both empty, and the arc form's `M₂` is the set-level `M₂` of the empty cut).
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

namespace BoundaryGaf02BasesV2

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} (Bs : BoundaryGaf02BasesV2 C)

/-- The slim piece of a set `K` of the slim base: `S_K = X₃ ∩ f₃⁻¹(K ∩ D₃)`. -/
def slimPieceOf_BIFc (Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) :
    Set W.Carrier :=
  Bs.source 2 ∩ C.stageMap 2 ⁻¹' (Kset ∩ Bs.slimBaseDomain_BIFc)

/-- `M₂` of a set `K`: `M₁ \ int_{M₁} S_K`. -/
def M₂Of_BIFc (Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) :
    Set W.Carrier :=
  C.M₁_BIFc \ relInterior_BIF C.M₁_BIFc (Bs.slimPieceOf_BIFc Kset)

end BoundaryGaf02BasesV2

/-- **BCF01's slim cut at set level** (BCF01 (K) with the regular piece): `K ⊆ B₃` compact, the
images of ALL original closed slim slabs and of `∂M₁ ∩ X₃` in the relative interior of `K` in `B₃`,
and `cl(int S_K) = S_K`. -/
structure BoundarySlimCut_BIFc {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (Bs : BoundaryGaf02BasesV2 C)
    (Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) : Prop where
  subset_base : Kset ⊆ Bs.base 2
  isCompact : IsCompact Kset
  slabs_subset : C.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ⊆ relInterior_BIF (Bs.base 2) Kset
  faces_subset : C.stageMap 2 '' (frontier C.M₁_BIFc ∩ Bs.source 2) ⊆
    relInterior_BIF (Bs.base 2) Kset
  piece_regular : closure (interior (Bs.slimPieceOf_BIFc Kset)) = Bs.slimPieceOf_BIFc Kset

/-- **BCF01's `K₃` as finitely many closed chart intervals** (the K₃ kernel's (K-a) output, lane
B-BCF134): closed intervals `[a r, b r]` inside the parameter domain of the chart `c r` of a graph
atlas `At` of `B₃`, with pairwise distinct endpoints, whose union `K₃` satisfies (K) and has a
regular slim piece. -/
structure BoundarySlimChartIntervals_BIFc {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (Bs : BoundaryGaf02BasesV2 C) {ι : Type*} (At : GraphAtlas1_BCF ι (Bs.base 2)) : Type _ where
  /-- The number of intervals. -/
  count : ℕ
  /-- The chart of each interval. -/
  chart : Fin count → ι
  /-- The left endpoints. -/
  lo : Fin count → ℝ
  /-- The right endpoints. -/
  hi : Fin count → ℝ
  lo_lt_hi : ∀ r, lo r < hi r
  Icc_subset : ∀ r, Icc (lo r) (hi r) ⊆ At.dom (chart r)
  /-- Genericity: the endpoints are pairwise distinct points of `B₃`. -/
  ends_distinct : Injective fun e : Fin count × Bool =>
    At.param (chart e.1) (if e.2 then hi e.1 else lo e.1)
  /-- (K), slabs. -/
  slabs_subset : C.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ⊆
    relInterior_BIF (Bs.base 2) (⋃ r, At.param (chart r) '' Icc (lo r) (hi r))
  /-- (K), old faces. -/
  faces_subset : C.stageMap 2 '' (frontier C.M₁_BIFc ∩ Bs.source 2) ⊆
    relInterior_BIF (Bs.base 2) (⋃ r, At.param (chart r) '' Icc (lo r) (hi r))
  /-- The regular slim piece. -/
  piece_regular : closure (interior (Bs.slimPieceOf_BIFc
      (⋃ r, At.param (chart r) '' Icc (lo r) (hi r)))) =
    Bs.slimPieceOf_BIFc (⋃ r, At.param (chart r) '' Icc (lo r) (hi r))

namespace BoundarySlimChartIntervals_BIFc

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)} (Ki : BoundarySlimChartIntervals_BIFc Bs At)

/-- `K₃ = ⋃ r, ψ_{c r}([a r, b r])`. -/
def K₃ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ r, At.param (Ki.chart r) '' Icc (Ki.lo r) (Ki.hi r)

/-- **The chart-interval `K₃` is a slim cut.** -/
theorem slimCut_BIFc : BoundarySlimCut_BIFc Bs Ki.K₃ where
  subset_base := iUnion_subset fun r => by
    rintro _ ⟨t, ht, rfl⟩
    exact At.param_mem_BCF (Ki.Icc_subset r ht)
  isCompact := isCompact_iUnion fun r => isCompact_Icc.image_of_continuousOn
    ((At.param_smooth (Ki.chart r)).continuousOn.mono (Ki.Icc_subset r))
  slabs_subset := Ki.slabs_subset
  faces_subset := Ki.faces_subset
  piece_regular := Ki.piece_regular

end BoundarySlimChartIntervals_BIFc

namespace BoundaryCompactSlimChoiceV2

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (Kc : BoundaryCompactSlimChoiceV2 Bs)

/-- The arc form's piece is the set-level piece of its `K₃`. -/
theorem piece_eq_slimPieceOf_BIFc : Kc.piece = Bs.slimPieceOf_BIFc Kc.K₃ :=
  rfl

/-- The arc form's `M₂` is the set-level `M₂` of its `K₃`. -/
theorem M₂_eq_M₂Of_BIFc : Kc.M₂ = Bs.M₂Of_BIFc Kc.K₃ :=
  rfl

/-- **The arc-form `K₃` is a slim cut.** -/
theorem slimCut_BIFc : BoundarySlimCut_BIFc Bs Kc.K₃ where
  subset_base := iUnion_subset fun k => Kc.arc_subset_base k
  isCompact := Kc.isCompact_K₃_BIFc
  slabs_subset := Kc.slabs_subset
  faces_subset := Kc.faces_subset
  piece_regular := Kc.piece_regular

end BoundaryCompactSlimChoiceV2

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **Inhabitant**: the empty set is a slim cut of the empty v2 bases. -/
theorem emptySlimCut_BIFc : BoundarySlimCut_BIFc (C.emptyBasesV2_BIFc hc hF) ∅ where
  subset_base := empty_subset _
  isCompact := isCompact_empty
  slabs_subset := by
    rw [S.slimSlabs_eq_empty_BIF (hc 2)]
    simp
  faces_subset := by
    change C.stageMap 2 '' (frontier _ ∩ ∅) ⊆ _
    simp
  piece_regular := by
    change closure (interior ((∅ : Set W.Carrier) ∩ _)) = (∅ : Set W.Carrier) ∩ _
    simp

/-- **Inhabitant**: no chart interval, for any graph atlas of the (empty) slim base. -/
def emptySlimChartIntervals_BIFc {ι : Type*}
    (At : GraphAtlas1_BCF ι ((C.emptyBasesV2_BIFc hc hF).base 2)) :
    BoundarySlimChartIntervals_BIFc (C.emptyBasesV2_BIFc hc hF) At where
  count := 0
  chart := fun r => r.elim0
  lo := fun r => r.elim0
  hi := fun r => r.elim0
  lo_lt_hi := fun r => r.elim0
  Icc_subset := fun r => r.elim0
  ends_distinct := fun x => x.1.elim0
  slabs_subset := by
    rw [S.slimSlabs_eq_empty_BIF (hc 2)]
    simp
  faces_subset := by
    change C.stageMap 2 '' (frontier _ ∩ ∅) ⊆ _
    simp
  piece_regular := by
    change closure (interior ((∅ : Set W.Carrier) ∩ _)) = (∅ : Set W.Carrier) ∩ _
    simp

/-- **Inhabitant**: the graph atlas with no chart of the (empty) slim base of the empty v2 bases. -/
def emptySlimAtlas_BIFc : GraphAtlas1_BCF Empty ((C.emptyBasesV2_BIFc hc hF).base 2) where
  coord := fun j => j.elim
  param := fun j => j.elim
  dom := fun j => j.elim
  isOpen_dom := fun j => j.elim
  param_smooth := fun j => j.elim
  coord_param := fun j => j.elim
  piece_relOpen := fun j => j.elim
  cover := by
    change (∅ : Set _) = _
    simp

/-- **Consumer (G1c)**: on the empty-family chain the arc-form `K₃` of the empty decomposition and
the chart-interval `K₃` over the empty atlas are both slim cuts, both are empty, and the arc form's
`M₂` is the set-level `M₂` of the empty cut. -/
theorem emptyDecomposition_slimCut_BIFc :
    BoundarySlimCut_BIFc (C.emptyBasesV2_BIFc hc hF) (C.emptySlimChoiceV2_BIFc hc hF).K₃ ∧
      BoundarySlimCut_BIFc (C.emptyBasesV2_BIFc hc hF)
        (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).K₃ ∧
      (C.emptySlimChoiceV2_BIFc hc hF).K₃ = ∅ ∧
      (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).K₃ = ∅ ∧
      (C.emptySlimChoiceV2_BIFc hc hF).M₂ = (C.emptyBasesV2_BIFc hc hF).M₂Of_BIFc ∅ := by
  have h1 : (C.emptySlimChoiceV2_BIFc hc hF).K₃ = ∅ := by
    simp [BoundaryCompactSlimChoiceV2.K₃, emptySlimChoiceV2_BIFc]
  have h2 : (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).K₃ = ∅ := by
    simp [BoundarySlimChartIntervals_BIFc.K₃, emptySlimChartIntervals_BIFc]
  refine ⟨(C.emptySlimChoiceV2_BIFc hc hF).slimCut_BIFc,
    (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).slimCut_BIFc, h1, h2, ?_⟩
  rw [BoundaryCompactSlimChoiceV2.M₂_eq_M₂Of_BIFc, h1]

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
