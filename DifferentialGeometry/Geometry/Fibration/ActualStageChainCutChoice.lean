import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimClosedComponent
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRemainderCircle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Inhabitant

/-!
# Draft 74, D74-3: the explicit cut choice `D` of a chain (kernel form) and its producer

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G12. Draft 74 §1.3 (D74-1: "keep an explicit cut choice
`D` — `S`, `B` do not determine `K₃` nor the good open base neighbourhoods"; D74-3; D74-9 `K₃`
contract). On a chain `C : Gaf02ChainE P` (stages `0, 1, 2` = circle, edge, slim; final maps
`q_j = π_j ∘ E` = `cutQ_R74 j`) the ACTUAL pieces of the blueprint are, for a slim base set `K`:

* `Z = ⋃_k Z_k` (`zeroUnion_ZSP35`), `M₁ = M ∖ int Z` (`cutM1_R74`),
  `M^slim = f₃⁻¹(K ∩ C₃)` (`slimPiece_ZSP35`), `M₂ = M₁ ∖ int_{M₁} M^slim` (`cutM2_R74`);
* `B₂ = W₂ ∩ ⋃_k {v_k > .9R_k, |u_k| < 4Δ v_k}` (`edgeRatio_R74`, EDP02's (ED)), `V` the union of
  (ED) (`edgeVertical_R74`, low branch RETAINED, D74-11), `X₂ = q₁⁻¹(B₂) ∩ V` (`edgeRegion_R74`),
  `M^edge = M₂ ∩ X₂` (`cutEdgeSet_R74`, FDC02), `C₂ = q₁(M^edge)` (`cutC2_R74`);
* `M₃ = M₂ ∖ int_{M₂} M^edge` (`cutM3_R74`, FDC03 (Last)), `C₁ = q₀(M₃)` (`cutC1_R74`).

`CutChoiceOn74 C` keeps the CHOICES: `K₃` (a `SmoothCompactOneDomain_BCF` of `Bs = W₃ ∩ R₃` with
interval AND circle components, never excluding loops), `D₃` (compact smooth one-domain) with
`D₃ = K₃ ∩ C₃`, the `K₃` contract `slab image ∪ F₃ ⊆ int_{Bs} K₃`, `∂K₃ ∩ F₃ = ∅` (`F₃ = ∂C₃`,
ZSP35 G13), and the open base neighbourhoods `edgeBaseOpen ⊇ C₂` (relatively open in `W₂`, EMPTY
when `C₂ = ∅`) and `circleBaseOpen ⊇ C₁` (relatively open in `W₁`). Accessors (not fields):
`slimSet = f₃⁻¹(D₃)`, `edgeSource = q₁⁻¹(edgeBaseOpen)`, `circleSource = q₀⁻¹(circleBaseOpen)`
(whole fibres by construction), `C₂`, `C₁`, `M₂`, `M₃`, `edgeSet` (`C₃` and `M₁` are the chain's
`slimC3_ZSP35`, `cutM1_R74`).

* `Gaf02ChainEJA.cutM3_subset_X₁_R74`: for every `K` with (SK) and `M^slim = M₁ ∩ f⁻¹(K)`,
  `M₃ ⊆ X₁ = q₀⁻¹(W₁ ∩ R₁)` with the blueprint `M^edge = M₂ ∩ X₂` (lane C14-EDP-FDCd's kernel
  `remainder_subset_X₁_EFC` with `stageTwo_mem_base_FDC` for `X₂° ∩ V ⊆ X₂`).
* **`Gaf02ChainEJA.exists_cutChoice_R74`** (producer, final family C14Z): ZSP04's actual `K₃`, `D₃`
  (`zsp0405_row_ZSP35`), `edgeBaseOpen = B₂` (or `∅`), `circleBaseOpen = W₁ ∩ R₁`; with the
  decomposition `M = Z ∪ M^slim ∪ M₂` and `M₃ ⊆ X₁` for the SAME `K₃`. Numeric premises
  (`ε_r < 1/2`, `σ_c ≤ 1/2`, `0 ≤ γ ≤ 3/4`) are explicit (D74-18: row hypotheses).
* `cutChoice_dihedralTiny_R74`: inhabitant on the `RP³ # RP³` C14Z fixture (empty circle / edge /
  slim families, one zero ball covering the source: `M₁ = ∅`, `K₃ = D₃ = ∅`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- EDP02's (ED) ratio condition of the edge stage on the block space:
`⋃_k {v_k > .9R_k, |u_k| < 4Δ v_k}` (`B₂ = W₂ ∩` this set). -/
def edgeRatio_R74 (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  {w | ∃ k : P.edge.finite_centres.toFinset,
    9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl k))) w ∧
    ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl k))) w‖ <
      4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) w}

/-- The edge ratio set is open (so `B₂` is relatively open in `W₂`). -/
theorem isOpen_edgeRatio_R74 (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s'
    ε γc βc Lmax τ γ δ εr e T V vs ζ Λz) : IsOpen (edgeRatio_R74 P) := by
  rw [edgeRatio_R74, ofPred_exists]
  refine isOpen_iUnion fun k => ?_
  exact (isOpen_lt continuous_const (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²) (.inr (.inr (.inl k)))).continuous).inter
    (isOpen_lt (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl k)))).continuous.norm (continuous_const.mul (blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl k)))).continuous))

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The final stage maps `q_j = π_j ∘ E`. -/
def cutQ_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (j : Fin 3) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  fun p => (gafStageQ P.toLocalChartFamily P.zero j).starProjection (C.toChain.E p)

/-- `M₁ = M ∖ int Z`. -/
def cutM1_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Set X :=
  (interior C.zeroUnion_ZSP35)ᶜ

/-- `M₂ = M₁ ∖ int_{M₁} M^slim` for the slim base set `Kb` (`M^slim = f₃⁻¹(Kb ∩ C₃)`). -/
def cutM2_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) : Set X :=
  C.cutM1_R74 \ Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 Kb : Set C.cutM1_R74)

/-- EDP02's `V = {t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ}` (the low branch retained, D74-11). -/
def edgeVertical_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Set X :=
  {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.toChain.scale p ∧
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.toChain.E p)) /
      C.toChain.scale p ≤ 4 * Δ}

/-- EDP02's actual `X₂ = q₁⁻¹(B₂) ∩ V`, `B₂ = W₂ ∩ edgeRatio`. -/
def edgeRegion_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Set X :=
  C.cutQ_R74 1 ⁻¹' (C.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 P) ∩ C.edgeVertical_R74

/-- FDC02's `M^edge = M₂ ∩ X₂`. -/
def cutEdgeSet_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) : Set X :=
  C.cutM2_R74 Kb ∩ C.edgeRegion_R74

/-- FDC02's actual compact edge base `C₂ = q₁(M^edge)`. -/
def cutC2_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.cutQ_R74 1 '' C.cutEdgeSet_R74 Kb

/-- FDC03's (Last): `M₃ = M₂ ∖ int_{M₂} M^edge`. -/
def cutM3_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) : Set X :=
  C.cutM2_R74 Kb \
    Subtype.val '' interior (Subtype.val ⁻¹' C.cutEdgeSet_R74 Kb : Set (C.cutM2_R74 Kb))

/-- FDC03's actual remaining circle base `C₁ = q₀(M₃)`. -/
def cutC1_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.cutQ_R74 0 '' C.cutM3_R74 Kb

/-- `C₂ ⊆ B₂ = W₂ ∩ edgeRatio`. -/
theorem cutC2_subset_R74 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    C.cutC2_R74 Kb ⊆ C.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 P := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2.1

end Gaf02ChainE

/-- **D74-3: the explicit cut choice of a chain** (kernel form; see the module doc). -/
structure CutChoiceOn74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Type where
  /-- The compact smooth one-dimensional domain `K₃ ⊆ Bs` (intervals AND circles). -/
  K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35
  /-- The compact smooth one-dimensional domain `D₃` (intervals AND circles). -/
  D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35
  /-- `D₃ = K₃ ∩ C₃`. -/
  D₃_eq : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35
  /-- (SK): the slab image and the faces `F₃` lie in the relative interior of `K₃`. -/
  K₃_req : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
    Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)
  /-- `∂K₃ ∩ ∂C₃ = ∅` (`∂C₃ = F₃`). -/
  K₃_faces : Disjoint (K₃.carrier \
    Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    C.slimFacePoints_ZSP35
  /-- The open edge base neighbourhood. -/
  edgeBaseOpen : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
  /-- It is relatively open in `W₂`. -/
  edgeBaseOpen_rel : ∃ G, IsOpen G ∧ G ∩ C.toChain.finalBase_BAS 1 = edgeBaseOpen
  /-- It contains `C₂`. -/
  edgeBaseOpen_sub : C.cutC2_R74 K₃.carrier ⊆ edgeBaseOpen
  /-- It is empty when `C₂` is empty (canonical empty edge base). -/
  edgeBaseOpen_empty : C.cutC2_R74 K₃.carrier = ∅ → edgeBaseOpen = ∅
  /-- The open circle base neighbourhood. -/
  circleBaseOpen : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
  /-- It is relatively open in `W₁`. -/
  circleBaseOpen_rel : ∃ G, IsOpen G ∧ G ∩ C.toChain.finalBase_BAS 0 = circleBaseOpen
  /-- It contains `C₁`. -/
  circleBaseOpen_sub : C.cutC1_R74 K₃.carrier ⊆ circleBaseOpen

namespace CutChoiceOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {C : Gaf02ChainE P Kj Ξ Γ S eg c cw}

/-- `slimSet = f₃⁻¹(D₃)`. -/
def slimSet (D : CutChoiceOn74 C) : Set X :=
  C.slimMap_ZSP35 ⁻¹' D.D₃.carrier

/-- The edge source: the whole `q₁`-preimage of the open edge base. -/
def edgeSource (D : CutChoiceOn74 C) : Set X :=
  C.cutQ_R74 1 ⁻¹' D.edgeBaseOpen

/-- The circle source: the whole `q₀`-preimage of the open circle base (whole fibres). -/
def circleSource (D : CutChoiceOn74 C) : Set X :=
  C.cutQ_R74 0 ⁻¹' D.circleBaseOpen

/-- `C₂` of the choice. -/
def C₂ (D : CutChoiceOn74 C) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.cutC2_R74 D.K₃.carrier

/-- `C₁` of the choice. -/
def C₁ (D : CutChoiceOn74 C) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.cutC1_R74 D.K₃.carrier

/-- `M₂` of the choice. -/
def M₂ (D : CutChoiceOn74 C) : Set X :=
  C.cutM2_R74 D.K₃.carrier

/-- `M^edge` of the choice. -/
def edgeSet (D : CutChoiceOn74 C) : Set X :=
  C.cutEdgeSet_R74 D.K₃.carrier

/-- `M₃` of the choice. -/
def M₃ (D : CutChoiceOn74 C) : Set X :=
  C.cutM3_R74 D.K₃.carrier

/-- `slimSet = M^slim(K₃) = f₃⁻¹(K₃ ∩ C₃)`. -/
theorem slimSet_eq (D : CutChoiceOn74 C) : D.slimSet = C.slimPiece_ZSP35 D.K₃.carrier := by
  rw [slimSet, D.D₃_eq]
  rfl

/-- `M₂ = M₁ ∖ int_{M₁} slimSet` (relative interior). -/
theorem M₂_eq (D : CutChoiceOn74 C) :
    D.M₂ = C.cutM1_R74 \ Subtype.val '' interior
      (Subtype.val ⁻¹' D.slimSet : Set C.cutM1_R74) := by
  rw [slimSet_eq]
  rfl

/-- `M₃ = M₂ ∖ int_{M₂} edgeSet` (relative interior). -/
theorem M₃_eq (D : CutChoiceOn74 C) :
    D.M₃ = D.M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' D.edgeSet : Set D.M₂) :=
  rfl

/-- The open edge base lies in `W₂`. -/
theorem edgeBaseOpen_subset (D : CutChoiceOn74 C) :
    D.edgeBaseOpen ⊆ C.toChain.finalBase_BAS 1 := by
  obtain ⟨G, -, hG⟩ := D.edgeBaseOpen_rel
  rw [← hG]
  exact inter_subset_right

/-- The open circle base lies in `W₁`. -/
theorem circleBaseOpen_subset (D : CutChoiceOn74 C) :
    D.circleBaseOpen ⊆ C.toChain.finalBase_BAS 0 := by
  obtain ⟨G, -, hG⟩ := D.circleBaseOpen_rel
  rw [← hG]
  exact inter_subset_right

/-- `M^edge ⊆` the edge source, and `M₃ ⊆` the circle source. -/
theorem edgeSet_subset_source (D : CutChoiceOn74 C) :
    D.edgeSet ⊆ D.edgeSource ∧ D.M₃ ⊆ D.circleSource :=
  ⟨fun x hx => D.edgeBaseOpen_sub ⟨x, hx, rfl⟩, fun x hx => D.circleBaseOpen_sub ⟨x, hx, rfl⟩⟩

end CutChoiceOn74

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {cadj : ℝ}

/-- **FDC03's first clause for the blueprint `M^edge = M₂ ∩ X₂`**: for a slim base set `Kb` with
(SK) and `M^slim(Kb) = M₁ ∩ f⁻¹(Kb)`, `M₃ ⊆ X₁ = q₀⁻¹(W₁ ∩ R₁)`. -/
theorem cutM3_subset_X₁_R74 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hεr : εr < 1 / 2)
    (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hK : C.toChain.slimSlabImage_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35))
    (hsl : C.slimPiece_ZSP35 Kb = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' Kb) :
    C.toGaf02ChainE.cutM3_R74 Kb ⊆
      {x | C.toGaf02ChainE.cutQ_R74 0 x ∈
        C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
  have hzero : ∀ x ∈ C.toGaf02ChainE.cutM2_R74 Kb,
      x ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 :=
    fun x hx => C.toGaf02ChainE.not_zero_of_mem_M1_EFC hεr hx.1
  have hS : ∀ x ∈ C.toGaf02ChainE.cutM2_R74 Kb, ∀ k (hk : k ∈ P.slim.centres),
      dist x k < 9 * Δ * ρ k → 10 * Δ ≤ |(P.slim.centre k hk).coord x| :=
    fun q hq k hk hd => C.toGaf02ChainE.slim_far_of_relint_EFC hK
      (M₁ := C.toGaf02ChainE.cutM1_R74) (fun p hp hpK => by rw [hsl]; exact ⟨hp, hpK⟩) hq hk hd
  refine C.remainder_subset_X₁_EFC hσc hγ hγ1 hzero hS ?_
  rintro x ⟨hxM, hxT, k, hv, hu⟩
  have hV : x ∈ C.toGaf02ChainE.edgeVertical_R74 :=
    Or.inr ⟨(C.toChain.scale_pos x).2, le_of_lt hxT⟩
  obtain ⟨hW, h9, h4⟩ := C.toChain.stageTwo_mem_base_FDC k hv hu hV
  exact ⟨hxM, ⟨hW, k, h9, h4⟩, hV⟩

end Gaf02ChainEJA

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **D74-3 producer** (final family C14Z): a cut choice built from ZSP04's ACTUAL `K₃, D₃`
(`zsp0405_row_ZSP35`, intervals and loops), `edgeBaseOpen = B₂` (empty if `C₂ = ∅`) and
`circleBaseOpen = W₁ ∩ R₁`; for the SAME `K₃`: `slimSet = M₁ ∩ f⁻¹(K₃)` compact,
`M = Z ∪ slimSet ∪ M₂`, and `M₃ ⊆ X₁`. -/
theorem exists_cutChoice_R74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    ∃ D : CutChoiceOn74 C.toGaf02ChainE,
      D.slimSet = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' D.K₃.carrier ∧
      IsCompact D.slimSet ∧ C.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.M₂ = univ ∧
      D.M₃ ⊆ {x | C.toGaf02ChainE.cutQ_R74 0 x ∈
        C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, -, hSeq, hSc, -, -, -, -, -, -, hcov⟩ :=
    C.zsp0405_row_ZSP35 hεr
  have hM3 := C.cutM3_subset_X₁_R74 hεr hσc hγ hγ1 (fun w hw => hKs (Or.inl hw)) hSeq
  have hC1 : C.toGaf02ChainE.cutC1_R74 K₃.carrier ⊆
      gaf07CircleRatio_G47 P.toLocalChartPackets ∩ C.toChain.finalBase_BAS 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hM3 hx).symm
  have hslim : C.slimMap_ZSP35 ⁻¹' D₃.carrier = C.slimPiece_ZSP35 K₃.carrier := by
    rw [hD]
    rfl
  by_cases hC2 : C.toGaf02ChainE.cutC2_R74 K₃.carrier = ∅
  · refine ⟨⟨K₃, D₃, hD, hKs, hKF, ∅, ⟨∅, isOpen_empty, empty_inter _⟩, hC2.subset,
      fun _ => rfl, _, ⟨_, isOpen_gaf07CircleRatio_GAFC _, rfl⟩, hC1⟩, ?_, ?_, ?_, hM3⟩
    · change C.slimMap_ZSP35 ⁻¹' D₃.carrier = _
      rw [hslim, hSeq]
    · change IsCompact (C.slimMap_ZSP35 ⁻¹' D₃.carrier)
      rw [hslim]
      exact hSc
    · change C.zeroUnion_ZSP35 ∪ C.slimMap_ZSP35 ⁻¹' D₃.carrier ∪ _ = univ
      rw [hslim]
      exact hcov
  · refine ⟨⟨K₃, D₃, hD, hKs, hKF, edgeRatio_R74 _ ∩ C.toChain.finalBase_BAS 1,
      ⟨_, isOpen_edgeRatio_R74 _, rfl⟩, ?_, fun h => absurd h hC2, _,
      ⟨_, isOpen_gaf07CircleRatio_GAFC _, rfl⟩, hC1⟩, ?_, ?_, ?_, hM3⟩
    · intro w hw
      exact (C.toGaf02ChainE.cutC2_subset_R74 _ hw).symm
    · change C.slimMap_ZSP35 ⁻¹' D₃.carrier = _
      rw [hslim, hSeq]
    · change IsCompact (C.slimMap_ZSP35 ⁻¹' D₃.carrier)
      rw [hslim]
      exact hSc
    · change C.zeroUnion_ZSP35 ∪ C.slimMap_ZSP35 ⁻¹' D₃.carrier ∪ _ = univ
      rw [hslim]
      exact hcov

end Gaf02ChainEJA

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **Inhabitant on the `RP³ # RP³` C14Z fixture** (lane C14-EDP-FDCd's
`exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC`: `ε_r = 0`, `σ_c = 0`, `γ = 0`): the enhanced chain
with (JA) on the final family carries a cut choice. VACUOUS-TRUTH CHECK: the fixture's circle,
edge and slim families are empty and its zero ball covers the source (`M₁ = ∅`). -/
theorem cutChoice_dihedralTiny_R74 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      Nonempty (CutChoiceOn74 C.toGaf02ChainE) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -⟩ :=
    exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC Kj 0
  obtain ⟨D, -⟩ := C.exists_cutChoice_R74 (by norm_num) (by norm_num) le_rfl (by norm_num)
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨D⟩⟩

end DifferentialGeometry.Geometry.Collapse
