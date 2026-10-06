import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactApplicationsEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseEFE

/-!
# Draft 74 CL0, G1 (chain kernel): the produced cut choice `D_R` with whole-fibre good bases

Lane O-CL0 (`_OCL`), G1. Draft 74 §1.3 / D74-3 / D74-11 / D74-13: the open base neighbourhoods of
the cut choice must be GOOD over every point (`EdgeBundle.fibre_disk` and
`CircleBundle.trivialization` quantify over the whole base). The lead's decision of 2026-10-05
(named revision for the closed landing): the exports are produced at ONE explicit choice `D_R`.
On a chain `C : Gaf02ChainEJA` of the final closed family (stages `0, 1, 2` = circle, edge,
slim) this module fixes that choice as a DEFINITION:

* `slimK₃_OCL`, `slimD₃_OCL`: ZSP04's actual `K₃, D₃` (`zsp0405_row_ZSP35`, intervals and loops),
  chosen once;
* **`goodCutOn_OCL C hεr hσc hγ hγ1 : CutChoiceOn74 C.toGaf02ChainE`** with
  `edgeBaseOpen = B₂ = W₂ ∩ edgeRatio` (EMPTY when `C₂ = ∅`) and `circleBaseOpen = W₁ ∩ R₁`;
* `goodCutOn_facts_OCL`: `slimSet = M₁ ∩ f₃⁻¹(K₃)` compact, `M = Z ∪ slimSet ∪ M₂`, `M₃ ⊆ X₁`;
* `goodCutOn_edgeBaseOpen_OCL`: `edgeBaseOpen ⊆ B₂ = edgeBase_EDP23` (and `= B₂` if `C₂ ≠ ∅`);
* **`goodCutOn_edge_disk_OCL`** (EDP04 over EVERY point of the edge base, through EDP02's base-level
  exactness `edgeBase_fibre_disk_EDP23`): the whole fibre `{q₁ = w, T ≤ 4Δ}` is a smooth embedded
  disk with boundary circle the rim `{T = 4Δ}`;
* `goodCutOn_edge_local_OCL` (ELoc): a point over the edge base with `T ≤ 4Δ` lies in FC33's open
  threshold-5 edge domain `U₂` (the whole disks lie in the open ambient parent);
* **`goodCutOn_circleSource_OCL`**: the circle source `q₀⁻¹(W₁ ∩ R₁)` is lane S-EDP-FDC2's
  `circleDomain_EFE` (the domain of FDC03's circle bundle), and it lies in FC33's threshold-5
  circle domain `U₀`;
* **`goodCutOn_circle_fibre_OCL`** (GAF07 over EVERY point of the circle base): the whole fibre
  `q₀⁻¹(w)` is a smooth embedded circle.

Numeric premises are the chain's (row hypotheses at the register layer, D74-18): `ε_r < 1/2`,
`σ_c ≤ 1/2`, `0 ≤ γ ≤ 3/4` (the cut), EDP-E / EDP04's list (the edge disks), `β₂ ≤ 10⁻⁷`,
`γ + β₂ < 1/10` (GAF07). Consumer: `goodCutOn_dihedralTiny_OCL` (RP³ # RP³ fixture; its circle,
edge and slim families are EMPTY — the known acceptance gap D70-8 / D71-7).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- ZSP04's actual compact slim base domain `K₃` (`zsp0405_row_ZSP35`), chosen once. -/
def slimK₃_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35 :=
  (C.zsp0405_row_ZSP35 hεr).choose

/-- ZSP04's actual `D₃ = K₃ ∩ C₃` (`zsp0405_row_ZSP35`), chosen once with `K₃`. -/
def slimD₃_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35 :=
  (C.zsp0405_row_ZSP35 hεr).choose_spec.choose

/-- The `K₃` contract and the slim facts of the chosen `K₃, D₃` (the conjuncts of
`zsp0405_row_ZSP35` the cut uses). -/
theorem slimDomains_spec_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    (C.slimD₃_OCL hεr).carrier = (C.slimK₃_OCL hεr).carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' (C.slimK₃_OCL hεr).carrier :
          Set C.slimBs_ZSP35) ∧
      Disjoint ((C.slimK₃_OCL hεr).carrier \ Subtype.val '' interior
          (Subtype.val ⁻¹' (C.slimK₃_OCL hεr).carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      C.slimPiece_ZSP35 (C.slimK₃_OCL hεr).carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' (C.slimK₃_OCL hεr).carrier ∧
      IsCompact (C.slimPiece_ZSP35 (C.slimK₃_OCL hεr).carrier) ∧
      C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 (C.slimK₃_OCL hεr).carrier ∪
        ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 (C.slimK₃_OCL hεr).carrier :
            Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) = univ := by
  have h := (C.zsp0405_row_ZSP35 hεr).choose_spec.choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The circle base `W₁ ∩ R₁` contains `C₁` of the chosen `K₃` (FDC03's `M₃ ⊆ X₁`). -/
theorem goodCutOn_C₁_sub_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    C.toGaf02ChainE.cutC1_R74 (C.slimK₃_OCL hεr).carrier ⊆
      gaf07CircleRatio_G47 P.toLocalChartPackets ∩ C.toChain.finalBase_BAS 0 := by
  obtain ⟨-, hKs, -, hSeq, -⟩ := C.slimDomains_spec_OCL hεr
  have hM3 := C.cutM3_subset_X₁_R74 hεr hσc hγ hγ1 (fun w hw => hKs (Or.inl hw)) hSeq
  rintro _ ⟨x, hx, rfl⟩
  exact (hM3 hx).symm

open Classical in
/-- **The produced cut choice `D_R`** (lead's decision 2026-10-05): ZSP04's actual `K₃, D₃`,
`edgeBaseOpen = B₂ = edgeRatio ∩ W₂` (EMPTY when `C₂ = ∅`), `circleBaseOpen = R₁ ∩ W₁`. -/
def goodCutOn_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    CutChoiceOn74 C.toGaf02ChainE where
  K₃ := C.slimK₃_OCL hεr
  D₃ := C.slimD₃_OCL hεr
  D₃_eq := (C.slimDomains_spec_OCL hεr).1
  K₃_req := (C.slimDomains_spec_OCL hεr).2.1
  K₃_faces := (C.slimDomains_spec_OCL hεr).2.2.1
  edgeBaseOpen := if C.toGaf02ChainE.cutC2_R74 (C.slimK₃_OCL hεr).carrier = ∅ then ∅ else
    edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 ∩ C.toChain.finalBase_BAS 1
  edgeBaseOpen_rel := by
    split_ifs
    · exact ⟨∅, isOpen_empty, empty_inter _⟩
    · exact ⟨_, isOpen_edgeRatio_R74 _, rfl⟩
  edgeBaseOpen_sub := by
    split_ifs with h
    · exact h.subset
    · intro w hw
      exact (C.toGaf02ChainE.cutC2_subset_R74 _ hw).symm
  edgeBaseOpen_empty := fun h => by simp only [h, ↓reduceIte]
  circleBaseOpen := gaf07CircleRatio_G47 P.toLocalChartPackets ∩ C.toChain.finalBase_BAS 0
  circleBaseOpen_rel := ⟨_, isOpen_gaf07CircleRatio_GAFC _, rfl⟩
  circleBaseOpen_sub := C.goodCutOn_C₁_sub_OCL hεr hσc hγ hγ1

/-- The circle base of `D_R` is `R₁ ∩ W₁` (by definition). -/
theorem goodCutOn_circleBaseOpen_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    (C.goodCutOn_OCL hεr hσc hγ hγ1).circleBaseOpen =
      gaf07CircleRatio_G47 P.toLocalChartPackets ∩ C.toChain.finalBase_BAS 0 :=
  rfl

/-- **The facts of `D_R`** (as for every ZSP04 cut choice): `slimSet = M₁ ∩ f₃⁻¹(K₃)` compact,
`M = Z ∪ slimSet ∪ M₂`, and `M₃ ⊆ X₁ = q₀⁻¹(W₁ ∩ R₁)`. -/
theorem goodCutOn_facts_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    (C.goodCutOn_OCL hεr hσc hγ hγ1).slimSet =
        (interior C.zeroUnion_ZSP35)ᶜ ∩
          C.slimMap_ZSP35 ⁻¹' (C.goodCutOn_OCL hεr hσc hγ hγ1).K₃.carrier ∧
      IsCompact (C.goodCutOn_OCL hεr hσc hγ hγ1).slimSet ∧
      C.zeroUnion_ZSP35 ∪ (C.goodCutOn_OCL hεr hσc hγ hγ1).slimSet ∪
        (C.goodCutOn_OCL hεr hσc hγ hγ1).M₂ = univ ∧
      (C.goodCutOn_OCL hεr hσc hγ hγ1).M₃ ⊆ {x | C.toGaf02ChainE.cutQ_R74 0 x ∈
        C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
  obtain ⟨-, hKs, -, hSeq, hSc, hcov⟩ := C.slimDomains_spec_OCL hεr
  have hslim := (C.goodCutOn_OCL hεr hσc hγ hγ1).slimSet_eq
  refine ⟨hslim.trans hSeq, hslim ▸ hSc, ?_,
    C.cutM3_subset_X₁_R74 hεr hσc hγ hγ1 (fun w hw => hKs (Or.inl hw)) hSeq⟩
  rw [hslim]
  exact hcov

/-- **The edge base of `D_R` lies in `B₂`** (EDP02's base `edgeBase_EDP23`). -/
theorem goodCutOn_edgeBaseOpen_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    (C.goodCutOn_OCL hεr hσc hγ hγ1).edgeBaseOpen ⊆ C.toGaf02ChainE.edgeBase_EDP23 := by
  intro w hw
  change w ∈ (if C.toGaf02ChainE.cutC2_R74 (C.slimK₃_OCL hεr).carrier = ∅ then ∅ else
    edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 ∩
      C.toChain.finalBase_BAS 1) at hw
  split_ifs at hw
  · exact absurd hw (notMem_empty w)
  · exact ⟨hw.2, hw.1⟩

/-- **When `C₂ ≠ ∅` the edge base of `D_R` is all of `B₂`.** -/
theorem goodCutOn_edgeBaseOpen_eq_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    (hC₂ : (C.goodCutOn_OCL hεr hσc hγ hγ1).C₂ ≠ ∅) :
    (C.goodCutOn_OCL hεr hσc hγ hγ1).edgeBaseOpen = C.toGaf02ChainE.edgeBase_EDP23 := by
  refine (C.goodCutOn_edgeBaseOpen_OCL hεr hσc hγ hγ1).antisymm fun w hw => ?_
  change w ∈ (if C.toGaf02ChainE.cutC2_R74 (C.slimK₃_OCL hεr).carrier = ∅ then ∅ else
    edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 ∩ C.toChain.finalBase_BAS 1)
  have hC₂' : C.toGaf02ChainE.cutC2_R74 (C.slimK₃_OCL hεr).carrier ≠ ∅ := hC₂
  simp only [hC₂', ↓reduceIte]
  exact ⟨hw.2, hw.1⟩

/-- **EDP04 over EVERY point of the edge base of `D_R`** (EDP02's base-level exactness): the whole
fibre `{x | q₁ x = w, T x ≤ 4Δ}` is the range of a smooth embedding of the closed disk, whose
boundary circle goes onto the whole rim `{q₁ = w, T = 4Δ}`. -/
theorem goodCutOn_edge_disk_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc' : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.goodCutOn_OCL hεr hσc hγ hγ1).edgeBaseOpen) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | C.toGaf02ChainE.cutQ_R74 1 x = w ∧ EuclideanSpace.proj (0 : Fin 2)
          (gafHeightVector P.toLocalChartFamily P.zero (C.toChain.E x)) / C.toChain.scale x ≤
            4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x | C.toGaf02ChainE.cutQ_R74 1 x = w ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
          (C.toChain.E x)) / C.toChain.scale x = 4 * Δ} :=
  C.toGaf02ChainE.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc' hb hγc hγc1 hβc1
    (C.goodCutOn_edgeBaseOpen_OCL hεr hσc hγ hγ1 hw)

/-- **ELoc for the edge base of `D_R`**: a point over the edge base with `T ≤ 4Δ` lies in FC33's
open threshold-5 edge domain `U₂` (so the whole disks lie in the open ambient parent). -/
theorem goodCutOn_edge_local_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) (hΔ2 : 2 ≤ Δ)
    {x : X} (hx : C.toGaf02ChainE.cutQ_R74 1 x ∈ (C.goodCutOn_OCL hεr hσc hγ hγ1).edgeBaseOpen)
    (hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
      (C.toChain.E x)) / C.toChain.scale x ≤ 4 * Δ) :
    x ∈ gafStageDomain5_BAS P.toLocalChartPackets 1 := by
  obtain ⟨-, k, hv, hu⟩ := C.goodCutOn_edgeBaseOpen_OCL hεr hσc hγ hγ1 hx
  have hV : x ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
        (C.toChain.E p)) / C.toChain.scale p ≤ 4 * Δ} :=
    Or.inr ⟨(C.toChain.scale_pos x).2, hT⟩
  obtain ⟨hball, hη, ht, -⟩ := C.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu hV
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨k, hball, ?_, ?_⟩
  · rw [abs_lt] at hη ⊢
    constructor <;> linarith [hη.1, hη.2]
  · change P.edge.smoothing x / ρ x < 5 * Δ
    linarith

/-- **The circle source of `D_R` is the domain of FDC03's circle bundle** (lane S-EDP-FDC2's
`circleDomain_EFE`, the whole preimage of `B₁ = W₁ ∩ R₁`), and it lies in FC33's open
threshold-5 circle domain `U₀`. -/
theorem goodCutOn_circleSource_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    (C.goodCutOn_OCL hεr hσc hγ hγ1).circleSource = (C.circleDomain_EFE : Set X) ∧
      (C.goodCutOn_OCL hεr hσc hγ hγ1).circleSource ⊆
        gafStageDomain5_BAS P.toLocalChartPackets 0 := by
  obtain ⟨⟨hB1, -⟩, -, hloc, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  have heq : (C.goodCutOn_OCL hεr hσc hγ hγ1).circleSource =
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        C.toChain.circleBase_BAS := by
    rw [hB1, inter_comm]
    rfl
  refine ⟨heq.trans (C.circleDomain_eq_EFE hβ hd).symm, fun x hx => ?_⟩
  rw [heq] at hx
  obtain ⟨i, hb, hco, -⟩ := hloc x hx
  exact ⟨i, hb, by linarith⟩

/-- **GAF07 over EVERY point of the circle base of `D_R`**: the whole fibre `q₀⁻¹(w)` is a smooth
embedded circle. -/
theorem goodCutOn_circle_fibre_OCL
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.goodCutOn_OCL hεr hσc hγ hγ1).circleBaseOpen) :
    ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = C.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w} := by
  have hwB : w ∈ C.toChain.finalBase_BAS 0 := hw.2
  let cc : C.circleBaseOpens_EFE := ⟨⟨w, hwB⟩, hw.1⟩
  obtain ⟨f, hf, hr⟩ := C.circleProj_circle_EFE hβ hd cc
  exact ⟨f, hf, hr.trans (C.circleProj_fibre_EFE cc)⟩

end Gaf02ChainEJA

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **Consumer on the `RP³ # RP³` C14Z fixture** (`ε_r = 0`, `σ_c = 0`, `γ = 0`): the produced
cut choice `D_R` exists on a chain with (JA), with `M = Z ∪ slimSet ∪ M₂`. VACUOUS-TRUTH CHECK: the
fixture's circle, edge and slim families are empty (known acceptance gap D70-8 / D71-7). -/
theorem goodCutOn_dihedralTiny_OCL (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      C.zeroUnion_ZSP35 ∪ (C.goodCutOn_OCL (by norm_num) (by norm_num) le_rfl
        (by norm_num)).slimSet ∪
        (C.goodCutOn_OCL (by norm_num) (by norm_num) le_rfl (by norm_num)).M₂ = univ := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -⟩ :=
    exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC Kj 0
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C,
    (C.goodCutOn_facts_OCL _ _ _ _).2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
