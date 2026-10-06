import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRowFacesEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimFullRowZSP35
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemovalEdge

/-!
# FDC04, clause "finite lists of compact pieces": the cover and the edge pieces (G1, part 2)

Lane S-FDC04 (`_FD4`), group G1. Blueprint `master207B.tex`, FDC04 (B:7367-7435): the four domains
"are finite unions of compact embedded pieces, cover the carrier, and have disjoint ambient
interiors". On the final family, for an admissible `K₃, D₃` (the five properties of
`zsp04_D3_ZSP35`) and `hcpt` = FDC02's compactness of `M^edge` (discharged by the tail in G3):

* `fdc04_cover_FD4`: with `Z = ⋃ Z_k`, `M^slim = f₃⁻¹(D₃)`, the actual `M₂ = M₁ ∖ int_{M₁} M^slim`,
  `M^edge = M₂ ∩ X₂` (low part) and `M₃ = M₂ ∖ int_{M₂} M^edge`: `M^edge` and `M₃` are compact,
  `M₂ = M^edge ∪ M₃`, `M^edge ∩ M₃` is the relative frontier, `Z ∪ M^slim ∪ M^edge ∪ M₃ = M`, and
  the four ambient interiors are pairwise disjoint (the point-set content of
  `eventually_fdc04_M2_C14Z_EFC`, for the pair `K₃, D₃` of the other rows, from `hcpt` alone);
* `edge_pieces_FD4`: the edge base `C₂ = f₂(M^edge)` is the disjoint union of the finitely many
  compact components of E2 (`edge_components_EFE`), and `M^edge` is the disjoint union of the
  compact pieces over them (properness below `4Δ`, `edgeBundleData_EFE`); the saturation of E1
  makes each piece a union of whole fibres.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Pieces

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- FDC02's edge piece `M^edge = M₂ ∩ X₂` (the low part, `T ≤ 4Δ`), in the form of
`edgeRow_EFE`'s compactness hypothesis. -/
abbrev edgeA_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (Δ : ℝ) : Set X :=
  C.edgeM2_EFE K₃ ∩ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}

/-- FDC03's remainder `M₃ = M₂ ∖ int_{M₂} M^edge`. -/
abbrev edgeM3_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (Δ : ℝ) : Set X :=
  C.edgeM2_EFE K₃ \ Subtype.val '' interior
    (Subtype.val ⁻¹' C.edgeA_FD4 K₃ Δ : Set (C.edgeM2_EFE K₃))

/-- The piece of the edge bundle over a set `B` of base points: the whole low fibres over `B`. -/
abbrev edgePieceOver_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (Δ : ℝ) (B : Set C.edgeBaseOpens_EFE) : Set X :=
  Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ B ∧ C.edgeHeight_EFE x ≤ 4 * Δ}

/-- Pieces over disjoint sets of base points are disjoint. -/
theorem edgePieceOver_disjoint_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    {B B' : Set C.edgeBaseOpens_EFE} (h : Disjoint B B') :
    Disjoint (C.edgePieceOver_FD4 Δ B) (C.edgePieceOver_FD4 Δ B') := by
  refine Set.disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨x, ⟨hxB, -⟩, rfl⟩ := hy
  obtain ⟨x', ⟨hxB', -⟩, hxx⟩ := hy'
  have : x' = x := Subtype.ext hxx
  subst this
  exact Set.disjoint_left.mp h hxB hxB'

/-- **FDC04's four-piece cover for the pair `K₃, D₃`** (see the module docstring). -/
theorem fdc04_cover_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hcpt : IsCompact (C.edgeA_FD4 K₃ Δ)) :
    IsCompact (C.edgeA_FD4 K₃ Δ) ∧ IsCompact (C.edgeM3_FD4 K₃ Δ) ∧
      C.edgeM2_EFE K₃ = C.edgeA_FD4 K₃ Δ ∪ C.edgeM3_FD4 K₃ Δ ∧
      C.edgeA_FD4 K₃ Δ ∩ C.edgeM3_FD4 K₃ Δ =
        C.edgeA_FD4 K₃ Δ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.edgeA_FD4 K₃ Δ : Set (C.edgeM2_EFE K₃)) ∧
      C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 K₃.carrier ∪ C.edgeA_FD4 K₃ Δ ∪ C.edgeM3_FD4 K₃ Δ =
        univ ∧
      Disjoint (interior C.zeroUnion_ZSP35) (interior (C.slimPiece_ZSP35 K₃.carrier)) ∧
      Disjoint (interior C.zeroUnion_ZSP35) (interior (C.edgeA_FD4 K₃ Δ)) ∧
      Disjoint (interior C.zeroUnion_ZSP35) (interior (C.edgeM3_FD4 K₃ Δ)) ∧
      Disjoint (interior (C.slimPiece_ZSP35 K₃.carrier)) (interior (C.edgeA_FD4 K₃ Δ)) ∧
      Disjoint (interior (C.slimPiece_ZSP35 K₃.carrier)) (interior (C.edgeM3_FD4 K₃ Δ)) ∧
      Disjoint (interior (C.edgeA_FD4 K₃ Δ)) (interior (C.edgeM3_FD4 K₃ Δ)) := by
  obtain ⟨-, hSeq, -, hreg, -, hcollar, -⟩ :=
    C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  have hSM : C.slimPiece_ZSP35 K₃.carrier ⊆ (interior C.zeroUnion_ZSP35)ᶜ := by
    rw [hSeq]
    exact inter_subset_left
  have hAM : C.edgeA_FD4 K₃ Δ ⊆ C.edgeM2_EFE K₃ := inter_subset_left
  obtain ⟨hM₃c, hM₂, hAM₃, hcov, h1, h2, h3, h4, h5, h6⟩ :=
    DifferentialGeometry.Topology.relative_removal_third_FDC C.zeroUnion_ZSP35
      (C.slimPiece_ZSP35 K₃.carrier) (C.edgeA_FD4 K₃ Δ) (interior C.zeroUnion_ZSP35)ᶜ
      (C.edgeM2_EFE K₃) (C.edgeM3_FD4 K₃ Δ) rfl rfl rfl hSM hreg hcollar hAM
  exact ⟨hcpt, hM₃c.isCompact, hM₂, hAM₃, hcov, h1, h2, h3, h4, h5, h6⟩

/-- **The edge pieces** (see the module docstring): the finitely many compact components of
`C₂ = f₂(M^edge)` and the compact pieces of `M^edge` over them. -/
theorem edge_pieces_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (C.edgeA_FD4 K₃ Δ)) :
    ∃ (m l : ℕ) (Ba : Fin m → Set C.edgeBaseOpens_EFE) (Bc : Fin l → Set C.edgeBaseOpens_EFE),
      (∀ i, IsCompact (Ba i)) ∧ (∀ j, IsCompact (Bc j)) ∧
      Pairwise (Disjoint on Ba) ∧ Pairwise (Disjoint on Bc) ∧
      (∀ (i : Fin m) (j : Fin l), Disjoint (Ba i) (Bc j)) ∧
      C.edgeC2_EFE K₃ = (⋃ i, Ba i) ∪ ⋃ j, Bc j ∧
      (∀ i, IsCompact (C.edgePieceOver_FD4 Δ (Ba i))) ∧
      (∀ j, IsCompact (C.edgePieceOver_FD4 Δ (Bc j))) ∧
      C.edgeA_FD4 K₃ Δ =
        (⋃ i, C.edgePieceOver_FD4 Δ (Ba i)) ∪ ⋃ j, C.edgePieceOver_FD4 Δ (Bc j) ∧
      Pairwise (Disjoint on fun i => C.edgePieceOver_FD4 Δ (Ba i)) ∧
      Pairwise (Disjoint on fun j => C.edgePieceOver_FD4 Δ (Bc j)) ∧
      (∀ (i : Fin m) (j : Fin l),
        Disjoint (C.edgePieceOver_FD4 Δ (Ba i)) (C.edgePieceOver_FD4 Δ (Bc j))) := by
  let _ := A.edgeChartedSpace1
  have _ : IsManifold (𝓡 1) ∞ (C.toChain.finalBase_BAS 1) := A.edge_isManifold1.1
  have hE1 := C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
    hKs hKF hDreg hdD hcpt
  have hbun := C.edgeBundleData_EFE A hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
  obtain ⟨m, l, e, a, cc, -, ha, hra, hcc, hrc, -⟩ :=
    C.edge_components_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt
  have hBa : ∀ i, IsCompact (e (Sum.inl i)).1 := fun i => by
    rw [← hra i]
    exact isCompact_range (ha i).isEmbedding.continuous
  have hBc : ∀ j, IsCompact (e (Sum.inr j)).1 := fun j => by
    rw [← hrc j]
    exact isCompact_range (hcc j).isEmbedding.continuous
  have hdisj : ∀ s s', s ≠ s' → Disjoint (e s).1 (e s').1 := fun s s' h =>
    ActualComponent.disjoint_of_ne (fun h' => h (e.injective h'))
  have hunion : C.edgeC2_EFE K₃ = (⋃ i, (e (Sum.inl i)).1) ∪ ⋃ j, (e (Sum.inr j)).1 := by
    ext p
    constructor
    · intro hp
      obtain ⟨s, hs⟩ := e.surjective (ActualComponent.of hp)
      have hps : p ∈ (e s).1 := by
        rw [hs]
        exact mem_connectedComponentIn hp
      rcases s with i | j
      · exact Or.inl (mem_iUnion.mpr ⟨i, hps⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨j, hps⟩)
    · rintro (hp | hp)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        exact (e (Sum.inl i)).subset hi
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
        exact (e (Sum.inr j)).subset hj
  refine ⟨m, l, fun i => (e (Sum.inl i)).1, fun j => (e (Sum.inr j)).1, hBa, hBc,
    fun i i' h => hdisj _ _ (fun h' => h (Sum.inl_injective h')),
    fun j j' h => hdisj _ _ (fun h' => h (Sum.inr_injective h')),
    fun i j => hdisj _ _ (fun h' => Sum.inl_ne_inr h'), hunion,
    fun i => hbun.2.2.2.1 _ (hBa i), fun j => hbun.2.2.2.1 _ (hBc j), ?_,
    fun i i' h => C.edgePieceOver_disjoint_FD4 (hdisj _ _ (fun h' => h (Sum.inl_injective h'))),
    fun j j' h => C.edgePieceOver_disjoint_FD4 (hdisj _ _ (fun h' => h (Sum.inr_injective h'))),
    fun i j => C.edgePieceOver_disjoint_FD4 (hdisj _ _ (fun h' => Sum.inl_ne_inr h'))⟩
  -- `M^edge` is the union of the pieces (saturation of E1)
  have hsat : C.edgeA_FD4 K₃ Δ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈
      C.edgeC2_EFE K₃ ∧ C.edgeHeight_EFE x ≤ 4 * Δ} := hE1.2.1
  rw [hsat]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxT⟩, rfl⟩
    have hx' : C.edgeProj_EFE x ∈ (⋃ i, (e (Sum.inl i)).1) ∪ ⋃ j, (e (Sum.inr j)).1 :=
      hunion ▸ hx
    rcases hx' with hx' | hx'
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      exact Or.inl (mem_iUnion.mpr ⟨i, x, ⟨hi, hxT⟩, rfl⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
      exact Or.inr (mem_iUnion.mpr ⟨j, x, ⟨hj, hxT⟩, rfl⟩)
  · rintro (hy | hy)
    · obtain ⟨i, x, ⟨hxB, hxT⟩, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, ⟨hunion ▸ Or.inl (mem_iUnion.mpr ⟨i, hxB⟩), hxT⟩, rfl⟩
    · obtain ⟨j, x, ⟨hxB, hxT⟩, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, ⟨hunion ▸ Or.inr (mem_iUnion.mpr ⟨j, hxB⟩), hxT⟩, rfl⟩

end Pieces

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
