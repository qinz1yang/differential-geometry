import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleBaseFacesBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1Applications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsLandingLND
import DifferentialGeometry.Topology.Surface.Recognition.PartitionOfHalfChartsBCF

/-!
# BCF03 G7, first conjunct: the embedded face partition of every component of `∂M₂` (lane S-BCF03b)

`BoundaryGaf02ChainE.bcf03_face_partition_part1_BCF`: for every `x ∈ ∂M₂` an
`EmbeddedFacePartition_BCF (connectedComponentIn (∂M₂) x)` whose disks are `Y ∩` whole horizontal
edge fibres over `f₂(H_e)` and whose pieces cover `Y ∩ R_c` (the first conjunct of the frozen
`bcf03_face_partition_BCF03`), on arbitrary `(Bs, WF v2b, Z, Kc, er)`.

Inputs (all of existing shapes; nothing is a conclusion of this theorem):
* the numerical premises of F4c (`hrd … hθ`), and F1's call numerics `3βc ≤ β₂`, `β₂ < 10⁻⁶` (hence
  `β₂ < 1`), `0 ≤ γ ≤ 3/4`, `100(bder + 1)(1 + bcut + cw₀/Σ₀)ΛΔ < 10⁻⁶` (`c₂ < 10⁻⁵` is
  `C.validity.c_two_lt_E4`); F1 is used ONLY through O-F1's
  `wholeDiskBoundary_eq_wholeCircleFiber_OF1`;
* BCF02's five remaining conjuncts `hG6` (G6, text v3.1);
* the corner record of the circle base with its LABEL CLAUSE `hG6c` (G6c strengthened: named
  revision candidate for text v3.2, "all labels whose face contains the fibre belong to `L`").
Everything else is proved on this route: saturation of `∂M₂ ∩ R_c` by whole circle fibres, the half
charts of the base curve, the finiteness and degrees of the disks, the parametrizations.
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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The circle-base corner record with its label clause** (G6c strengthened). -/
theorem circleCornerRecord_unfold_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    circleFaceSet74 Kc = Sum.elim Kc.edgeFaceSet_BIFc (fun _ => Kc.verticalFace) := by
  funext s
  rcases s with ℓ | u <;> rfl

/-- **BCF03 G7, first conjunct** (see the module docstring for the inputs). -/
theorem bcf03_face_partition_part1_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1 / 1000000)
    (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hG6 : Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩
        C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : ∀ y ∈ C.toChain.stageMap 0 '' Kc.remainder,
      y ∉ relInterior_BIF (Bs.base 0) (C.toChain.stageMap 0 '' Kc.remainder) →
      ∃ (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (L : Finset (CircleFaceLabel74 Kc))
        (φ : CircleFaceLabel74 Kc →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen O ∧ y ∈ O ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0 ∧
          {y' | y' ∈ O ∧ y' ∈ C.toChain.stageMap 0 '' Kc.remainder ∧ φ f y' = 0} =
            {y' | y' ∈ O ∧ y' ∈ C.toChain.stageMap 0 '' Kc.remainder ∧
              Bs.fibre 0 y' ⊆ circleFaceSet74 Kc f}) ∧
        (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
          fun f : L => mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v) ∧
        (C.toChain.stageMap 0 '' Kc.remainder) ∩ O =
          {y' | y' ∈ O ∩ Bs.base 0 ∧ ∀ f ∈ L, φ f y' ≤ 0} ∧
        (∀ f, Bs.fibre 0 y ⊆ circleFaceSet74 Kc f → f ∈ L)) :
    ∀ x ∈ frontier Kc.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        ↥(connectedComponentIn (frontier Kc.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) =
        connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder := by
  classical
  obtain ⟨hRX, hVe, -, hRsat, -⟩ := hG6
  have hβ2' : β 2 < 1 := by linarith
  have hF1 := C.wholeDiskBoundary_eq_wholeCircleFiber_OF1 h3βc hβ2' hγ hγ34
    C.validity.c_two_lt_E4 hC WF
  have hM₂c : IsClosed Kc.M₂ := Kc.isClosed_M₂_BCF
  have hRcc : IsClosed Kc.remainder := isClosed_sdiff_relInterior_BCF hM₂c Kc.edgePiece
  have hBdM : frontier Kc.M₂ ⊆ Kc.M₂ := hM₂c.frontier_subset
  have hRM : Kc.remainder ⊆ Kc.M₂ := fun p hp => hp.1
  have hcf := C.circleCornerRecord_unfold_BCF Kc
  have hB : ∀ q ∈ Bs.source 0, C.toChain.stageMap 0 q ∈ Bs.base 0 := fun q hq =>
    Bs.image_eq 0 ▸ mem_image_of_mem _ hq
  have hRsat' : ∀ q ∈ Bs.source 0,
      C.toChain.stageMap 0 q ∈ C.toChain.stageMap 0 '' Kc.remainder → q ∈ Kc.remainder :=
    fun q hq h => hRsat ▸ ⟨hq, h⟩
  have hFBd : ∀ ℓ, Kc.edgeFaceSet_BIFc ℓ ∩ Kc.M₂ ⊆ frontier Kc.M₂ := fun ℓ p hp =>
    C.edgeFaceSet_inter_M₂_subset_frontier_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ hp.2 hp.1
  have hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (Kc.edgeFaceSet_BIFc ℓ ∩ Kc.M₂)
      (Kc.edgeFaceSet_BIFc ℓ' ∩ Kc.M₂) := fun ℓ ℓ' hne =>
    C.edgeFaceSet_disjoint_inter_M₂_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ ℓ' hne
  have hKcl : ∀ ℓ, ∃ G : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsClosed G ∧ ∀ y ∈ Bs.base 0, (Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ ↔ y ∈ G) := fun ℓ =>
    C.exists_closed_fibreIn_BCF WF (C.isClosed_edgeFaceSet_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ)
  have hF1' : ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
        Bs.fibre 0 (C.toChain.stageMap 0 p) := fun y hy p hp hT => (hF1 y hy p hp hT).2
  -- the horizontal label over every point of the base curve
  have hsat1 : ∀ p ∈ frontier Kc.M₂ ∩ Kc.remainder, ∃ ℓ,
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' {C.toChain.stageMap 0 p} ⊆
        Kc.edgeFaceSet_BIFc ℓ := by
    rintro p ⟨hpBd, hpR⟩
    obtain ⟨O, L, φ, hO, hyO, hL1, -, hφ, -, -, -⟩ := hG6c _ ⟨p, hpR, rfl⟩
      (C.not_mem_relInterior_circleBase_BCF Kc hRsat hpBd hpR)
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hL1
    have hmem : C.toChain.stageMap 0 p ∈ {y' | y' ∈ O ∧
        y' ∈ C.toChain.stageMap 0 '' Kc.remainder ∧ φ s y' = 0} :=
      ⟨hyO, ⟨p, hpR, rfl⟩, (hφ s hs).2.1⟩
    rw [(hφ s hs).2.2] at hmem
    have hfib : Bs.fibre 0 (C.toChain.stageMap 0 p) ⊆ circleFaceSet74 Kc s := hmem.2.2
    rcases s with ℓ | u
    · exact ⟨ℓ, hfib⟩
    · exact C.exists_label_of_vertical_fibre_BCF Kc er hF1' hpBd (hRX hpR) hfib
  -- saturation of `∂M₂ ∩ R_c` by the whole circle fibres
  have hsat : ∀ p ∈ frontier Kc.M₂ ∩ Kc.remainder, ∀ q ∈ Bs.source 0,
      C.toChain.stageMap 0 q = C.toChain.stageMap 0 p → q ∈ frontier Kc.M₂ ∩ Kc.remainder := by
    intro p hp q hq hqp
    obtain ⟨ℓ, hℓ⟩ := hsat1 p hp
    have hqR : q ∈ Kc.remainder := hRsat' q hq (by rw [hqp]; exact ⟨p, hp.2, rfl⟩)
    exact ⟨C.edgeFaceSet_inter_M₂_subset_frontier_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ hqR.1
      (hℓ ⟨hq, hqp⟩), hqR⟩
  have hsatHe := C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er
  have hHe : ∀ p ∈ frontier Kc.M₂ ∩ Bs.source 1, ∀ q ∈ Bs.source 1,
      C.toChain.stageMap 1 q = C.toChain.stageMap 1 p → q ∈ frontier Kc.M₂ ∩ Bs.source 1 :=
    fun p hp q hq hqp => hsatHe p hp q ⟨hq, hqp⟩
  have hdisk : ∀ p ∈ frontier Kc.M₂ ∩ Bs.source 1, ∃ ed : Bs.fibre 1 (C.toChain.stageMap 1 p) ≃ₜ
      ClosedCell 2, Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
        Surface.rim_BCF (Bs.fibre 1) C.toChain.heightRatio (4 * Δ) (C.toChain.stageMap 1 p) :=
    fun p hp => WF.edge_fibre_OWF _ (Bs.image_eq 1 ▸ mem_image_of_mem _ hp.2)
  have hF1'' : ∀ p ∈ frontier Kc.M₂ ∩ Bs.source 1, C.toChain.heightRatio p = 4 * Δ →
      Surface.rim_BCF (Bs.fibre 1) C.toChain.heightRatio (4 * Δ) (C.toChain.stageMap 1 p) =
        Bs.fibre 0 (C.toChain.stageMap 0 p) := fun p hp hT =>
    hF1' _ (Bs.image_eq 1 ▸ mem_image_of_mem _ hp.2) p ⟨hp.2, rfl⟩ hT
  have hcover : frontier Kc.M₂ ⊆ (frontier Kc.M₂ ∩ Bs.source 1) ∪
      (frontier Kc.M₂ ∩ Kc.remainder) := by
    intro p hp
    by_cases hpX : p ∈ Bs.source 1
    · exact Or.inl ⟨hp, hpX⟩
    · exact Or.inr ⟨hp, hBdM hp, fun hr => hpX (relInterior_subset_BCF hr).2⟩
  have hrim : ∀ p ∈ frontier Kc.M₂ ∩ Bs.source 1, p ∈ Kc.remainder ↔
      C.toChain.heightRatio p = 4 * Δ := by
    intro p hp
    have hpPe : p ∈ Kc.edgePiece := ⟨hBdM hp.1, hp.2⟩
    constructor
    · intro hpR
      have : p ∈ Kc.verticalFace := hVe ▸ ⟨hpPe, hpR⟩
      exact this.2
    · intro hT
      have : p ∈ Kc.edgePiece ∩ Kc.remainder := hVe ▸ ⟨hpPe, hT⟩
      exact this.2
  have hRb1 : ∀ y ∈ C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder),
      (∃ p ∈ frontier Kc.M₂ ∩ Bs.source 1, C.toChain.heightRatio p = 4 * Δ ∧
        C.toChain.stageMap 0 p = y) →
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' {y} ⊆ Kc.verticalFace := by
    rintro y - ⟨p, hp, hT, rfl⟩ q hq
    have hrimeq := hF1'' p hp hT
    have hq' : q ∈ Surface.rim_BCF (Bs.fibre 1) C.toChain.heightRatio (4 * Δ)
        (C.toChain.stageMap 1 p) := hrimeq ▸ hq
    have hq1 : q ∈ Bs.source 1 := hq'.1.1
    have hqHe : q ∈ frontier Kc.M₂ ∩ Bs.source 1 := hHe p hp q hq1 hq'.1.2
    exact ⟨⟨hBdM hqHe.1, hq1⟩, hq'.2⟩
  have hRb2 : ∀ y ∈ C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder),
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' {y} ⊆ Kc.verticalFace →
      ∃ p ∈ frontier Kc.M₂ ∩ Bs.source 1, C.toChain.heightRatio p = 4 * Δ ∧
        C.toChain.stageMap 0 p = y := by
    rintro y ⟨p, hp, rfl⟩ hsub
    have hpV : p ∈ Kc.verticalFace := hsub ⟨hRX hp.2, rfl⟩
    exact ⟨p, ⟨hp.1, hpV.1.2⟩, hpV.2, rfl⟩
  have hhalf : ∀ y ∈ C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder),
      ∃ (B : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (d : HalfChart_BCF B (C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder))),
        y ∈ d.O ∧ (d.L y + d.κ = 0 ↔ ∃ p ∈ frontier Kc.M₂ ∩ Bs.source 1,
          C.toChain.heightRatio p = 4 * Δ ∧ C.toChain.stageMap 0 p = y) := by
    intro y hyΓ
    obtain ⟨p, hp, rfl⟩ := hyΓ
    obtain ⟨σ, φc, Oσ, hσ0, hσ, hσe, hσd, hOσ, hrange, hφ, hφr, hf⟩ :=
      C.circleChart_raw_BCF WF (hB p (hRX hp.2))
    obtain ⟨O, L, ψ, hO, hyO, -, -, hψ, hsurj, hC₁, hcl⟩ := hG6c _ ⟨p, hp.2, rfl⟩
      (C.not_mem_relInterior_circleBase_BCF Kc hRsat hp.1 hp.2)
    rw [hcf] at hψ hcl
    exact exists_halfChart_at_BCF (I := W.model) (by simp) (X := Bs.source 0) (Rc := Kc.remainder)
      (Bd := frontier Kc.M₂) (M₂ := Kc.M₂) (B₀ := Bs.base 0) (F := Kc.edgeFaceSet_BIFc)
      (V := Kc.verticalFace) hRM hRsat' hRX hB hdisj hFBd hKcl hsat1 hRb1 hRb2 ⟨p, hp, rfl⟩ hσ0 hσ
      hσe hσd hOσ hrange hφ hf hφr hO hyO L ψ hψ hsurj hC₁ hcl
  have hΓB : ∀ y ∈ C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder), y ∈ Bs.base 0 := by
    rintro _ ⟨q, hq, rfl⟩
    exact hB q (hRX hq.2)
  choose Bsf d hdO hE using fun y : ↥(C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder)) =>
    hhalf y.1 y.2
  have hch : ∀ y ∈ C.toChain.stageMap 0 '' (frontier Kc.M₂ ∩ Kc.remainder),
      ∃ (σ : EuclideanSpace ℝ (Fin 2) → BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)) (φ : EuclideanSpace ℝ (Fin 2) × Circle → W.Carrier)
        (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (x₀ : EuclideanSpace ℝ (Fin 2)), σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧
        range σ = Bs.base 0 ∩ O ∧ Continuous φ ∧ Injective φ ∧
        range φ = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' range σ ∧
        ∀ x z, C.toChain.stageMap 0 (φ (x, z)) = σ x := by
    intro y hy
    obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrange, hφ, hr, hf⟩ := C.circleChart_raw_BCF WF (hΓB y hy)
    exact ⟨σ, φ, O, 0, h0, hσ, hO, hrange, hφ.isEmbedding.continuous, hφ.isEmbedding.injective,
      hr, hf⟩
  exact Surface.exists_partition_of_halfCharts_BCF (fib₀ := Bs.fibre 0) (fib₁ := Bs.fibre 1)
    (f₁ := C.toChain.stageMap 0) (f₂ := C.toChain.stageMap 1) (T := C.toChain.heightRatio)
    (c := 4 * Δ) (X₁ := Bs.source 0) (X₂ := Bs.source 1) (Bd := frontier Kc.M₂)
    (Rc := Kc.remainder) (B₀ := Bs.base 0) (fun _ => rfl) (fun _ => rfl) isClosed_frontier
    hRcc.isCompact hRX (Bs.continuousOn_stageMap_BCF 0) hsat (fun y hy => hΓB y hy) hch hHe hdisk
    hF1'' hcover hrim Bsf d hdO hE

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
