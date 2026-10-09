import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersInteriorConfigG6C

/-!
# BCF02 G4, group G1: the edge fibres and the saturation of `M₂ ∩ X₂` (lane S-BCF02-G4)

Frozen target G4 (`exists_boundaryRelativeEdgeRestrictionV2_BCF02`, TB32:529). This file proves the
field `saturated` of `BoundaryRelativeEdgeRestrictionV2` for the ACTUAL `M₂`, without any face
function: `M₂ ∩ X₂ = X₂ ∩ f₂⁻¹(f₂(M₂ ∩ X₂))` (every whole edge disk meeting `M₂` lies in `M₂`).

* `isPreconnected_edgeFibre_BG4`: whole edge fibres are preconnected (v2b layer);
* `stageMap_two_eq_of_one_BG4`: `f₂ q = f₂ p → f₃ q = f₃ p` (`π₃ π₂ = π₃` on the actual slot);
* `edgeFaceSet_iff_of_stageMap_one_eq_BG4`: the labelled faces are saturated along `f₂`
  (edge twin of `edgeFaceSet_iff_of_E_eq_G6C`);
* `face_saturated_edge_BG4`, `M₁_saturated_edge_BG4`: `M₁ ∩ X₂` is saturated along `f₂` (ZSP03's
  connected-fibre argument with the preconnected edge disks);
* `exists_open_nbhd_image_of_chart_BG4`, `exists_open_nbhd_image_slim_BG4`: openness of `f₃`
  from ONE slim product chart (the slim chart is an `S²`-or-`T²` disjunction, so the chart-uniform
  lemma `exists_open_image_fibreProj_BCF` does not apply);
* `relInterior_piece_of_stageMap_two_eq_BG4`: `int_{M₁} S` is saturated along `f₃`;
* **`edgePiece_saturated_BG4`**: the field `saturated`;
* `horizontalFace_saturated_BG4` (consumer): P1 (`H_e` is a union of whole edge fibres), no `er`.
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

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Openness from ONE product chart**: if `f` has a product chart `φ : E × Q → Wt` over a
topological embedding `σ : E → H` at `y = f q`, then every open `U' ∋ q` has `f(X ∩ U')` containing
`V ∩ Bs` for an open `V ∋ y`. -/
theorem exists_open_nbhd_image_of_chart_BG4 {E Q Wt H : Type*} [TopologicalSpace E]
    [TopologicalSpace Q] [TopologicalSpace Wt] [TopologicalSpace H] {X : Set Wt} {f : Wt → H}
    {Bs : Set H} (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E) (hσ : IsEmbedding σ)
    (hO : IsOpen O) (hσr : range σ = Bs ∩ O) (hφc : Continuous φ)
    (hφr : range φ = X ∩ f ⁻¹' range σ) (hφf : ∀ x z, f (φ (x, z)) = σ x)
    {U' : Set Wt} (hU' : IsOpen U') {q : Wt} (hqX : q ∈ X) (hqy : f q = σ x₀) (hqU : q ∈ U') :
    ∃ V : Set H, IsOpen V ∧ f q ∈ V ∧ V ∩ Bs ⊆ f '' (X ∩ U') := by
  have hqr : q ∈ range φ := by
    rw [hφr]
    exact ⟨hqX, ⟨x₀, hqy.symm⟩⟩
  obtain ⟨⟨x₁, z₁⟩, rfl⟩ := hqr
  have hopen : IsOpen (φ ⁻¹' U') := hU'.preimage hφc
  obtain ⟨N, M, hN, hM, hx₁N, hz₁M, hsub⟩ := isOpen_prod_iff.mp hopen x₁ z₁ hqU
  obtain ⟨V₀, hV₀, hV₀N⟩ := hσ.isInducing.isOpen_iff.mp hN
  have hV₀' : V₀ ∩ range σ = σ '' N := by
    ext y
    constructor
    · rintro ⟨hy, x, rfl⟩
      exact ⟨x, by rw [← hV₀N]; exact hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by have := hV₀N ▸ hx; exact this, x, rfl⟩
  refine ⟨V₀ ∩ O, hV₀.inter hO, ⟨?_, ?_⟩, ?_⟩
  · have : σ x₁ ∈ V₀ ∩ range σ := by
      rw [hV₀']
      exact ⟨x₁, hx₁N, rfl⟩
    rw [hφf x₁ z₁]
    exact this.1
  · rw [hφf x₁ z₁]
    have : σ x₁ ∈ range σ := mem_range_self x₁
    rw [hσr] at this
    exact this.2
  · rintro y ⟨⟨hyV, hyO⟩, hyB⟩
    have hyr : y ∈ range σ := by
      rw [hσr]
      exact ⟨hyB, hyO⟩
    have hyN : y ∈ σ '' N := by
      rw [← hV₀']
      exact ⟨hyV, hyr⟩
    obtain ⟨x, hxN, rfl⟩ := hyN
    refine ⟨φ (x, z₁), ⟨?_, ?_⟩, hφf x z₁⟩
    · have : φ (x, z₁) ∈ range φ := mem_range_self _
      rw [hφr] at this
      exact this.1
    · exact hsub ⟨hxN, hz₁M⟩

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Whole edge fibres are preconnected** (`≃ₜ ClosedCell 2`, v2b layer). -/
theorem isPreconnected_edgeFibre_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 1) :
    IsPreconnected (Bs.fibre 1 y) := by
  obtain ⟨ed, -⟩ := WF.edge_fibre_OWF y hy
  have := closedCell_preconnectedSpace_BCF 2
  exact isPreconnected_of_homeomorph_BGR ed

/-- **`f₂` fibres lie in `f₃` fibres** (`π₃ π₂ = π₃` on the actual slot). -/
theorem stageMap_two_eq_of_one_BG4 {p q : W.Carrier}
    (h : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p) :
    C.toChain.stageMap 2 q = C.toChain.stageMap 2 p := by
  have hq : C.toChain.stageMap 2 q = (actualSlotsV2_BAUGD S).stageProj 2
      (C.toChain.stageMap 1 q) :=
    ((stageProj_one_two_V2_BAUGD S (C.toChain.E q)).1).symm
  have hp : C.toChain.stageMap 2 p = (actualSlotsV2_BAUGD S).stageProj 2
      (C.toChain.stageMap 1 p) :=
    ((stageProj_one_two_V2_BAUGD S (C.toChain.E p)).1).symm
  rw [hq, hp, h]

variable {C} in
/-- **The labelled faces are saturated along `f₂`** (edge twin of
`edgeFaceSet_iff_of_E_eq_G6C`). -/
theorem edgeFaceSet_iff_of_stageMap_one_eq_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} {ℓ : Kc.EdgeFaceLabel_BIFc} {p q : W.Carrier}
    (h : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p) :
    q ∈ Kc.edgeFaceSet_BIFc ℓ ↔ p ∈ Kc.edgeFaceSet_BIFc ℓ := by
  have h' : C.toChain.stageMap 1 p = C.toChain.stageMap 1 q := h.symm
  have h2 := stageMap_two_eq_of_one_BG4 C h
  rcases ℓ with k | i | ⟨j, e⟩
  · exact ⟨fun hq => C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k) hq h',
      fun hp => C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k) hp h⟩
  · exact ⟨fun hq => C.toChain.cuspFront_saturated_BIF 1 i hq h',
      fun hp => C.toChain.cuspFront_saturated_BIF 1 i hp h⟩
  · change q ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {_} ↔
      p ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {_}
    rw [Bs.slim_source_eq]
    simp only [mem_inter_iff, mem_preimage, h2]

/-- **`face_saturated` for the edge stage** (ZSP03's connected-fibre argument with the preconnected
edge disks of the v2b layer): `M₁ ∩ X₂` is a union of whole `f₂`-disks. -/
theorem face_saturated_edge_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ p ∈ Bs.source 1, ∀ q ∈ Bs.source 1,
      C.toChain.stageMap 1 q = C.toChain.stageMap 1 p →
      p ∉ interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) →
      q ∉ interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  let P : S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count → Set W.Carrier :=
    Sum.elim C.toChain.actualZeroDomain_BIFc C.toChain.cuspCore_BIF
  have hcl : ∀ j, IsClosed (P j) := by
    rintro (k | i)
    · change IsClosed (C.toChain.actualZeroDomain_BIFc k)
      rw [Zd.domain_eq k]
      exact isClosed_le (Zd.defFn_smooth k).continuous continuous_const
    · exact (hcomp i).compact_core.isClosed
  have hdisj : Pairwise (Disjoint on P) := by
    rintro (k | i) (k' | i') hne
    · exact C.actualZeroDomain_pairwise_disjoint_BGR (fun h => hne (congrArg Sum.inl h))
    · exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i' k).symm
    · exact C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k'
    · exact hspec.pairwise_disjoint i i' (fun h => hne (congrArg Sum.inr h))
  have hA : (⋃ j, P j) = (⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF :=
    Set.iUnion_sum
  have hfr : frontier ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) ⊆
      ⋃ j, frontier (P j) := hA ▸ frontier_iUnion_subset_of_finite_BGR P
  have hFA : Disjoint (⋃ j, frontier (P j))
      (interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF)) :=
    hA ▸ disjoint_iUnion_frontier_interior_BGR P hcl hdisj
  intro p hp q hq hpq hpA hqI
  have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
  have hZ := C.isPreconnected_edgeFibre_BG4 WF hy
  refine hpA (mem_interior_of_isPreconnected_BGR hZ hfr hFA ?_ ⟨hp, rfl⟩ ⟨hq, hpq⟩ hqI)
  rintro ⟨r, ⟨hrX, hr⟩, hrF⟩ x ⟨hxX, hx⟩
  have hxr : C.toChain.stageMap 1 x = C.toChain.stageMap 1 r := hx.trans hr.symm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hrF
  refine mem_iUnion.mpr ⟨j, ?_⟩
  rcases j with k | i
  · change x ∈ frontier (C.toChain.actualZeroDomain_BIFc k)
    change r ∈ frontier (C.toChain.actualZeroDomain_BIFc k) at hj
    rw [Zd.frontier_eq k] at hj ⊢
    exact C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k) hj hxr
  · change x ∈ frontier (C.toChain.cuspCore_BIF i)
    change r ∈ frontier (C.toChain.cuspCore_BIF i) at hj
    have hf : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
      (hcomp i).relative_frontier_eq
    rw [hf] at hj ⊢
    exact C.toChain.cuspFront_saturated_BIF 1 i hj hxr

/-- **`M₁ ∩ X₂` is saturated along `f₂`.** -/
theorem M₁_saturated_edge_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    C.toChain.M₁_BIFc ∩ Bs.source 1 =
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' (C.toChain.stageMap 1 '' (C.toChain.M₁_BIFc ∩
        Bs.source 1)) := by
  ext q
  constructor
  · rintro ⟨hqM, hqX⟩
    exact ⟨hqX, q, ⟨hqM, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hpM, hpX⟩, hpq⟩
    exact ⟨C.face_saturated_edge_BG4 WF Zd hrd hrd4 hrdc hprem hθ p hpX q hqX hpq.symm hpM, hqX⟩

/-- **Openness of `f₃` at a point of `X₃`** from the slim chart (`S²` or `T²` branch). -/
theorem exists_open_nbhd_image_slim_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {U' : Set W.Carrier} (hU' : IsOpen U')
    {q : W.Carrier} (hqX : q ∈ Bs.source 2) (hqU : q ∈ U') :
    ∃ V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen V ∧
      C.toChain.stageMap 2 q ∈ V ∧ V ∩ Bs.base 2 ⊆ C.toChain.stageMap 2 '' (Bs.source 2 ∩ U') := by
  have hy : C.toChain.stageMap 2 q ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hqX
  rcases WF.slim_chart _ hy with h | h
  · obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrσ, hφ, hr, hf⟩ := h
    exact exists_open_nbhd_image_of_chart_BG4 σ φ O 0 hσ hO hrσ
      (hφ.isEmbedding.continuous) hr hf hU' hqX h0.symm hqU
  · obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrσ, hφ, hr, hf⟩ := h
    exact exists_open_nbhd_image_of_chart_BG4 σ φ O 0 hσ hO hrσ
      (hφ.isEmbedding.continuous) hr hf hU' hqX h0.symm hqU

/-- **`int_{M₁} S` is saturated along `f₃`**: if `q ∈ int_{M₁} S` and `p ∈ M₁` has the same `f₃`
value, then `p ∈ int_{M₁} S`. -/
theorem relInterior_piece_of_stageMap_two_eq_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) {p q : W.Carrier}
    (hpM : p ∈ C.toChain.M₁_BIFc) (hpq : C.toChain.stageMap 2 p = C.toChain.stageMap 2 q)
    (hq : q ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece) :
    p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece := by
  obtain ⟨hqM, U, hU, hqU, hUS⟩ := mem_relInterior_iff_BCF.mp hq
  have hqS : q ∈ Kc.piece := hUS ⟨hqU, hqM⟩
  have hqX : q ∈ Bs.source 2 := hqS.1
  obtain ⟨V, hV, hqV, hVimg⟩ := C.exists_open_nbhd_image_slim_BG4 WF hU hqX hqU
  have hsat := C.M₁_saturated_of_defining_V2b_BGR WF Zd hrd hrd4 hrdc hprem hθ 2 (by decide)
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hpX : p ∈ Bs.source 2 := by
    rw [Bs.slim_source_eq]
    have : q ∈ Bs.source 2 := hqX
    rw [Bs.slim_source_eq] at this
    change C.toChain.stageMap 2 p ∈ Bs.base 2
    rw [hpq]
    exact this
  have hclaim : ∀ r ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' V, r ∈ C.toChain.M₁_BIFc →
      r ∈ Kc.piece := by
    rintro r ⟨hrX, hrV⟩ hrM
    have hrB : C.toChain.stageMap 2 r ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hrX
    obtain ⟨r', ⟨hr'X, hr'U⟩, hr'r⟩ := hVimg ⟨hrV, hrB⟩
    have hr'M : r' ∈ C.toChain.M₁_BIFc ∩ Bs.source 2 := by
      rw [hsat]
      exact ⟨hr'X, r, ⟨hrM, hrX⟩, hr'r.symm⟩
    have hr'S : r' ∈ Kc.piece := hUS ⟨hr'U, hr'M.1⟩
    exact ⟨hrX, by
      change C.toChain.stageMap 2 r ∈ Kc.K₃ ∩ Bs.slimBaseDomain_BIFc
      rw [← hr'r]
      exact hr'S.2⟩
  have hopen : IsOpen (Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' V) :=
    (Bs.isOpen_source 2 (by decide)).inter (hV.preimage hf₃)
  refine mem_relInterior_iff_BCF.mpr ⟨hpM, _, hopen, ⟨hpX, by rw [mem_preimage, hpq]; exact hqV⟩,
    fun r hr => hclaim r hr.1 hr.2⟩

/-- **The field `saturated` of `BoundaryRelativeEdgeRestrictionV2`, for the ACTUAL `M₂`**:
`M₂ ∩ X₂ = X₂ ∩ f₂⁻¹(f₂(M₂ ∩ X₂))`. -/
theorem edgePiece_saturated_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.M₂ ∩ Bs.source 1 =
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' (C.toChain.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1)) := by
  ext q
  constructor
  · rintro ⟨hqM, hqX⟩
    exact ⟨hqX, q, ⟨hqM, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hpM, hpX⟩, hpq⟩
    have hq1 : q ∈ C.toChain.M₁_BIFc :=
      C.face_saturated_edge_BG4 WF Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc hprem hθ p hpX q hqX
        hpq.symm hpM.1
    refine ⟨⟨hq1, fun hrel => hpM.2 ?_⟩, hqX⟩
    exact C.relInterior_piece_of_stageMap_two_eq_BG4 WF Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
      hprem hθ Kc hpM.1 (C.stageMap_two_eq_of_one_BG4 hpq.symm).symm hrel

/-- **Consumer: P1 without `er`** (`horizontalFace_saturated_BCF` without the restriction): the
horizontal face `H_e = ∂M₂ ∩ X₂` is a union of whole edge fibres, from the saturation of `M₂ ∩ X₂`
and the saturation of the labelled faces along `f₂`. -/
theorem horizontalFace_saturated_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    ∀ p ∈ Kc.horizontalFace, ∀ q ∈ Bs.fibre 1 (C.toChain.stageMap 1 p),
      q ∈ Kc.horizontalFace := by
  intro p hp q hq
  have hM₂c : IsClosed Kc.M₂ := isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF Kc.piece
  have hpM : p ∈ Kc.M₂ := hM₂c.frontier_subset hp.1
  have hsat := C.edgePiece_saturated_BG4 WF Z hrd hrd4 hrdc hprem hθ Kc
  have hqM : q ∈ Kc.M₂ ∩ Bs.source 1 := by
    rw [hsat]
    exact ⟨hq.1, p, ⟨hpM, hp.2⟩, hq.2.symm⟩
  obtain ⟨ℓ, hℓ⟩ := C.exists_label_of_mem_frontier_M₂_G6C WF Z hrd hrd4 hrdc hprem hθ Kc hp.1 hpM
  have hqℓ : q ∈ Kc.edgeFaceSet_BIFc ℓ :=
    (edgeFaceSet_iff_of_stageMap_one_eq_BG4 (C := C) (Kc := Kc) (ℓ := ℓ) hq.2).mpr hℓ
  exact ⟨C.edgeFaceSet_inter_M₂_subset_frontier_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ hqM.1 hqℓ,
    hqM.2⟩


end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
