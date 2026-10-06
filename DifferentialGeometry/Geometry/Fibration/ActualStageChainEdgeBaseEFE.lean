import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeFibreDiskEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroDescentEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactApplicationsEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBasesEuclid
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice
import DifferentialGeometry.Topology.Manifold.LinearChartAtlasEFE

/-!
# FDC02 / EDP05 binding to the abstract edge base `B₂ ⊆ W₂` (E1 inputs), group G2a

Lane S-EDP-FDC2, group G2 (first part: the rows' `EdgeBundle` data over the ABSTRACT base; draft 74
D74-11, packages E0 / E1). On a chain `Ĉ : Gaf02ChainE L …` with the smooth stage bases
`A : SmoothStageBasesOn74 Ĉ.toChain` (D74-2; `A.edgeChartedSpace1`, model `𝓡 1`):

* `SmoothStageBasesOn74.edge_contMDiff_of_val_EFE` (kernel K0 for `W₂`);
* defs `edgeBaseOpens_EFE : Opens W₂` (`B₂ = W₂ ∩ edgeRatio`), `edgeSource_EFE : Opens X` (the open
  ambient parent `U₂ ∩ (π₂E)⁻¹(edgeRatio)`), `edgeProj_EFE` (`p ↦ π₂E p`), `edgeHeight_EFE`
  (`T = A/s`); `edgeSource_mem_EFE`; `edgeProj_contMDiff_EFE` (`proj` smooth for the
  abstract structure);
* `mem_edgeSource_EFE`: (ELoc) for `B₂` — `π₂E x ∈ edgeRatio`, `T x ≤ 4Δ` put `x` in the source;
* `edgeProj_disk_EFE`: `EdgeBundle.fibre_disk` over EVERY point of `B₂` (EDP23's
  `edgeBase_fibre_disk_EDP23`): the whole fibre `{x ∈ source | proj x = c, T x ≤ 4Δ}` is a smooth
  embedded disk;
* `edge_descent_wrap_EFE`: wrapper turning a defining function `h` on an open set of the block
  space (`y ∈ M₂ ↔ h(π₂E y) ≥ 0`, ambient `F = h ∘ π₂E` with `dF ≠ 0` at a source point) into
  exactly E1's `hdesc` data over a neighbourhood in the abstract base;
* `isClosed_cutM1_EFE`, `frontier_cutM1_subset_faces_EFE`: `∂M₁ ⊆ ⋃_k ∂Z_k`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into `W₂` is smooth for the rows' structure (model `𝓡 1`) as soon as its composite with
the inclusion `W₂ → BlockSpace` is. -/
theorem edge_contMDiff_of_val_EFE (A : SmoothStageBasesOn74 C) (F : M → C.finalBase_BAS 1)
    (hF : ContMDiff I
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (fun z => (F z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) :
    let _ := A.edgeChartedSpace1
    ContMDiff I (𝓡 1) ∞ F :=
  contMDiff_of_val_EFE _ _ _ _ _ _ _ _ _ _ F hF

end SmoothStageBasesOn74

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **The rows' edge base `B₂` as an open subset of the abstract base `W₂`**
(`B₂ = W₂ ∩ edgeRatio`, relatively open). -/
def edgeBaseOpens_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    TopologicalSpace.Opens (Ĉ.toChain.finalBase_BAS 1) :=
  ⟨Subtype.val ⁻¹' edgeRatio_R74 L, (isOpen_edgeRatio_R74 L).preimage continuous_subtype_val⟩

/-- **The open source of the edge bundle**: the open ambient parent `U₂` (threshold-5 domain) of
the edge stage intersected with the open ratio condition on `π₂E`. -/
def edgeSource_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) : TopologicalSpace.Opens X :=
  ⟨gafStageDomain5_BAS L.toLocalChartPackets 1 ∩
      (fun p => (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E p)) ⁻¹'
        edgeRatio_R74 L,
    (isOpen_gafStageDomain5_R74 L.toLocalChartPackets 1).inter
      ((isOpen_edgeRatio_R74 L).preimage
        ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection.continuous.comp
          Ĉ.toChain.stage_smooth.2.2.continuous))⟩

/-- A point of the edge source has `π₂E` in `W₂ ∩` the ratio set. -/
theorem edgeSource_mem_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) {p : X}
    (hp : p ∈ Ĉ.edgeSource_EFE) :
    (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E p) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
      (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E p) ∈
        edgeRatio_R74 L := by
  obtain ⟨⟨k, hk, hη, ht⟩, hR⟩ := hp
  exact ⟨(Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hk hη ht).1.1, hR⟩

/-- **The projection of the edge bundle**: `p ↦ π₂E p ∈ B₂`. -/
def edgeProj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    Ĉ.edgeSource_EFE → Ĉ.edgeBaseOpens_EFE := fun x =>
  ⟨⟨(gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x.1),
      (Ĉ.edgeSource_mem_EFE x.2).1⟩, (Ĉ.edgeSource_mem_EFE x.2).2⟩

/-- The height `T = A/s` on the edge source. -/
def edgeHeight_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) : Ĉ.edgeSource_EFE → ℝ := fun x =>
  EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero (Ĉ.toChain.E x.1)) /
    Ĉ.toChain.scale x.1

/-- **The projection of the edge bundle is smooth** for the rows' structure of `W₂`. -/
theorem edgeProj_contMDiff_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) :
    let _ := A.edgeChartedSpace1
    ContMDiff 𝓘(ℝ, E3) (𝓡 1) ∞ Ĉ.edgeProj_EFE := by
  intro _
  have hFval : ContMDiff 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) ∞
      (fun z : Ĉ.edgeSource_EFE => (((Ĉ.edgeProj_EFE z : Ĉ.edgeBaseOpens_EFE) :
        Ĉ.toChain.finalBase_BAS 1) :
        BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))) :=
    (A.proj.final_smooth 1).comp (contMDiff_subtype_val (I := 𝓘(ℝ, E3)))
  have hF : ContMDiff 𝓘(ℝ, E3) (𝓡 1) ∞ (fun z : Ĉ.edgeSource_EFE =>
      ((Ĉ.edgeProj_EFE z : Ĉ.edgeBaseOpens_EFE) : Ĉ.toChain.finalBase_BAS 1)) :=
    A.edge_contMDiff_of_val_EFE _ hFval
  exact (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff Ĉ.edgeBaseOpens_EFE
    Ĉ.edgeProj_EFE).mp hF

/-- **(ELoc) for the base `B₂`**: a point `x` with `π₂E x` in the ratio set and `T x ≤ 4Δ` lies in
the open edge source (the whole disk over a point of `B₂` lies in the source). -/
theorem mem_edgeSource_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ) {x : X}
    (hR : (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
      edgeRatio_R74 L)
    (hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
      (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ) : x ∈ Ĉ.edgeSource_EFE := by
  obtain ⟨k, hv, hu⟩ := hR
  have hV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
    Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hT⟩
  obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu hV
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨⟨k, hball, by rw [abs_lt] at hη ⊢; constructor <;> linarith [hη.1, hη.2], ?_⟩,
    ⟨k, hv, hu⟩⟩
  change L.edge.smoothing x / ρ x < 5 * Δ
  linarith

/-- **EDP04 for the bundle (`EdgeBundle.fibre_disk` over `Base := B₂`)**: over every point `c` of
`B₂` the whole fibre `{x ∈ source | proj x = c, T x ≤ 4Δ}` is the range of a continuous (indeed
smooth embedded) disk. -/
theorem edgeProj_disk_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (cc : Ĉ.edgeBaseOpens_EFE) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = Subtype.val '' {x : Ĉ.edgeSource_EFE |
        Ĉ.edgeProj_EFE x = cc ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ} := by
  have hw : (cc : Ĉ.toChain.finalBase_BAS 1).1 ∈ Ĉ.edgeBase_EDP23 := ⟨cc.1.2, cc.2⟩
  obtain ⟨φ, hφ, hr, -⟩ := Ĉ.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
    hβc1 hw
  refine ⟨φ, hφ, hr.trans ?_⟩
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxs : x ∈ Ĉ.edgeSource_EFE := Ĉ.mem_edgeSource_EFE hΔ2 (hx1 ▸ cc.2) hx2
    exact ⟨⟨x, hxs⟩, ⟨Subtype.ext (Subtype.ext hx1), hx2⟩, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨congrArg (fun v : Ĉ.edgeBaseOpens_EFE => ((v : Ĉ.toChain.finalBase_BAS 1) :
      BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))) hy1, hy2⟩

/-- **Wrapper for the descended defining function**: an open `N` of the block space and a function
`h`, smooth on `N`, with the descended identity `y ∈ M₂ ↔ h(π₂E y) ≥ 0` for `π₂E y ∈ N`, together
with an ambient `F = h ∘ π₂E` of nonzero differential at a source point `x`, give EXACTLY the
local data of E1's `hdesc` over a neighbourhood of `proj x` in the abstract base `B₂`. -/
theorem edge_descent_wrap_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (M₂ : Set X) (Lv : ℝ) (x : Ĉ.edgeSource_EFE)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    (hxN : (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x.1) ∈ N)
    {h : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hh : ContDiffOn ℝ ∞ h N)
    (hdef : ∀ y : X, (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E y) ∈ N →
      (y ∈ M₂ ↔ 0 ≤ h ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
        (Ĉ.toChain.E y))))
    {F : X → ℝ} (hF : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x.1)
    (hFne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x.1 ≠ 0)
    (hFeq : ∀ z : X, F z = h ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
      (Ĉ.toChain.E z))) :
    let _ := A.edgeChartedSpace1
    ∃ U : TopologicalSpace.Opens Ĉ.edgeBaseOpens_EFE, Ĉ.edgeProj_EFE x ∈ U ∧
      ∃ b : Ĉ.edgeBaseOpens_EFE → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ z : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE z ∈ U → Ĉ.edgeHeight_EFE z ≤ Lv →
          ((z : X) ∈ M₂ ↔ 0 ≤ b (Ĉ.edgeProj_EFE z))) ∧
        ∃ x' : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE x' = Ĉ.edgeProj_EFE x ∧ ∃ F' : X → ℝ,
          MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F' x'.1 ∧ mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F' x'.1 ≠ 0 ∧
          (fun z : Ĉ.edgeSource_EFE => F' z) =ᶠ[nhds x'] b ∘ Ĉ.edgeProj_EFE := by
  intro _
  let valB : Ĉ.edgeBaseOpens_EFE → BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) :=
    fun c => ((c : Ĉ.toChain.finalBase_BAS 1) :
      BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
  have hval : ContMDiff (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      ∞ valB :=
    (A.edge_isManifold1.2.1).comp (contMDiff_subtype_val (I := 𝓡 1))
  have hUo : IsOpen (valB ⁻¹' N) := hN.preimage hval.continuous
  refine ⟨⟨valB ⁻¹' N, hUo⟩, hxN, fun c => h (valB c),
    (hh.contMDiffOn.comp hval.contMDiffOn (fun c hc => hc)).mono (fun c hc => hc), ?_, x, rfl, F,
    hF, hFne, ?_⟩
  · intro z hz _
    exact hdef z.1 hz
  · exact Filter.Eventually.of_forall fun z => hFeq z.1

/-- `M₁ = (int Z)ᶜ` is closed. -/
theorem isClosed_cutM1_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) : IsClosed Ĉ.cutM1_R74 :=
  isOpen_interior.isClosed_compl

/-- **`∂M₁ ⊆ ⋃_k ∂Z_k`** (`M₁ = M ∖ int Z`, `Z = ⋃_k Z_k` closed): a frontier point of `M₁` lies
on a zero face. -/
theorem frontier_cutM1_subset_faces_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    frontier Ĉ.cutM1_R74 ⊆ ⋃ k : L.zero.finite_centres.toFinset,
      frontier (zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E) := by
  have hclk : ∀ k : L.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E) := fun k =>
    (Ĉ.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨-, hfU⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : L.zero.finite_centres.toFinset => zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E)
    hclk (fun k k' hkk => Ĉ.zsp02_disjoint_ZSP35 hεr hkk)
  have hZc : IsClosed Ĉ.zeroUnion_ZSP35 := isClosed_iUnion_of_finite hclk
  intro x hx
  have hx' : x ∈ frontier (interior Ĉ.zeroUnion_ZSP35) := by
    rw [← frontier_compl]
    exact hx
  have hxZ : x ∈ frontier Ĉ.zeroUnion_ZSP35 := by
    refine ⟨?_, ?_⟩
    · exact subset_closure ((closure_minimal interior_subset hZc) hx'.1)
    · have h2 := hx'.2
      rw [interior_interior] at h2
      exact h2
  rw [show Ĉ.zeroUnion_ZSP35 = ⋃ k : L.zero.finite_centres.toFinset,
    zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E from rfl, hfU] at hxZ
  exact hxZ

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
