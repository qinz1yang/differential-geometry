import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1Applications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovedRegionBufferBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCorollaries

/-!
# BCG07: the whole row on the enhanced boundary chain with an A4 output (S-BCG-ROWS3, G34)

BCG07 (blueprint `thm:fibration-actual-retained-internal-torus-faces`, B:9471–9580) is the
conjunction of the frozen targets F1–F5 of `TargetsBoundary-v3.1`, here on the enhanced chain `C`
(A2 v3: `exists_boundaryGaf02ChainE_v3_BAUGD`) and an A4 output `(Bs, WF)` (v2 bases and the
whole-fibre layer v2b; `Bs` and `WF` are explicit data). The pieces are the delivered theorems of
O-F1 (F1), BIFACE (F2, F4a), S-BCG-ROWS (F4b, F4c, F4d, F5, F3).

* **`BoundaryGaf02ChainE.bcg07_row_BGR`**: F1 ∧ F2 ∧ F3 ∧ F4a ∧ F4b ∧ F4c ∧ F4d ∧ F5 in this order;
* **`BoundaryGaf02ChainE.bcg07_row_extras_BGR`**: the consequences used by BCF01 (the slim base
  domain `D₃`: `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, its relative frontier, F5z, the one base point of a cusp
  front, the finiteness of `f₃(∂M₁ ∩ X₃)`, `∂M₁ ⊆ {D ≥ 35}` (no external boundary component
  remains), and the relative closedness of the circle and slim base domains).

Deviations from the frozen v3.1 text: `ZC.M₁` of the v1 interface `BoundaryInitialCoresSpec` is
`C.toChain.M₁_BIFc` (the removed region of the ACTUAL zero domains and the cusp cores of the SAME
chain); F3 is `Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs)` (the v2 form of the frozen
`Nonempty (BoundaryInitialCoresSpec C)`). Numerical premises (parameters only, discharged at the
register layer): F1's six (`3βc ≤ β 2 < 1`, `0 ≤ γ ≤ 3/4`, `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`),
F3's `εr < 1/2` and `e ≤ 1/1000`, and E4's `r_∂` block with `θ < 1/100`.
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

/-- **The base image of a closed set under a proper restriction is relatively closed**
(generic): for `f` continuous on `U`, proper over `Bs = f(U)` and `M` closed, the set
`f(M ∩ U)` is closed in the subspace `Bs`. -/
theorem isClosed_relImage_of_proper_BGR {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {f : X → Y} {U : Set X} {Bs : Set Y} (hcont : ContinuousOn f U) (himg : f '' U = Bs)
    (hproper : ∀ Kc ⊆ Bs, IsCompact Kc → IsCompact (U ∩ f ⁻¹' Kc)) {M : Set X}
    (hM : IsClosed M) : IsClosed (Subtype.val ⁻¹' (f '' (M ∩ U)) : Set Bs) := by
  have hmaps : ∀ p ∈ U, f p ∈ Bs := fun p hp => himg ▸ mem_image_of_mem f hp
  let g : U → Bs := fun p => ⟨f p, hmaps p.1 p.2⟩
  have hgc : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hgc, fun K hK => ?_⟩
    have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
    have hc := hproper _ (Subtype.coe_image_subset _ _) hK'
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hc using 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.2, g q', hq', rfl⟩
    · rintro ⟨hqU, z, hzK, hz⟩
      refine ⟨⟨q, hqU⟩, ?_, rfl⟩
      have : g ⟨q, hqU⟩ = z := Subtype.ext hz.symm
      change g ⟨q, hqU⟩ ∈ K
      rw [this]
      exact hzK
  have hclosed : IsClosed (g '' {x : U | x.1 ∈ M}) :=
    hgp.isClosedMap _ (hM.preimage continuous_subtype_val)
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨q, ⟨hqM, hqU⟩, hq⟩
    exact ⟨⟨q, hqU⟩, hqM, Subtype.ext hq⟩
  · rintro ⟨x, hxM, rfl⟩
    exact ⟨x.1, ⟨hxM, x.2⟩, rfl⟩

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCG07, the whole row** (F1 ∧ F2 ∧ F3 ∧ F4a ∧ F4b ∧ F4c ∧ F4d ∧ F5) on the enhanced chain
`C` and an A4 output `(Bs, WF)`. -/
theorem bcg07_row_BGR (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    -- F1: the rim of every whole edge disk is ONE whole circle fibre
    (∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      p ∈ Bs.source 0 ∧
        Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
          Bs.fibre 0 (C.toChain.stageMap 0 p)) ∧
    -- F2 (Sat): cusp fronts are saturated for every stage projection
    (∀ (st : Fin 3) (i : Fin S.packet.cusp.count) (p q : W.Carrier),
      p ∈ C.toChain.cuspFront_BIF i → C.toChain.stageMap st q = C.toChain.stageMap st p →
        q ∈ C.toChain.cuspFront_BIF i) ∧
    -- F3: the actual zero domains of `C.E`
    Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs) ∧
    -- F4a: `M₁` is compact
    IsCompact C.toChain.M₁_BIFc ∧
    -- F4b: `M₁ ⊆ {D ≥ 35}`
    C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
    -- F4c: the faces of `M₁`
    frontier C.toChain.M₁_BIFc =
      (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i ∧
    -- F4d: saturation of `M₁` on the circle and slim sources
    (∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
      Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
        Bs.source st))) ∧
    -- F5: a cusp front meeting `X₃` is ONE whole slim fibre
    (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y) :=
  ⟨C.wholeDiskBoundary_eq_wholeCircleFiber_OF1 h3βc hβ2 hγ hγ34 hc hC WF,
    fun st i _ _ hp hpq => C.toChain.cuspFront_saturated_BIF st i hp hpq,
    C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ,
    C.toChain.isClosed_M₁_BCF.isCompact,
    C.toChain.M₁_subset_buffer_BGR (⋃ k, C.toChain.actualZeroDomain_BIFc k),
    C.frontier_M₁_unconditional_BGR hεr hrd hrd4 hrdc hprem hθ,
    C.M₁_saturated_unconditional_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ,
    C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ⟩

/-- **BCG07, the complement used by BCF01** on the same data: the slim base domain
`D₃ = f₃(M₁ ∩ X₃)` satisfies `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, its relative frontier lies in
`f₃(∂M₁ ∩ X₃)`, a zero face meeting `X₃` is ONE whole slim fibre (F5z), a cusp front meeting `X₃`
has ONE base point, `f₃(∂M₁ ∩ X₃)` is finite, `∂M₁ ⊆ {D ≥ 35}`, and the base images
`D_j = f_j(M₁ ∩ X_j)` (`j ≠ 1`) are relatively closed in `B_j`. -/
theorem bcg07_row_extras_BGR (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
        C.toChain.M₁_BIFc ∩ Bs.source 2 ∧
      Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
        C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) ∧
      (∀ k : S.ZeroIdx_BAUGC, (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty →
        ∃ y ∈ Bs.base 2, C.toChain.actualZeroFace_BIFc k = Bs.fibre 2 y) ∧
      (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
        ∃ y ∈ Bs.base 2, C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2) = {y}) ∧
      (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2)).Finite ∧
      frontier C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
      (∀ st : Fin 3, st ≠ 1 →
        IsClosed (Subtype.val ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩ Bs.source st)) :
          Set (Bs.base st))) :=
  ⟨C.slimSource_inter_preimage_unconditional_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ,
    C.relFrontier_slimBaseDomain_of_chain_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ,
    C.zeroFace_eq_slimFibre_direct_V2b_BGR WF hεr,
    fun i hne => C.cuspFront_image_eq_singleton_V2b_BGR WF hrd hrd4 hrdc hprem hθ i hne,
    C.frontier_M₁_image_finite_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ,
    C.toChain.isClosed_M₁_BCF.frontier_subset.trans
      (C.toChain.M₁_subset_buffer_BGR (⋃ k, C.toChain.actualZeroDomain_BIFc k)),
    fun st _ => isClosed_relImage_of_proper_BGR (Bs.continuousOn_stageMap_BCF st)
      (Bs.image_eq st) (Bs.proper st) C.toChain.isClosed_M₁_BCF⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
