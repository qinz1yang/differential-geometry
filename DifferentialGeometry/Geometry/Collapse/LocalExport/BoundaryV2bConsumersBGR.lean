import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowOfChainApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontSlimFibreApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimBaseDomainBGR

/-!
# The row consumers on the whole-fibre layer v2b (S-BCG-ROWS2 G31)

Lead decision 2026-10-05 20:4x (relayed by O-WF): the frozen
`BoundaryWholeFiberSpecV2.source_buffered` (sources in `{D > 10}`) is unprovable; the named revision
for text v3.2 is v2b (`BoundaryWholeFiberSpecV2b`, sources in `{D > 5}`,
LE/BoundaryInterfaceFibresV2b.lean, lane O-WF). The production A4 gives v2b. Every consumer of this
lane that takes the whole-fibre layer uses it only through its charts and the derived fibre types,
so it is re-stated here on v2b (same proofs, the exits `circle_fibre_OWF`, `slim_fibre_OWF`,
`edge_fibre_OWF`):

* `isPreconnected_*_V2b_BGR` (circle / slim whole fibres), **`face_saturated_actual_V2b_BGR`**,
  `M₁_saturated_of_defining_V2b_BGR`, **`M₁_saturated_unconditional_V2b_BGR`** (BCG07 F4d);
* `slim_isolation_V2b_BGR`, **`cuspFront_eq_slimFibre_direct_V2b_BGR`** (F5),
  `cuspFront_image_eq_singleton_V2b_BGR`;
* **`relFrontier_slimBaseDomain_of_chain_V2b_BGR`** (D₃ regularity input of BCF01 G1a);
* **`fc43_row_V2b_BGR`**, **`fc43_row_of_chain_V2b_BGR`** (FC43 on a non-empty chain with an A4
  output).
Not ported (take Z / `face_param`): the F5z chain (`zeroFace_eq_slimFibre_BGR`, G19 / G23).
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

section Fibres

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **Whole slim fibres are preconnected** (`≃ₜ S²` or `≃ₜ T²`). -/
theorem isPreconnected_slimFibre_V2b_BGR (WF : BoundaryWholeFiberSpecV2b C Bs) {y : _}
    (hy : y ∈ Bs.base 2) : IsPreconnected (Bs.fibre 2 y) := by
  rw [isPreconnected_iff_preconnectedSpace]
  rcases WF.slim_fibre_OWF y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : PreconnectedSpace (Metric.sphere (0 : E3) 1) := by
      rw [← isPreconnected_iff_preconnectedSpace]
      refine (isConnected_sphere ?_ 0 zero_le_one).isPreconnected
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
      exact_mod_cast (by norm_num : 1 < 3)
    exact e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous
  · exact e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous

/-- **Whole circle fibres are preconnected** (`≃ₜ S¹`). -/
theorem isPreconnected_circleFibre_V2b_BGR (WF : BoundaryWholeFiberSpecV2b C Bs) {y : _}
    (hy : y ∈ Bs.base 0) : IsPreconnected (Bs.fibre 0 y) := by
  obtain ⟨e⟩ := WF.circle_fibre_OWF y hy
  exact isPreconnected_of_homeomorph_BGR e

/-- **The whole circle and slim fibres of the v2 bases are preconnected.** -/
theorem isPreconnected_fibre_V2b_BGR (WF : BoundaryWholeFiberSpecV2b C Bs) {st : Fin 3}
    (hst : st ≠ 1) {y : _} (hy : y ∈ Bs.base st) : IsPreconnected (Bs.fibre st y) := by
  fin_cases st
  · exact isPreconnected_circleFibre_V2b_BGR WF hy
  · exact absurd rfl hst
  · exact isPreconnected_slimFibre_V2b_BGR WF hy

end Fibres

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

/-- **`face_saturated`** (BCG07 F4d, the field of `BoundaryActualZeroDomains_BIFc`, verbatim): a
point of the saturated frontier carrier `⋃ faces ∪ ⋃ fronts` has its whole `f_st`-fibre in the
carrier (`π_j` retains the whole zero and boundary blocks), the carrier is disjoint from the
interior of `⋃ Z_k ∪ C_∂`, and the circle / slim fibres are connected (ZSP03). Premises: the
analytic half `Zd` of the actual zero domains (ZSP02, G22) and E4's `r_∂` block with `θ < 1/100`. -/
theorem face_saturated_actual_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
      C.toChain.stageMap st q = C.toChain.stageMap st p →
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
  intro st hst p hp q hq hpq hpA hqI
  have hy : C.toChain.stageMap st p ∈ Bs.base st := Bs.image_eq st ▸ mem_image_of_mem _ hp
  have hZ := isPreconnected_fibre_V2b_BGR WF hst hy
  refine hpA (mem_interior_of_isPreconnected_BGR hZ hfr hFA ?_ ⟨hp, rfl⟩ ⟨hq, hpq⟩ hqI)
  rintro ⟨r, ⟨hrX, hr⟩, hrF⟩ x ⟨hxX, hx⟩
  have hxr : C.toChain.stageMap st x = C.toChain.stageMap st r := hx.trans hr.symm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hrF
  refine mem_iUnion.mpr ⟨j, ?_⟩
  rcases j with k | i
  · change x ∈ frontier (C.toChain.actualZeroDomain_BIFc k)
    change r ∈ frontier (C.toChain.actualZeroDomain_BIFc k) at hj
    rw [Zd.frontier_eq k] at hj ⊢
    exact C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S st k) hj hxr
  · change x ∈ frontier (C.toChain.cuspCore_BIF i)
    change r ∈ frontier (C.toChain.cuspCore_BIF i) at hj
    have hf : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
      (hcomp i).relative_frontier_eq
    rw [hf] at hj ⊢
    exact C.toChain.cuspFront_saturated_BIF st i hj hxr

/-- **F4d `M₁_saturated`** (frozen v3.1 statement verbatim) from the analytic half only: for
`st ≠ 1`, `M₁ ∩ X_st` is the whole `f_st`-preimage of its image in `X_st`. -/
theorem M₁_saturated_of_defining_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
      Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
        Bs.source st)) := by
  intro st hst
  ext q
  constructor
  · rintro ⟨hqM, hqX⟩
    exact ⟨hqX, q, ⟨hqM, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hpM, hpX⟩, hpq⟩
    exact ⟨C.face_saturated_actual_V2b_BGR WF Zd hrd hrd4 hrdc hprem hθ st hst p hpX q hqX hpq.symm
      hpM, hqX⟩

/-- **F4d on the enhanced chain, unconditional** (premises: `εr < 1/2` of ZSP02, E4's `r_∂` block,
`θ < 1/100`; inputs: the v2 bases and the whole-fibre layer). -/
theorem M₁_saturated_unconditional_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
      Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
        Bs.source st)) := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact C.M₁_saturated_of_defining_V2b_BGR WF Zd hrd hrd4 hrdc hprem hθ

/-- **`X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`** (the slim base domain `D₃ = f₃(M₁ ∩ X₃)`), unconditional. -/
theorem slimSource_inter_preimage_unconditional_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
      C.toChain.M₁_BIFc ∩ Bs.source 2 :=
  (C.M₁_saturated_unconditional_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ 2 (by decide)).symm

/-- slim isolation, chart cases combined. -/
theorem slim_isolation_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {Fd : W.Carrier → ℝ}
    (hFd : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fd) {cc : ℝ} {p : W.Carrier} (hpX : p ∈ Bs.source 2)
    (hfib : ∀ q ∈ Bs.source 2, C.toChain.stageMap 2 q = C.toChain.stageMap 2 p → Fd q = cc)
    (hsat : ∀ q ∈ Bs.source 2, ∀ q' ∈ Bs.source 2,
      C.toChain.stageMap 2 q = C.toChain.stageMap 2 q' → Fd q = cc → Fd q' = cc)
    (hreg : mfderiv W.model 𝓘(ℝ, ℝ) Fd p ≠ 0) :
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
      O ∩ C.toChain.stageMap 2 '' ({q | Fd q = cc} ∩ Bs.source 2) = {C.toChain.stageMap 2 p} := by
  have hw : C.toChain.stageMap 2 p ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hpX
  have hB : C.toChain.stageMap 2 '' Bs.source 2 ⊆ Bs.base 2 := (Bs.image_eq 2).subset
  rcases WF.slim_chart _ hw with h | h
  · exact exists_isOpen_inter_image_zero_eq_singleton_BGR h hB
      (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]) hFd hfib hsat hpX rfl hreg
  · exact exists_isOpen_inter_image_zero_eq_singleton_BGR h hB
      (by rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin]) hFd hfib
      hsat hpX rfl hreg

/-- **F5 without `Z`: a cusp front meeting `X₃` is ONE whole slim fibre** (frozen v3.1 F5 with the
premises of E4; the zero domains of `C.E` do not occur). -/
theorem cuspFront_eq_slimFibre_direct_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y := by
  rintro i ⟨p, hp, hpX⟩
  obtain ⟨hsm, hfeq, hreg⟩ := C.cuspFront_level_data_BGR hrd hrd4 hrdc hprem hθ i
  have hSX : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
      (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2)) := by
    ext q
    constructor
    · rintro ⟨hq, hqX⟩
      exact ⟨hqX, q, ⟨hq, hqX⟩, rfl⟩
    · rintro ⟨hqX, p', ⟨hp', hpX'⟩, hpq⟩
      exact ⟨C.toChain.cuspFront_saturated_BIF 2 i hp' hpq.symm, hqX⟩
  have hfibsub := C.cuspFront_fibre_subset_direct_BGR (Bs := Bs) i hp
  obtain ⟨O, hO, hOD⟩ := C.slim_isolation_V2b_BGR WF hsm hpX (cc := 40)
    (fun q hq hqp => by
      have h : q ∈ C.toChain.cuspFront_BIF i := hfibsub ⟨hq, hqp⟩
      rw [hfeq] at h
      exact h)
    (fun q hq q' hq' hqq' hq0 => by
      have hqf : q ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 :=
        ⟨by rw [hfeq]; exact hq0, hq⟩
      have h : q' ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 := by
        rw [hSX]
        exact ⟨hq', q, hqf, hqq'⟩
      have h' : q' ∈ C.toChain.cuspFront_BIF i := h.1
      rw [hfeq] at h'
      exact h')
    (hreg p hp)
  rw [← hfeq] at hOD
  refine ⟨C.toChain.stageMap 2 p, Bs.image_eq 2 ▸ mem_image_of_mem _ hpX, ?_⟩
  exact DifferentialGeometry.Topology.eq_fiber_of_isPreconnected_of_isolated
    (C.toChain.stageMap 2) (Bs.source 2) (C.toChain.cuspFront_BIF i)
    (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2))
    (Bs.isOpen_source 2 (by decide)) (Bs.continuousOn_stageMap_BCF 2)
    (C.isPreconnected_cuspFront_BGR hrd hrd4 hrdc hprem hθ i) hSX ⟨O, hO, hOD⟩
    (Bs.proper 2 {C.toChain.stageMap 2 p}
      (singleton_subset_iff.mpr (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX)) isCompact_singleton)
    ⟨p, hpX, rfl⟩

section

variable {Bs : BoundaryGaf02BasesV2 C.toChain}

/-- **A cusp front meeting `X₃` has ONE base point**: `f₃(H_b ∩ X₃) = {y}` with `y ∈ B₃` (the cusp
half of the finiteness of `f₃(∂M₁ ∩ X₃)`, BCF01 G1a input (a)). -/
theorem cuspFront_image_eq_singleton_V2b_BGR (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count)
    (hne : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty) :
    ∃ y ∈ Bs.base 2,
      C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2) = {y} := by
  obtain ⟨y, hy, hfib⟩ := C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ i hne
  refine ⟨y, hy, ?_⟩
  obtain ⟨p, hp, hpX⟩ := hne
  have hpy : C.toChain.stageMap 2 p = y := by
    have hp' : p ∈ Bs.fibre 2 y := hfib ▸ hp
    exact hp'.2
  ext z
  constructor
  · rintro ⟨q, ⟨hq, hqX⟩, rfl⟩
    have hq' : q ∈ Bs.fibre 2 y := hfib ▸ hq
    exact hq'.2
  · intro hz
    rw [mem_singleton_iff] at hz
    exact ⟨p, ⟨hp, hpX⟩, hpy.trans hz.symm⟩

end

/-- **`D₃ ∖ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)` on the enhanced chain** (properness of `f₃|X₃` and the
saturation of `M₁`, `face_saturated_actual_V2b_BGR`; premises `hεr : εr < 1/2` of ZSP02 and
E4's). -/
theorem relFrontier_slimBaseDomain_of_chain_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
      C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact relFrontier_image_subset_BCF (Bs.continuousOn_stageMap_BCF 2) (Bs.image_eq 2)
    (Bs.proper 2) C.toChain.isClosed_M₁_BCF fun p hp q hq hpq hpM =>
    C.face_saturated_actual_V2b_BGR WF Zd hrd hrd4 hrdc hprem hθ 2 (by decide) p hp q hq hpq hpM

/-- **FC43, assembly form** on the enhanced chain `C` (A2's output) and an A4 output `(Bs, WF)`:
(FC43 block) the E-free collar block of the export packet for every boundary component;
(BCG03) the A3 exits of `C` (smoothness of every stage, value errors `< c_k ρ`, derivative errors
`< c_k`) and the whole circle / slim (`S²` or `T²`) / edge-disk fibres derived from `WF`;
(BCG04) E1 (isolation, whole-block exit, segment) and E2 (derivative half on the tight band);
(BCG06) the STRONG component exit and the two-branch geometric output. Premises: the `r_∂` block
and `θ < 1/100`. -/
theorem fc43_row_V2b_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (∀ i : Fin S.packet.cusp.count,
      ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (S.packet.block i) ∧
        (∀ x, (S.packet.block i x).1 = S.packet.height i x * (S.packet.block i x).2 ∧
          (S.packet.block i x).2 = S.packet.cutoff i x) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) =
            boundaryProfile (S.packet.height i ((S.packet.cusp.collar i).toFun p))) ∧
        (∀ x, S.packet.cutoff i x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, S.packet.block i x ≠ 0 → 20 < S.packet.height i x ∧ S.packet.height i x < 90) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.height i ((S.packet.cusp.collar i).toFun p) ∈ Icc (30 : ℝ) 80 →
            S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) = 1) ∧
        tsupport (S.packet.block i) ⊆ (S.packet.cusp.collar i).toFun ''
          {p : CuspHalfSpace | 20 - cuspTolerance_BCUSP1 (β 1) βd εN ≤ p.2.val 0 ∧
            p.2.val 0 ≤ 90 + cuspTolerance_BCUSP1 (β 1) βd εN}) ∧
    ((∀ k : Fin 4, ContMDiff W.model
        𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.toChain.stage k)) ∧
      (∀ (k : Fin 3) (p : W.Carrier),
        ‖C.toChain.stage k.succ p - S.boundaryOriginalMap p‖ < c k * S.rho p) ∧
      (∀ k : Fin 3, ∃ Hd : ℝ, Hd < c k ∧ ∀ (p : W.Carrier) (v : TangentSpace W.model p),
        ‖mvfderiv W.model (C.toChain.stage k.succ) p v -
            mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ Hd * Real.sqrt (g.inner p v v)) ∧
      (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
      (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          Bs.fibre 1 y ∩ {p | C.toChain.heightRatio p = 4 * Δ})) ∧
    (((∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd) ∧
    (∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤
          c 2 * Real.sqrt (g.inner x v v))) ∧
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K :=
  ⟨fun i => fc43_collar_block_FCF S.packet i,
    ⟨C.stage_smooth_BAUGD, C.stage_error_lt_BAUGD, C.stage_derivative_lt_BAUGD,
      WF.circle_fibre_OWF, WF.slim_fibre_OWF, WF.edge_fibre_OWF⟩,
    ⟨C.bcg04_on_boundary_chain_BGR hrd hprem, C.bcg04_derivative_on_boundary_chain_BGR⟩,
    C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ⟩

end BoundaryGaf02ChainE

/-- **FC43 on a non-empty enhanced chain with an A4 output**: `h` is the conclusion of the
production A2 v3 (a chain on `DP`), `hA4` the conclusion of A4 (v2 bases with the whole-fibre layer
on every chain). The conclusion is `fc43_row_V2b_BGR`'s conjunction (FC43 collar block ∧ BCG03 (A3
exits, fibre types of `WF`) ∧ BCG04 ∧ BCG06 strong exit) on one chain and one A4 output.
Premises: the `r_∂` block and `θ < 1/100`. -/
theorem fc43_row_of_chain_V2b_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hA4 : ∀ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
    ((∀ i : Fin S.packet.cusp.count,
      ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (S.packet.block i) ∧
        (∀ x, (S.packet.block i x).1 = S.packet.height i x * (S.packet.block i x).2 ∧
          (S.packet.block i x).2 = S.packet.cutoff i x) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) =
            boundaryProfile (S.packet.height i ((S.packet.cusp.collar i).toFun p))) ∧
        (∀ x, S.packet.cutoff i x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, S.packet.block i x ≠ 0 → 20 < S.packet.height i x ∧ S.packet.height i x < 90) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.height i ((S.packet.cusp.collar i).toFun p) ∈ Icc (30 : ℝ) 80 →
            S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) = 1) ∧
        tsupport (S.packet.block i) ⊆ (S.packet.cusp.collar i).toFun ''
          {p : CuspHalfSpace | 20 - cuspTolerance_BCUSP1 (β 1) βd εN ≤ p.2.val 0 ∧
            p.2.val 0 ≤ 90 + cuspTolerance_BCUSP1 (β 1) βd εN}) ∧
    ((∀ k : Fin 4, ContMDiff W.model
        𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.toChain.stage k)) ∧
      (∀ (k : Fin 3) (p : W.Carrier),
        ‖C.toChain.stage k.succ p - S.boundaryOriginalMap p‖ < c k * S.rho p) ∧
      (∀ k : Fin 3, ∃ Hd : ℝ, Hd < c k ∧ ∀ (p : W.Carrier) (v : TangentSpace W.model p),
        ‖mvfderiv W.model (C.toChain.stage k.succ) p v -
            mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ Hd * Real.sqrt (g.inner p v v)) ∧
      (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
      (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          Bs.fibre 1 y ∩ {p | C.toChain.heightRatio p = 4 * Δ})) ∧
    (((∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd) ∧
    (∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤
          c 2 * Real.sqrt (g.inner x v v))) ∧
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K ) := by
  obtain ⟨C⟩ := h
  obtain ⟨Bs, WF⟩ := hA4 C
  exact ⟨C, Bs, WF, C.fc43_row_V2b_BGR WF hrd hrd4 hrdc hprem hθ⟩

end DifferentialGeometry.Geometry.Collapse
