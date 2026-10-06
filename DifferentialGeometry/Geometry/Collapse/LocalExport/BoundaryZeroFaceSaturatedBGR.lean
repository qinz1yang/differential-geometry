import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroCoreSatBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroIsolationChainBGR

/-!
# BCG07 F4d / F3 `face_saturated`: `M₁ ∩ X_st` is saturated, on the v2 bases (S-BCG-ROWS2 G25)

Blueprint BCG07 (B:9471; proof B:9565–9585): every `π_j` retains the WHOLE physical boundary block,
a whole fibre meeting a face is wholly in that frontier, and the connected-fibre argument of ZSP03
applies to both sorts of disjoint internal face: a fibre avoiding all frontiers cannot lie on both
sides, so the complement restriction is saturated.

This is the field `face_saturated` of `BoundaryActualZeroDomains_BIFc` (and F4d of
`TargetsBoundary-v3.1`), proved WITHOUT the standard face parametrization `face_param`: it needs
only the analytic half `BoundaryZeroDefining_BIFc` (G22), the connected whole circle / slim fibres
of the v2 bases (`BoundaryWholeFiberSpecV2`), and the premises of E4 (BCG06).

* **`face_saturated_actual_BGR`**: the field `face_saturated` verbatim;
* **`M₁_saturated_of_defining_BGR`**: F4d verbatim
  (`M₁ ∩ X_st = X_st ∩ f_st⁻¹ (f_st '' (M₁ ∩ X_st))` for `st ≠ 1`) from the analytic half only;
* `isPreconnected_circleFibre_BGR`, `isPreconnected_fibre_V2_BGR` (circle and slim whole fibres).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

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

/-- **Whole circle fibres are preconnected** (`≃ₜ S¹`). -/
theorem isPreconnected_circleFibre_BGR (WF : BoundaryWholeFiberSpecV2 C Bs) {y : _}
    (hy : y ∈ Bs.base 0) : IsPreconnected (Bs.fibre 0 y) := by
  obtain ⟨e⟩ := WF.circle_fibre_BIFc y hy
  exact isPreconnected_of_homeomorph_BGR e

/-- **The whole circle and slim fibres of the v2 bases are preconnected.** -/
theorem isPreconnected_fibre_V2_BGR (WF : BoundaryWholeFiberSpecV2 C Bs) {st : Fin 3}
    (hst : st ≠ 1) {y : _} (hy : y ∈ Bs.base st) : IsPreconnected (Bs.fibre st y) := by
  fin_cases st
  · exact isPreconnected_circleFibre_BGR WF hy
  · exact absurd rfl hst
  · exact isPreconnected_slimFibre_BGR WF hy

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
theorem face_saturated_actual_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
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
  have hZ := isPreconnected_fibre_V2_BGR WF hst hy
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
theorem M₁_saturated_of_defining_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
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
    exact ⟨C.face_saturated_actual_BGR WF Zd hrd hrd4 hrdc hprem hθ st hst p hpX q hqX hpq.symm
      hpM, hqX⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
