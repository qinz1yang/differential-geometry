import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroIsolationChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainIsotopySupportedBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceZeroDomainsV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainSmoothV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreMove
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# BCG07 F3, step Z2 (part): binding the boundary chain to the ported ZSP02 kernel (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG07 (B:9518–9524): ZSP01–ZSP02 on the boundary chain, "its entire
radial level trace is in the original interior zero ball"; the producer of BIFACEc's
`BoundaryActualZeroDomains_BIFc` (lane B-BCG-ROWS). The ported kernel
`zsp02_supported_isotopy_kernel_ZSP35_BGR` lives on `(W°, ĝ)` with the boundary family; it is fed
with `f = pr_int ∘ C.E ∘ val` (`zeroBindMap_BGR`).

* `BoundaryGaf02Chain.zeroBindMap_BGR`, `zeroBindMap_apply_BGR`, `contMDiff_zeroBindMap_BGR` (the
  kernel's smoothness input, from A3a on the v2 slot);
* `BoundarySupply.zeroBlock_original_of_notMem_BGR`: at a point of `∂W` the zero blocks of `F_∂`
  vanish (zero extension);
* **`BoundaryGaf02Chain.zeroBind_ZE_BGR`**: the kernel's (ZE) input
  `‖J_k(f − 𝓔⁰)‖ < (200c₃/T) R_k` on `W°` (from G9's `zsp01_ZE_actualSlotsV2_BGR`);
* **`BoundaryGaf02Chain.actualZeroDomain_eq_image_BGR`**, **`actualZeroFace_eq_image_BGR`**:
  BIFACEc's actual zero domain / face of `C.E` on `W` are the `val`-images of the kernel's
  `zspDomain` / `zspFace` of `f` on `W°` (no point of `∂W` carries a marker `≥ .9R_k`);
* **`isCompact_zeroAnnulus_BGR`**: the kernel's compactness input `hS` on `(W°, ĝ)` (Hopf–Rinow).
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

/-- **At a point of `∂W` the zero blocks of `F_∂` vanish** (the interior slots are zero
extensions from `W°`). -/
theorem zeroBlock_original_of_notMem_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (k : S.ZeroIdx_BAUGC) {y : W.Carrier}
    (hy : ¬ ∃ x : W.pieceInterior ⊤, x.val = y) :
    S.zeroBlockCLM_BAUGC k (S.boundaryOriginalMap y) = 0 := by
  change S.intSlotW_BAUGA (S.zeroTag_BAUGC k) y = 0
  have hne : S.zeroTag_BAUGC k ≠ S.scaleTag_BAUGA := by
    intro h
    cases h
  unfold BoundarySupplyCore.intSlotW_BAUGA
  simp only [hne, ↓reduceIte]
  rw [Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hy ⟨x, hx⟩)]
  rfl

end BoundarySupply

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **The kernel input map** `f = pr_int ∘ C.E ∘ val` on `W°` (the interior blocks of the final
map of the chain). -/
def zeroBindMap_BGR : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  fun x => augmentedInteriorProj_BAUGA (C.E x.val)

theorem zeroBindMap_apply_BGR (x : W.pieceInterior ⊤) (t : S.IntTag_BAUGA) :
    C.zeroBindMap_BGR x t = C.E x.val (Sum.inl t) :=
  rfl

end BoundaryGaf02Chain

section Actual

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- **The kernel's (ZE) input on `W°`** (from G9's (ZE) at `val x`, `j = 3`): with
`δ₀ = 200c₃/T`, `‖f(x)_k − 𝓔⁰(x)_k‖ < δ₀R_k` for `f = zeroBindMap_BGR` and the ported global map
`𝓔⁰ = cgpGlobalMap_BAUGP` of the SAME active family. -/
theorem BoundaryGaf02Chain.zeroBind_ZE_BGR (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ x : W.pieceInterior ⊤, ‖C.zeroBindMap_BGR x (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero x
          (.inr (.inr (.inr (.inl k))))‖ <
      200 * c 2 / T * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro x
  have h := (C.zsp01_ZE_actualSlotsV2_BGR hT he k x.val).1 3
  have hF : S.boundaryOriginalMap x.val (Sum.inl (S.zeroTag_BAUGC k)) =
      cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero x
        (.inr (.inr (.inr (.inl k)))) := by
    change S.interiorMapW_BAUGA x.val (S.zeroTag_BAUGC k) = _
    rw [S.interiorMapW_val_BAUGA, S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
    rfl
  change ‖C.E x.val (Sum.inl (S.zeroTag_BAUGC k)) -
    cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero x
      (.inr (.inr (.inr (.inl k))))‖ < _
  rw [← hF]
  exact h

/-- No point of `∂W` carries a zero marker `≥ .9R_k` of `C.E` (`J_kF_∂ = 0` there and (ZE)). -/
theorem BoundaryGaf02Chain.exists_val_of_zeroMarker_BGR (hT : 1 ≤ T) (he : e < 1 / 40)
    (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hv : 9 / 10 * S.zeroRadius_BAUGC k ≤ C.zeroMarker_BIFc k p) :
    ∃ x : W.pieceInterior ⊤, x.val = p := by
  by_contra hp
  have hT0 : 0 < T := by linarith only [hT]
  have h := (C.zsp01_ZE_actualSlotsV2_BGR hT0 he k p).1 3
  have h0 := S.zeroBlock_original_of_notMem_BGR k hp
  change ‖S.zeroBlockCLM_BAUGC k (C.E p - S.boundaryOriginalMap p)‖ < _ at h
  rw [map_sub, h0, sub_zero] at h
  have hR : 0 < S.zeroRadius_BAUGC k := by
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    let _ := S.family.instMetricN
    let _ := S.family.instChartedN
    let _ := S.family.instMetricC
    exact (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hc2' : 200 * c 2 / T ≤ 200 / 512 := by
    rw [div_le_iff₀ hT0]
    have : 0 ≤ c 2 := (C.c_pos_mono_V3_BGR.1.le.trans C.c_pos_mono_V3_BGR.2.1).trans
      C.c_pos_mono_V3_BGR.2.2
    nlinarith
  have hsnd := (abs_block_components_le_GAF2 (S.zeroBlockCLM_BAUGC k (C.E p))).2
  have hm : C.zeroMarker_BIFc k p = (S.zeroBlockCLM_BAUGC k (C.E p)).snd := rfl
  have hb : 200 * c 2 / T * S.zeroRadius_BAUGC k ≤ 200 / 512 * S.zeroRadius_BAUGC k :=
    mul_le_mul_of_nonneg_right hc2' hR.le
  have habs := le_abs_self (S.zeroBlockCLM_BAUGC k (C.E p)).snd
  rw [← hm] at habs hsnd
  linarith

/-- **BIFACEc's actual zero domain is the `val`-image of the kernel's domain**:
`Z_k(C.E) = val '' zspDomain(f)` with `f = pr_int ∘ C.E ∘ val`. -/
theorem BoundaryGaf02Chain.actualZeroDomain_eq_image_BGR (hT : 1 ≤ T) (he : e < 1 / 40)
    (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    C.actualZeroDomain_BIFc k = Subtype.val ''
      zspDomain_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hc : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center = k.1 :=
    S.family.zero.zero_center k.1 _
  ext p
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨hv, hu⟩)
    · refine ⟨x, Or.inl ?_, rfl⟩
      change x ∈ ball (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center _
      rw [hc]
      exact hx
    · obtain ⟨x, rfl⟩ := C.exists_val_of_zeroMarker_BGR hT he k hv
      exact ⟨x, Or.inr ⟨hv, hu⟩, rfl⟩
  · rintro ⟨x, hx | ⟨hv, hu⟩, rfl⟩
    · refine Or.inl ⟨x, ?_, rfl⟩
      change x ∈ ball (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center _
        at hx
      rw [hc] at hx
      exact hx
    · exact Or.inr ⟨hv, hu⟩

/-- **BIFACEc's actual zero face is the `val`-image of the kernel's face set**. -/
theorem BoundaryGaf02Chain.actualZeroFace_eq_image_BGR (hT : 1 ≤ T) (he : e < 1 / 40)
    (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    C.actualZeroFace_BIFc k = Subtype.val ''
      zspFace_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  ext p
  constructor
  · rintro ⟨hv, hu⟩
    obtain ⟨x, rfl⟩ := C.exists_val_of_zeroMarker_BGR hT he k hv
    exact ⟨x, ⟨hv, hu⟩, rfl⟩
  · rintro ⟨x, ⟨hv, hu⟩, rfl⟩
    exact ⟨hv, hu⟩

/-- **The kernel input map is smooth on `W°`** (A3a on the v2 slot, `contMDiff_E_V2_BAUGD`, through
the smooth inclusion `W° → W` and the interior projection). -/
theorem BoundaryGaf02Chain.contMDiff_zeroBindMap_BGR (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞ C.zeroBindMap_BGR :=
  (augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA) (κ := Fin S.packet.cusp.count)).contDiff.contMDiff.comp
    ((C.contMDiff_E_V2_BAUGD hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).comp (contMDiff_val_interior_BCG6K W))

/-- **The thin closed annulus of a zero ball is compact in `(W°, ĝ)`** (the kernel's `hS` input):
`(W°, ĝ)` is complete, hence proper (Hopf–Rinow, `inducedMetricSpace_properSpace_of_
riemannianMetricComplete`), and `η_k⁻¹[.398, .402]` is closed and inside the ĝ-ball of radius
`(.402 + e)R_k` (LC30's `|η_k − R_k⁻¹d(·, c_k)| < e`). -/
theorem isCompact_zeroAnnulus_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    IsCompact ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Icc (398 / 1000 : ℝ) (402 / 1000)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hP : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete
      ((riemannianMetricComplete_iff_completeSpace
        (inducedMetricSpace_hmetric S.completion.metric)).mpr S.completion.complete)
  obtain ⟨hηc, hcl, -⟩ := zsp_radial_facts_ZSP35_BGR S.family.zero k
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  refine (isCompact_closedBall (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
    ((402 / 1000 + e) * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    ).of_isClosed_subset (isClosed_Icc.preimage hηc) fun x hx => ?_
  rw [mem_closedBall]
  have h1 := (abs_lt.mp (hcl x)).1
  have h2 : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 402 / 1000 :=
    hx.2
  have h3 : ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
      dist x (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center <
      402 / 1000 + e := by linarith
  rw [inv_mul_lt_iff₀ hR] at h3
  linarith

end Actual

end DifferentialGeometry.Geometry.Collapse
