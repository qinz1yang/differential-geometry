import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefinerRegularBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEExits

/-!
# BCG07 F3 (analytic half): the global defining functions of the actual zero domains
(lane S-BCG-ROWS)

On `C : BoundaryGaf02ChainE DP …` with `εr < 1/2`: for every zero index `k`, the linearized definer
`zeroDefinerW_BGR` of G16 (smooth on `W` by G21, regular at its zeros by `zeroDefinerW_regular_BGR`)
is replaced by `F = G / â` (`exists_ratioCompatible_global_definer_ZSP35` on `W`, `a = v_k / R_k`,
`O = val '' {.39 < η_k < .41}`); the result has

* `F` smooth on `W`, regular on `{F = 0}`, `{F ≤ 0} = Z_k(C.E)` and `{F = 0} =` the actual face;
* `F = u_k/v_k − 2/5` and `v_k > .99 R_k` on an open neighbourhood of the face (`ratio_near`);
* `frontier Z_k = face` (Fermat at the interior face points).

`exists_boundaryZeroDefining_BGR` assembles `BoundaryZeroDefining_BIFc C.toChain` (the transport
field is G18's `zsp02_transport_BGR`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The zero marker `v_k(E ·)` of the chain is smooth on `W` (A3a). -/
theorem contMDiff_zeroMarker_W_BGR (k : S.ZeroIdx_BAUGC) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (C.toChain.zeroMarker_BIFc k) :=
  (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (S.zeroTag_BAUGC k))).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3)

/-- The retained coordinate `u_k(E ·)` of the chain is smooth on `W` (A3a). -/
theorem contMDiff_zeroCoord_W_BGR (k : S.ZeroIdx_BAUGC) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (C.toChain.zeroCoord_BIFc k) :=
  ((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
    (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inl (S.zeroTag_BAUGC k)))).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3)
/-- **The ratio-compatible global defining function of one actual zero domain** (D74-7):
`F` smooth on `W`, regular at its zeros, `{F ≤ 0} = Z_k`, `{F = 0} = face`, and `F = u_k/v_k − 2/5`
with `v_k > .99 R_k` on an open neighbourhood of the face. -/
theorem exists_defFn_BGR (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p, F p = 0 → mfderiv W.model 𝓘(ℝ, ℝ) F p ≠ 0) ∧
      C.toChain.actualZeroDomain_BIFc k = {p | F p ≤ 0} ∧
      C.toChain.actualZeroFace_BIFc k = {p | F p = 0} ∧
      ∃ O : Set W.Carrier, IsOpen O ∧ C.toChain.actualZeroFace_BIFc k ⊆ O ∧
        ∀ p ∈ O, 99 / 100 * S.zeroRadius_BAUGC k < C.toChain.zeroMarker_BIFc k p ∧
          F p = C.toChain.zeroCoord_BIFc k p / C.toChain.zeroMarker_BIFc k p - 2 / 5 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, he, hT, -⟩ := C.std
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, -⟩ := zsp_radial_facts_ZSP35_BGR S.family.zero k
  have hδ := C.delta_zero_lt_E_BGR
  have hZE := C.toChain.zeroBind_ZE_BGR (by linarith only [hT1]) he k
  have hrad := zsp02_original_radial_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.toChain.zeroBindMap_BGR hδ hZE
  have hband : IsOpen {x : W.pieceInterior ⊤ |
      39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100} :=
    (isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const)
  have hOo : IsOpen (Subtype.val '' {x : W.pieceInterior ⊤ |
      39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100}) :=
    (W.pieceInterior ⊤).isOpen.isOpenMap_subtype_val _ hband
  have hGz : {p | C.toChain.zeroDefinerW_BGR k p = 0} = C.toChain.actualZeroFace_BIFc k :=
    C.toChain.zeroDefinerW_eq_zero_iff_BGR hΔ hT he k
  have hGle : {p | C.toChain.zeroDefinerW_BGR k p ≤ 0} = C.toChain.actualZeroDomain_BIFc k :=
    C.toChain.zeroDefinerW_le_iff_BGR hΔ hT he k
  have hzero : {p | C.toChain.zeroDefinerW_BGR k p = 0} ⊆ Subtype.val '' {x : W.pieceInterior ⊤ |
      39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100} := by
    intro p hp
    have hp' : p ∈ C.toChain.actualZeroFace_BIFc k := by rw [← hGz]; exact hp
    rw [C.toChain.actualZeroFace_eq_image_BGR hT1 he k] at hp'
    obtain ⟨y, hy, rfl⟩ := hp'
    have hyη := abs_lt.mp ((hrad y hy.1).2.2
      (by rw [show (4 / 10 : ℝ) = 2 / 5 by norm_num]; exact hy.2))
    exact ⟨y, ⟨by linarith only [hyη.1], by linarith only [hyη.2]⟩, rfl⟩
  have hmark : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun p => ((S.family.zero.zero k.1
      ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ * C.toChain.zeroMarker_BIFc k p) :=
    contMDiff_const.mul (C.contMDiff_zeroMarker_W_BGR k)
  have hapos : ∀ p ∈ Subtype.val '' {x : W.pieceInterior ⊤ |
      39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100},
      0 < ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        C.toChain.zeroMarker_BIFc k p := by
    rintro p ⟨x, hx, rfl⟩
    have hv := C.zeroMarker_pos_band_BGR k x hx.1 hx.2
    exact mul_pos (inv_pos.mpr hR) (by change 0 < (C.toChain.zeroBindMap_BGR x
      (.inr (.inr (.inr (.inl k))))).snd; linarith only [hv, hR])
  have hfactor : ∀ p ∈ Subtype.val '' {x : W.pieceInterior ⊤ |
      39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100},
      C.toChain.zeroDefinerW_BGR k p =
        (((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          C.toChain.zeroMarker_BIFc k p) *
        (C.toChain.zeroCoord_BIFc k p / C.toChain.zeroMarker_BIFc k p - 2 / 5) := by
    rintro p ⟨x, hx, rfl⟩
    have hv := C.zeroMarker_pos_band_BGR k x hx.1 hx.2
    rw [C.toChain.zeroDefinerW_val_BGR k x]
    exact zspDefiner_sub_eq_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.toChain.zeroBindMap_BGR hx.1 hx.2 (by linarith only [hv, hR])
  obtain ⟨F, N, hNo, hZN, hNO, hFs, hFN, hle, heq, hFreg⟩ :=
    exists_ratioCompatible_global_definer_ZSP35 (C.contMDiff_zeroDefinerW_BGR k)
      (C.zeroDefinerW_regular_BGR hεr k) hOo hzero hmark.contMDiffOn hapos hfactor
  refine ⟨F, hFs, hFreg, ?_, ?_, N, hNo, ?_, fun p hp => ?_⟩
  · rw [← hGle, hle]
  · rw [← hGz, heq]
  · rw [← hGz]
    exact hZN
  · obtain ⟨x, hx, rfl⟩ := hNO (subset_closure hp)
    exact ⟨by
      have hv := C.zeroMarker_pos_band_BGR k x hx.1 hx.2
      exact hv, hFN _ hp⟩
/-- **`∂Z_k = face`** (ZSP02 (ZF)) from a defining function regular on its zero set: the face points
are interior points of `W` (G12), `F` takes larger values arbitrarily close to them (Fermat). -/
theorem frontier_actualZeroDomain_BGR (k : S.ZeroIdx_BAUGC) {F : W.Carrier → ℝ}
    (hFc : Continuous F) (hreg : ∀ p, F p = 0 → mfderiv W.model 𝓘(ℝ, ℝ) F p ≠ 0)
    (hdom : C.toChain.actualZeroDomain_BIFc k = {p | F p ≤ 0})
    (hface : C.toChain.actualZeroFace_BIFc k = {p | F p = 0}) :
    frontier (C.toChain.actualZeroDomain_BIFc k) = C.toChain.actualZeroFace_BIFc k := by
  rw [hdom, hface, (isClosed_le hFc continuous_const).frontier_eq]
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    refine le_antisymm hx (not_lt.mp fun hlt => hxi ?_)
    exact interior_mono (fun y (hy : F y < 0) => le_of_lt hy)
      ((isOpen_lt hFc continuous_const).interior_eq ▸ hlt)
  · intro hx
    have hx0 : F x = 0 := hx
    refine ⟨le_of_eq hx0, fun hint => ?_⟩
    have hxf : x ∈ C.toChain.actualZeroFace_BIFc k := by rw [hface]; exact hx
    obtain ⟨y, hy1, hy2⟩ := exists_gt_of_mfderiv_ne_zero_BCG6K
      (C.isInteriorPoint_of_mem_actualZeroFace_BGR k hxf) (hreg x hx0)
      (isOpen_interior.mem_nhds hint)
    have hyc : y ∈ {p | F p ≤ 0} := interior_subset hy1
    have hyc' : F y ≤ 0 := hyc
    linarith

/-- **BCG07 F3, analytic half, on the enhanced chain**: the global defining functions of the actual
zero domains of `C.E` (`BoundaryZeroDefining_BIFc`, review 69 §1.6 / D69-4), with the ratio normal
form near the faces (D74-7) and the transport of the original model sublevel (G18). -/
theorem exists_boundaryZeroDefining_BGR (hεr : εr < 1 / 2) :
    Nonempty (BoundaryZeroDefining_BIFc C.toChain) := by
  choose F hFs hFreg hdom hface O hOo hfO hratio using C.exists_defFn_BGR hεr
  exact ⟨{
    defFn := F
    defFn_smooth := hFs
    defFn_regular := hFreg
    domain_eq := hdom
    face_eq := hface
    frontier_eq := fun k => C.frontier_actualZeroDomain_BGR k (hFs k).continuous (hFreg k)
      (hdom k) (hface k)
    ratio_near := fun k => ⟨O k, hOo k, hfO k, hratio k⟩
    transport := C.zsp02_transport_BGR hεr }⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
