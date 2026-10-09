import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainHderBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefinerWBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR
import DifferentialGeometry.Topology.Manifold.RatioCompatibleDefiner

/-!
# BCG07 F3, step Z4 (part 2): smoothness of the linearized definer on `W` and the regularity input
of the retained ratio on the enhanced chain (lane B-BCG-ROWS)

On `C : BoundaryGaf02ChainE DP …` (register `C.std`, A3c): the inputs of the ported ZSP02 kernel as
light standalone lemmas (`T_ge_one_BGR`, `delta_zero_lt_E_BGR`, `e_lt_E_BGR`,
`contMDiff_zeroBindMap_E_BGR`, `contMDiff_cgpGlobalMap_E_BGR`, `derivConstTwo_lt_BGR` (A3c's
`H₂`, made nonnegative, `< 1/100`), `zeroBind_hder_E_BGR`), and

* **`zeroRatio_regular_BGR`**: the retained ratio `u_k/v_k − 2/5` of `f = pr_int ∘ C.E ∘ val` has
  nonzero differential on ZSP02's face set (ported `zsp_defining_ZSP35_BGR`);
* `contMDiff_zspDefiner_E_BGR`, `tsupport_zspDefiner_sub_BGR` (support of `H_k − 1/2` in the closed
  `ĝ`-ball `B̄(c_k, (1/2 + e)R_k)`);
* **`contMDiff_zeroDefinerW_BGR`**: G16's linearized definer `zeroDefinerW_BGR` is smooth on ALL of
  `W` (zero extension from the compact `val '' B̄_ĝ`, `(W°, ĝ)` proper).
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

include C in
/-- `1 ≤ T` from the register (`1 ≤ Δ`, `1600·10⁶Δ ≤ T`). -/
theorem T_ge_one_BGR : 1 ≤ T := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, -, hT, -⟩ := C.std
  nlinarith only [hT, hΔ]

include C in
/-- `δ₀ = 200c₂/T < 1/1000` on the enhanced chain. -/
theorem delta_zero_lt_E_BGR : 200 * c 2 / T < 1 / 1000 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, -, hT, -⟩ := C.std
  exact C.toChain.delta_zero_lt_BGR hΔ hT

include C in
/-- `e < 1/40` from the register. -/
theorem e_lt_E_BGR : e < 1 / 40 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := C.std
  exact he

/-- The kernel input map `pr_int ∘ C.E ∘ val` is smooth (register `C.std`). -/
theorem contMDiff_zeroBindMap_E_BGR :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞
      C.toChain.zeroBindMap_BGR := by
  obtain ⟨hΛ, hΔ0, hμ, hτ, hΔΛ, hV, hβ1, hb, he10, -⟩ := C.std
  exact C.toChain.contMDiff_zeroBindMap_BGR hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he10

include C in
/-- The ported CGP01 map of the active family is smooth on `W°` (register `C.std`). -/
theorem contMDiff_cgpGlobalMap_E_BGR :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞
      (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  obtain ⟨hΛ, hΔ0, hμ, hτ, hΔΛ, -, -, -, he10, -⟩ := C.std
  rw [← S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact S.contMDiff_interiorMapOn_BAUGP hΛ hΔ0 hμ hτ hΔΛ (by linarith only [he10])

include C in
/-- A3c's stage-three constant `H₂` (GAF01's `d₂`), made nonnegative, is `< 1/100`. -/
theorem derivConstTwo_lt_BGR :
    max ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) + Ξ 2 * (bder + c 1) +
      eg 2 + 2 * c 1) 0 < 1 / 100 := by
  have hN := C.toChain.numbers
  exact (max_lt hN.2.2.2.2.2.2.2.2.2.2.2.2.2 C.toChain.c_two_pos_BCG6K).trans
    (C.validity.c_two_lt.trans (by norm_num))

/-- **The `hder` input with the explicit constant `H₂`** (A3c + G18). -/
theorem zeroBind_hder_E_BGR :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ p (v : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) C.toChain.zeroBindMap_BGR p v -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) p v‖ ≤
        max ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) + Ξ 2 * (bder + c 1) +
          eg 2 + 2 * c 1) 0 *
          Real.sqrt (S.completion.metric.inner p v v) :=
  C.zeroBind_hder_of_BGR (le_max_right _ _) fun p v => (C.deriv_lt_two_BAUGD p v).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

/-- **The retained ratio `u_k/v_k − 2/5` of `f = pr_int ∘ C.E ∘ val` has nonzero differential on
ZSP02's face set** (ported `zsp_defining_ZSP35_BGR` with the chain's inputs). -/
theorem zeroRatio_regular_BGR (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ z ∈ zspFace_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.toChain.zeroBindMap_BGR,
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y =>
        ((C.toChain.zeroBindMap_BGR y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (C.toChain.zeroBindMap_BGR y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ≠ 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  exact (zsp_defining_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.toChain.zeroBindMap_BGR C.contMDiff_zeroBindMap_E_BGR C.contMDiff_cgpGlobalMap_E_BGR
    C.delta_zero_lt_E_BGR (C.toChain.zeroBind_ZE_BGR (by linarith only [C.T_ge_one_BGR])
      C.e_lt_E_BGR k) C.derivConstTwo_lt_BGR C.zeroBind_hder_E_BGR hεr C.e_lt_E_BGR).elim
      fun _ hO => hO.2.2.2

/-- ZSP02's linearized definer of `f = pr_int ∘ C.E ∘ val` is smooth on `W°`. -/
theorem contMDiff_zspDefiner_E_BGR (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
        C.toChain.zeroBindMap_BGR) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  exact (contMDiff_zspH0_ZSP35_BGR S.family.zero k).add
    (contMDiff_zspK_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.toChain.zeroBindMap_BGR C.contMDiff_zeroBindMap_E_BGR)

/-- **The support of `H_k − 1/2` lies in the closed `ĝ`-ball `B̄(c_k, (1/2 + e)R_k)`** (`H_k = 1/2`
where `η_k ≥ 1/2`, LC30's `|η_k − d(·, c_k)/R_k| < e`). -/
theorem tsupport_zspDefiner_sub_BGR (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    tsupport (fun x => zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
        C.toChain.zeroBindMap_BGR x - 1 / 2) ⊆
      closedBall (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((1 / 2 + e) * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  obtain ⟨hηc, hcl, -⟩ := zsp_radial_facts_ZSP35_BGR S.family.zero k
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  refine (closure_minimal (fun x hx => ?_) (isClosed_le hηc continuous_const)).trans
    (fun x (hx : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 1 / 2)
      => ?_)
  · by_contra hlt
    have hlt' : 1 / 2 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x :=
      lt_of_not_ge hlt
    apply hx
    change zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.toChain.zeroBindMap_BGR x - 1 / 2 = 0
    rw [zspDefiner_ZSP35_BGR, zspPsi_eq_high_ZSP35 hlt'.le,
      zspChi_eq_zero_ZSP35 (Or.inr (by linarith)), zero_mul, add_zero, sub_self]
  · rw [mem_closedBall]
    have h1 := (abs_lt.mp (hcl x)).1
    have h3 : ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        dist x (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center <
        1 / 2 + e := by linarith
    rw [inv_mul_lt_iff₀ hR] at h3
    linarith

/-- **The linearized defining function is smooth on `W`** (zero extension of `H_k − 1/2` from the
compact `val '' B̄_ĝ(c_k, (1/2 + e)R_k)`; `(W°, ĝ)` is proper). -/
theorem contMDiff_zeroDefinerW_BGR (k : S.ZeroIdx_BAUGC) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (C.toChain.zeroDefinerW_BGR k) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hP : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete
      ((riemannianMetricComplete_iff_completeSpace
        (inducedMetricSpace_hmetric S.completion.metric)).mpr S.completion.complete)
  have hK := (isCompact_closedBall (S.family.zero.zero k.1
    ((Set.Finite.mem_toFinset _).mp k.2)).center ((1 / 2 + e) *
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)).image
    continuous_subtype_val
  have hext := DifferentialGeometry.Manifold.contMDiff_extend_zero_pieceInterior_BAUGA W hK
    (W.pieceInterior ⊤).isOpen (image_subset_iff.mpr fun x _ => x.2) subset_rfl
    (fun x hx => mem_image_of_mem _ (C.tsupport_zspDefiner_sub_BGR k hx))
    ((C.contMDiff_zspDefiner_E_BGR k).sub contMDiff_const).contMDiffOn
  exact contMDiff_const.add hext


end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
