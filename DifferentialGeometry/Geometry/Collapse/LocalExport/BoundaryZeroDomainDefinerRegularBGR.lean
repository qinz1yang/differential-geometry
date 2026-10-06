import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefinerSmoothBGR

/-!
# BCG07 F3, step Z4 (part 3): regularity of the linearized definer at the zero face
(lane S-BCG-ROWS)

On `C : BoundaryGaf02ChainE DP …`: near ZSP02's face `H_k − 2/5 = (v_k/R_k)(u_k/v_k − 2/5)` on `W°`
(`zspDefiner_sub_eq_ZSP35_BGR`) and the retained ratio `u_k/v_k − 2/5` is regular on the face
(`zeroRatio_regular_BGR`, G21). Product rule at a zero of the ratio:

* `mfderiv_zspDefiner_ne_zero_BGR`: `d(H_k − 2/5) ≠ 0` on ZSP02's face set (in `W°`);
* `zeroDefinerW_regular_BGR`: the linearized definer of `W` has nonzero differential at each of
  its zeros (G16: `{F = 0}` is the actual face `= val '' (ZSP02 face)`).
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

/-- **Product rule at a simple zero of a factor** (generic): if `F = r · a` near `y`, `r y = 0`,
`a y ≠ 0` and `dr(y) ≠ 0`, then `dF(y) ≠ 0`. -/
theorem mfderiv_eventually_mul_ne_zero_BGR {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {F r a : M → ℝ} {y : M} (hev : F =ᶠ[𝓝 y] fun z => r z * a z)
    (hr : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) r y) (ha : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) a y)
    (h0 : r y = 0) (hapos : a y ≠ 0) (hreg : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) r y ≠ 0) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F y ≠ 0 := by
  rw [hev.mfderiv_eq, mfderiv_mul_of_eq_zero_ZSP35 hr ha h0]
  exact smul_ne_zero hapos hreg

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- `0 ≤ 200 c₂ / T` on the enhanced chain. -/
theorem delta_zero_nonneg_E_BGR : 0 ≤ 200 * c 2 / T := by
  have := C.toChain.c_two_pos_BCG6K
  have hT := C.T_ge_one_BGR
  positivity

/-- **The adjusted zero marker is positive on the thin band** `.39 < η_k < .41` (band `3/10 ..
4/5` of (ZE) and `δ₀ < 1/1000`). -/
theorem zeroMarker_pos_band_BGR (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ z, 39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z →
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100 →
      99 / 100 * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
        (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro z h1 h2
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hδ := C.delta_zero_lt_E_BGR
  have hZE := C.toChain.zeroBind_ZE_BGR (by linarith only [C.T_ge_one_BGR]) C.e_lt_E_BGR k
  have h1' : 3 / 10 ≤ (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z :=
    by linarith only [h1]
  have h2' : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 4 / 5 :=
    by linarith only [h2]
  have hb := zsp_band_marker_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.toChain.zeroBindMap_BGR hZE (z := z) ⟨h1', h2'⟩
  have hδ0 := C.delta_zero_nonneg_E_BGR
  nlinarith
/-- **Eventual factorization**: near a point of the thin band,
`H_k − 2/5 = (u_k/v_k − 2/5) · (R_k⁻¹ v_k)`. -/
theorem zspDefiner_sub_eventually_BGR (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ y, 39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y →
      (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y < 41 / 100 →
      (fun z => zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
        C.toChain.zeroBindMap_BGR z - 2 / 5) =ᶠ[𝓝 y] fun z =>
        (((C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) *
        (((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro y h1 h2
  obtain ⟨hηc, -⟩ := zsp_radial_facts_ZSP35_BGR S.family.zero k
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hmem : y ∈
      {z | 39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z} ∩
      {z | (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100} :=
    ⟨h1, h2⟩
  filter_upwards [((isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const)).mem_nhds
    hmem] with z hz
  have hvz := C.zeroMarker_pos_band_BGR k z hz.1 hz.2
  rw [zspDefiner_sub_eq_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.toChain.zeroBindMap_BGR hz.1 hz.2 (by linarith only [hvz, hR])]
  ring
/-- The coordinate `u_k` and the marker `v_k` of `f = pr_int ∘ C.E ∘ val` are smooth on `W°`. -/
theorem contMDiff_zeroCoord_marker_E_BGR (k : S.ZeroIdx_BAUGC) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun z => ((C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun z => (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd) := by
  have hsm := C.contMDiff_zeroBindMap_E_BGR
  exact ⟨((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA => ℝ²)
        (.inr (.inr (.inr (.inl k)))))).contDiff.comp_contMDiff hsm,
    (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA => ℝ²)
      (.inr (.inr (.inr (.inl k))))).contDiff.comp_contMDiff hsm⟩

/-- **`H_k − 2/5` has nonzero differential on ZSP02's face set** (on `W°`): near the face
`H_k − .4 = (u_k/v_k − .4)·(v_k/R_k)` (`zspDefiner_sub_eq_ZSP35_BGR` on the thin band) and the
ratio is regular there (`zeroRatio_regular_BGR`). -/
theorem mfderiv_zspDefiner_ne_zero_BGR (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ y ∈ zspFace_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.toChain.zeroBindMap_BGR,
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB
        S.family.zero k C.toChain.zeroBindMap_BGR z - 2 / 5) y ≠ 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro y hy
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hδ := C.delta_zero_lt_E_BGR
  have hZE := C.toChain.zeroBind_ZE_BGR (by linarith only [C.T_ge_one_BGR]) C.e_lt_E_BGR k
  have hrad := zsp02_original_radial_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.toChain.zeroBindMap_BGR hδ hZE
  have hyη := abs_lt.mp ((hrad y hy.1).2.2
    (by rw [show (4 / 10 : ℝ) = 2 / 5 by norm_num]; exact hy.2))
  have h1 : 39 / 100 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y :=
    by linarith only [hyη.1]
  have h2 : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y < 41 / 100 :=
    by linarith only [hyη.2]
  have hvy := C.zeroMarker_pos_band_BGR k y h1 h2
  obtain ⟨hud, hvd⟩ := C.contMDiff_zeroCoord_marker_E_BGR k
  have hvpos : 0 < (C.toChain.zeroBindMap_BGR y (.inr (.inr (.inr (.inl k))))).snd :=
    by linarith only [hvy, hR]
  have hrd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
      ((C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) y :=
    (((hud y).div₀ (hvd y) hvpos.ne').sub contMDiffAt_const).mdifferentiableAt (by simp)
  have hbd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
      ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        (C.toChain.zeroBindMap_BGR z (.inr (.inr (.inr (.inl k))))).snd) y :=
    ((contMDiffAt_const.mul (hvd y))).mdifferentiableAt (by simp)
  have hr0 : ((C.toChain.zeroBindMap_BGR y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.toChain.zeroBindMap_BGR y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 = 0 := by
    rw [hy.2, mul_div_assoc, div_self hvpos.ne', mul_one, sub_self]
  exact mfderiv_eventually_mul_ne_zero_BGR (C.zspDefiner_sub_eventually_BGR k y h1 h2) hrd hbd hr0
    (mul_pos (inv_pos.mpr hR) hvpos).ne' (C.zeroRatio_regular_BGR hεr k y hy)
/-- **The linearized definer of `W` is regular at its zeros**: `{F = 0}` is the actual face
`= val '' (ZSP02 face)` (G16), `F ∘ val = H_k − 2/5` on `W°` and the inclusion `val` is
differentiable, so a vanishing `dF` at `val y` would kill `d(H_k − 2/5)(y)`. -/
theorem zeroDefinerW_regular_BGR (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    ∀ p, C.toChain.zeroDefinerW_BGR k p = 0 →
      mfderiv W.model 𝓘(ℝ, ℝ) (C.toChain.zeroDefinerW_BGR k) p ≠ 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, he, hT, -⟩ := C.std
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  intro p hp
  have hpf : p ∈ C.toChain.actualZeroFace_BIFc k := by
    rw [← C.toChain.zeroDefinerW_eq_zero_iff_BGR hΔ hT he k]
    exact hp
  rw [C.toChain.actualZeroFace_eq_image_BGR hT1 he k] at hpf
  obtain ⟨y, hy, rfl⟩ := hpf
  intro hd
  have hG := (C.contMDiff_zeroDefinerW_BGR k).mdifferentiableAt (n := ∞) (by simp) (x := y.val)
  have hfun : (fun z => zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.toChain.zeroBindMap_BGR z - 2 / 5) = C.toChain.zeroDefinerW_BGR k ∘ Subtype.val :=
    funext fun z => (C.toChain.zeroDefinerW_val_BGR k z).symm
  have hcomp := mfderiv_comp y hG (mdifferentiableAt_val_BCG7 W y)
  have hne := C.mfderiv_zspDefiner_ne_zero_BGR hεr k y hy
  rw [hfun, hcomp, hd] at hne
  exact hne (ContinuousLinearMap.ext fun v => rfl)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
