import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBase

/-!
# EDP02's (ELoc) for EVERY preimage of the ratio base, on the chain object (no (JA), no `P₀`)

Blueprint `master207B.tex`, EDP02 (B:6762–6765, B:6797–6825: "For EVERY `p ∈ X₂` and every
witnessing base index `i`: `|η_i(p)| < 4.01Δ`, `t(p) < 4.01Δ`, `p ∈ U₂`"), used by FDC02
(B:7259–7277) to show that EVERY point of `M₂ ∩ X₂` satisfies FDC01's hypotheses. The witness is
only the RATIO condition `v_i > .9R_i`, `|u_i| < 4Δ v_i` (no exact marker, no GAF05 patch clause).

ROUTE: segment (AM0) at `E` makes `ζ_i ≠ 0` (so `q ∈ U_i`); the strict error gives
`ζ_i > .9 − 1.0001c₃ > .898` and `ζ_i|η_i| < 4Δ(ζ_i + 1.0001c₃) + 1.0001c₃`, hence `|η_i| < 4.01Δ`
for `Δ ≥ 2` (GAF06 and GAF01's (JA) are not used); the height splits at `t = 8Δ` as in
`Gaf02Chain.vertical_height_FDC`, with `z₀ ≥ 3ζ_i/4 ≥ .6` above `8Δ` (EDP02's
`β = (1 + 2P₀)d` is not used).

* Numbers: `fdc02_ratio_numbers_FDC`, `fdc02_height_high_numbers_weak_FDC`.
* `Gaf02Chain.ratio_original_FDC` (`q ∈ U_i`, `ζ_i > .898`, `|η_i| < 4.01Δ`),
  `Gaf02Chain.ratio_height_FDC` (`q ∈ V` ⇒ `t < 4.01Δ`), `Gaf02Chain.ratio_localization_FDC`
  (both, and `ζ_i = 1`), `Gaf02Chain.stageTwo_ratio_localization_FDC` (the same with the ratio
  condition read on `π₂E q`).
* `Gaf02Chain.edgePiece_eq_witnessed_FDC` (FDC02's set identity, kernel form): for `M₂` on which
  FDC01 holds (every point of `M₂ ∩ V` satisfying FDC01's hypotheses at some `i` has an exact
  witness `v_k(E x) = R_k`, `|u_k(E x)| < 4ΔR_k`), `M₂ ∩ X₂` equals the witnessed piece
  `M₂ ∩ V ∩ {∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` (`W₂ = C.finalBase_BAS 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The ratio numbers**: `a > .9`, `a < ζ + k`, `u < 4Δa`, `ζ|η| < u + k` (`k ≤ 1.0001/512`,
`Δ ≥ 2`) give `ζ > .898` and `|η| < 4.01Δ`. -/
theorem fdc02_ratio_numbers_FDC {Δ k ζ η a u : ℝ} (hΔ : 2 ≤ Δ)
    (hk : k ≤ 10001 / 5120000) (ha : 9 / 10 < a) (hav : a < ζ + k) (hu : u < 4 * Δ * a)
    (hζη : ζ * |η| < u + k) : 898 / 1000 < ζ ∧ |η| < 401 / 100 * Δ := by
  have hζ : 898 / 1000 < ζ := by linarith
  refine ⟨hζ, ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ζ * (401 / 100 * Δ) ≤ ζ * |η| := mul_le_mul_of_nonneg_left hcon (by linarith)
  have h2 : 4 * Δ * a < 4 * Δ * (ζ + k) := mul_lt_mul_of_pos_left hav (by linarith)
  have h3 : 898 / 1000 * Δ < ζ * Δ := mul_lt_mul_of_pos_right hζ (by linarith)
  have h4 : k * Δ ≤ 10001 / 5120000 * Δ := mul_le_mul_of_nonneg_right hk (by linarith)
  nlinarith

/-- **The weak high height numbers**: `z ≥ .6`, `F > 8Δr`, `zF − c₂r < A ≤ 4Δs`, `s < (1 + c₀)r`,
`c₀, c₂ ≤ 1/512`, `Δ ≥ 1` are contradictory. -/
theorem fdc02_height_high_numbers_weak_FDC {Δ r F A s c₀ c₂ z : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (hz : 6 / 10 ≤ z)
    (hF : 8 * Δ * r < F) (hA : z * F - c₂ * r < A) (hAs : A ≤ 4 * Δ * s)
    (hs : s < (1 + c₀) * r) : False := by
  have h1 : 4 * Δ * s ≤ 4 * Δ * ((1 + c₀) * r) :=
    mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 6 / 10 * (8 * Δ * r) ≤ z * F := mul_le_mul hz hF.le (by positivity) (by linarith)
  nlinarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The original edge block under the ratio condition**: `v_i(E q) > .9R_i` and
`|u_i(E q)| < 4Δ v_i(E q)` (`Δ ≥ 2`) give `q ∈ U_i`, `ζ_i(q) > .898` and `|η_i(q)| < 4.01Δ`. -/
theorem ratio_original_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q))
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j))) (C.E q)) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ 898 / 1000 < P.edge.cutoff j.1 q ∧
      |P.edge.coord j.1 q| < 401 / 100 * Δ := by
  obtain ⟨hΛ, -, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hc2 : c 2 ≤ 1 / 512 := C.numbers.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc2pos : 0 < c 2 := by
    obtain ⟨h0, h1, h2⟩ := C.accuracy_order_EDPE
    linarith
  have hrj := hρ j.1
  have hζI := cgpEdgeCutoff_mem_Icc P.toLocalChartFamily hΔ0 j.1 q
  have hζ0 : P.edge.cutoff j.1 q ≠ 0 := by
    intro h0
    have h := C.prefix_am0.2.2 (.inr (.inr j)) q h0
    change |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)| ≤ ρ j.1 / 32 at h
    have := (abs_le.mp h).2
    linarith
  have hball : q ∈ ball j.1 (100 * Δ * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) q hζ0
  have hρq : ρ q ≤ (1 + 1 / 10000) * ρ j.1 := by
    have h1 := (abs_le.mp (scale_ratio_ball_EDPE P hΛ hball)).2
    have h2 : 100 * Δ * Λ ≤ 1 / 10000 := by nlinarith
    have h4 : ρ q / ρ j.1 ≤ 1 + 1 / 10000 := by linarith
    rwa [div_le_iff₀ hrj] at h4
  have hk : c 2 * ρ q ≤ 10001 / 5120000 * ρ j.1 := by
    have h1 := mul_le_mul_of_nonneg_left hρq hc2pos.le
    have h2 : c 2 * ((1 + 1 / 10000) * ρ j.1) ≤ 1 / 512 * ((1 + 1 / 10000) * ρ j.1) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    linarith
  have herr := C.stage_error_lt.2.2 q
  have hblk := cgpGlobalMap_edgeBlock P.toLocalChartFamily P.zero j q
  have hm0 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q) =
        ρ j.1 * P.edge.cutoff j.1 q := by
    rw [blockMarkerCLM_apply]
    exact hblk.2
  have hv0 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ =
        ρ j.1 * (P.edge.cutoff j.1 q * |P.edge.coord j.1 q|) := by
    rw [blockVectorCLM_apply]
    change ‖(cgpGlobalMap P.toLocalChartFamily P.zero q
      (cgpEdgeBlockTag P.toLocalChartFamily P.zero j)).fst‖ = _
    rw [hblk.1, norm_smul, norm_planeAxis, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hrj.le hζI.1), mul_assoc]
  have hmd : |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) - blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)| ≤
      ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_blockMarkerCLM_le _) (norm_nonneg _))
  have hvd : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) - blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ ≤
      ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ := by
    rw [← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_blockVectorCLM_le _) (norm_nonneg _))
  rw [hm0] at hmd
  set v := blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) with hvdef
  set U := ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ with hUdef
  have hav : v / ρ j.1 < P.edge.cutoff j.1 q + 10001 / 5120000 := by
    rw [div_lt_iff₀ hrj]
    have := (abs_lt.mp (lt_of_le_of_lt hmd herr)).2
    linarith
  have ha : 9 / 10 < v / ρ j.1 := by
    rw [lt_div_iff₀ hrj]
    linarith
  have hu' : U / ρ j.1 < 4 * Δ * (v / ρ j.1) := by
    rw [div_lt_iff₀ hrj]
    have : 4 * Δ * (v / ρ j.1) * ρ j.1 = 4 * Δ * v := by field_simp
    linarith
  have hζη : P.edge.cutoff j.1 q * |P.edge.coord j.1 q| < U / ρ j.1 + 10001 / 5120000 := by
    have htri := norm_le_insert' (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q))
      (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q))
    rw [hv0, norm_sub_rev] at htri
    have h2 : ρ j.1 * (P.edge.cutoff j.1 q * |P.edge.coord j.1 q|) <
        ρ j.1 * (U / ρ j.1 + 10001 / 5120000) := by
      have : ρ j.1 * (U / ρ j.1) = U := by field_simp
      nlinarith
    exact lt_of_mul_lt_mul_left h2 hrj.le
  obtain ⟨h1, h2⟩ := fdc02_ratio_numbers_FDC hΔ le_rfl ha hav hu' hζη
  exact ⟨hball, h1, h2⟩

/-- **The height under `ζ_i > .898`** in `U_i` with `|η_i| < 8Δ`, at a point of `V`:
`t(q) < 4.01Δ`. -/
theorem ratio_height_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X} (hball : q ∈ ball j.1 (100 * Δ * ρ j.1))
    (hη8 : |P.edge.coord j.1 q| < 8 * Δ) (hζk : 898 / 1000 < P.edge.cutoff j.1 q)
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    P.edge.smoothing q / ρ q < 401 / 100 * Δ := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hc0 : c 0 ≤ 1 / 512 := C.numbers.2.2.1
  have hc2 : c 2 ≤ 1 / 512 := C.numbers.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hrq := hρ q
  rcases hV with ht | ⟨hs, hT⟩
  · have ht' : P.edge.smoothing q / ρ q ≤ 7 / 20 * Δ := ht
    linarith
  by_cases ht35 : P.edge.smoothing q / ρ q ≤ 7 / 20 * Δ
  · linarith
  push Not at ht35
  have hA := (abs_lt.mp (C.heightAxis_value_EDPE q).1).1
  have hsρ : C.scale q < (1 + c 0) * ρ q := by
    have := (abs_lt.mp (C.scale_pos q).1).2
    linarith
  have hAs : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
      (C.E q)) ≤ 4 * Δ * C.scale q := by
    rwa [div_le_iff₀ hs] at hT
  by_cases ht8 : P.edge.smoothing q / ρ q ≤ 8 * Δ
  · have hz := edgeMarker_eq_one_EDPE P hΔ0 hj hball hη8 (by linarith) ht8
    rw [hz, one_mul] at hA
    rw [div_lt_iff₀ hrq]
    exact fdc02_height_low_numbers_FDC hΔ hrq hc0 hc2 (by linarith) hAs hsρ
  · exfalso
    push Not at ht8
    have hu3 : 3 / 10 ≤ cgpHeight P.toLocalChartFamily q / Δ := by
      rw [le_div_iff₀ hΔ0]
      change 3 / 10 * Δ ≤ P.edge.smoothing q / ρ q
      linarith
    have hid := cgp01_edge_identity P.toLocalChartFamily hj hball hη8 hΔ0
    have hsum : 3 / 4 ≤ cgpEdgeSum P.toLocalChartFamily q := by
      have h := le_cgpEdgeSum_GAFS P.toLocalChartFamily hΔ0 j q
      linarith
    have hz : cgpEdgeMarker P.toLocalChartFamily q = P.edge.cutoff j.1 q *
        cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum P.toLocalChartFamily q) := by
      rw [cgpEdgeMarker, cgpEdgeH_eq_of_le hu3, hid]
    have hzlo : 6 / 10 ≤ cgpEdgeMarker P.toLocalChartFamily q := by
      rw [hz]
      have h := mul_le_mul hζk.le (edgeSumRamp_ge_FDC hsum) (by norm_num) (by linarith)
      linarith
    have hP8 : 8 * Δ * ρ q < P.edge.smoothing q := by
      rwa [lt_div_iff₀ hrq] at ht8
    exact fdc02_height_high_numbers_weak_FDC hΔ hrq hc0 hc2 hzlo hP8 (by linarith) hAs hsρ

/-- **EDP02's (ELoc) for every ratio preimage** (`Δ ≥ 2`): `v_i(E q) > .9R_i`,
`|u_i(E q)| < 4Δ v_i(E q)` and `q ∈ V` give `q ∈ U_i`, `|η_i(q)| < 4.01Δ`, `t(q) < 4.01Δ`,
`ζ_i(q) = 1`. -/
theorem ratio_localization_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q))
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j))) (C.E q))
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| < 401 / 100 * Δ ∧
      P.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ P.edge.cutoff j.1 q = 1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have h := C.ratio_original_FDC hΔ j hv hu
  have hη8 : |P.edge.coord j.1 q| < 8 * Δ := by linarith [h.2.2]
  have ht := C.ratio_height_FDC j h.1 hη8 h.2.1 hV
  exact ⟨h.1, h.2.2, ht, edge_cutoff_eq_one_EDPE P hΔ0 hj h.1 hη8 (by linarith)⟩

/-- **(ELoc) with the ratio condition on `π₂E q`** (the base condition of `B₂`). -/
theorem stageTwo_ratio_localization_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q)))
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (C.E q))‖ <
      4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.E q)))
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| < 401 / 100 * Δ ∧
      P.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ P.edge.cutoff j.1 q = 1 := by
  rw [gafStageQ_edgeMarker_FDC] at hv hu
  rw [gafStageQ_edgeVector_FDC] at hu
  exact C.ratio_localization_FDC hΔ j hv hu hV

/-- **FDC02's set identity, kernel form**: if every point of `M₂ ∩ V` satisfying FDC01's hypotheses
(`x ∈ U_i`, `|η_i(x)| ≤ 4.01Δ`, `t(x) ≤ 4.01Δ`) has an exact witness `v_k(E x) = R_k`,
`|u_k(E x)| < 4ΔR_k` (`Δ ≥ 2`), then `M₂ ∩ X₂` (`X₂ = (π₂E)⁻¹(B₂) ∩ V`, `W₂ = C.finalBase_BAS 1`)
equals the witnessed piece `M₂ ∩ V ∩ {∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}`. -/
theorem edgePiece_eq_witnessed_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (M₂ : Set X)
    (hrep : ∀ x ∈ M₂, x ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} → ∀ i : P.edge.finite_centres.toFinset,
      x ∈ ball i.1 (100 * Δ * ρ i.1) → |P.edge.coord i.1 x| ≤ 401 / 100 * Δ →
      P.edge.smoothing x / ρ x ≤ 401 / 100 * Δ → ∃ k : P.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E x)‖ < 4 * Δ * ρ k.1) :
    M₂ ∩ ({x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E x) ∈
        C.finalBase_BAS 1 ∧ ∃ k : P.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (C.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (C.E x))‖ <
            4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
                (C.E x))} ∩
      ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
          C.scale p ≤ 4 * Δ})) =
    M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
          C.scale p ≤ 4 * Δ}) ∩
      {x | ∃ k : P.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E x)‖ < 4 * Δ * ρ k.1} := by
  ext x
  constructor
  · intro hx
    have hxM := hx.1
    have hxV := hx.2.2
    obtain ⟨i, hvi, hui⟩ := hx.2.1.2
    have hloc := C.stageTwo_ratio_localization_FDC hΔ i hvi hui hxV
    exact ⟨⟨hxM, hxV⟩, hrep x hxM hxV i hloc.1 hloc.2.1.le hloc.2.2.1.le⟩
  · intro hx
    obtain ⟨⟨hxM, hxV⟩, k, hv, hu⟩ := hx
    have hb := C.stageTwo_mem_base_FDC k hv hu hxV
    exact ⟨hxM, ⟨hb.1, k, hb.2.1, hb.2.2⟩, hxV⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
