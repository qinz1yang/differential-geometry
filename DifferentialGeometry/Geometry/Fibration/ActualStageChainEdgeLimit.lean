import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Fibration.ActualEdgeHeightFactors
import DifferentialGeometry.Geometry.Fibration.ActualEdgeWitnessSubsequence
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CompactEdgePiece

/-!
# FDC02's limit step on the chain object (no (JA), no profile-derivative number)

Blueprint `master207B.tex`, FDC02 (`thm:fibration-actual-compact-edge-piece`, B:7246–7283), the
limit step of its proof, and the (EZ) height calculation of EDP02 (B:6797–6825) that it reuses.
Everything is about ONE chain `C : Gaf02Chain P …` (it applies unchanged to `Gaf02ChainE.toChain`
and to `Gaf02ChainEJA`'s projection). Conventions of lane C14-EDP-E:
`A = proj₀(gafHeightVector (C.E p))`, `s = C.scale`, `T = A/s`, the vertical set of (ED)
`V = {t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ}`; `v_j`, `u_j` are the marker and vector of the `j`-th edge
block of `C.E`; blueprint `c₃` = chain `c 2`.

ROUTE (strengthening of the blueprint's): with the EXACT final marker `v_j(E q) = R_j`, segment
(AM0) at `E` makes the original cutoff nonzero (so `q ∈ U_j`), and the strict error gives
`ζ_j(q) > 1 − 1.0001c₃` directly (GAF06 is not needed, hence neither is GAF01's (JA)
`c₃ < 1/1000`). The height splits at `t = 8Δ`: below, `z₀ = 1` EXACTLY (`edgeMarker_eq_one_EDPE`);
above, `z₀ = ζ_j χ_{1/2,1}(Σζ) ≥ ζ_j χ_E(1/2) = 3ζ_j/4`, which contradicts `T ≤ 4Δ`. So the
blueprint's `β = (1 + 2P₀)d < 1/1000` (a smallness of `c₃` against the profile constant `P₀`) is not
used either; only `c₀, c₃ ≤ 1/512` and `Δ ≥ 1` (the chain's own `numbers` / `std`).

* `lc87EdgeTransition_half_FDC` (`χ_E(1/2) = 3/4`), `edgeSumRamp_ge_FDC` (`χ_{1/2,1} ≥ 3/4` on
  `[3/4, ∞)`); the number lemmas `fdc02_tangential_numbers_FDC`, `fdc02_height_low_numbers_FDC`,
  `fdc02_height_high_numbers_FDC`.
* `Gaf02Chain.isClosed_vertical_FDC`: `V` is closed (`s > 0` everywhere, `T` continuous).
* `Gaf02Chain.exact_marker_original_FDC`: exact marker and `|u_j(E q)| ≤ 4ΔR_j` ⇒ `q ∈ U_j`,
  `ζ_j(q) > 1 − 1.0001/512`, `ζ_j(q)|η_j(q)| < 4Δ + 1.0001/512`.
* `Gaf02Chain.vertical_height_FDC`: in `U_j` with `|η_j| < 8Δ`, `ζ_j > 1 − 1.0001/512`, `q ∈ V` ⇒
  `t(q) < 4.01Δ`.
* `Gaf02Chain.fdc02_limit_point_FDC`: exact marker, weak vector bound, `q ∈ V` ⇒ `q ∈ U_j`,
  `|η_j(q)| < 4.01Δ`, `t(q) < 4.01Δ`, `ζ_j(q) = 1` (FDC01's hypotheses at the limit; no `q ∈ X₂`,
  `B₂` or `W₂` assumed).
* `Gaf02Chain.fdc02_limit_FDC` (one witnessing index along `q_n → q`; continuity of `v_j ∘ E`,
  `|u_j ∘ E|` and closedness of `V`), `Gaf02Chain.fdc02_limit_witness_FDC` (varying witnesses,
  pigeonhole `exists_strictMono_eq_of_mem_finite_FDC1`).
* `Gaf02Chain.fdc02_isCompact_FDC`: any `S ⊆ M₂ ∩ V` (`M₂` closed) whose points have a witnessing
  index (`v_j = R_j`, `|u_j| < 4ΔR_j`, EDP02) and which contains every point of `M₂ ∩ V` satisfying
  FDC01's hypotheses (`q ∈ U_i`, `|η_i| ≤ 4.01Δ`, `t ≤ 4.01Δ`) is compact (`EdgeDisk` kernel).
NOT here: `π₂E(q) ∈ W₂ ∩ B₂` for the limit (BASES / FDC01's exact marker), closedness of `M₂`
(ZSP / GAF07), `C₂`'s 1-manifold structure (EDP05, FC34).
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

/-- `χ_E(1/2) = 3/4` for the LC87 transition `χ_E = 1 − (1 − smoothTransition)²`. -/
theorem lc87EdgeTransition_half_FDC : lc87EdgeTransition (1 / 2) = 3 / 4 := by
  rw [lc87EdgeTransition, CutoffProfile.value, CutoffProfile.stem,
    show (1 : ℝ) + 1 / 2 - 1 = 1 / 2 by norm_num,
    DifferentialGeometry.Topology.smoothTransition_half]
  norm_num

/-- CGP01's sum profile `χ_{1/2,1}` is at least `3/4` on `[3/4, ∞)` (no derivative bound). -/
theorem edgeSumRamp_ge_FDC {x : ℝ} (hx : 3 / 4 ≤ x) :
    3 / 4 ≤ cfsRamp lc87EdgeTransition (1 / 2) 1 x := by
  rw [cfsRamp, ← lc87EdgeTransition_half_FDC]
  apply lc87EdgeTransition_monotone
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- The tangential numbers: `ζ > 1 − k`, `ζ|η| < 4Δ + k`, `k ≤ 1.0001/512`, `Δ ≥ 1` give
`|η| < 4.01Δ`. -/
theorem fdc02_tangential_numbers_FDC {Δ k ζ η : ℝ} (hΔ : 1 ≤ Δ) (hk : k ≤ 10001 / 5120000)
    (hζ : 1 - k < ζ) (hζη : ζ * |η| < 4 * Δ + k) : |η| < 401 / 100 * Δ := by
  by_contra hcon
  push Not at hcon
  have h1 : (1 - k) * (401 / 100 * Δ) ≤ ζ * |η| :=
    mul_le_mul hζ.le hcon (by positivity) (by linarith)
  nlinarith

/-- The low height numbers: `F − c₂r < A ≤ 4Δs`, `s < (1 + c₀)r`, `c₀, c₂ ≤ 1/512`, `Δ ≥ 1`
give `F < 4.01Δr`. -/
theorem fdc02_height_low_numbers_FDC {Δ r F A s c₀ c₂ : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (hA : F - c₂ * r < A) (hAs : A ≤ 4 * Δ * s)
    (hs : s < (1 + c₀) * r) : F < 401 / 100 * Δ * r := by
  have h1 : 4 * Δ * s ≤ 4 * Δ * ((1 + c₀) * r) :=
    mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

/-- The high height numbers: `z ≥ (1 − 1.0001/512)·3/4`, `F > 8Δr`, `zF − c₂r < A ≤ 4Δs`,
`s < (1 + c₀)r`, `c₀, c₂ ≤ 1/512`, `Δ ≥ 1` are contradictory. -/
theorem fdc02_height_high_numbers_FDC {Δ r F A s c₀ c₂ z : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (hz : (1 - 10001 / 5120000) * (3 / 4) ≤ z)
    (hF : 8 * Δ * r < F) (hA : z * F - c₂ * r < A) (hAs : A ≤ 4 * Δ * s)
    (hs : s < (1 + c₀) * r) : False := by
  have h1 : 4 * Δ * s ≤ 4 * Δ * ((1 + c₀) * r) :=
    mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : (1 - 10001 / 5120000) * (3 / 4) * (8 * Δ * r) ≤ z * F :=
    mul_le_mul hz hF.le (by positivity) (by linarith)
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

/-- **The vertical set of (ED) is closed**: `V = {t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ}` (`s > 0`
everywhere, `T = A/s` continuous). -/
theorem isClosed_vertical_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    IsClosed ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) := by
  have hT := C.final_smooth_EDPE.2.2.2.1.continuous
  refine IsClosed.union (isClosed_le (continuous_cgpHeight P.toLocalChartFamily)
    continuous_const) ?_
  have heq : {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} = {p |
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} := by
    ext p
    exact ⟨fun h => h.2, fun h => ⟨(C.scale_pos p).2, h⟩⟩
  rw [heq]
  exact isClosed_le hT continuous_const

/-- **The original edge block under an exact final marker** (no (JA)): `v_j(E q) = R_j` and
`|u_j(E q)| ≤ 4ΔR_j` give `q ∈ U_j = B(j, 100ΔR_j)` (segment (AM0) at `E`),
`ζ_j(q) > 1 − 1.0001/512` and `ζ_j(q)|η_j(q)| < 4Δ + 1.0001/512` (strict error, `ρ(q) ≤ 1.0001R_j`,
original block `(R_jζ_jη_j, R_jζ_j)`). -/
theorem exact_marker_original_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) = ρ j.1)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ ≤ 4 * Δ * ρ j.1) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ 1 - 10001 / 5120000 < P.edge.cutoff j.1 q ∧
      P.edge.cutoff j.1 q * |P.edge.coord j.1 q| < 4 * Δ + 10001 / 5120000 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hc2pos : 0 < c 2 := by
    obtain ⟨h0, h1, h2⟩ := C.accuracy_order_EDPE
    linarith
  have hrj := hρ j.1
  have hζI := cgpEdgeCutoff_mem_Icc P.toLocalChartFamily hΔ0 j.1 q
  -- (AM0) at the final map: the original cutoff is not zero
  have hζ0 : P.edge.cutoff j.1 q ≠ 0 := by
    intro h0
    have h := C.prefix_am0.2.2 (.inr (.inr j)) q h0
    change |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)| ≤ ρ j.1 / 32 at h
    rw [hv, abs_of_pos hrj] at h
    linarith
  have hball : q ∈ ball j.1 (100 * Δ * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) q hζ0
  -- the scale at `q`
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
  have herr' : ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ <
      10001 / 5120000 * ρ j.1 := lt_of_lt_of_le herr hk
  -- the original edge block at `q`
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
  refine ⟨hball, ?_, ?_⟩
  · rw [hv, hm0] at hmd
    have h1 := (abs_lt.mp (lt_of_le_of_lt hmd herr')).2
    have h2 : ρ j.1 * (1 - 10001 / 5120000) < ρ j.1 * P.edge.cutoff j.1 q := by linarith
    exact lt_of_mul_lt_mul_left h2 hrj.le
  · have htri := norm_le_insert' (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q))
      (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q))
    rw [hv0, norm_sub_rev] at htri
    have h2 : ρ j.1 * (P.edge.cutoff j.1 q * |P.edge.coord j.1 q|) <
        ρ j.1 * (4 * Δ + 10001 / 5120000) := by linarith
    exact lt_of_mul_lt_mul_left h2 hrj.le

/-- **The height at a point of `V`** ((EZ) without `P₀`): in `U_j` with `|η_j| < 8Δ` and
`ζ_j > 1 − 1.0001/512`, `q ∈ V` gives `t(q) < 4.01Δ` (`z₀ = 1` for `.3Δ ≤ t ≤ 8Δ`; `t > 8Δ` is
excluded by `z₀ ≥ 3ζ_j/4`). -/
theorem vertical_height_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X} (hball : q ∈ ball j.1 (100 * Δ * ρ j.1))
    (hη8 : |P.edge.coord j.1 q| < 8 * Δ) (hζk : 1 - 10001 / 5120000 < P.edge.cutoff j.1 q)
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    P.edge.smoothing q / ρ q < 401 / 100 * Δ := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, -, hc0, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
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
    have hzlo : (1 - 10001 / 5120000) * (3 / 4) ≤ cgpEdgeMarker P.toLocalChartFamily q := by
      rw [hz]
      exact mul_le_mul hζk.le (edgeSumRamp_ge_FDC hsum) (by norm_num) (by linarith)
    have hP8 : 8 * Δ * ρ q < P.edge.smoothing q := by
      rwa [lt_div_iff₀ hrq] at ht8
    exact fdc02_height_high_numbers_FDC hΔ hrq hc0 hc2 hzlo hP8 (by linarith) hAs hsρ

/-- **FDC02's limit point** (B:7268–7276): the exact final marker `v_j(E q) = R_j`, the WEAK
bound `|u_j(E q)| ≤ 4ΔR_j` and `q ∈ V` give `q ∈ U_j`, `|η_j(q)| < 4.01Δ`, `t(q) < 4.01Δ` and
`ζ_j(q) = 1`, without assuming `q ∈ X₂`, `π₂E(q) ∈ B₂` or `W₂`, and without (JA). -/
theorem fdc02_limit_point_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) = ρ j.1)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ ≤ 4 * Δ * ρ j.1)
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| < 401 / 100 * Δ ∧
      P.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ P.edge.cutoff j.1 q = 1 := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨hball, hζk, hζη⟩ := C.exact_marker_original_FDC j hv hu
  have hη := fdc02_tangential_numbers_FDC hΔ le_rfl hζk hζη
  have hη8 : |P.edge.coord j.1 q| < 8 * Δ := by linarith
  have ht := C.vertical_height_FDC j hball hη8 hζk hV
  exact ⟨hball, hη, ht, edge_cutoff_eq_one_EDPE P hΔ0 hj hball hη8 (by linarith)⟩

/-- `p ↦ v_j(E p)` is continuous. -/
theorem continuous_edgeMarker_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) :
    Continuous fun p => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E p) :=
  (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inr (.inr (.inl j)))).continuous.comp C.stage_smooth.2.2.continuous

/-- `p ↦ |u_j(E p)|` is continuous. -/
theorem continuous_edgeVector_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) :
    Continuous fun p => ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E p)‖ :=
  ((blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inr (.inr (.inl j)))).continuous.comp C.stage_smooth.2.2.continuous).norm

/-- **FDC02's limit step, one witnessing index**: for `q_n → q` with `v_j(E q_n) = R_j`,
`|u_j(E q_n)| < 4ΔR_j`, `q_n ∈ V`, the limit has `v_j(E q) = R_j`, `|u_j(E q)| ≤ 4ΔR_j`, `q ∈ V`,
and the conclusions of `fdc02_limit_point_FDC`. -/
theorem fdc02_limit_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {qs : ℕ → X} {q : X} (hq : Tendsto qs atTop (𝓝 q))
    (hv : ∀ n, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E (qs n)) = ρ j.1)
    (hu : ∀ n, ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E (qs n))‖ < 4 * Δ * ρ j.1)
    (hV : ∀ n, qs n ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q) = ρ j.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q)‖ ≤ 4 * Δ * ρ j.1 ∧
      q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
          C.scale p ≤ 4 * Δ} ∧
      q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| < 401 / 100 * Δ ∧
      P.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ P.edge.cutoff j.1 q = 1 := by
  have hcl : IsClosed ({p | blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E p) = ρ j.1} ∩
      {p | ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E p)‖ ≤ 4 * Δ * ρ j.1} ∩
      ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
          C.scale p ≤ 4 * Δ})) :=
    ((isClosed_eq (C.continuous_edgeMarker_FDC j) continuous_const).inter
      (isClosed_le (C.continuous_edgeVector_FDC j) continuous_const)).inter
      C.isClosed_vertical_FDC
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcl.mem_of_tendsto hq
    (Eventually.of_forall fun n => ⟨⟨hv n, (hu n).le⟩, hV n⟩)
  exact ⟨h1, h2, h3, C.fdc02_limit_point_FDC j h1 h2 h3⟩

/-- **FDC02's limit step** (B:7259–7276): for `q_n → q` with witnessing edge indices `w_n`
(`v_{w_n}(E q_n) = R_{w_n}`, `|u_{w_n}(E q_n)| < 4ΔR_{w_n}`, `q_n ∈ V`), one index `j` (pigeonhole
over the finite edge family) has the limit conclusions of `fdc02_limit_FDC` at `q`. -/
theorem fdc02_limit_witness_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {qs : ℕ → X} {q : X}
    (hq : Tendsto qs atTop (𝓝 q)) (w : ℕ → P.edge.finite_centres.toFinset)
    (hv : ∀ n, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl (w n)))) (C.E (qs n)) = ρ (w n).1)
    (hu : ∀ n, ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl (w n)))) (C.E (qs n))‖ < 4 * Δ * ρ (w n).1)
    (hV : ∀ n, qs n ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    ∃ j : P.edge.finite_centres.toFinset,
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q) = ρ j.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q)‖ ≤ 4 * Δ * ρ j.1 ∧
      q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
          C.scale p ≤ 4 * Δ} ∧
      q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| < 401 / 100 * Δ ∧
      P.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ P.edge.cutoff j.1 q = 1 := by
  obtain ⟨j, -, φ, hφ, hφj⟩ := exists_strictMono_eq_of_mem_finite_FDC1 Set.finite_univ
    (w := w) (fun n => Set.mem_univ (w n))
  refine ⟨j, C.fdc02_limit_FDC j (hq.comp hφ.tendsto_atTop) (fun n => ?_) (fun n => ?_)
    (fun n => hV (φ n))⟩
  · have h := hv (φ n)
    rw [hφj n] at h
    exact h
  · have h := hu (φ n)
    rw [hφj n] at h
    exact h

/-- **FDC02's compactness, reduced to FDC01's hypotheses**: for closed `M₂` and
`S ⊆ M₂ ∩ V` whose points have a witnessing index (`v_j(E x) = R_j`, `|u_j(E x)| < 4ΔR_j`, EDP02),
if `S` contains every `x ∈ M₂ ∩ V` with `x ∈ U_i`, `|η_i(x)| ≤ 4.01Δ`, `t(x) ≤ 4.01Δ` for some edge
centre `i` (what FDC01 + BASES give), then `S` is compact. -/
theorem fdc02_isCompact_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {M₂ Sx : Set X}
    (hM₂ : IsClosed M₂)
    (hSK : Sx ⊆ M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}))
    (hwit : ∀ x ∈ Sx, ∃ j : P.edge.finite_centres.toFinset,
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E x) = ρ j.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E x)‖ < 4 * Δ * ρ j.1)
    (hrepl : ∀ x ∈ M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}), ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
      |P.edge.coord j x| ≤ 401 / 100 * Δ → P.edge.smoothing x / ρ x ≤ 401 / 100 * Δ → x ∈ Sx) :
    IsCompact Sx := by
  refine EdgeDisk.isCompact_of_weak_limit_replacement (ι := P.edge.finite_centres.toFinset)
    (hM₂.inter C.isClosed_vertical_FDC) hSK
    (fun j x => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E x))
    (fun j x => ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E x)‖)
    C.continuous_edgeMarker_FDC C.continuous_edgeVector_FDC (fun j => ρ j.1)
    (fun j => 4 * Δ * ρ j.1) (fun x hx => ?_) (fun x hx j h1 h2 => ?_)
  · obtain ⟨j, h1, h2⟩ := hwit x hx
    exact ⟨j, h1, by rwa [abs_norm]⟩
  · rw [abs_norm] at h2
    obtain ⟨hb, hη, ht, -⟩ := C.fdc02_limit_point_FDC j h1 h2 hx.2
    exact hrepl x hx j.1 ((Set.Finite.mem_toFinset _).mp j.2) hb hη.le ht.le

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
