import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf05

/-!
# GAF07 on the chain object: the interface (ratio bases, whole proper restrictions)

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6049–6165);
review 66, disposition D66-8: "GAF07 interface now, parametrized by chain + bases"; no
whole-fibre equality is claimed before GAF06/BASES exclude all extra preimages.

For `j = 1, 3` (stages `st = 0, 2`, circle and slim) GAF07's base is `B_j = W_j ∩ R_j`, where
`W_j` is the embedded base of `Gaf02Bases` (lane C14-BASES) and `R_j` the RATIO set
`⋃_i {v_i > .9R_i, |u_i| < 4ℓ_i v_i}` (`gaf07CircleRatio_G47`, `gaf07SlimRatio_G47`, `ℓ_i = 1`,
`10⁵Δ`); `X_j = (π_jE)⁻¹(B_j)`. Everything below holds for EVERY base set `W` (so for `W = W_j`
once BASES provides it) and is about ONE chain `C`, with GAF01's `c₃ = c 2 < 1/1000`:

* no extra base points (`Gaf02Chain.gaf07_marker_bounds_G47`): `v_i(E p) > .9R_i` ⇒
  `v_i(E p) < (1 + 1/800)R_i`, and the ratio threshold puts `u_i(E p)` in the `5.5ℓR_i` ball;
* the first inclusion up to `W` (`gaf07_circle_first_inclusion_G47`,
`gaf07_slim_first_inclusion_G47`):
  `|η_i(p)| ≤ 3.5ℓ_i` ⇒ `π_jE p ∈ R_j` (direct estimate `(3.5ℓ + δ)/(1 − δ) < 4ℓ`, `δ < 1/800`);
* `X_j ⊂ U_j` (`gaf07_circle_total_subset_G47`, `gaf07_slim_total_subset_G47`): EVERY point of the
  whole preimage of `R_j` has, for a witnessing index, original cutoff one and
  `|η_i| < 4.01ℓ_i < 5ℓ_i`;
* properness of the WHOLE restriction (`gaf07_proper_G47`): for every base set `B`,
  `π_jE : (π_jE)⁻¹(B) → B` is a proper map, and preimages of compact sets are compact;
* the coordinate comparison on `Y_i = {|η_i| < 5ℓ_i}` (`gaf07_circle_coordinate_G47`,
  `gaf07_slim_coordinate_G47`): `g_i = u_i(π_jE)/R_i` has `|g_i − η_i| < 1/800`, and every level
  point `h_τ(p) = a`, `|a| < 4ℓ_i`, of `h_τ = (1 − τ)η_i + τg_i` lies in `{|η_i| < 4.01ℓ_i}`.

NOT here (interface for later lanes, recorded in `state-C14-GAF47.md`): openness of `B_j`, ontoness
(CGP07–CGP08), the submersion of `π_jE` on `X_j` onto `W_j` and its local trivializations (BASES),
the fibre type and the isotopy (FC34 on the compact whole slab `Q_i`, FIBRE-PRE's
`circle_gaf07_buffer_FPRE` / `slim_gaf07_buffer_FPRE`, least singular value of `Dη_i`, smooth slim
fibre type), and the whole stage/final fibre equality (CGP08's `Θ_j`, then GAF06).
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

/-- **The first-inclusion estimate** (GAF07, B:6086–6089, without GAF05): at a full-marker block
`(u, v)(F) = (Rη, R)` with `|η| ≤ 3.5ℓ`, a point `E` with `|E − F| < c₃ρ`, `ρ ≤ 5R/4`,
`c₃ < 1/1000`, `ℓ ≥ 1` satisfies `v(E) > .9R` and `|u(E)| < 4ℓ v(E)`. -/
theorem ratio_lt_of_full_block_G47 {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (u : H →L[ℝ] W) (v : H →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) {F E : H} {η : W} {R ρ c₃ ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hc₃ : c₃ < 1 / 1000) (huF : u F = R • η) (hvF : v F = R) (hη : ‖η‖ ≤ 7 / 2 * ℓ)
    (hE : ‖E - F‖ < c₃ * ρ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 5 * R / 4) :
    9 / 10 * R < v E ∧ ‖u E‖ < 4 * ℓ * v E := by
  have hc0 : 0 < c₃ := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hρ0.le
    linarith [norm_nonneg (E - F)]
  have hd : ‖E - F‖ < R / 800 := by
    have h1 : c₃ * ρ ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ hc0.le
    have h2 : c₃ * (5 * R / 4) < 1 / 1000 * (5 * R / 4) :=
      mul_lt_mul_of_pos_right hc₃ (by linarith)
    linarith
  have hvE : |v E - R| ≤ ‖E - F‖ := by
    rw [← hvF, ← map_sub, ← Real.norm_eq_abs]
    exact (v.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hv)
  have huE : ‖u E - R • η‖ ≤ ‖E - F‖ := by
    rw [← huF, ← map_sub]
    exact (u.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  have hv1 : R - ‖E - F‖ ≤ v E := by linarith [neg_abs_le (v E - R)]
  have hu1 : ‖u E‖ ≤ R * (7 / 2 * ℓ) + ‖E - F‖ := by
    have h := norm_le_insert' (u E) (R • η)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h
    have h' : R * ‖η‖ ≤ R * (7 / 2 * ℓ) := mul_le_mul_of_nonneg_left hη hR.le
    linarith
  have hkey : ‖E - F‖ * (1 + 4 * ℓ) < ℓ * R / 2 := by
    have h1 : ‖E - F‖ * (1 + 4 * ℓ) ≤ ‖E - F‖ * (5 * ℓ) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h2 : ‖E - F‖ * (5 * ℓ) < R / 800 * (5 * ℓ) :=
      mul_lt_mul_of_pos_right hd (by linarith)
    nlinarith
  refine ⟨by linarith, ?_⟩
  have h4 : 4 * ℓ * (R - ‖E - F‖) ≤ 4 * ℓ * v E :=
    mul_le_mul_of_nonneg_left hv1 (by linarith)
  nlinarith

/-- **The coordinate comparison** (GAF07, B:6111–6125): at a full-marker block `(u, v)(F) = (Rη, R)`
with `|E − F| < c₃ρ`, `ρ ≤ 5R/4`, `c₃ < 1/1000`: `|R⁻¹u(E) − η| < 1/800`; hence a level point
`(1 − τ)η + τR⁻¹u(E) = a`, `|a| < 4ℓ`, `τ ∈ [0, 1]`, has `|η| < 4.01ℓ` (`ℓ ≥ 1`). -/
theorem coordinate_close_of_full_block_G47 {H W : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W] (u : H →L[ℝ] W) (hu : ‖u‖ ≤ 1)
    {F E : H} {η : W} {R ρ c₃ ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hc₃ : c₃ < 1 / 1000)
    (huF : u F = R • η) (hE : ‖E - F‖ < c₃ * ρ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 5 * R / 4) :
    ‖R⁻¹ • u E - η‖ < 1 / 800 ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, ∀ a : W, ‖a‖ < 4 * ℓ → (1 - τ) • η + τ • (R⁻¹ • u E) = a →
        ‖η‖ < 401 / 100 * ℓ := by
  have hc0 : 0 < c₃ := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hρ0.le
    linarith [norm_nonneg (E - F)]
  have hd : ‖E - F‖ < R / 800 := by
    have h1 : c₃ * ρ ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ hc0.le
    have h2 : c₃ * (5 * R / 4) < 1 / 1000 * (5 * R / 4) :=
      mul_lt_mul_of_pos_right hc₃ (by linarith)
    linarith
  have huE : ‖u E - R • η‖ ≤ ‖E - F‖ := by
    rw [← huF, ← map_sub]
    exact (u.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  have hclose : ‖R⁻¹ • u E - η‖ < 1 / 800 := by
    have h : R⁻¹ • u E - η = R⁻¹ • (u E - R • η) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have h1 : R⁻¹ * ‖u E - R • η‖ ≤ R⁻¹ * ‖E - F‖ :=
      mul_le_mul_of_nonneg_left huE (inv_pos.mpr hR).le
    have h2 : R⁻¹ * ‖E - F‖ < R⁻¹ * (R / 800) := mul_lt_mul_of_pos_left hd (inv_pos.mpr hR)
    have h3 : R⁻¹ * (R / 800) = 1 / 800 := by field_simp
    linarith
  refine ⟨hclose, fun τ hτ a ha hlev => ?_⟩
  have h : η = a - τ • (R⁻¹ • u E - η) := by
    rw [← hlev, smul_sub, sub_smul, one_smul]
    abel
  have h1 : ‖τ • (R⁻¹ • u E - η)‖ ≤ 1 / 800 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    have := mul_le_mul hτ.2 hclose.le (norm_nonneg _) zero_le_one
    linarith
  rw [h]
  have h2 := norm_sub_le a (τ • (R⁻¹ • u E - η))
  linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

open Classical in
/-- A block vector of a tag retained by the stage target `Q_st` is unchanged by `π_{Q_st}`. -/
theorem vector_stageQ_G47 {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
    [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {st : Fin 3} {t : CGPTag L Z}
    (ht : t ∈ gafStageTags L Z st) (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) t ((gafStageQ L Z st).starProjection y) =
      blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) t y := by
  rw [gafStageQ_starProjection, blockVectorCLM_apply, blockVectorCLM_apply, blockRestrict_apply]
  simp [ht]

/-- GAF07's RATIO set of the circle stage (`j = 1`, `ℓ_i = 1`):
`⋃_i {w | v_i(w) > .9R_i, |u_i(w)| < 4 v_i(w)}`; GAF07's base is `B₁ = W₁ ∩` this set. -/
def gaf07CircleRatio_G47 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  ⋃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
    {w | 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w}

/-- GAF07's RATIO set of the slim stage (`j = 3`, `ℓ_i = 10⁵Δ`):
`⋃_i {w | v_i(w) > .9R_i, |u_i(w)| < 4·10⁵Δ v_i(w)}`; GAF07's base is `B₃ = W₃ ∩` this set. -/
def gaf07SlimRatio_G47 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  ⋃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
    {w | 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inl i)) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w‖ <
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl i)) w}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, no extra base points, on the chain** (B:6077–6082): for every retained index `i` and
`ℓ ≥ 1`, `v_i(C.E p) > .9R_i` forces `v_i(C.E p) < (1 + 1/800)R_i`, and the ratio threshold `4ℓ`
puts `u_i(C.E p)` in the `5.5ℓR_i` ball (the chain's (AM0) at `E` and strict error). -/
theorem gaf07_marker_bounds_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000) {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (i : CGPMarkerIndex P.toLocalChartFamily) :
    ∀ p, 9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i) (C.E p) →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i) (C.E p) <
        (1 + 1 / 800) * ρ (cgpMarkerCentre P.toLocalChartFamily i) ∧
      (‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i) (C.E p)‖ <
          4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero i) (C.E p) →
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i) (C.E p)‖ <
          11 / 2 * ℓ * ρ (cgpMarkerCentre P.toLocalChartFamily i)) := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -, -, -⟩ := C.std
  exact gaf07_marker_bounds P.toLocalChartFamilyQ P.zero hΔ hσs hσs1 hΛ C.small_range_G47 C.E hc
    hℓ i (C.prefix_am0.2.2 i) C.stage_error_lt.2.2

/-- **GAF07, properness of the WHOLE restriction, on the chain** (B:6097–6102): for every stage
`st` and EVERY base set `B` (in particular GAF07's `B_j = W_j ∩ R_j` once BASES provides `W_j`),
`π_st ∘ C.E : (π_st ∘ C.E)⁻¹(B) → B` is a proper map, and the whole preimage of every compact set
is compact (`C.E` is continuous on the compact manifold). -/
theorem gaf07_proper_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (B : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    IsProperMap (B.restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p))) ∧
    ∀ Kc : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsCompact Kc →
      IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)) ⁻¹'
        Kc) := by
  have hcont : Continuous
      (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)) :=
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection.continuous.comp
      C.stage_smooth.2.2.continuous
  have hp := hcont.isProperMap
  exact ⟨hp.restrictPreimage B, fun Kc hK => hp.isCompact_preimage hK⟩

/-- The circle block of `𝓔⁰` on the circle plateau `‖η_i‖ ≤ 8`: cutoff one, `u_i = R_iη_i`,
`v_i = R_i`, and `ρ ≤ 5R_i/4`. -/
theorem circle_full_block_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 8)
        :
    P.circle.cutoff i.1 p = 1 ∧
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          (cgpGlobalMap P.toLocalChartFamily P.zero p) =
        ρ i.1 • cgpCoord P.toLocalChartFamily P.zero (.inl i) p ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          (cgpGlobalMap P.toLocalChartFamily P.zero p) = ρ i.1 ∧
      ρ p ≤ 5 * ρ i.1 / 4 := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -, -, -⟩ := C.std
  have hcut : P.circle.cutoff i.1 p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyQ P.zero i hpi hη
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inl i) p = 1 := hcut
  obtain ⟨hu, hv⟩ := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inl i) p
  rw [hcut', mul_one] at hu hv
  have hsc := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
    C.small_range_G47 (.inl i) p (by rw [hcut']; exact one_pos)
  exact ⟨hcut, hu, hv, hsc.2⟩

/-- The slim block of `𝓔⁰` on the slim plateau `|η_i| ≤ 8·10⁵Δ`: cutoff one,
`u_i = R_i·axis(η_i)`, `v_i = R_i`, and `ρ ≤ 5R_i/4`. -/
theorem slim_full_block_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 8 * (10 ^ 5 * Δ)) :
    P.slim.cutoff i.1 p = 1 ∧
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          (cgpGlobalMap P.toLocalChartFamily P.zero p) =
        ρ i.1 • planeAxis ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p) ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          (cgpGlobalMap P.toLocalChartFamily P.zero p) = ρ i.1 ∧
      ρ p ≤ 5 * ρ i.1 / 4 := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -, -, -⟩ := C.std
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hcut : P.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
    refine (P.slim.centre i.1 hj).cutoff_eq_one_of_abs_coord_le ?_ ?_
    · convert hpi using 2
      norm_num
    · linarith
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inl i)) p = 1 := hcut
  obtain ⟨hu, hv⟩ := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inr (.inl i)) p
  rw [hcut', mul_one] at hu hv
  have hsc := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
    C.small_range_G47 (.inr (.inl i)) p (by rw [hcut']; exact one_pos)
  exact ⟨hcut, hu, hv, hsc.2⟩

/-- **GAF07, first inclusion up to the base, circle stage** (B:6086–6089): at a circle point with
`‖η_i(p)‖ ≤ 3.5`, the final image `π₁E p` lies in the ratio set `R₁` (marker `> .9R_i`, ratio
`< 4`), by the direct estimate `(3.5 + δ)/(1 − δ) < 4`, `δ = (5/4)c₃ < 1/800` (no GAF05 needed). -/
theorem gaf07_circle_first_inclusion_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈ gaf07CircleRatio_G47 P := by
  obtain ⟨-, hu, hv, hsc⟩ := C.circle_full_block_G47 i hpi (by linarith)
  have key := ratio_lt_of_full_block_G47
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i))
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i))
    (norm_blockVectorCLM_le _) (norm_blockMarkerCLM_le _) (hρ i.1) le_rfl hc hu hv
    (by rw [mul_one]; exact hη) (C.stage_error_lt.2.2 p) (hρ p) hsc
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have hm := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
    (Finset.mem_univ _) (C.E p)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
    (Finset.mem_univ _) (C.E p)
  rw [mem_ofPred_eq, hm, hw]
  rw [mul_one] at key
  exact key

/-- **GAF07, first inclusion up to the base, slim stage** (B:6086–6089): at a slim point with
`|η_i(p)| ≤ 3.5·10⁵Δ`, the final image `π₃E p` lies in the ratio set `R₃`. -/
theorem gaf07_slim_first_inclusion_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 / 2 * (10 ^ 5 * Δ)) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈ gaf07SlimRatio_G47 P := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨-, hu, hv, hsc⟩ := C.slim_full_block_G47 i hpi (by nlinarith)
  have key := ratio_lt_of_full_block_G47
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    (norm_blockVectorCLM_le _) (norm_blockMarkerCLM_le _) (hρ i.1) hℓ hc hu hv
    (by rw [norm_planeAxis]; exact hη) (C.stage_error_lt.2.2 p) (hρ p) hsc
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have hm := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  rw [mem_ofPred_eq, hm, hw]
  exact key

/-- **GAF07, `X₁ ⊂ U₁`, on the chain** (B:6090–6094): EVERY point of the WHOLE preimage of the
circle
ratio set under `π₁E` has, for a witnessing index, `p ∈ B(c_i, 200ρ(c_i))`, `‖η_i(p)‖ < 4.01 < 5`
and original cutoff one (GAF06 at `τ = 1`); no source component is discarded. -/
theorem gaf07_circle_total_subset_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (p : X)
    (hp : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈ gaf07CircleRatio_G47
        P) :
    ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 ∧
      P.circle.cutoff i.1 p = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hm := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
    (Finset.mem_univ _) (C.E p)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
    (Finset.mem_univ _) (C.E p)
  rw [mem_ofPred_eq, hm, hw] at hi
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.E p =
      C.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  exact ⟨i, C.gaf06_circle_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩ (by rw [h1]; exact hi.1)
    (by rw [h1]; exact hi.2.le)⟩

/-- **GAF07, `X₃ ⊂ U₃`, on the chain** (B:6090–6094): EVERY point of the WHOLE preimage of the slim
ratio set under `π₃E` has, for a witnessing index, `p ∈ B(c_i, 10⁶Δρ(c_i))`,
`|η_i(p)| < 4.01·10⁵Δ < 5·10⁵Δ` and original cutoff one. -/
theorem gaf07_slim_total_subset_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (p : X)
    (hp : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈ gaf07SlimRatio_G47 P) :
    ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset, p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
        401 / 100 * (10 ^ 5 * Δ) ∧
      P.slim.cutoff i.1 p = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hm := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  rw [mem_ofPred_eq, hm, hw] at hi
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.E p =
      C.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  exact ⟨i, C.gaf06_slim_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩ (by rw [h1]; exact hi.1)
    (by rw [h1]; exact hi.2.le)⟩

/-- **GAF07, coordinate comparison on `Y_i`, circle stage** (B:6111–6125): on
`Y_i = {‖η_i‖ < 5} ∩ B(c_i, 200ρ(c_i))` the adjusted coordinate `g_i = R_i⁻¹u_i(π₁E)` satisfies
`‖g_i − η_i‖ < 1/800`, and every level point `h_τ(p) = a`, `‖a‖ < 4`, of
`h_τ = (1 − τ)η_i + τg_i` lies in `{‖η_i‖ < 4.01}`. -/
theorem gaf07_circle_coordinate_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 5)
        :
    ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) -
      cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 1 / 800 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℝ², ‖a‖ < 4 →
      (1 - t) • cgpCoord P.toLocalChartFamily P.zero (.inl i) p + t • ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p))) = a →
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 := by
  obtain ⟨-, hu, -, hsc⟩ := C.circle_full_block_G47 i hpi (by linarith)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
    (Finset.mem_univ _) (C.E p)
  rw [hw]
  obtain ⟨k1, k2⟩ := coordinate_close_of_full_block_G47
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i))
    (norm_blockVectorCLM_le _) (hρ i.1) le_rfl hc hu (C.stage_error_lt.2.2 p) (hρ p) hsc
  refine ⟨k1, fun t ht a ha hlev => ?_⟩
  have h := k2 t ht a (by linarith) hlev
  linarith

/-- **GAF07, coordinate comparison on `Y_i`, slim stage** (B:6111–6125): on
`Y_i = {|η_i| < 5·10⁵Δ} ∩ B(c_i, 10⁶Δρ(c_i))` the adjusted coordinate `g_i = R_i⁻¹u_i(π₃E)`
satisfies
`‖g_i − axis(η_i)‖ < 1/800`, and every level point `h_τ(p) = a`, `‖a‖ < 4·10⁵Δ`, lies in
`{|η_i| < 4.01·10⁵Δ}`. -/
theorem gaf07_slim_coordinate_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ)) :
    ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) -
      planeAxis ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)‖ < 1 / 800 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℝ², ‖a‖ < 4 * (10 ^ 5 * Δ) →
      (1 - t) • planeAxis ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p) +
          t • ((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p))) =
        a →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
        401 / 100 * (10 ^ 5 * Δ) := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨-, hu, -, hsc⟩ := C.slim_full_block_G47 i hpi (by nlinarith)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  rw [hw]
  obtain ⟨k1, k2⟩ := coordinate_close_of_full_block_G47
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    (norm_blockVectorCLM_le _) (hρ i.1) hℓ hc hu (C.stage_error_lt.2.2 p) (hρ p) hsc
  refine ⟨k1, fun t ht a ha hlev => ?_⟩
  have h := k2 t ht a ha hlev
  rwa [norm_planeAxis] at h

/-- **GAF07's interface, circle stage, for EVERY base set `W`** (to be instantiated with BASES'
embedded base `W₁`): with `B₁ = W ∩ R₁` and `X₁ = (π₁E)⁻¹(B₁)`, the slab `{‖η_i‖ ≤ 3.5}` lies in
`X₁` up to `π₁E p ∈ W`, `X₁ ⊂ U₁` (cutoff one, `‖η_i‖ < 4.01`), and `π₁E : X₁ → B₁` is proper. -/
theorem gaf07_circle_interface_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball i.1 (200 * ρ i.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2) →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈ W →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        W ∩ gaf07CircleRatio_G47 P) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        W ∩ gaf07CircleRatio_G47 P →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 ∧
        P.circle.cutoff i.1 p = 1) ∧
    IsProperMap ((W ∩ gaf07CircleRatio_G47 P).restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p))) :=
  ⟨fun p hp hW => by
      obtain ⟨i, hpi, hη⟩ := hp
      exact ⟨hW, C.gaf07_circle_first_inclusion_G47 (p := p) hc i hpi hη⟩,
    fun p hp => C.gaf07_circle_total_subset_G47 hc p hp.2, (C.gaf07_proper_G47 0 _).1⟩

/-- **GAF07's interface, slim stage, for EVERY base set `W`** (to be instantiated with BASES'
embedded base `W₃`): with `B₃ = W ∩ R₃` and `X₃ = (π₃E)⁻¹(B₃)`, the slab `{|η_i| ≤ 3.5·10⁵Δ}` lies
in `X₃` up to `π₃E p ∈ W`, `X₃ ⊂ U₃` (cutoff one, `|η_i| < 4.01·10⁵Δ`), and `π₃E : X₃ → B₃` is
proper. -/
theorem gaf07_slim_interface_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          7 / 2 * (10 ^ 5 * Δ)) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈ W →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        W ∩ gaf07SlimRatio_G47 P) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        W ∩ gaf07SlimRatio_G47 P →
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff i.1 p = 1) ∧
    IsProperMap ((W ∩ gaf07SlimRatio_G47 P).restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p))) :=
  ⟨fun p hp hW => by
      obtain ⟨i, hpi, hη⟩ := hp
      exact ⟨hW, C.gaf07_slim_first_inclusion_G47 (p := p) hc i hpi hη⟩,
    fun p hp => C.gaf07_slim_total_subset_G47 hc p hp.2, (C.gaf07_proper_G47 2 _).1⟩

end Gaf02Chain

/-- **Consumer: GAF07's interface for a chain on the final family** `LocalChartPacketsC14Z`
(projection `toLocalChartPackets`), for EVERY pair of base sets `W₁, W₃` (BASES' embedded bases):
the whole preimages `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`, `X₃ = (π₃E)⁻¹(W₃ ∩ R₃)` lie in the original threshold-5
domains with cutoff one, and contain the `3.5`-slabs over `W_j`. -/
theorem gaf07_final_family_interface_G47 {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (W₁ W₃ : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        W₁ ∩ gaf07CircleRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 5 ∧ P.circle.cutoff i.1 p = 1) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        W₃ ∩ gaf07SlimRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff i.1 p = 1) ∧
    (∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) p,
      p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2 →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈ W₁ →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        W₁ ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) ∧
    ∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) p,
      p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 / 2 * (10 ^ 5 * Δ) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈ W₃ →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        W₃ ∩ gaf07SlimRatio_G47 P.toLocalChartPackets := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have q1 := C.gaf07_circle_interface_G47 hc W₁
  have q3 := C.gaf07_slim_interface_G47 hc W₃
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun i p hpi hη hW => q1.1 p ⟨i, hpi, hη⟩ hW,
    fun i p hpi hη hW => q3.1 p ⟨i, hpi, hη⟩ hW⟩
  · obtain ⟨i, -, hη, hcut⟩ := q1.2.1 p hp
    have hη' : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 := hη
    exact ⟨i, by linarith, hcut⟩
  · obtain ⟨i, -, hη, hcut⟩ := q3.2.1 p hp
    have hη' : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
        401 / 100 * (10 ^ 5 * Δ) := hη
    have h0 : (0 : ℝ) ≤ 10 ^ 5 * Δ := by linarith
    exact ⟨i, by linarith, hcut⟩

end DifferentialGeometry.Geometry.Collapse
