import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateOrthogonalGraph
import DifferentialGeometry.Topology.FixedPoint.NearIdentityHitsCenter
import DifferentialGeometry.Geometry.Collapse.OneSheetBudget

/-!
# CGP07 on naive data: one sheet, Brouwer surjectivity, threshold-6 exhaustion, chart inverse

Blueprint `master207B.tex`, CGP07 (`thm:fibration-marked-base-one-sheet`, B:4176–4247); external
draft 59 §4, fourth and fifth steps (disposition D59-5). Everything is stated on naive data: a set
`Z ⊆ H` (the native zero set), coordinates `u : H →L E` (the vector block, `‖u‖ ≤ 1`) and
`v : H →L ℝ` (the marker), a radius `R > 0`, `ℓ`, local graphs in orthogonal-sum form with the
two-sided set equality `Z ∩ B(x, ρ) = graph ∩ B(x, ρ)`, a stage map `f`, a source map `F'`, an
inner section `s`. Nothing refers to a chain object; C14-BASES instantiates the fields.

* `markedPatch_BPRE Z u v R ℓ` (PATCH): `V_i⁰ = {w ∈ Z | v w > .9R, |u w| < 5.5ℓR}`; it is `Z ∩ O`
  with `O` open (`markedPatch_eq_inter_BPRE`, `isOpen_markedCondition_BPRE`), and `u/R` maps it into
  `B(0, 5.5ℓ)` (`mapsTo_markedPatch_BPRE`).
* Uniqueness. `injOn_zeroSet_inter_ball_of_graph_BPRE`: the two-sided set equality puts every point
  of `Z ∩ B(x, ρ)` on the one graph `G_x`, and CGP06 makes the coordinate injective there.
  `sn_proximity_BPRE` / `sn_lt_quarter_radius_BPRE` ((SN)): from a witness `y` with
  `|w - y| ≤ δR`, `u y = R s` and the rough-graph comparison `|R⁻¹y - Φ s|, |R⁻¹x - Φ a| ≤ e`
  (`‖DΦ‖ ≤ Ω` on a convex set), `|w - x| ≤ (2e + (1 + Ω)δ)R`, and under (OS) with
  `δ = (25/12)εΣ` this is `< ΣR/100 < r_x/4`. `injOn_of_local_injOn_BPRE`: all candidates over the
  same target lie in one ball on which the coordinate is injective, so it is injective on `V`.
* Surjectivity. `exists_section_coordinate_eq_BPRE` (Brouwer, any finite dimension, so also the
  one-dimensional IVT case): `H(b) = R⁻¹u(f(s b))` moves points by at most `(5/4)c ≤ r₀` on the
  closed ball, so it hits the center. `marker_gt_of_err_BPRE`: the marker stays `> .9R`.
  `cgp07_existence_BPRE`: the constructed point is a threshold-6 image in `V`.
* Exhaustion. `bijOn_and_exhaustion_BPRE`: injectivity + existence over the WHOLE ball give
  `u/R : V ≅ B(0, 5.5ℓ)` as sets and `V ⊆ f(B⁶)` (every point of `V` has a preimage in the
  ORIGINAL threshold-6 source domain), with no smaller domain substituted.
* Chart. `exists_local_section_of_graph_BPRE`: CGP06's smooth inverse on a graph gives a smooth local
  section `γ` of the coordinate through every point of `Z ∩ B(x, ρ)`.
  `exists_smooth_inverse_of_local_sections_BPRE`: a bijection `Z ∩ O → D` (`O`, `D` open) with
  smooth local sections has a global inverse `φ : E → H`, smooth on `D` (bijective local
  diffeomorphism ⇒ diffeomorphism). `isCompact_inter_preimage_BPRE`: compact sets have compact full
  preimages in `V` (properness of the chart).
* Assemblies. `cgp07_marked_patch_chart_BPRE` (graph data and (SN) containment for every target,
  existence over every target); `cgp07_existence_all_BPRE` (existence over every target from the
  inner section, the cumulative error, the scale bound and the plateau); `cgp07_one_sheet_BPRE`
  (the CGP07 statement on primitive data: rough graph `Φ` with (OS), centers `x_a` with
  `|R⁻¹x_a - Φ a| ≤ e` and `r_{x_a} ≥ (9/20)ΣR`, local graphs on `B(x_a, ρ_a)` with
  `r_{x_a}/4 ≤ ρ_a`, CGP05's (MW) witnesses for every point of `V`, and the inner-section data).

The marker condition is `v > .9R` only: GAF05's exact marker is NOT used (draft 59 §4 fifth step).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

section Patch

theorem clm_smul_apply_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (u : H →L[ℝ] E) (w : H) :
    (c • u) w = c • u w := rfl

/-- (PATCH) The marked patch `V_i⁰ = {w ∈ Z | v_i(w) > .9R_i, |u_i(w)| < 5.5ℓ_iR_i}`. -/
def markedPatch_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) : Set H :=
  {w | w ∈ Z ∧ 9 / 10 * R < v w ∧ ‖u w‖ < 11 / 2 * ℓ * R}

/-- The ambient marked condition `{v > .9R, |u| < 5.5ℓR}`. -/
def markedCondition_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) : Set H :=
  {w | 9 / 10 * R < v w ∧ ‖u w‖ < 11 / 2 * ℓ * R}

theorem markedPatch_eq_inter_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) :
    markedPatch_BPRE Z u v R ℓ = Z ∩ markedCondition_BPRE u v R ℓ := by
  ext w
  exact Iff.rfl

theorem isOpen_markedCondition_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) :
    IsOpen (markedCondition_BPRE u v R ℓ) :=
  (isOpen_lt continuous_const v.continuous).inter
    (isOpen_lt (continuous_norm.comp u.continuous) continuous_const)

/-- `u/R` maps the marked patch into the full ball `B(0, 5.5ℓ)`. -/
theorem mapsTo_markedPatch_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) {R : ℝ} (ℓ : ℝ)
    (hR : 0 < R) : MapsTo (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) := by
  intro w hw
  rw [mem_ball_zero_iff, clm_smul_apply_BPRE, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), inv_mul_lt_iff₀ hR]
  linarith [hw.2.2]

end Patch

section Uniqueness

/-- **Same-graph uniqueness.** If the two-sided set equality puts `Z ∩ B(x, ρ)` on the graph of
`g : L → Lᗮ` over `B_L(0, R₀)` and CGP06's hypotheses hold, the coordinate is injective on
`Z ∩ B(x, ρ)`. -/
theorem injOn_zeroSet_inter_ball_of_graph_BPRE {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Set H) (L : Submodule ℝ H) (π : H →L[ℝ] E)
    (hπ : ‖π‖ ≤ 1) {m a R₀ ρ : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m) (g : L → Lᗮ)
    (hg : ∀ t ∈ ball (0 : L) R₀, DifferentiableAt ℝ g t)
    (hDg : ∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ a) (x : H)
    (hZ : Z ∩ ball x ρ = {z | ∃ t ∈ ball (0 : L) R₀, z = x + orthogonalCoordinateSum L (t, g t)} ∩
      ball x ρ) :
    InjOn π (Z ∩ ball x ρ) := by
  have hinj := injOn_retained_coordinate_graph L π hπ hm hma (fun s : L => ((g s : Lᗮ) : H))
    (fun t ht => Lᗮ.subtypeL.differentiableAt.comp t (hg t ht))
    (fun t ht => (norm_fderiv_coe_le_BPRE L g (hg t ht)).trans (hDg t ht)) x
  intro w₁ h₁ w₂ h₂ heq
  rw [hZ] at h₁ h₂
  obtain ⟨⟨t₁, ht₁, rfl⟩, -⟩ := h₁
  obtain ⟨⟨t₂, ht₂, rfl⟩, -⟩ := h₂
  have h := hinj ht₁ ht₂ (by
    simp only [← orthogonalGraph_apply_BPRE]
    exact heq)
  rw [h]

/-- **(SN), triangle form.** A witness `y` with `|w - y| ≤ δR`, `u y = R s`, `u w = R a`, and the
rough graph `Φ` (slope `≤ Ω` on a convex set containing `s, a`) with `|R⁻¹y - Φ s| ≤ e`,
`|R⁻¹x - Φ a| ≤ e`, give `|w - x| ≤ (2e + (1 + Ω)δ)R`. -/
theorem sn_proximity_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → H} {C : Set E} (hC : Convex ℝ C) {Ω e δ R : ℝ} (hR : 0 < R)
    (hΦ : ∀ b ∈ C, DifferentiableAt ℝ Φ b) (hDΦ : ∀ b ∈ C, ‖fderiv ℝ Φ b‖ ≤ Ω)
    (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) {w y x : H} {s a : E} (hs : s ∈ C) (ha : a ∈ C)
    (hy : ‖R⁻¹ • y - Φ s‖ ≤ e) (hx : ‖R⁻¹ • x - Φ a‖ ≤ e)
    (huy : u y = R • s) (huw : u w = R • a) (hwy : ‖w - y‖ ≤ δ * R) :
    ‖w - x‖ ≤ (2 * e + (1 + Ω) * δ) * R := by
  have hΩ0 : 0 ≤ Ω := (norm_nonneg _).trans (hDΦ a ha)
  have hsa : ‖s - a‖ ≤ δ := by
    have h1 : R • (s - a) = u (y - w) := by rw [map_sub, huy, huw, smul_sub]
    have h2 : R * ‖s - a‖ ≤ δ * R := by
      have := congrArg norm h1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [this]
      refine (u.le_opNorm _).trans ?_
      rw [norm_sub_rev]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans hwy
    nlinarith
  have hΦsa : ‖Φ s - Φ a‖ ≤ Ω * δ :=
    (hC.norm_image_sub_le_of_norm_fderiv_le hΦ hDΦ ha hs).trans
      (mul_le_mul_of_nonneg_left hsa hΩ0)
  have hyx : ‖R⁻¹ • y - R⁻¹ • x‖ ≤ 2 * e + Ω * δ := by
    have hsplit : R⁻¹ • y - R⁻¹ • x = (R⁻¹ • y - Φ s) + (Φ s - Φ a) - (R⁻¹ • x - Φ a) := by abel
    rw [hsplit]
    have h1 := norm_sub_le ((R⁻¹ • y - Φ s) + (Φ s - Φ a)) (R⁻¹ • x - Φ a)
    have h2 := norm_add_le (R⁻¹ • y - Φ s) (Φ s - Φ a)
    linarith
  have hyx' : ‖y - x‖ ≤ (2 * e + Ω * δ) * R := by
    have h := hyx
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      inv_mul_le_iff₀ hR] at h
    linarith
  calc ‖w - x‖ = ‖(w - y) + (y - x)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖w - y‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ δ * R + (2 * e + Ω * δ) * R := add_le_add hwy hyx'
    _ = (2 * e + (1 + Ω) * δ) * R := by ring

/-- **(SN) under (OS).** With `δ = (25/12)εΣ`, `Ω ≥ 1`, `e ≤ Σ/1000`, `0 ≤ ε ≤ 1/(1000(Ω+1))` and
`r_x ≥ (9/20)ΣR`, every such candidate satisfies `|w - x| < ΣR/100 < r_x/4`. -/
theorem sn_lt_quarter_radius_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → H} {C : Set E} (hC : Convex ℝ C) {Ω e ε S R rx : ℝ}
    (hR : 0 < R) (hΦ : ∀ b ∈ C, DifferentiableAt ℝ Φ b) (hDΦ : ∀ b ∈ C, ‖fderiv ℝ Φ b‖ ≤ Ω)
    (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) {w y x : H} {s a : E} (hs : s ∈ C) (ha : a ∈ C)
    (hy : ‖R⁻¹ • y - Φ s‖ ≤ e) (hx : ‖R⁻¹ • x - Φ a‖ ≤ e)
    (huy : u y = R • s) (huw : u w = R • a) (hwy : ‖w - y‖ ≤ 25 / 12 * ε * S * R)
    (hΩ : 1 ≤ Ω) (hS : 0 < S) (he : e ≤ S / 1000) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (1000 * (Ω + 1))) (hrx : 9 / 20 * S * R ≤ rx) :
    ‖w - x‖ < S * R / 100 ∧ S * R / 100 < rx / 4 := by
  have h := sn_proximity_BPRE hC hR hΦ hDΦ u hu hs ha hy hx huy huw
    (δ := 25 / 12 * ε * S) (by linarith)
  obtain ⟨h1, h2, -⟩ := one_sheet_proximity_budget hΩ hS hR he hε0 hε hrx
  refine ⟨lt_of_le_of_lt h ?_, h2⟩
  calc (2 * e + (1 + Ω) * (25 / 12 * ε * S)) * R = (2 * e + 25 / 12 * (1 + Ω) * ε * S) * R := by
        ring
    _ < S * R / 100 := h1

/-- **No second sheet.** If every two candidates over the same target lie in one ball on which the
coordinate is injective, the coordinate is injective on `V ⊆ Z`. -/
theorem injOn_of_local_injOn_BPRE {H α : Type*} [PseudoMetricSpace H] (V Z : Set H) (hVZ : V ⊆ Z) (κ : H → α)
    (hloc : ∀ w ∈ V, ∃ x : H, ∃ ρ : ℝ, InjOn κ (Z ∩ ball x ρ) ∧
      ∀ w' ∈ V, κ w' = κ w → w' ∈ ball x ρ) :
    InjOn κ V := by
  intro w₁ h₁ w₂ h₂ heq
  obtain ⟨x, ρ, hinj, hball⟩ := hloc w₁ h₁
  exact hinj ⟨hVZ h₁, hball w₁ h₁ rfl⟩ ⟨hVZ h₂, hball w₂ h₂ heq.symm⟩ heq

end Uniqueness

section Existence

/-- **CGP07 existence (Brouwer / IVT).** On the closed ball of radius `r₀ ≥ (5/4)c` about `a`, the
map `H(b) = R⁻¹u(f(s b))` moves points by at most `(5/4)c`, because `u(F'(s b)) = R b`, the
cumulative error is `≤ cρ` and `ρ ≤ (5/4)R` there. Hence `u(f(s b)) = R a` for some `b`. -/
theorem exists_section_coordinate_eq_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {M : Type*} (f F' : M → H) (s : E → M)
    (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) (ρ : M → ℝ) {R c r₀ : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (a : E)
    (hcont : ContinuousOn (fun b => f (s b)) (closedBall a r₀))
    (hsec : ∀ b ∈ closedBall a r₀, u (F' (s b)) = R • b)
    (herr : ∀ b ∈ closedBall a r₀, ‖f (s b) - F' (s b)‖ ≤ c * ρ (s b))
    (hρ : ∀ b ∈ closedBall a r₀, ρ (s b) ≤ 5 / 4 * R) (hsmall : 5 / 4 * c ≤ r₀) :
    ∃ b ∈ closedBall a r₀, u (f (s b)) = R • a := by
  have hr₀ : 0 ≤ r₀ := le_trans (by positivity) hsmall
  have hHc : ContinuousOn (fun b => R⁻¹ • u (f (s b))) (closedBall a r₀) :=
    continuousOn_const.smul (u.continuous.comp_continuousOn hcont)
  have hnear : ∀ b ∈ closedBall a r₀, ‖R⁻¹ • u (f (s b)) - b‖ ≤ r₀ := by
    intro b hb
    have hb' : b = R⁻¹ • u (F' (s b)) := by
      rw [hsec b hb, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    have h1 : ‖R⁻¹ • u (f (s b)) - b‖ = R⁻¹ * ‖u (f (s b) - F' (s b))‖ := by
      have h0 : R⁻¹ • u (f (s b)) - b = R⁻¹ • u (f (s b) - F' (s b)) := by
        rw [map_sub, smul_sub, ← hb']
      rw [h0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have h2 : ‖u (f (s b) - F' (s b))‖ ≤ c * (5 / 4 * R) :=
      (u.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hu).trans
        ((herr b hb).trans (mul_le_mul_of_nonneg_left (hρ b hb) hc)))
    rw [h1, inv_mul_le_iff₀ hR]
    nlinarith
  obtain ⟨b, hb, hHb⟩ := DifferentialGeometry.Topology.FixedPoint.exists_eq_center_of_norm_sub_le
    (fun b => R⁻¹ • u (f (s b))) hr₀ hHc hnear
  refine ⟨b, hb, ?_⟩
  have h := congrArg (fun z => R • z) hHb
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using h

/-- The marker stays above `.9R`: `v(F'(p)) = R`, `‖v‖ ≤ 1`, error `≤ cρ ≤ (5/4)cR`,
`(5/4)c < 1/10`. -/
theorem marker_gt_of_err_BPRE {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : Type*} (f F' : M → H) (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1)
    (ρ : M → ℝ) {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) {p : M} (hvF : v (F' p) = R)
    (herr : ‖f p - F' p‖ ≤ c * ρ p) (hρ : ρ p ≤ 5 / 4 * R) (hsmall : 5 / 4 * c < 1 / 10) :
    9 / 10 * R < v (f p) := by
  have h1 : |v (f p) - v (F' p)| ≤ c * (5 / 4 * R) := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact (v.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hv).trans
      (herr.trans (mul_le_mul_of_nonneg_left hρ hc)))
  have h2 := neg_abs_le (v (f p) - v (F' p))
  rw [hvF] at h1 h2
  nlinarith

/-- **CGP07 existence, the constructed point is a threshold-6 image in `V`.** For a target `a` of
the full ball `B(0, 5.5ℓ)`, the inner section `s` on `closedBall a r₀` (values `u = R b`,
marker `v = R` for the source map `F'`), cumulative error `≤ cρ`, `ρ ≤ (5/4)R`, the plateau
(`s b ∈ B⁶` and `f(s b) ∈ Z`, i.e. (PLAT)) and `(5/4)c ≤ r₀`, `(5/4)c < 1/10` give a point of the
ORIGINAL threshold-6 domain whose image lies in the marked patch with coordinate `a`. -/
theorem cgp07_existence_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {M : Type*} (Z : Set H) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1)
    (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1) (f F' : M → H) (s : E → M) (ρ : M → ℝ) (B6 : Set M)
    {R ℓ c r₀ : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hsmall : 5 / 4 * c ≤ r₀)
    (hsmall' : 5 / 4 * c < 1 / 10) {a : E} (ha : a ∈ ball (0 : E) (11 / 2 * ℓ))
    (hcont : ContinuousOn (fun b => f (s b)) (closedBall a r₀))
    (hsec : ∀ b ∈ closedBall a r₀, u (F' (s b)) = R • b ∧ v (F' (s b)) = R)
    (herr : ∀ b ∈ closedBall a r₀, ‖f (s b) - F' (s b)‖ ≤ c * ρ (s b))
    (hρ : ∀ b ∈ closedBall a r₀, ρ (s b) ≤ 5 / 4 * R)
    (hplat : ∀ b ∈ closedBall a r₀, s b ∈ B6 ∧ f (s b) ∈ Z) :
    ∃ p ∈ B6, f p ∈ markedPatch_BPRE Z u v R ℓ ∧ (R⁻¹ • u) (f p) = a := by
  obtain ⟨b, hb, hub⟩ := exists_section_coordinate_eq_BPRE f F' s u hu ρ hR hc a hcont
    (fun b hb => (hsec b hb).1) herr hρ hsmall
  refine ⟨s b, (hplat b hb).1, ⟨(hplat b hb).2,
    marker_gt_of_err_BPRE f F' v hv ρ hR hc (hsec b hb).2 (herr b hb) (hρ b hb) hsmall', ?_⟩, ?_⟩
  · rw [hub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    rw [mem_ball_zero_iff] at ha
    nlinarith
  · rw [clm_smul_apply_BPRE, hub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

/-- **Threshold-6 exhaustion.** Injectivity on `V`, `κ(V) ⊆ D` and, for EVERY target of `D`, a
source point of `B⁶` whose image lies in `V` over that target, give `κ : V → D` bijective and
`V ⊆ f(B⁶)`: every point of the whole marked patch has a preimage in the original threshold-6
domain. -/
theorem bijOn_and_exhaustion_BPRE {H M α : Type*} (V : Set H) (κ : H → α) (D : Set α) (f : M → H)
    (B6 : Set M) (hinj : InjOn κ V) (hmaps : MapsTo κ V D)
    (hex : ∀ a ∈ D, ∃ p ∈ B6, f p ∈ V ∧ κ (f p) = a) :
    BijOn κ V D ∧ ∀ w ∈ V, ∃ p ∈ B6, f p = w := by
  refine ⟨⟨hmaps, hinj, fun a ha => ?_⟩, fun w hw => ?_⟩
  · obtain ⟨p, -, hpV, hpa⟩ := hex a ha
    exact ⟨f p, hpV, hpa⟩
  · obtain ⟨p, hp, hpV, hpa⟩ := hex (κ w) (hmaps hw)
    exact ⟨p, hp, hinj hpV hw hpa⟩

end Existence

section Chart

/-- **Local smooth section from one graph.** Under CGP06's hypotheses and the two-sided set
equality on `B(x, ρ)`, through every `w ∈ Z ∩ B(x, ρ)` the coordinate `R⁻¹π` has a smooth local
section with values in `Z`. -/
theorem exists_local_section_of_graph_BPRE {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Z : Set H) (L : Submodule ℝ H) (π : H →L[ℝ] E)
    (hπ : ‖π‖ ≤ 1) {m a R₀ ρ R : ℝ} (hR : 0 < R) (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ E) (g : L → Lᗮ)
    (hg : ContDiffOn ℝ ∞ g (ball 0 R₀)) (hDg : ∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ a)
    (x : H)
    (hZ : Z ∩ ball x ρ = {z | ∃ t ∈ ball (0 : L) R₀, z = x + orthogonalCoordinateSum L (t, g t)} ∩
      ball x ρ)
    {w : H} (hw : w ∈ Z ∩ ball x ρ) :
    ∃ U : Set E, IsOpen U ∧ (R⁻¹ • π) w ∈ U ∧ ∃ γ : E → H, ContDiffOn ℝ ∞ γ U ∧
      (∀ b ∈ U, γ b ∈ Z ∧ (R⁻¹ • π) (γ b) = b) ∧ γ ((R⁻¹ • π) w) = w := by
  obtain ⟨-, -, hopen, σ, hinv, hσ⟩ := cgp06_orthogonal_graph_BPRE L π hπ hm hma hdim g hg hDg x
  set G : L → H := fun t => x + orthogonalCoordinateSum L (t, g t) with hGdef
  set P : Set E := (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R₀ with hP
  have hG : ContDiffOn ℝ ∞ G (ball 0 R₀) :=
    contDiffOn_const.add ((orthogonalCoordinateSum L).contDiff.comp_contDiffOn
      (contDiffOn_id.prodMk hg))
  have hσmaps : MapsTo σ P (ball 0 R₀) := by
    rintro y ⟨t, ht, rfl⟩
    rw [hinv.1 ht]
    exact ht
  have hGσ : ContDiffOn ℝ ∞ (fun y => G (σ y)) P := hG.comp hσ hσmaps
  have hopen' : IsOpen (P ∩ (fun y => G (σ y)) ⁻¹' ball x ρ) :=
    hGσ.continuousOn.isOpen_inter_preimage hopen isOpen_ball
  set U : Set E := (fun b : E => R • b) ⁻¹' (P ∩ (fun y => G (σ y)) ⁻¹' ball x ρ) with hU
  have hUo : IsOpen U := hopen'.preimage (continuous_const_smul R)
  have hRR (b : H) : R • (R⁻¹ • π) b = π b := by
    rw [clm_smul_apply_BPRE, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hw' := hw
  rw [hZ] at hw'
  obtain ⟨⟨t₀, ht₀, hwt⟩, -⟩ := hw'
  have hσw : σ (π w) = t₀ := by
    rw [hwt]
    exact hinv.1 ht₀
  refine ⟨U, hUo, ?_, fun b => G (σ (R • b)), ?_, fun b hb => ?_, ?_⟩
  · change R • (R⁻¹ • π) w ∈ P ∩ (fun y => G (σ y)) ⁻¹' ball x ρ
    rw [hRR]
    refine ⟨⟨t₀, ht₀, hwt ▸ rfl⟩, ?_⟩
    change G (σ (π w)) ∈ ball x ρ
    rw [hσw]
    change x + orthogonalCoordinateSum L (t₀, g t₀) ∈ ball x ρ
    rw [← hwt]
    exact hw.2
  · exact hGσ.comp (contDiff_const_smul R).contDiffOn (fun b hb => hb.1)
  · have hbP : R • b ∈ P := hb.1
    have hball : G (σ (R • b)) ∈ ball x ρ := hb.2
    have hZmem : G (σ (R • b)) ∈ Z ∩ ball x ρ := by
      rw [hZ]
      exact ⟨⟨σ (R • b), hσmaps hbP, rfl⟩, hball⟩
    refine ⟨hZmem.1, ?_⟩
    rw [clm_smul_apply_BPRE]
    change R⁻¹ • π (x + orthogonalCoordinateSum L (σ (R • b), g (σ (R • b)))) = b
    have h2 : π (x + orthogonalCoordinateSum L (σ (R • b), g (σ (R • b)))) = R • b := hinv.2 hbP
    rw [h2, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  · change G (σ (R • (R⁻¹ • π) w)) = w
    rw [hRR, hσw, hwt]

/-- **Chart (bijective local diffeomorphism ⇒ diffeomorphism).** If `κ` is a bijection from
`Z ∩ O` (`O` open) onto an open `D`, and through every point of `Z ∩ O` it has a smooth local
section with values in `Z`, then its inverse `φ : E → H` is smooth on `D`. -/
theorem exists_smooth_inverse_of_local_sections_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z O : Set H) (hO : IsOpen O) (κ : H → E)
    (D : Set E) (hD : IsOpen D) (hbij : BijOn κ (Z ∩ O) D)
    (hloc : ∀ w ∈ Z ∩ O, ∃ U : Set E, IsOpen U ∧ κ w ∈ U ∧ ∃ γ : E → H, ContDiffOn ℝ ∞ γ U ∧
      (∀ b ∈ U, γ b ∈ Z ∧ κ (γ b) = b) ∧ γ (κ w) = w) :
    ∃ φ : E → H, ContDiffOn ℝ ∞ φ D ∧ InvOn φ κ (Z ∩ O) D ∧ MapsTo φ D (Z ∩ O) := by
  set φ : E → H := invFunOn κ (Z ∩ O) with hφ
  have hinv : InvOn φ κ (Z ∩ O) D := hbij.invOn_invFunOn
  have hmaps : MapsTo φ D (Z ∩ O) := fun b hb => invFunOn_mem (hbij.surjOn hb)
  refine ⟨φ, fun b hb => ?_, hinv, hmaps⟩
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨U, hU, hbU, γ, hγ, hγZ, hγw⟩ := hloc (φ b) (hmaps hb)
  rw [hinv.2 hb] at hbU hγw
  have hγb : ContDiffAt ℝ ∞ γ b := hγ.contDiffAt (hU.mem_nhds hbU)
  have hγO : ∀ᶠ b' in 𝓝 b, γ b' ∈ O :=
    hγb.continuousAt.preimage_mem_nhds (hO.mem_nhds (hγw ▸ (hmaps hb).2))
  have heq : φ =ᶠ[𝓝 b] γ := by
    filter_upwards [hU.mem_nhds hbU, hD.mem_nhds hb, hγO] with b' hb'U hb'D hb'O
    have h1 : γ b' ∈ Z ∩ O := ⟨(hγZ b' hb'U).1, hb'O⟩
    exact hbij.injOn (hmaps hb'D) h1 ((hinv.2 hb'D).trans (hγZ b' hb'U).2.symm)
  exact hγb.congr_of_eventuallyEq heq

/-- **Properness of the chart.** For a continuous inverse `φ` on `D`, compact subsets of `D` have
compact full preimages in `V`. -/
theorem isCompact_inter_preimage_BPRE {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
    (V : Set H) (κ : H → E) (D : Set E) (φ : E → H)
    (hφ : ContinuousOn φ D) (hinv : InvOn φ κ V D) (hmaps : MapsTo φ D V) {K : Set E}
    (hKD : K ⊆ D) (hK : IsCompact K) : IsCompact (V ∩ κ ⁻¹' K) := by
  have heq : V ∩ κ ⁻¹' K = φ '' K := by
    ext w
    constructor
    · rintro ⟨hw, hwK⟩
      exact ⟨κ w, hwK, hinv.1 hw⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hmaps (hKD hb), by rw [mem_preimage, hinv.2 (hKD hb)]; exact hb⟩
  rw [heq]
  exact hK.image_of_continuousOn (hφ.mono hKD)

end Chart

section Assembly

/-- **CGP07 on naive data (assembly).** For every target `a` of the full ball `B(0, 5.5ℓ)` suppose
there is a local graph (orthogonal-sum form over `L` with CGP06's hypotheses for the coordinate `u`,
the two-sided set equality on `B(x, ρ)`) containing every candidate of `V = V_i⁰` over `a` ((SN)
containment), and a source point of the threshold-6 domain `B⁶` whose image is in `V` over `a`.
Then `u/R : V → B(0, 5.5ℓ)` is bijective, `V ⊆ f(B⁶)`, its inverse is smooth on the ball, and
compact subsets of the ball have compact preimages in `V`. -/
theorem cgp07_marked_patch_chart_BPRE {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type*} (Z : Set H) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1)
    (v : H →L[ℝ] ℝ) {R ℓ : ℝ} (hR : 0 < R) (f : M → H) (B6 : Set M)
    (hgraph : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∃ (x : H) (ρ R₀ m s : ℝ) (L : Submodule ℝ H)
      (g : L → Lᗮ), (∀ v' ∈ L, m * ‖v'‖ ≤ ‖u v'‖) ∧ s < m ∧
      Module.finrank ℝ L = Module.finrank ℝ E ∧ ContDiffOn ℝ ∞ g (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ s) ∧
      Z ∩ ball x ρ =
        {z | ∃ t ∈ ball (0 : L) R₀, z = x + orthogonalCoordinateSum L (t, g t)} ∩ ball x ρ ∧
      ∀ w ∈ markedPatch_BPRE Z u v R ℓ, (R⁻¹ • u) w = a → w ∈ ball x ρ)
    (hex : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ),
      ∃ p ∈ B6, f p ∈ markedPatch_BPRE Z u v R ℓ ∧ (R⁻¹ • u) (f p) = a) :
    BijOn (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
    (∀ w ∈ markedPatch_BPRE Z u v R ℓ, ∃ p ∈ B6, f p = w) ∧
    ∃ φ : E → H, ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * ℓ)) ∧
      InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
      MapsTo φ (ball 0 (11 / 2 * ℓ)) (markedPatch_BPRE Z u v R ℓ) ∧
      ∀ K ⊆ ball (0 : E) (11 / 2 * ℓ), IsCompact K →
        IsCompact (markedPatch_BPRE Z u v R ℓ ∩ (R⁻¹ • u) ⁻¹' K) := by
  set V := markedPatch_BPRE Z u v R ℓ with hV
  have hmapsV := mapsTo_markedPatch_BPRE Z u v ℓ hR
  have hVZ : V ⊆ Z := fun w hw => hw.1
  -- uniqueness: all candidates over one target lie on one graph
  have hinj : InjOn (R⁻¹ • u) V := by
    refine injOn_of_local_injOn_BPRE V Z hVZ _ fun w hw => ?_
    obtain ⟨x, ρ, R₀, m, s, L, g, hm, hsm, -, hg, hDg, hZ, hball⟩ := hgraph _ (hmapsV hw)
    refine ⟨x, ρ, ?_, fun w' hw' h => hball w' hw' h⟩
    have hu' := injOn_zeroSet_inter_ball_of_graph_BPRE Z L u hu hm hsm g
      (fun t ht => (hg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)) hDg x hZ
    intro w₁ h₁ w₂ h₂ h12
    refine hu' h₁ h₂ ?_
    have h := congrArg (fun z => R • z) h12
    simpa only [clm_smul_apply_BPRE, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      using h
  obtain ⟨hbij, hexh⟩ := bijOn_and_exhaustion_BPRE V (R⁻¹ • u) _ f B6 hinj hmapsV hex
  -- chart: local sections from the graphs
  have hloc : ∀ w ∈ Z ∩ markedCondition_BPRE u v R ℓ, ∃ U : Set E, IsOpen U ∧ (R⁻¹ • u) w ∈ U ∧
      ∃ γ : E → H, ContDiffOn ℝ ∞ γ U ∧ (∀ b ∈ U, γ b ∈ Z ∧ (R⁻¹ • u) (γ b) = b) ∧
        γ ((R⁻¹ • u) w) = w := by
    intro w hw
    rw [← markedPatch_eq_inter_BPRE] at hw
    obtain ⟨x, ρ, R₀, m, s, L, g, hm, hsm, hdim, hg, hDg, hZ, hball⟩ := hgraph _ (hmapsV hw)
    exact exists_local_section_of_graph_BPRE Z L u hu hR hm hsm hdim g hg hDg x hZ
      ⟨hw.1, hball w hw rfl⟩
  rw [hV, markedPatch_eq_inter_BPRE] at hbij
  obtain ⟨φ, hφ, hinvφ, hmapsφ⟩ := exists_smooth_inverse_of_local_sections_BPRE Z _
    (isOpen_markedCondition_BPRE u v R ℓ) (R⁻¹ • u) _ isOpen_ball hbij hloc
  rw [← markedPatch_eq_inter_BPRE] at hinvφ hmapsφ hbij
  refine ⟨hbij, hexh, φ, hφ, hinvφ, hmapsφ, fun K hKD hK => ?_⟩
  exact isCompact_inter_preimage_BPRE V _ _ φ hφ.continuousOn hinvφ hmapsφ hKD hK

/-- Existence over every target from the inner section (the hypothesis `hex` of the assembly):
`cgp07_existence_BPRE` for every `a ∈ B(0, 5.5ℓ)`. -/
theorem cgp07_existence_all_BPRE {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {M : Type*} (Z : Set H) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1)
    (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1) (f F' : M → H) (s : E → M) (ρ : M → ℝ) (B6 : Set M)
    {R ℓ c r₀ : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hsmall : 5 / 4 * c ≤ r₀)
    (hsmall' : 5 / 4 * c < 1 / 10)
    (hcont : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ContinuousOn (fun b => f (s b)) (closedBall a r₀))
    (hsec : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀,
      u (F' (s b)) = R • b ∧ v (F' (s b)) = R)
    (herr : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀,
      ‖f (s b) - F' (s b)‖ ≤ c * ρ (s b))
    (hρ : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀, ρ (s b) ≤ 5 / 4 * R)
    (hplat : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀, s b ∈ B6 ∧ f (s b) ∈ Z) :
    ∀ a ∈ ball (0 : E) (11 / 2 * ℓ),
      ∃ p ∈ B6, f p ∈ markedPatch_BPRE Z u v R ℓ ∧ (R⁻¹ • u) (f p) = a := fun a ha =>
  cgp07_existence_BPRE Z u hu v hv f F' s ρ B6 hR hc hsmall hsmall' ha (hcont a ha) (hsec a ha)
    (herr a ha) (hρ a ha) (hplat a ha)

/-- **CGP07 on primitive data.** Rough graph `Φ` (slope `≤ Ω` on a convex `C`), (OS)
`Ω ≥ 1`, `e ≤ Σ/1000`, `0 ≤ ε ≤ 1/(1000(Ω+1))`; for every target `a ∈ B(0, 5.5ℓ)` a center `x a`
with `a ∈ C`, `|R⁻¹ x a - Φ a| ≤ e`, `r(a) ≥ (9/20)ΣR`, `r(a)/4 ≤ ρ(a)`, and a local graph (CGP06's
hypotheses for `u`, two-sided set equality on `B(x a, ρ a)`); CGP05's (MW) witness for every point of
`V = V_i⁰`; and the inner-section data on the closed balls `B̄(a, r₀)` (values, cumulative error,
scale, plateau). Then `u/R : V → B(0, 5.5ℓ)` is bijective, `V ⊆ f(B⁶)`, the inverse is smooth on the
ball and compact sets have compact preimages in `V`. -/
theorem cgp07_one_sheet_BPRE {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} (Z : Set H) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1)
    {R ℓ Ω e ε S c r₀ : ℝ} (hR : 0 < R) (hΩ : 1 ≤ Ω) (hS : 0 < S) (he : e ≤ S / 1000)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (1000 * (Ω + 1)))
    (Φ : E → H) {C : Set E} (hC : Convex ℝ C) (hΦ : ∀ b ∈ C, DifferentiableAt ℝ Φ b)
    (hDΦ : ∀ b ∈ C, ‖fderiv ℝ Φ b‖ ≤ Ω) (x : E → H) (rx ρ : E → ℝ)
    (hxC : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), a ∈ C ∧ ‖R⁻¹ • x a - Φ a‖ ≤ e ∧
      9 / 20 * S * R ≤ rx a ∧ rx a / 4 ≤ ρ a)
    (hgraph : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∃ (R₀ m sl : ℝ) (L : Submodule ℝ H)
      (g : L → Lᗮ), (∀ v' ∈ L, m * ‖v'‖ ≤ ‖u v'‖) ∧ sl < m ∧
      Module.finrank ℝ L = Module.finrank ℝ E ∧ ContDiffOn ℝ ∞ g (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ sl) ∧
      Z ∩ ball (x a) (ρ a) =
        {z | ∃ t ∈ ball (0 : L) R₀, z = x a + orthogonalCoordinateSum L (t, g t)} ∩
          ball (x a) (ρ a))
    (hMW : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, ∃ (y : H) (sw : E), sw ∈ C ∧
      ‖R⁻¹ • y - Φ sw‖ ≤ e ∧ u y = R • sw ∧ ‖w - y‖ ≤ 25 / 12 * ε * S * R)
    (f F' : M → H) (sec : E → M) (ρM : M → ℝ) (B6 : Set M) (hc : 0 ≤ c)
    (hsmall : 5 / 4 * c ≤ r₀) (hsmall' : 5 / 4 * c < 1 / 10)
    (hcont : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ),
      ContinuousOn (fun b => f (sec b)) (closedBall a r₀))
    (hsec : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀,
      u (F' (sec b)) = R • b ∧ v (F' (sec b)) = R)
    (herr : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀,
      ‖f (sec b) - F' (sec b)‖ ≤ c * ρM (sec b))
    (hρ : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀, ρM (sec b) ≤ 5 / 4 * R)
    (hplat : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a r₀,
      sec b ∈ B6 ∧ f (sec b) ∈ Z) :
    BijOn (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
    (∀ w ∈ markedPatch_BPRE Z u v R ℓ, ∃ p ∈ B6, f p = w) ∧
    ∃ φ : E → H, ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * ℓ)) ∧
      InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
      MapsTo φ (ball 0 (11 / 2 * ℓ)) (markedPatch_BPRE Z u v R ℓ) ∧
      ∀ K ⊆ ball (0 : E) (11 / 2 * ℓ), IsCompact K →
        IsCompact (markedPatch_BPRE Z u v R ℓ ∩ (R⁻¹ • u) ⁻¹' K) := by
  have hex := cgp07_existence_all_BPRE Z u hu v hv f F' sec ρM B6 hR hc hsmall hsmall' hcont
    hsec herr hρ hplat
  refine cgp07_marked_patch_chart_BPRE Z u hu v hR f B6 (fun a ha => ?_) hex
  obtain ⟨haC, hxa, hrx, hrρ⟩ := hxC a ha
  obtain ⟨R₀, m, sl, L, g, hm, hsm, hdim, hg, hDg, hZ⟩ := hgraph a ha
  refine ⟨x a, ρ a, R₀, m, sl, L, g, hm, hsm, hdim, hg, hDg, hZ, fun w hw hwa => ?_⟩
  obtain ⟨y, sw, hsw, hy, huy, hwy⟩ := hMW w hw
  have huw : u w = R • a := by
    have h := congrArg (fun z => R • z) hwa
    simpa only [clm_smul_apply_BPRE, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using h
  obtain ⟨h1, h2⟩ := sn_lt_quarter_radius_BPRE hC hR hΦ hDΦ u hu hsw haC hy hxa huy huw hwy hΩ hS
    he hε0 hε hrx
  rw [mem_ball, dist_eq_norm]
  linarith

end Assembly

end DifferentialGeometry.Geometry.Collapse
