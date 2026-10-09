import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarSingularMargin

/-!
# The surjective co-norm of the collar pair at the anchor scale (review 50, item B)

Lane C14-EDP6 (blueprint 207B, EDP03 collar clause B:6862–6865 and its proof B:6938–6946, used in
EDP04 B:6988–6995 and EDP06 B:7124–7127; external review 50 item B, lead decision T50-3).

`J = (η, F/ρ) : M → ℝ²` has a kernel, so the consumable lower bound is on the SURJECTIVE co-norm
`inf_{‖ξ‖ = 1} sup_{g(W,W) = 1} ⟪DJ(y) W, ξ⟫` (`= inf ‖DJ(y)* ξ‖`), written
`∀ ξ, ‖ξ‖ = 1 → ∃ W, g(W, W) = 1 ∧ c < ⟪DJ(y) W, ξ⟫`; never a bound `‖DJ(y) W‖ ≥ c‖W‖`.

* Step 1 (point scale) is `EdgeChart.collar_lower_FAM`: `⟪ρ(x) DJ(y) W, ξ⟫ > 1 − (γ + β)` for a unit
  `W` of the chart metric; `ρ(x) DJ(y) W = DJ(y) W'` with `W' = ρ(x) W` a unit vector of the point's
  own metric `ρ(x)⁻² g` (one normalization only).
* `EdgeChart.collar_ratio_EDP6`: the scale-comparison certificate `99/100 ≤ ρ(x) ≤ 101/100` at a
  collar point (`ρ(center) = 1`, so `ρ(x)` is the ratio of the point's scale to the anchor's).
* `EdgeChart.collar_conorm_anchor_EDP6` (step 2, anchor scale): for a unit `W` of the chart metric
  (the anchor metric `R⁻² g`), `⟪DJ(y) W, ξ⟫ > (1 − (γ + β))/ρ(x) > 9/10`.
* `conorm_perturb_EDP6`: a co-norm bound survives a perturbation of size `ε` on the unit sphere with
  loss `ε` (EDP04: the adjusted pair is within `.002` of `D(η_i, t)`).
* `surjective_of_conorm_pos_EDP6`: a positive co-norm into `ℝ²` gives surjectivity.
* `edp03_collar_mem_band_EDP6`, `edp06_band_mem_band_EDP6`: EDP03's collar (`|η| < 5Δ`,
  `3.9Δ < t < 4.1Δ`) and EDP06's band (`|η| < 4.01Δ`, `|t − 4Δ| < h ≤ 1/1000`, `Δ ≥ 1`) lie in the
  chart's collar band (`|η| ≤ 10Δ`, `Δ/10 ≤ t ≤ 10Δ`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **A co-norm bound survives a small perturbation**: if every unit `ξ ∈ ℝ²` has `W ∈ S` with
`c < ⟪a W, ξ⟫`, and `‖b W − a W‖ ≤ ε` on `S`, then every unit `ξ` has `W ∈ S` with
`c − ε < ⟪b W, ξ⟫`. -/
theorem conorm_perturb_EDP6 {T : Type*} (S : Set T) (a b : T → EuclideanSpace ℝ (Fin 2))
    {c ε : ℝ} (ha : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W ∈ S, c < inner ℝ (a W) ξ)
    (hab : ∀ W ∈ S, ‖b W - a W‖ ≤ ε) (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ‖ξ‖ = 1) :
    ∃ W ∈ S, c - ε < inner ℝ (b W) ξ := by
  obtain ⟨W, hW, h⟩ := ha ξ hξ
  refine ⟨W, hW, ?_⟩
  have h1 : inner ℝ (b W) ξ = inner ℝ (b W - a W) ξ + inner ℝ (a W) ξ := by
    rw [inner_sub_left]
    ring
  have h2 : |inner ℝ (b W - a W) ξ| ≤ ‖b W - a W‖ := by
    have h3 := abs_real_inner_le_norm (b W - a W) ξ
    rwa [hξ, mul_one] at h3
  have h4 := (abs_le.mp h2).1
  linarith [hab W hW]

/-- **A positive co-norm gives surjectivity**: a linear map into `ℝ²` such that every unit `ξ` has
some `W` with `0 < ⟪A W, ξ⟫` is onto. -/
theorem surjective_of_conorm_pos_EDP6 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (h : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W, 0 < inner ℝ (A W) ξ) :
    Function.Surjective A := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hK : (LinearMap.range A)ᗮ ≠ ⊥ := by
    rwa [Ne, Submodule.orthogonal_eq_bot_iff]
  obtain ⟨ξ, hξK, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hζ : ‖‖ξ‖⁻¹ • ξ‖ = 1 := norm_smul_inv_norm hξ0
  obtain ⟨W, hW⟩ := h (‖ξ‖⁻¹ • ξ) hζ
  have hζK : ‖ξ‖⁻¹ • ξ ∈ (LinearMap.range A)ᗮ := Submodule.smul_mem _ _ hξK
  have h0 : inner ℝ (A W) (‖ξ‖⁻¹ • ξ) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self A W) hζK
  linarith

/-- **EDP03's collar lies in the chart's collar band**: `|η| < 5Δ`, `3.9Δ < t < 4.1Δ` give
`|η| ≤ 10Δ`, `Δ/10 ≤ t ≤ 10Δ`. -/
theorem edp03_collar_mem_band_EDP6 {Δ η t : ℝ} (hΔ : 0 < Δ) (hη : |η| < 5 * Δ)
    (ht1 : 39 / 10 * Δ < t) (ht2 : t < 41 / 10 * Δ) :
    |η| ≤ 10 * Δ ∧ Δ / 10 ≤ t ∧ t ≤ 10 * Δ :=
  ⟨by linarith, by linarith, by linarith⟩

/-- **EDP06's band lies in the chart's collar band**: `|η| < 4.01Δ`, `|t − 4Δ| < h`, `h ≤ 1/1000`,
`Δ ≥ 1` give `|η| ≤ 10Δ`, `Δ/10 ≤ t ≤ 10Δ`. -/
theorem edp06_band_mem_band_EDP6 {Δ η t h : ℝ} (hΔ : 1 ≤ Δ) (hh : h ≤ 1 / 1000)
    (hη : |η| < 401 / 100 * Δ) (ht : |t - 4 * Δ| < h) :
    |η| ≤ 10 * Δ ∧ Δ / 10 ≤ t ∧ t ≤ 10 * Δ := by
  have h1 := (abs_lt.mp ht).1
  have h2 := (abs_lt.mp ht).2
  exact ⟨by linarith, by linarith, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **The scale-comparison certificate at a collar point** (LFR38 through `EdgeChart.collar`): the
ratio `ρ(x) = ρ(x)/ρ(center)` of the point's scale to the anchor's lies in `[99/100, 101/100]`. -/
theorem EdgeChart.collar_ratio_EDP6 {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g}
    {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ} (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F)
    {x : M} (hx : x ∈ ball c.center (100 * Δ)) (hη : |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F x / ρ x) (hF2 : F x / ρ x ≤ 10 * Δ) :
    99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100 := by
  obtain ⟨hq, -⟩ := c.collar x hx hη hF1 hF2
  exact hq

/-- **The collar co-norm at the anchor scale** (review 50 B3, step 2): at a collar point `x` and
every `y ∈ B(x, 100ρ(x))`, every unit `ξ ∈ ℝ²` has a unit `W` of the chart (anchor) metric with
`⟪DJ(y) W, ξ⟫ > (1 − (γ + β))/ρ(x) > 9/10`, `J = (η, F/ρ)`; the ratio `ρ(x)` is the certified one of
`EdgeChart.collar_ratio_EDP6`. -/
theorem EdgeChart.collar_conorm_anchor_EDP6 {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm g} {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}
    (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100)
    (hβ1 : β ≤ 1 / 100000) {x : M} (hx : x ∈ ball c.center (100 * Δ)) (hη : |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F x / ρ x) (hF2 : F x / ρ x ≤ 10 * Δ) {y : M} (hy : y ∈ ball x (100 * ρ x))
    (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ‖ξ‖ = 1) :
    ∃ W : TangentSpace I y, g.inner y W W = 1 ∧
      (1 - (γ + β)) / ρ x < inner ℝ (mvfderiv (I := I)
        (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ ∧
      9 / 10 < inner ℝ (mvfderiv (I := I)
        (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ := by
  have hq := c.collar_ratio_EDP6 hx hη hF1 hF2
  obtain ⟨W, hW, hlow, -⟩ := c.collar_singular_margin_FAM hγ hγ1 hβ1 hx hη hF1 hF2 hy ξ hξ
  have hρx : 0 < ρ x := by linarith [hq.1]
  have hsc : inner ℝ (ρ x • mvfderiv (I := I)
      (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ =
      ρ x * inner ℝ (mvfderiv (I := I)
        (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ :=
    real_inner_smul_left _ ξ (ρ x)
  rw [hsc] at hlow
  have h1 : (1 - (γ + β)) / ρ x < inner ℝ (mvfderiv (I := I)
      (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ := by
    rw [div_lt_iff₀ hρx]
    linarith
  have h2 : 9 / 10 ≤ (1 - (γ + β)) / ρ x := by
    rw [le_div_iff₀ hρx]
    linarith [hq.2]
  exact ⟨W, hW, h1, by linarith⟩

end DifferentialGeometry.Geometry.Collapse
