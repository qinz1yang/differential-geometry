import DifferentialGeometry.Geometry.Fibration.ZeroAdaptedPhysicalTest
import DifferentialGeometry.Geometry.Fibration.ActualEdgeConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignmentApplications

/-!
# TCP03 (zero block): the meeting zero block compared with the reference circle chart

Blueprint `master207B.tex`, TCP03 (`lem:fibration-first-constant-comparison`, B:5370), the zero
block (B:5383: "For the meeting zero block use `λ₀(a) = A₀a + s₀η₀(p_i)`; (TC) also holds for it";
proof B:5430–5440), on `P : LocalChartPacketsZ … ζ Λz`: `s₀ = R/ρ(i)` (`R` the zero radius),
`η₀ = (P.zero.zero k hk).radial`, `A₀` the unit row of TCP02's (TR0) (`tcp02_zero_supplier_ZERO`).

* `zero_gain_KA5`: (TR0) at `x, y` and the reference lift give the raw distance gain
  `|ρ(i)⁻¹(d(k, y) − d(k, x)) − 400| ≤ 2E₀ + 2β₂`.
* `zero_component_saturation_KA5`: the reference lift of length `400` in direction `A₀* 1`, one
  physical minimizing direction; the circle test (reference side) and LC73's test at `x`
  (`zero_adapted_test_phys_KA5`, own side) saturate on it.
* `zero_derivative_comparison_KA5` (FC15, `k = 1`; LC73's Lipschitz bound for the row norm).
* `zero_value_lc67_KA5` (LC67's centred difference-Lipschitz error, `radial_spec`),
  `zero_value_comparison_KA5`.
* `tcp03_zero_row`: TCP03 (TR0) + (TC) for the meeting zero block, with the zero adapted quality
  `0 < ζ ≤ θ²/1000` and the radial difference-Lipschitz constant `εr ≤ θ/100` as the row's
  parameter bounds (the final producer must request the cap on `εr`: review 48, R4).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The raw distance gain of the zero block: (TR0) `‖a e₀ − A₀ W‖ < E₀` at `x` and `y`, `A₀ ξ = e₀`
and the reference lift `‖W_y − W_x − 400ξ‖ < 2β` give `|a_y − a_x − 400| ≤ 2E₀ + 2β`. -/
theorem zero_gain_KA5 (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) {ξ : ℝ²}
    (hAξ : A ξ = EuclideanSpace.single 0 1) {ay ax E₀ β : ℝ} {Wy Wx : ℝ²}
    (hy : ‖EuclideanSpace.single 0 ay - A Wy‖ < E₀) (hx : ‖EuclideanSpace.single 0 ax - A Wx‖ < E₀)
    (hl : ‖Wy - Wx - (400 : ℝ) • ξ‖ < 2 * β) :
    |ay - ax - 400| ≤ 2 * E₀ + 2 * β := by
  have hAn := DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one A hA
  have hdec : (EuclideanSpace.single 0 (ay - ax - 400) : ℝ¹) =
      (EuclideanSpace.single 0 ay - A Wy) - (EuclideanSpace.single 0 ax - A Wx) +
        A (Wy - Wx - (400 : ℝ) • ξ) := by
    rw [map_sub, map_sub, map_smul, hAξ]
    ext m
    fin_cases m
    simp
    ring
  have h3 : ‖A (Wy - Wx - (400 : ℝ) • ξ)‖ ≤ ‖Wy - Wx - (400 : ℝ) • ξ‖ := by
    have := A.le_opNorm (Wy - Wx - (400 : ℝ) • ξ)
    nlinarith [norm_nonneg (Wy - Wx - (400 : ℝ) • ξ)]
  have hn : ‖(EuclideanSpace.single 0 (ay - ax - 400) : ℝ¹)‖ ≤ 2 * E₀ + 2 * β := by
    rw [hdec]
    calc _ ≤ ‖(EuclideanSpace.single 0 ay - A Wy) - (EuclideanSpace.single 0 ax - A Wx)‖ +
          ‖A (Wy - Wx - (400 : ℝ) • ξ)‖ := norm_add_le _ _
      _ ≤ (‖EuclideanSpace.single 0 ay - A Wy‖ + ‖EuclideanSpace.single 0 ax - A Wx‖) +
          ‖Wy - Wx - (400 : ℝ) • ξ‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 2 * E₀ + 2 * β := by linarith
  rwa [PiLp.norm_single, Real.norm_eq_abs] at hn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_TCP03Z_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_TCP03Z_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_TCP03Z_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP03, zero block saturation.** At `x ∈ D_i` in the closed shell of the zero ball at `k`
(radius `R`, `Λz ≤ R/ρ(i)`, `0 < ζ ≤ 1/1000`, `β₂ ≤ 1/1000`), with (TR0)
`‖ρ(i)⁻¹(d(k, z) − d(k, i)) e₀ − A₀ u_i(z)‖ < E₀` on `B(i, 1000ρ(i))`, some `g`-unit `w₀` has
`R dη₀(w₀) ≥ 1 − ε` and `(A₀(ρ(i) dη_i(w₀)))₀ ≥ 1 − ε`, `ε = γ + ζ + E₀ + β₂`. -/
theorem zero_component_saturation_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {i k : X} (hi : i ∈ P.circle.centres) (hk : k ∈ P.zero.centres) {x : X}
    (hx : x ∈ ball i (10 * ρ i)) (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius)
    (hΛi : Λz ≤ (P.zero.zero k hk).radius / ρ i) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 1000)
    (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k z - dist k i)) -
        A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i z)‖ <
        E₀) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧
      1 - (γ + ζ + E₀ + β 2) ≤
        (P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ ∧
      1 - (γ + ζ + E₀ + β 2) ≤
        A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀) 0 := by
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hri := hρ i
  have hγ0 := circle_quality_nonneg_KA4 P' hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P'.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  obtain ⟨hξ1, hAξ, hin⟩ := coisometry_adjoint_single_KA4 A hA 0
  set ξ := ContinuousLinearMap.adjoint A (EuclideanSpace.single (0 : Fin 1) 1) with hξdef
  obtain ⟨y, hd1, hd2, hyi, hlift⟩ := circle_reference_lift_KA4 P' hi hx hβ ξ hξ1
  have hdpos : 0 < dist x y := lt_of_lt_of_le (by positivity) hd1
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hdpos; exact lt_irrefl _ hdpos
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hxi2 : x ∈ ball i (200 * ρ i) := by rw [mem_ball]; linarith
  have hyi2 : y ∈ ball i (201 * 10000 * ρ i) := by rw [mem_ball]; linarith
  have hT := circle_test_of_scaled_KA4 P' hi hxi2 hyi2 (by linarith) w₀ hw₀ hgy
  have hq : 1 / (400 + 3 * β 2) ≤ ρ i / dist x y := by
    rw [div_le_div_iff₀ (by linarith) hdpos]
    linarith
  -- reference side
  obtain ⟨r₁, hr₁, hc₁⟩ := reference_component_vector_KA4 hξ1 hlift hT
  have href : 1 - (γ + 0 + β 2) ≤
      A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀) 0 := by
    rw [hin]
    exact saturation_scalar_KA4 hq hβ0 hβ le_rfl zero_le_one (by linarith) hc₁
  -- own side
  have hown0 := zero_adapted_test_phys_KA5 P hk h1 h2 hri hΛi hζ (by linarith)
    (by nlinarith) w₀ hw₀ hgy
  have hg := zero_gain_KA5 A hA hAξ (hTR y (by linarith)) (hTR x (by linarith)) hlift
  set r₂ := (ρ i)⁻¹ * (dist k y - dist k i) - (ρ i)⁻¹ * (dist k x - dist k i) - 400 with hr₂
  have hratio : (dist k y - dist k x) / dist x y = ρ i / dist x y * (400 + r₂) := by
    rw [hr₂]
    field_simp
    ring
  rw [hratio] at hown0
  have hown := saturation_scalar_KA4 hq hβ0 hβ hE0 hE hg hown0.le
  exact ⟨w₀, hw₀, by linarith, by linarith⟩

/-- **TCP03, zero derivative clause** (FC15 with `k = 1` on the normalized tangent space of
`ρ(i)⁻² g`): under the hypotheses of `zero_component_saturation_KA5`, with `ε = γ + ζ + E₀ + β₂`,
every tangent vector `w` at `x` has
`‖s₀ dη₀(w) e₀ − A₀ dη_i(w)‖ ≤ 2√(4ε + ε²) · √(ρ(i)⁻² g(w, w))`, `s₀ = R/ρ(i)`. -/
theorem zero_derivative_comparison_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {i k : X} (hi : i ∈ P.circle.centres) (hk : k ∈ P.zero.centres) {x : X}
    (hx : x ∈ ball i (10 * ρ i)) (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius)
    (hΛi : Λz ≤ (P.zero.zero k hk).radius / ρ i) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 1000)
    (hβ : β 2 ≤ 1 / 1000) {E₀ : ℝ} (hE : E₀ ≤ 1) (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k z - dist k i)) -
        A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i z)‖ <
        E₀)
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
          mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
      2 * Real.sqrt (4 * (γ + ζ + E₀ + β 2) + (γ + ζ + E₀ + β 2) ^ 2) *
        Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hri := hρ i
  have hR := (P.zero.zero k hk).radius_pos
  let _ := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
  have hnorm : ∀ v : TangentSpace 𝓘(ℝ, E3) x, ‖v‖ = Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) :=
    norm_tangent_radialScaled_KA4 g hri x
  have hγ0 := circle_quality_nonneg_KA4 P' hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P'.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  set ε' := γ + ζ + E₀ + β 2 with hε'
  have hε0 : 0 ≤ ε' := by positivity
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  set s₀ := (P.zero.zero k hk).radius / ρ i with hs₀
  have hs0 : 0 < s₀ := div_pos hR hri
  set f : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ¹ := s₀ •
    (mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) with hfdef
  set gg : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ² :=
    mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x with hgdef
  have hfv : ∀ v, f v = EuclideanSpace.single 0
      (s₀ * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v) := fun v => by
    rw [hfdef, smul_apply, smulRight_single_apply_KA4]
    ext m
    fin_cases m
    simp
  have hrows : ∀ a : Fin 1, ‖(EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f‖ ≤ 1 + ε' := by
    intro a
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hfa : ((EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f) v =
        s₀ * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v := by
      fin_cases a
      change (f v) 0 = _
      rw [hfv]
      simp
    rw [hfa, Real.norm_eq_abs, hnorm v]
    have hb := zero_adapted_deriv_bound_KA5 P hk h1 h2 hri hΛi v
    have hsq : s₀ * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v =
        (ρ i)⁻¹ *
          ((P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v) := by
      rw [hs₀]; field_simp
    have hsq2 : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) =
        (ρ i)⁻¹ * Real.sqrt (g.inner x v v) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
    rw [hsq, abs_mul, abs_of_pos (inv_pos.mpr hri), hsq2]
    have hv0 := Real.sqrt_nonneg (g.inner x v v)
    calc (ρ i)⁻¹ * |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v|
        ≤ (ρ i)⁻¹ * ((1 + ζ) * Real.sqrt (g.inner x v v)) :=
          mul_le_mul_of_nonneg_left hb (inv_pos.mpr hri).le
      _ ≤ (1 + ε') * ((ρ i)⁻¹ * Real.sqrt (g.inner x v v)) := by
          have : 1 + ζ ≤ 1 + ε' := by linarith
          have h0 : 0 ≤ (ρ i)⁻¹ * Real.sqrt (g.inner x v v) :=
            mul_nonneg (inv_pos.mpr hri).le hv0
          nlinarith
  have hgb : ‖gg‖ ≤ 1 + ε' := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h := circleAdapted_gram_upper_KA2 P' hγ0 hi hxi v
    rw [hnorm v]
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc ‖gg v‖ ≤ (1 + γ) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := h
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + γ ≤ 1 + ε' := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  have htests : ∀ a : Fin 1, ∃ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖w‖ = 1 ∧ 1 - ε' ≤ f w a ∧ 1 - ε' ≤ A (gg w) a := by
    intro a
    obtain ⟨w₀, hw₀, ho, hr⟩ := zero_component_saturation_KA5 P hi hk hx h1 h2 hΛi hζ hζ1 hβ hE A
      hA hTR
    refine ⟨ρ i • w₀, ?_, ?_, ?_⟩
    · rw [hnorm, gInner_smul_self, hw₀]
      have : (ρ i)⁻¹ ^ 2 * (ρ i ^ 2 * 1) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    · fin_cases a
      change 1 - ε' ≤ (f (ρ i • w₀)) 0
      rw [hfv, map_smul, smul_eq_mul]
      have he : (EuclideanSpace.single (0 : Fin 1)
          (s₀ * (ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀)) : ℝ¹) 0 =
          (P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ := by
        simp only [PiLp.single_apply, ite_true]
        rw [hs₀]
        field_simp
      rw [he]
      exact ho
    · fin_cases a
      have hge : gg (ρ i • w₀) =
          ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w₀ := map_smul _ _ _
      change 1 - ε' ≤ A (gg (ρ i • w₀)) 0
      rw [hge]
      exact hr
  have hRz := DifferentialGeometry.Geometry.Fibration.norm_difference_of_common_directions f gg A hA
    hε0 hrows hgb htests
  have hw := (f - A.comp gg).le_opNorm w
  rw [hnorm w] at hw
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast, one_mul] at hRz
  have hfw : (f - A.comp gg) w = EuclideanSpace.single 0
      (s₀ * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) := by
    rw [sub_apply, hfv]
    rfl
  rw [← hfw]
  exact hw.trans (mul_le_mul_of_nonneg_right hRz (Real.sqrt_nonneg _))

/-- **LC67's centred difference-Lipschitz error** of the radial coordinate (`radial_spec`, constant
`εr`), in reference units `r`: `|(R/r)(η₀ x − η₀ y) − r⁻¹(d(k, x) − d(k, y))| ≤ εr r⁻¹ d(x, y)`. -/
theorem zero_value_lc67_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {k : X} (hk : k ∈ P.zero.centres) {r : ℝ} (hr : 0 < r) (x y : X) :
    |(P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial y) -
      r⁻¹ * (dist k x - dist k y)| ≤ εr * (r⁻¹ * dist x y) := by
  have hR := (P.zero.zero k hk).radius_pos
  have hc := P.zero.zero_center k hk
  obtain ⟨-, -, -, -, h5, -⟩ := (P.zero.zero k hk).radial_spec
  have h := h5 x y
  rw [@Metric.infDist_singleton X
      (mX.rescale (P.zero.zero k hk).radius⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace,
    @Metric.infDist_singleton X
      (mX.rescale (P.zero.zero k hk).radius⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace] at h
  change |((P.zero.zero k hk).radial x -
      (P.zero.zero k hk).radius⁻¹ * dist x (P.zero.zero k hk).center) -
    ((P.zero.zero k hk).radial y -
      (P.zero.zero k hk).radius⁻¹ * dist y (P.zero.zero k hk).center)| ≤
    εr * ((P.zero.zero k hk).radius⁻¹ * dist x y) at h
  rw [hc] at h
  have hlam : 0 < (P.zero.zero k hk).radius / r := div_pos hR hr
  have he : (P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial y) -
      r⁻¹ * (dist k x - dist k y) =
      (P.zero.zero k hk).radius / r * (((P.zero.zero k hk).radial x -
        (P.zero.zero k hk).radius⁻¹ * dist x k) - ((P.zero.zero k hk).radial y -
        (P.zero.zero k hk).radius⁻¹ * dist y k)) := by
    rw [dist_comm k x, dist_comm k y]
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hlam]
  calc (P.zero.zero k hk).radius / r * |((P.zero.zero k hk).radial x -
        (P.zero.zero k hk).radius⁻¹ * dist x k) - ((P.zero.zero k hk).radial y -
        (P.zero.zero k hk).radius⁻¹ * dist y k)|
      ≤ (P.zero.zero k hk).radius / r * (εr * ((P.zero.zero k hk).radius⁻¹ * dist x y)) :=
        mul_le_mul_of_nonneg_left h hlam.le
    _ = εr * (r⁻¹ * dist x y) := by field_simp

/-- **TCP03, zero value clause**: `‖s₀(η₀ x − η₀ i) e₀ − A₀ η_i(x)‖ < εr ρ(i)⁻¹ d(x, i) + E₀ + γ`
from LC67's centred error, (TR0) at `x` and the circle adaptation error
(`λ₀(a) = A₀a + s₀η₀(p_i)`). -/
theorem zero_value_comparison_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (hγ : 0 ≤ γ) {i k : X} (hi : i ∈ P.circle.centres) (hk : k ∈ P.zero.centres) {x : X}
    (hx : x ∈ ball i (10 * ρ i)) {E₀ : ℝ} (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
        A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i x)‖ <
        E₀) :
    ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
          ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
        A (cgpCircleCoord P.toLocalChartFamily i hi x)‖ <
      εr * ((ρ i)⁻¹ * dist x i) + E₀ + γ := by
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hri := hρ i
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  have hvi : ‖cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x‖ < γ := by
    have h := (circleAdapted_physical_KA2 P' hγ hi).1 x hxi
    rw [circleRaw_KA3_eq P' hi]
    exact h
  have hAn := DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one A hA
  have h3 : ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x)‖ < γ := by
    refine lt_of_le_of_lt ?_ hvi
    have := A.le_opNorm (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x)
    nlinarith [norm_nonneg (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x)]
  have h1 := zero_value_lc67_KA5 P hk hri x i
  set a := (P.zero.zero k hk).radius / ρ i *
    ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i) with ha
  set c := (ρ i)⁻¹ * (dist k x - dist k i) with hcdef
  have hdec : EuclideanSpace.single 0 a - A (cgpCircleCoord P.toLocalChartFamily i hi x) =
      EuclideanSpace.single 0 (a - c) + (EuclideanSpace.single 0 c - A (circleRaw_KA3 P' i x)) -
        A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x) := by
    have hsub : (EuclideanSpace.single 0 (a - c) : ℝ¹) =
        EuclideanSpace.single 0 a - EuclideanSpace.single 0 c := PiLp.single_sub 2 (0 : Fin 1)
    rw [map_sub, hsub]
    abel
  rw [hdec]
  have hn1 : ‖(EuclideanSpace.single 0 (a - c) : ℝ¹)‖ ≤ εr * ((ρ i)⁻¹ * dist x i) := by
    rw [PiLp.norm_single, Real.norm_eq_abs]
    exact h1
  calc _ ≤ ‖(EuclideanSpace.single 0 (a - c) : ℝ¹) +
        (EuclideanSpace.single 0 c - A (circleRaw_KA3 P' i x))‖ +
        ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x)‖ := norm_sub_le _ _
    _ ≤ (‖(EuclideanSpace.single 0 (a - c) : ℝ¹)‖ +
        ‖EuclideanSpace.single 0 c - A (circleRaw_KA3 P' i x)‖) +
        ‖A (cgpCircleCoord P.toLocalChartFamily i hi x - circleRaw_KA3 P' i x)‖ := by
        gcongr; exact norm_add_le _ _
    _ < εr * ((ρ i)⁻¹ * dist x i) + E₀ + γ := by linarith

/-- **TCP03 (zero block)** (`lem:fibration-first-constant-comparison`, B:5370, B:5383) on
`LocalChartPacketsZ … ζ Λz`: for an early `0 < θ < 1` (and `ν`, `3ν ≤ β₃ < 1`) there are an early
`σ`, an early circle quality bound `η₂`, an early adaptation bound `γ₀` and a zero quality bound
`η₁` (all independent of `Δ`) such that, with the zero ranges (`0 ≤ Λ`, `1 ≤ Δ`, `LΛ < 10⁻⁵`,
`e < 1/40`, `T ≥ 1600L`), `3β₂ ≤ σ`, `β₂ ≤ η₂`, `γ ≤ γ₀`, `β₁ ≤ η₁`, the zero adapted quality
`0 < ζ ≤ θ²/1000`, the radial difference-Lipschitz constant `εr ≤ θ/100`, `20Λz ≤ T` and
`σ⁻¹ ≤ Lmax`: at every circle centre `i`, every zero ball (centre `k`, radius `R`) whose support
meets `D_i` has ONE unit row `A₀ : ℝ² → ℝ¹` with TCP02's (TR0) at accuracy `θ²/2000` on
`B(i, 1000ρ(i))` and (TC) on `D_i` for `λ₀(a) = A₀a + s₀η₀(p_i)`, `s₀ = R/ρ(i)`: value `≤ θ/2`
and differential `≤ (θ/2)|w|` in the norm of `ρ(i)⁻² g`. -/
theorem tcp03_zero_row {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres), ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
          A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x, dist x i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
              A₀ (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                i x)‖ < θ ^ 2 / 2000) ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                  ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
                A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ θ / 2 ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                  A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hE₀ : (0 : ℝ) < θ ^ 2 / 2000 := by positivity
  obtain ⟨σz, hσz, hσz1, ηz, hηz, hzero⟩ := tcp02_zero_supplier_ZERO hE₀ hν hν1
  refine ⟨σz, hσz, hσz1, θ ^ 2 / 2000, hE₀, θ ^ 2 / 1000, by positivity, ηz, hηz, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ
    hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL i hi k hk hmeet
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hri := hρ i
  have hγ0 := circle_quality_nonneg_KA4 P' hi
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ21 : θ ^ 2 < 1 := by nlinarith
  have hζ1 : ζ ≤ 1 / 1000 := by linarith
  have hβ1000 : β 2 ≤ 1 / 1000 := by linarith
  have hE1 : θ ^ 2 / 2000 ≤ 1 := by linarith
  obtain ⟨A, hA, hTR⟩ := hzero P hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ1 hσL i hi k hk hmeet
  have hin := tcp01_zero_lc73_inputs_ZERO P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hΛz i hk hmeet
  obtain ⟨-, -, hΛi⟩ := hin i (mem_ball_self (by positivity))
  refine ⟨A, hA, hTR, fun x hx => ⟨?_, fun w => ?_⟩⟩
  · have hv := zero_value_comparison_KA5 P hγ0 hi hk hx A hA
      (hTR x (by have := mem_ball.mp hx; linarith))
    have hxi : (ρ i)⁻¹ * dist x i < 10 := inv_mul_dist_lt_of_mem_ball_LC87 hri hx
    have hxi0 : 0 ≤ (ρ i)⁻¹ * dist x i := by positivity
    have hεt : εr * ((ρ i)⁻¹ * dist x i) ≤ θ / 10 := by
      rcases le_or_gt 0 εr with h0 | h0
      · nlinarith
      · nlinarith
    linarith
  · obtain ⟨h1, h2, -⟩ := hin x hx
    have hd := zero_derivative_comparison_KA5 P hi hk hx h1 h2 hΛi hζ hζ1 hβ1000 hE1 A hA hTR w
    have hβ0 : 0 ≤ β 2 := by
      let Ai := P'.circleAdapted i hi
      let _ := Ai.instY
      exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
        Ai.split).le
    set ε' := γ + ζ + θ ^ 2 / 2000 + β 2 with hε'
    have hε0 : 0 ≤ ε' := by positivity
    have hbud := riesz_budget_KA4 hθ hθ1 (ε := ε') hε0 (by linarith)
    have hmono : 2 * Real.sqrt (4 * ε' + ε' ^ 2) ≤ 2 * Real.sqrt (2 * (4 * ε' + ε' ^ 2)) := by
      have : 4 * ε' + ε' ^ 2 ≤ 2 * (4 * ε' + ε' ^ 2) := by nlinarith
      have := Real.sqrt_le_sqrt this
      linarith
    exact hd.trans (mul_le_mul_of_nonneg_right (hmono.trans hbud) (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry.Collapse
