import DifferentialGeometry.Geometry.Collapse.EdgeAdaptedStability
import DifferentialGeometry.Geometry.Collapse.EdgeBandGradient
import DifferentialGeometry.Geometry.Collapse.EdgeSharedProfiles
set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

theorem exists_edgeVertical_ordered_tolerances {ι : ℝ} (hι : 0 < ι) :
    ∃ Δ₀ τ₀ ε₀ ℓ₀ : ℝ, 1000000 ≤ Δ₀ ∧ 0 < τ₀ ∧ 0 < ε₀ ∧ 0 < ℓ₀ ∧
      ∀ Δ, Δ₀ ≤ Δ → ∀ τ, 0 ≤ τ → τ < τ₀ → ∀ ε, ε < ε₀ →
        ∀ ℓ, ℓ < ℓ₀ →
          1000000 ≤ Δ ∧ τ < 1 / 10000 ∧ ε < 1 / 100 ∧ 100 * ℓ ≤ 1 / 1000000 ∧
            2 * ε + 300 * ℓ + Real.sqrt (504000 / Δ + 3780 * τ) < ι := by
  let Δ₀ : ℝ := max 1000000 (8064000 / ι ^ 2)
  let τ₀ : ℝ := min (1 / 10000) (ι ^ 2 / 60480)
  let ε₀ : ℝ := min (1 / 100) (ι / 16)
  let ℓ₀ : ℝ := min (1 / 100000000) (ι / 2400)
  refine ⟨Δ₀, τ₀, ε₀, ℓ₀, le_max_left _ _, by positivity, by positivity,
    by positivity, fun Δ hΔ τ hτ hτ' ε hε' ℓ hℓ' => ?_⟩
  have hΔ₁ : 1000000 ≤ Δ := (le_max_left _ _).trans hΔ
  have hΔ₂ : 8064000 / ι ^ 2 ≤ Δ := (le_max_right _ _).trans hΔ
  have hΔpos : 0 < Δ := by linarith only [hΔ₁]
  have hτ₁ : τ < 1 / 10000 := lt_of_lt_of_le hτ' (min_le_left _ _)
  have hτ₂ : τ < ι ^ 2 / 60480 := lt_of_lt_of_le hτ' (min_le_right _ _)
  have hε₁ : ε < 1 / 100 := lt_of_lt_of_le hε' (min_le_left _ _)
  have hε₂ : ε < ι / 16 := lt_of_lt_of_le hε' (min_le_right _ _)
  have hℓ₁ : ℓ < 1 / 100000000 := lt_of_lt_of_le hℓ' (min_le_left _ _)
  have hℓ₂ : ℓ < ι / 2400 := lt_of_lt_of_le hℓ' (min_le_right _ _)
  have hterm : 504000 / Δ ≤ ι ^ 2 / 16 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hι)).mp hΔ₂
    apply (div_le_iff₀ hΔpos).mpr
    nlinarith only [hh]
  have hpos : 0 ≤ 504000 / Δ + 3780 * τ := by positivity
  have hsqrt := Real.sq_sqrt hpos
  have hsqnonneg := Real.sqrt_nonneg (504000 / Δ + 3780 * τ)
  refine ⟨hΔ₁, hτ₁, hε₁, by linarith only [hℓ₁], ?_⟩
  have hsmall : Real.sqrt (504000 / Δ + 3780 * τ) < ι / 2 := by
    nlinarith only [hterm, hτ₂, hsqrt, hsqnonneg, hι]
  linarith only [hε₂, hℓ₂, hsmall, hι]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_edge_low_collar_smoothing_with_vertical_gradient (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {ρ : M → ℝ}
    {Λ : ℝ≥0} {Δ τ κ ε μ : ℝ}
    (hA : IsClosed A) (hΔ : 1000000 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1000000)
    (hθ : 140 * Real.sqrt τ < ε ^ 2 / 20)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 1000000)
    {ι : ℝ} (hbudget : 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < ι) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (closedBall p (20 * Δ) ∩ {x | Δ / 25 ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ}) ⊆ O ∧
      (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x, |F x - infDist x A| < μ * Δ) ∧
      ∀ f : M → ℝ, (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
        Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
        ∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ →
          ∀ y ∈ ball x (300 * ρ x), ∀ w ∈ minimizingDirectionsTo g hEnorm {a} y,
            Real.sqrt (g.inner y (ρ x • gradFun g (fun z => F z / ρ z) y - w)
              (ρ x • gradFun g (fun z => F z / ρ z) y - w)) < ι
 := by
  have hΔpos : 0 < Δ := by linarith only [hΔ]
  obtain ⟨F, O, hO, hCO, hFO, hF0, hFL, hval, _hsupport, _hdiff, hgrad,
    _hquot, _hprofiles⟩ := exists_edge_low_collar_smoothing g hEnorm hA hΔpos hτ hτsmall hQp
      hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ (by linarith)
      hθ hρ hρp hρs.contMDiffOn (by linarith)
  refine ⟨F, O, hO, hFO, hCO, hF0, hFL, hval, fun f hf x hx hfx hη hη' a ha hanchor => ?_⟩
  obtain ⟨hx15, hxA, hxA'⟩ := edgeBand_mem_ball_and_infDist_window hΔpos hτsmall.le hμ1 hlam
    hQp hdist hheight hpA hborder hρ hρp (fun y => (hval y).le) hf hx hfx hη hη'
  exact edgeBand_vertical_gradient g hEnorm hA hΔ hτ.le hτsmall.le hQp hdist hheight hpA
    hborder hbordercover hx15 hxA hxA' ha hanchor hκ hκΔ hsec hε.le hε1 (by linarith)
    hFL (fun y => (hval y).le)
    (fun y hy => (hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp))
    hgrad hρ hρp hρs (by linarith) hbudget

theorem edgeReference_translation_is_adapted (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {x : M} {χ Φ : M → EuclideanSpace ℝ (Fin 2)} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100)
    (hχ : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ χ (ball x 300))
    (hχx : χ x = 0)
    (hχL : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100,
      dist (χ y) (χ z) ≤ (1 + γ / 4) * dist y z)
    (hχI : ∀ y ∈ ball x 100, infDist (χ y) (ball 0 100) ≤ 100 * (γ / 4))
    (hχI' : ∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
      infDist w (χ '' ball x 100) ≤ 100 * (γ / 4))
    (hχtest : ∀ y ∈ ball x 100, ∀ z ∈ ball x (400 / γ), 100 < dist y z →
      ∀ w ∈ minimizingDirectionsTo g hEnorm {z} y,
        ‖mvfderiv I χ y w - (dist y z)⁻¹ • (Φ z - Φ y)‖ < γ / 4)
    (c : EuclideanSpace ℝ (Fin 2))
    (hgram : ∀ y ∈ ball x 300, ‖edgeCoordinateGradientGram g χ y - 1‖ < γ / 4)
 :
    (∀ y ∈ ball x 100, Function.Surjective (mvfderiv I (fun z => χ z + c) y)) ∧
      (∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (χ y + c) (χ z + c) ≤ (1 + γ) * dist y z) ∧
      (∀ y ∈ ball x 100, infDist (χ y + c) (ball c 100) ≤ 100 * γ) ∧
      (∀ w ∈ ball c 100, infDist w ((fun z => χ z + c) '' ball x 100) ≤ 100 * γ) ∧
      (∀ y ∈ ball x 100, ∀ z ∈ ball x (100 / γ), 100 < dist y z →
        ∀ w ∈ minimizingDirectionsTo g hEnorm {z} y,
          ‖mvfderiv I (fun z => χ z + c) y w - (dist y z)⁻¹ • (Φ z - Φ y)‖ < γ)
 := by
  have hh := rankTwo_adapted_of_buffered_perturbation (J := fun z => χ z + c) g hEnorm hγ hγ1 hχ
    (hχ.add contMDiffOn_const) hχx hχL hχI hχI' hχtest hgram (by
      intro y hy w
      have hχy := (hχ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)
      have he := _root_.mvfderiv_add hχy (mdifferentiableAt_const (c := c))
      simp only [_root_.mvfderiv_const, add_zero] at he
      change mvfderiv I (fun z => χ z + c) y = mvfderiv I χ y at he
      rw [he, sub_self, norm_zero]
      positivity)
  simpa only [hχx, zero_add] using hh

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem edgeCentre_normalized_gradient_error_eq (g : SmoothRiemannianMetric I M)
    (F η : M → ℝ) (y : M) (r : ℝ) (hr : 0 < r)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F y) :
    let gp := DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) (by positivity) g
    Real.sqrt (gp.inner y (gradFun gp η y - gradFun gp (fun z => F z / r) y)
      (gradFun gp η y - gradFun gp (fun z => F z / r) y)) =
      Real.sqrt (g.inner y (r • gradFun g η y - gradFun g F y)
        (r • gradFun g η y - gradFun g F y))
 := by
  dsimp only
  have he : (fun z => F z / r) = r⁻¹ • F := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hgr := gradientFun_const_smul g r⁻¹ hF
  rw [← he] at hgr
  change gradFun g (fun z => F z / r) y = r⁻¹ • gradFun g F y at hgr
  change Real.sqrt ((DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g).inner y
    (gradientFun (DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g) η y -
      gradientFun (DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g) (fun z => F z / r) y)
    (gradientFun (DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g) η y -
      gradientFun (DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g) (fun z => F z / r) y)) = _
  rw [gradientFun_scale, gradientFun_scale]
  change Real.sqrt ((DifferentialGeometry.scaleMetric (r⁻¹ ^ 2) _ g).inner y
    ((r⁻¹ ^ 2)⁻¹ • gradFun g η y - (r⁻¹ ^ 2)⁻¹ • gradFun g (fun z => F z / r) y)
    ((r⁻¹ ^ 2)⁻¹ • gradFun g η y - (r⁻¹ ^ 2)⁻¹ • gradFun g (fun z => F z / r) y)) = _
  rw [hgr]
  simp only [DifferentialGeometry.scaleMetric_inner, map_sub, sub_apply, map_smul,
    smul_apply, smul_eq_mul, smul_smul]
  congr 1
  field_simp

theorem exists_shared_edge_profiles_in_normalized_metric (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g)
    {A : Set M} (hA : IsClosed A) {P : Finset M} (hP : P.Nonempty)
    {Q : M → M → WithLp 2 (ℝ × ℝ)} {ρ : M → ℝ} (hρpos : ∀ x, 0 < ρ x) {Δ τ κ ε μ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hQp : ∀ p ∈ P, Q p p = 0)
    (hdist : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
      |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p))
    (hheight : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd)
    (hcover : ∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
      z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
        ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p))
    (hpA : ∀ p ∈ P, p ∈ A)
    (hborder : ∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p))
    (hbordercover : ∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
      ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
        dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p))
    (hκ : 0 ≤ κ) (hκΔ : ∀ p ∈ P, κ * (Δ * ρ p) ≤ 1 / 100)
    (hsec : ∀ p ∈ P, ∀ z ∈ ball p (1000 * (Δ * ρ p)), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20)
    {Λ : ℝ≥0} (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧ (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}) ⊆ O ∧
        (∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
            Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
        (∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)},
          (∀ w : TangentSpace I x, mvfderiv I (fun y => F y / ρ y) x w =
            (ρ x)⁻¹ * mvfderiv I F x w - F x * (ρ x ^ 2)⁻¹ * mvfderiv I ρ x w) ∧
          let gp := DifferentialGeometry.scaleMetric ((ρ p)⁻¹ ^ 2)
            (by exact pow_pos (inv_pos.mpr (hρpos p)) 2) g
          Real.sqrt (gp.inner x (gradFun gp (fun y => F y / ρ y) x -
              gradFun gp (fun y => F y / ρ p) x)
            (gradFun gp (fun y => F y / ρ y) x -
              gradFun gp (fun y => F y / ρ p) x)) ≤ 100 * Δ * Λ) ∧
        (∀ x ∈ ball p (20 * (Δ * ρ p)), infDist x A < 41 / 4 * (Δ * ρ p) →
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
              (F y / ρ y / Δ)) x) ∧
        (∀ s, 2 * Δ ≤ s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ x / Δ) ≤ s ↔
            F x / ρ x ≤ s)) ∧
        (∀ s, 2 * Δ < s → ∀ x,
          (Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F x / ρ x / Δ) = s ↔
            F x / ρ x = s)) ∧
        (∀ x ∈ ball p (100 * (Δ * ρ p)), 2 * Δ < F x / ρ x →
          (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile
            (F y / ρ y / Δ)) =ᶠ[𝓝 x] fun y => F y / ρ y) := by
  obtain ⟨F, O, hO, hFO, hF0, hFL, hdiff, hcentres⟩ :=
    exists_shared_edge_smoothing_with_profiles g hEnorm hA hP hρpos hΔ hτ hτsmall hQp
      hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ hρ hρs hlam
  refine ⟨F, O, hO, hFO, hF0, hFL, hdiff, fun p hp => ?_⟩
  obtain ⟨hval, hCO, hgrad, hquot, hsm, hle, heq, hnear⟩ := hcentres p hp
  refine ⟨hval, hCO, hgrad, ?_, hsm, hle, heq, hnear⟩
  intro x hx
  obtain ⟨hder, herr⟩ := hquot x hx
  refine ⟨hder, ?_⟩
  have hFx := (hFO.contMDiffAt (hO.mem_nhds (hCO hx))).mdifferentiableAt (by simp)
  dsimp only
  rw [edgeCentre_normalized_gradient_error_eq g F (fun y => F y / ρ y) x
    (ρ p) (hρpos p) hFx]
  exact herr

theorem exists_edge_low_collar_smoothing_with_vertical_gradient_rescaled
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {ρ : M → ℝ}
    {Λ : ℝ≥0} {Δ τ κ ε μ : ℝ}
    (hA : IsClosed A) (hΔ : 1000000 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1000000)
    (hθ : 140 * Real.sqrt τ < ε ^ 2 / 20)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 1000000)
    (hρpos : ∀ z, 0 < ρ z)
    {ι : ℝ} (hbudget : 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < ι) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (closedBall p (20 * Δ) ∩ {x | Δ / 25 ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ}) ⊆ O ∧
      (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x, |F x - infDist x A| < μ * Δ) ∧
      ∀ f : M → ℝ, (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
        Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
        ∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ →
          let gx := DifferentialGeometry.scaleMetric ((ρ x)⁻¹ ^ 2)
            (by exact pow_pos (inv_pos.mpr (hρpos x)) 2) g
          ∀ y ∈ ball x (300 * ρ x), ∀ w ∈ minimizingDirectionsTo g hEnorm {a} y,
            Real.sqrt (gx.inner y (gradFun gx (fun z => F z / ρ z) y - ρ x • w)
              (gradFun gx (fun z => F z / ρ z) y - ρ x • w)) < ι := by
  obtain ⟨F, O, hO, hFO, hCO, hF0, hFL, hval, hV⟩ :=
    exists_edge_low_collar_smoothing_with_vertical_gradient g hEnorm hA hΔ hτ hτsmall hQp
      hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ
      hρ hρp hρs hlam hbudget
  refine ⟨F, O, hO, hFO, hCO, hF0, hFL, hval, ?_⟩
  intro f hf x hx hfx hη hη' a ha hanchor
  dsimp only
  intro y hy w hw
  rw [edgeRescaled_gradient_norm g (fun z => F z / ρ z) y (ρ x) (hρpos x) w]
  exact hV f hf x hx hfx hη hη' a ha hanchor y hy w hw

end DifferentialGeometry.Geometry.Collapse
