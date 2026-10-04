import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartRows

/-!
# LFR35 with the row's quantifier order: every sufficiently small coarse error

Blueprint 207A, LFR35 (`lem:collapse-edge-plane-reference`, A:27944–28071): "Choose `τ`
sufficiently small in terms of these data". Codex X90's producers
(`exists_coarse_edge_reference_parameters`, `exists_edge_reference_chart_parameters`) state ONE
`τ` per `Δ`; their anchors are certified only up to that `τΔ`. LFR38 combines the SAME anchors with
LFR36's vertical estimate, whose budget needs the anchor error to be as small as later choices
demand. Here both producers are re-proved (by X90's own route and suppliers, unchanged) for EVERY
`τ ≤ τ₀`, and the row's value clause `|χ_x − Φ_x| < 100γ/32` is exported in the stronger form
`< γ` (X90 proves it internally).

* `exists_coarse_edge_reference_parameters_uniform`
* `exists_edge_reference_chart_parameters_uniform`
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold DifferentialGeometry.Analysis
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM


theorem exists_coarse_edge_reference_parameters_uniform {β ε R : ℝ}
    (hβ : 0 < β) (hβsmall : β < 1 / 100)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 400 < R) :
    ∃ Δ₀ > 1, ∀ Δ, Δ₀ ≤ Δ → ∃ τ₀ > 0, ∃ κ > 0, ∀ τ, τ ≤ τ₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Q : M → WithLp 2 (ℝ × ℝ)) (p : M) (A : Set M),
      (∀ y ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g y (-κ ^ 2)) →
      Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      ∀ x, x ∈ ball p (15 * Δ) → 9 / 100 * Δ ≤ infDist x A →
        infDist x A ≤ 101 / 10 * Δ →
      ∃ anchors : Fin 2 → M, ∃ f : Fin 2 → M → ℝ,
        (∀ j, anchors j ∈ ball p (20 * Δ) ∧
          dist (Q (anchors j)) (Q x + planeReferenceIsometry.symm
            (EuclideanSpace.single j (Δ / 40))) ≤ τ * Δ) ∧
        (∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (ball x 305)) ∧
        (∀ j, f j x = 0) ∧
        (∀ j, ∀ y ∈ ball x 305,
          ∀ v ∈ minimizingDirectionsTo g hEnorm {anchors j} y,
          Real.sqrt (g.inner y (gradFun g (f j) y - v) (gradFun g (f j) y - v)) < ε) ∧
        (∀ j, ∀ y ∈ ball x (R + 3),
          |f j y - planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) j| <
            ε * dist y x + ε ^ 2 / 40) ∧
        (∀ j, ∀ y ∈ ball x 305, ∀ z ∈ ball x (R + 3), 1 / 2 < dist y z →
          ∀ W : TangentSpace I y, g.inner y W W = 1 →
          intrinsicGeodesic g hEnorm y W (dist y z) = z →
          |mvfderiv (I := I) (f j) y W -
            (planeReferenceIsometry (planeComparisonMap Q p x Δ 1 z) j -
              planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) j) / dist y z| <
                ε + ε ^ 2 / 40) ∧
        (∀ y ∈ ball x 305, ∀ i j : Fin 2,
          |g.inner y (gradFun g (f i) y) (gradFun g (f j) y) -
            (if i = j then 1 else 0)| < ε ^ 2 / 40 + 2 * ε + ε ^ 2) ∧
        ∀ q : ℝ, (hq : 99 / 100 ≤ q) → q ≤ 101 / 100 →
          (letI := mM.rescale q⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq));
            ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
              ∀ y, Φ.toFun y = @planeComparisonMap M mM Q p x Δ q y)
    := by
  obtain ⟨s₀, hs₀, ν₀, hν₀, hparams⟩ :=
    exists_smooth_long_reference_parameters.{uE, uH, uM, 0} (b := 305) (ρ := 400)
      (by norm_num) (by norm_num) (by norm_num) hR hε hε1
  obtain ⟨Δ₀, hΔ₀⟩ := exists_gt (max (max (40 * s₀) (100000 / β))
    (max (max (30 / ν₀) (R + 4)) 1000))
  have hΔ₀1 : 1 < Δ₀ := by
    have ht := (le_max_right (max (30 / ν₀) (R + 4)) (1000 : ℝ)).trans
      (le_max_right (max (40 * s₀) (100000 / β)) _)
    linarith
  refine ⟨Δ₀, hΔ₀1, ?_⟩
  intro Δ hΔ
  have hΔbig := hΔ₀.trans_le hΔ
  have hΔpos : 0 < Δ := by linarith
  have hΔ1 : 1 ≤ Δ := by linarith
  have hs : s₀ ≤ Δ / 40 := by
    have ht : 40 * s₀ ≤ max (max (40 * s₀) (100000 / β))
        (max (max (30 / ν₀) (R + 4)) 1000) :=
      (le_max_left (40 * s₀) (100000 / β)).trans (le_max_left _ _)
    linarith
  have hβΔ : 100000 / β < Δ :=
    ((le_max_right (40 * s₀) (100000 / β)).trans (le_max_left _ _)).trans_lt hΔbig
  have hνΔ : 30 / ν₀ < Δ :=
    ((le_max_left (30 / ν₀) (R + 4)).trans
      ((le_max_left _ _).trans (le_max_right _ _))).trans_lt hΔbig
  have hRΔ : R + 4 < Δ :=
    ((le_max_right (30 / ν₀) (R + 4)).trans
      ((le_max_left _ _).trans (le_max_right _ _))).trans_lt hΔbig
  have h1000 : 1000 < Δ :=
    ((le_max_right _ (1000 : ℝ)).trans (le_max_right _ _)).trans_lt hΔbig
  let ν := 30 / Δ
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνsmall : ν < ν₀ := by
    dsimp [ν]
    rw [div_lt_iff₀ hΔpos]
    have hh := (div_lt_iff₀ hν₀).mp hνΔ
    nlinarith
  have hν1 : ν < 1 := by dsimp [ν]; rw [div_lt_iff₀ hΔpos]; linarith
  let τ₀ := min (1 / 100000 : ℝ) (min (ν / (8 * Δ)) (β / (8 * Δ)))
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  refine ⟨τ₀, hτ₀, ?_⟩
  obtain ⟨κ, hκ, hproduce⟩ := hparams (Δ / 40) hs
  refine ⟨κ, hκ, ?_⟩
  intro τ hττ₀
  have hτbound : τ ≤ 1 / 10000 :=
    hττ₀.trans ((min_le_left _ _).trans (by norm_num))
  have hτν : 4 * (τ * Δ) < ν := by
    have hh : τ ≤ ν / (8 * Δ) :=
      hττ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at hh
    nlinarith
  have hτβ : 4 * (τ * Δ) < β := by
    have hh : τ ≤ β / (8 * Δ) :=
      hττ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at hh
    nlinarith
  have hinv : ν⁻¹ = Δ / 30 := by dsimp [ν]; field_simp
  have hradius : ν⁻¹ ≤ Δ / 20 := by rw [hinv]; linarith
  have hanchors : Δ / 40 + 2 * (τ * Δ) < ν⁻¹ := by
    rw [hinv]
    have hh : τ ≤ (1 / 100000 : ℝ) := hττ₀.trans (min_le_left _ _)
    nlinarith
  intro E hnorm hspace hfinite hne H htop I hboundary M mM hcharts hmanifold hsigma
    hcomplete hRB hRiem hcontinuous g hEnorm Q p A hsec hQp hdist hheight hcover hpA
    hborder hbordercover x hx hxA hxA'
  have hb := coarseBorder_abs_infDist_sub_height_le hΔpos
    (hτbound.trans (by norm_num)) hQp hdist hheight hpA hborder hbordercover
    (ball_subset_ball (by linarith) hx)
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  have hlow : 8 / 100 * Δ ≤ (Q x).snd := by linarith [(abs_le.mp hb).2]
  have hhigh : (Q x).snd ≤ 102 / 10 * Δ := by linarith [(abs_le.mp hb).1]
  obtain ⟨F, hF, anchors, negatives, ha, hb'⟩ := exists_planeReference_rankTwo_source
    hΔpos hν hν1 hτbound hradius hanchors hτν hQp hdist hcover hx hlow hhigh
  have hcurv : ∀ y ∈ ball x (8 * (Δ / 40 + R + 4)),
      SectionalBoundedBelowAt g y (-κ ^ 2) := by
    intro y hy
    apply hsec y
    have hh := dist_triangle y x p
    have hx' := Metric.mem_ball.mp hx
    have hy' := Metric.mem_ball.mp hy
    change dist y p < 10000 * Δ
    linarith
  obtain ⟨f, hf, hf0, hg, hv, ht, hGram⟩ := hproduce ν κ hν hνsmall hκ le_rfl
    E H I M g hEnorm PUnit.{1} x (PUnit.unit : PUnit.{1}) F anchors negatives hcurv
    (fun j => (ha j).2.1) (fun j => (hb' j).2.1)
    (fun j => (ha j).2.2.2) (fun j => (hb' j).2.2.2)
  refine ⟨anchors, f, fun j => ⟨(ha j).1, (ha j).2.2.1⟩, hf, hf0, hg,
    ?_, ?_, hGram, ?_⟩
  · intro j y hy
    simpa only [hF] using hv j y hy
  · intro j y hy z hz hyz W hW hWz
    simpa only [hF] using ht j y hy z hz hyz W hW hWz
  · intro q hq hq'
    exact (exists_planeComparison_of_infDist hΔ1 hβ hβsmall hβΔ hτbound hτβ
      hQp hdist hheight hcover hpA hborder hbordercover hx hxA hxA' hq hq').1

private theorem uniformReference_pair_norm {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ j, |v j| ≤ a) : ‖v‖ ≤ 2 * a := by
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have h0 := (sq_le_sq₀ (abs_nonneg (v 0)) ha).mpr (hv 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (v 1)) ha).mpr (hv 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg v]

private theorem uniformReference_plane_scale {X : Type*} [MetricSpace X]
    (Q : X → WithLp 2 (ℝ × ℝ)) (p x y : X) (Δ q : ℝ) :
    planeReferenceIsometry (planeComparisonMap Q p x Δ q y) =
      q⁻¹ • planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) := by
  by_cases hy : y ∈ ball p (200 * Δ)
  · rw [planeComparisonMap_of_mem hy, planeComparisonMap_of_mem hy,
      inv_one, one_smul, map_smul]
  · rw [planeComparisonMap_of_not_mem hy, planeComparisonMap_of_not_mem hy,
      map_zero, smul_zero]

private theorem uniformReference_scaled_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) F x) (c : ℝ) :
    mvfderiv (I := I) (c • F) x = c • mvfderiv (I := I) F x := by
  have hh := mvfderiv_smul (a := fun _z : M => c) mdifferentiableAt_const hF
  rw [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hh
  exact hh

theorem exists_edge_reference_chart_parameters_uniform {β γ ι : ℝ}
    (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) (hι : 0 < ι) :
    ∃ Δ₀ > 1, ∀ Δ, Δ₀ ≤ Δ → ∃ τ₀ > 0, ∃ κ > 0, ∀ τ, τ ≤ τ₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Q : M → WithLp 2 (ℝ × ℝ)) (p : M) (A : Set M),
      (∀ y ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g y (-κ ^ 2)) →
      Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      ∀ x, x ∈ ball p (15 * Δ) → 9 / 100 * Δ ≤ infDist x A →
        infDist x A ≤ 101 / 10 * Δ →
      ∀ q : ℝ, (hq : 99 / 100 ≤ q) → q ≤ 101 / 100 →
      ∃ anchors : Fin 2 → M, ∃ χ : M → EuclideanSpace ℝ (Fin 2),
        (∀ j, anchors j ∈ ball p (20 * Δ) ∧
          dist (Q (anchors j)) (Q x + planeReferenceIsometry.symm
            (EuclideanSpace.single j (Δ / 40))) ≤ τ * Δ) ∧
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ χ (ball x (300 * q)) ∧
        χ x = 0 ∧
        (∀ y ∈ ball x (300 * q), Function.Surjective (mvfderiv (I := I) χ y)) ∧
        (∀ y ∈ ball x (300 * q),
          let L := q • mvfderiv (I := I) χ y
          ‖L.comp L.adjoint - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ < γ / 4) ∧
        (∀ j, ∀ y ∈ ball x (300 * q),
          ∀ v ∈ minimizingDirectionsTo g hEnorm {anchors j} y,
          Real.sqrt (g.inner y (q • gradFun g (fun z => χ z j) y - v)
            (q • gradFun g (fun z => χ z j) y - v)) < ι) ∧
        (∀ j, ∀ y ∈ ball x (300 * q),
          ∀ v ∈ minimizingDirectionsTo g hEnorm {anchors j} y,
          let gx := DifferentialGeometry.scaleMetric (q⁻¹ ^ 2) (by positivity) g
          Real.sqrt (gx.inner y (gradFun gx (fun z => χ z j) y - q • v)
            (gradFun gx (fun z => χ z j) y - q • v)) < ι) ∧
        (∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (100 * q),
          ‖χ y - χ z‖ ≤ (1 + γ / 4) * (dist y z / q)) ∧
        (∀ y ∈ ball x (100 * q),
          infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) < 25 * γ) ∧
        (∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
          ∃ y ∈ ball x (100 * q), ‖χ y - v‖ < 25 * γ) ∧
        (∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (400 * q / γ), q < dist y z →
          ∀ W : TangentSpace I y, g.inner y W W = 1 →
          intrinsicGeodesic g hEnorm y W (dist y z) = z →
          ‖q • mvfderiv (I := I) χ y W - (dist y z / q)⁻¹ •
            (planeReferenceIsometry (planeComparisonMap Q p x Δ q z) -
              planeReferenceIsometry (planeComparisonMap Q p x Δ q y))‖ < γ / 4) ∧
        (∀ y ∈ ball x (100 * q),
          ‖χ y - planeReferenceIsometry (planeComparisonMap Q p x Δ q y)‖ < γ) ∧
        (letI := mM.rescale q⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq));
          ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
            ∀ y, Φ.toFun y = @planeComparisonMap M mM Q p x Δ q y)
    := by
  let ε := min (γ / 100000000 : ℝ) (ι / 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεγ : ε ≤ γ / 100000000 := min_le_left _ _
  have hει : ε < ι := (min_le_right _ _).trans_lt (by linarith)
  have hε1 : ε < 1 := by linarith
  let R := 500 / γ
  have hR : 400 < R := by dsimp [R]; rw [lt_div_iff₀ hγ]; nlinarith
  have hβsmall : β < 1 / 100 := by linarith
  obtain ⟨Δ₀, hΔ₀, hparameters⟩ :=
    exists_coarse_edge_reference_parameters_uniform.{uE, uH, uM} hβ hβsmall hε hε1 hR
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ
  obtain ⟨τ₀, hτ₀, κ, hκ, hparametersτ⟩ := hparameters Δ hΔ
  refine ⟨τ₀, hτ₀, κ, hκ, ?_⟩
  intro τ hττ₀ E hnorm hspace hfinite hne H htop I hboundary M mM hcharts hmanifold hsigma
    hcomplete hRB hRiem hcontinuous g hEnorm Q p A hsec hQp hdist hheight hcover hpA
    hborder hbordercover x hx hxA hxA' q hq hq'
  have hqpos : 0 < q := by linarith
  obtain ⟨anchors, f, hanchors, hf, hf0, hgrad, hvalue, htest, hgram, hPhi⟩ :=
    hparametersτ τ hττ₀ E H I M g hEnorm Q p A hsec hQp hdist hheight hcover hpA hborder hbordercover
      x hx hxA hxA'
  let F := edgeReferenceCoordinates f
  let χ : M → EuclideanSpace ℝ (Fin 2) := q⁻¹ • F
  let c := ε ^ 2 / 40 + 2 * ε + ε ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcε : c < 4 * ε := by dsimp [c]; nlinarith
  have hcγ : 4 * c < γ / 4 := by nlinarith
  have hsqrt : Real.sqrt (1 + 4 * c) ≤ 1 + γ / 4 := by
    have hh := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * c)
    nlinarith [Real.sqrt_nonneg (1 + 4 * c)]
  have h300 : 300 * q < 305 := by linarith
  have h100 : 100 * q < 305 := by linarith
  have hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ F (ball x 305) :=
    edgeReferenceCoordinates_smooth hf
  have hFAt (y : M) (hy : y ∈ ball x 305) :=
    hF.contMDiffAt (Metric.isOpen_ball.mem_nhds hy)
  have hfAt (y : M) (hy : y ∈ ball x 305) (j : Fin 2) :=
    (hf j).contMDiffAt (Metric.isOpen_ball.mem_nhds hy)
  have hD (y : M) (hy : y ∈ ball x 305) :
      q • mvfderiv (I := I) χ y = mvfderiv (I := I) F y := by
    rw [uniformReference_scaled_derivative ((hFAt y hy).mdifferentiableAt (by simp)),
      smul_smul, mul_inv_cancel₀ hqpos.ne', one_smul]
  have hGram (y : M) (hy : y ∈ ball x 305) :
      ‖(mvfderiv (I := I) F y).comp (mvfderiv (I := I) F y).adjoint -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ < γ / 4 := by
    apply lt_of_le_of_lt (rankTwo_gram_operator_bound _
      (fun j => gradFun g (f j) y) hc ?_ ?_) hcγ
    · intro v i
      rw [edgeReferenceCoordinates_derivative (hfAt y hy)]
      have hh := inner_gradFun g (f i) y v
      change g.inner y (gradFun g (f i) y) v = mvfderiv (I := I) (f i) y v at hh
      exact hh.symm.trans (hEnorm.inner_eq y _ _).symm
    · intro i j
      simpa only [hEnorm.inner_eq] using (hgram y hy i j).le
  have hχ0 : χ x = 0 := by
    ext j
    change q⁻¹ * f j x = 0
    rw [hf0 j, mul_zero]
  have hLip : ∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (100 * q),
      ‖χ y - χ z‖ ≤ (1 + γ / 4) * (dist y z / q) := by
    intro y hy z hz
    have hh := edgeReferenceCoordinates_lipschitz g hEnorm hc
      (fun j => (hf j).mono (ball_subset_ball (by linarith)))
      (fun y hy i j => (hgram y (ball_subset_ball (by linarith) hy) i j).le) hy hz
    change ‖q⁻¹ • F y - q⁻¹ • F z‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqpos)]
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hsqrt dist_nonneg)
    have hh'' := mul_le_mul_of_nonneg_left hh' (inv_pos.mpr hqpos).le
    convert hh'' using 1
    ring
  have hclose : ∀ y ∈ ball x (100 * q),
      ‖χ y - planeReferenceIsometry (planeComparisonMap Q p x Δ q y)‖ < γ := by
    intro y hy
    have hRy : y ∈ ball x (R + 3) := ball_subset_ball (by linarith) hy
    have he : ‖F y - planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y)‖ ≤
        2 * (ε * dist y x + ε ^ 2 / 40) := by
      apply uniformReference_pair_norm (by positivity)
      intro j
      simpa only [F, edgeReferenceCoordinates, PiLp.sub_apply] using (hvalue j y hRy).le
    rw [uniformReference_plane_scale]
    change ‖q⁻¹ • F y - q⁻¹ • planeReferenceIsometry
      (planeComparisonMap Q p x Δ 1 y)‖ < _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqpos)]
    rw [← div_eq_inv_mul, div_lt_iff₀ hqpos]
    have hdisty : dist y x < 100 * q := Metric.mem_ball.mp hy
    have hsmall : ε ^ 2 < ε := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hdisty hε]
  have hImages :
      (∀ y ∈ ball x (100 * q),
        infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) < 25 * γ) ∧
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
        ∃ y ∈ ball x (100 * q), ‖χ y - v‖ < 25 * γ := by
    let instRescaled : MetricSpace M := mM.rescale q⁻¹ (inv_pos.mpr hqpos)
    have hball : @ball M (mM.rescale q⁻¹ (inv_pos.mpr hqpos)).toPseudoMetricSpace x 100 =
        @ball M mM.toPseudoMetricSpace x (100 * q) := by
      have he := MetricSpace.rescale_ball mM q⁻¹ (inv_pos.mpr hqpos) x (100 * q)
      simpa only [mul_comm (100 : ℝ) q, ← mul_assoc, inv_mul_cancel₀ hqpos.ne', one_mul]
        using he
    obtain ⟨Φ, hΦ⟩ := hPhi q hq hq'
    let e := planeReferenceIsometry.toIsometryEquiv
    have he0 : e (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) =
        (0 : EuclideanSpace ℝ (Fin 2)) := by
      change planeReferenceIsometry 0 = 0
      exact map_zero _
    let Φ' := Φ.mapTargetIsometryAt e _ he0
    have hΦ' (y : M) : Φ'.toFun y =
        planeReferenceIsometry (@planeComparisonMap M mM Q p x Δ q y) := by
      change e (Φ.toFun y) = _
      rw [hΦ]
      rfl
    have hh := edgeReference_image_clauses hβ hβγ hγ hγ1 Φ' χ hχ0
      (by intro y hy; rw [hΦ' y]; exact hclose y (hball ▸ hy))
      (by
        intro y hy z hz
        have hh := hLip y (hball ▸ hy) z (hball ▸ hz)
        change ‖χ y - χ z‖ ≤ (1 + γ / 4) * (q⁻¹ * @dist M mM.toDist y z)
        convert hh using 1
        ring)
    simpa only [hball] using hh
  have hAnchorGradient : ∀ j, ∀ y ∈ ball x (300 * q),
      ∀ v ∈ minimizingDirectionsTo g hEnorm {anchors j} y,
      Real.sqrt (g.inner y (q • gradFun g (fun z => χ z j) y - v)
        (q • gradFun g (fun z => χ z j) y - v)) < ι := by
    intro j y hy v hv
    have hy305 := ball_subset_ball h300.le hy
    have hgradχ : q • gradFun g (fun z => χ z j) y = gradFun g (f j) y := by
      change q • gradFun g (q⁻¹ • f j) y = _
      rw [DifferentialGeometry.Geometry.Connection.gradFun_const_smul g q⁻¹
        ((hfAt y hy305 j).mdifferentiableAt (by simp)), smul_smul,
        mul_inv_cancel₀ hqpos.ne', one_smul]
    rw [hgradχ]
    exact (hgrad j y hy305 v hv).trans hει
  have hχsmooth : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ χ (ball x 305) :=
    (((q⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))).contDiff.contMDiff)
      |>.comp_contMDiffOn hF
  refine ⟨anchors, χ, hanchors, hχsmooth.mono (ball_subset_ball h300.le),
    hχ0, ?_, ?_, hAnchorGradient, ?_, hLip, hImages.1, hImages.2, ?_, hclose, hPhi q hq hq'⟩
  · intro y hy
    have hy305 := ball_subset_ball h300.le hy
    have hs : Function.Surjective (mvfderiv (I := I) F y) :=
      surjective_of_gram_perturbation hγ1 (hGram y hy305) (by
        rw [sub_self, norm_zero]
        positivity)
    intro v
    obtain ⟨w, hw⟩ := hs (q • v)
    refine ⟨w, ?_⟩
    have he : q • mvfderiv (I := I) χ y w = q • v := by
      rw [← smul_apply, hD y hy305, hw]
    have he' := congrArg (fun z => q⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ hqpos.ne', one_smul] using he'
  · intro y hy
    dsimp only
    rw [hD y (ball_subset_ball h300.le hy)]
    exact hGram y (ball_subset_ball h300.le hy)
  · intro j y hy v hv
    dsimp only
    rw [edgeRescaled_gradient_norm g (fun z => χ z j) y q hqpos v]
    exact hAnchorGradient j y hy v hv
  · intro y hy z hz hyz W hW hWz
    have hy305 := ball_subset_ball h100.le hy
    have hzR : z ∈ ball x (R + 3) := by
      apply ball_subset_ball _ hz
      dsimp [R]
      have hh : 400 * q / γ ≤ 500 / γ :=
        div_le_div_of_nonneg_right (by nlinarith) hγ.le
      linarith
    have hder : q • mvfderiv (I := I) χ y W = mvfderiv (I := I) F y W := by
      rw [← smul_apply, hD y hy305]
    have htarget : (dist y z / q)⁻¹ •
        (planeReferenceIsometry (planeComparisonMap Q p x Δ q z) -
          planeReferenceIsometry (planeComparisonMap Q p x Δ q y)) =
        (dist y z)⁻¹ •
          (planeReferenceIsometry (planeComparisonMap Q p x Δ 1 z) -
            planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y)) := by
      rw [uniformReference_plane_scale Q p x z Δ q, uniformReference_plane_scale Q p x y Δ q,
        ← smul_sub, smul_smul]
      congr 1
      field_simp
    rw [hder, htarget]
    apply lt_of_le_of_lt
      (uniformReference_pair_norm (a := ε + ε ^ 2 / 40) (by positivity) ?_) (by nlinarith)
    intro j
    have ht := htest j y hy305 z hzR (by linarith : 1 / 2 < dist y z) W hW hWz
    change |mvfderiv (I := I) (edgeReferenceCoordinates f) y W j -
      (dist y z)⁻¹ * (planeReferenceIsometry (planeComparisonMap Q p x Δ 1 z) j -
        planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) j)| ≤ _
    rw [edgeReferenceCoordinates_derivative (hfAt y hy305)]
    simpa only [div_eq_inv_mul] using ht.le


end DifferentialGeometry.Geometry.Collapse
