import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartApplications
import DifferentialGeometry.Geometry.Collapse.EdgeBandGradient
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# Actual smooth edge reference charts on the full buffer

The parameters follow the blueprint order: the coarse and curvature tolerances
are chosen after each Delta. The same prescribed anchors, original comparison
map and smooth chart supply every scaled adapted clause.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
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

private theorem reference_pair_norm {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ j, |v j| ≤ a) : ‖v‖ ≤ 2 * a := by
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have h0 := (sq_le_sq₀ (abs_nonneg (v 0)) ha).mpr (hv 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (v 1)) ha).mpr (hv 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg v]

private theorem reference_plane_scale {X : Type*} [MetricSpace X]
    (Q : X → WithLp 2 (ℝ × ℝ)) (p x y : X) (Δ q : ℝ) :
    planeReferenceIsometry (planeComparisonMap Q p x Δ q y) =
      q⁻¹ • planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) := by
  by_cases hy : y ∈ ball p (200 * Δ)
  · rw [planeComparisonMap_of_mem hy, planeComparisonMap_of_mem hy,
      inv_one, one_smul, map_smul]
  · rw [planeComparisonMap_of_not_mem hy, planeComparisonMap_of_not_mem hy,
      map_zero, smul_zero]

private theorem reference_scaled_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) F x) (c : ℝ) :
    mvfderiv (I := I) (c • F) x = c • mvfderiv (I := I) F x := by
  have hh := mvfderiv_smul (a := fun _z : M => c) mdifferentiableAt_const hF
  rw [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hh
  exact hh

universe uE uH uM

theorem exists_edge_reference_chart_parameters {β γ ι : ℝ}
    (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) (hι : 0 < ι) :
    ∃ Δ₀ > 1, ∀ Δ, Δ₀ ≤ Δ → ∃ τ > 0, ∃ κ > 0,
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
    exists_coarse_edge_reference_parameters.{uE, uH, uM} hβ hβsmall hε hε1 hR
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ
  obtain ⟨τ, hτ, κ, hκ, hproduce⟩ := hparameters Δ hΔ
  refine ⟨τ, hτ, κ, hκ, ?_⟩
  intro E hnorm hspace hfinite hne H htop I hboundary M mM hcharts hmanifold hsigma
    hcomplete hRB hRiem hcontinuous g hEnorm Q p A hsec hQp hdist hheight hcover hpA
    hborder hbordercover x hx hxA hxA' q hq hq'
  have hqpos : 0 < q := by linarith
  obtain ⟨anchors, f, hanchors, hf, hf0, hgrad, hvalue, htest, hgram, hPhi⟩ :=
    hproduce E H I M g hEnorm Q p A hsec hQp hdist hheight hcover hpA hborder hbordercover
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
    rw [reference_scaled_derivative ((hFAt y hy).mdifferentiableAt (by simp)),
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
      apply reference_pair_norm (by positivity)
      intro j
      simpa only [F, edgeReferenceCoordinates, PiLp.sub_apply] using (hvalue j y hRy).le
    rw [reference_plane_scale]
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
    hχ0, ?_, ?_, hAnchorGradient, ?_, hLip, hImages.1, hImages.2, ?_, hPhi q hq hq'⟩
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
      rw [reference_plane_scale Q p x z Δ q, reference_plane_scale Q p x y Δ q,
        ← smul_sub, smul_smul]
      congr 1
      field_simp
    rw [hder, htarget]
    apply lt_of_le_of_lt
      (reference_pair_norm (a := ε + ε ^ 2 / 40) (by positivity) ?_) (by nlinarith)
    intro j
    have ht := htest j y hy305 z hzR (by linarith : 1 / 2 < dist y z) W hW hWz
    change |mvfderiv (I := I) (edgeReferenceCoordinates f) y W j -
      (dist y z)⁻¹ * (planeReferenceIsometry (planeComparisonMap Q p x Δ 1 z) j -
        planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) j)| ≤ _
    rw [edgeReferenceCoordinates_derivative (hfAt y hy305)]
    simpa only [div_eq_inv_mul] using ht.le

end DifferentialGeometry.Geometry.Collapse
