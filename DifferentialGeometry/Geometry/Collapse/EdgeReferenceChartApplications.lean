import DifferentialGeometry.Geometry.Collapse.LocalGradientLipschitz
import DifferentialGeometry.Geometry.Metric.Approximation.PlaneReferenceRadius
import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChart
import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProduct

/-!
# Native plane coordinates and actual coarse-chart anchor consumers

The exact plane isometry transports the original comparison map. All four
prescribed anchors lie in the actual approximation source, not merely in the
coarse chart's larger ball.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold DifferentialGeometry.Analysis
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

namespace GC.MetricGeometry


def planeReferenceIsometry : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toLinearEquiv := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toLinearEquiv.trans
    euclideanPlaneProdEquiv.symm.toLinearEquiv
  norm_map' := by
    intro z
    have h : ‖euclideanPlaneProdEquiv.symm z.ofLp‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [euclideanPlaneProdEquiv_symm_apply, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, WithLp.prod_norm_sq_eq_of_L2]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.norm_eq_abs, sq_abs]
      rfl
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp h

@[simp] theorem planeReferenceIsometry_apply_zero (z : WithLp 2 (ℝ × ℝ)) :
    planeReferenceIsometry z 0 = z.fst := by
  simp [planeReferenceIsometry, euclideanPlaneProdEquiv_symm_apply]

@[simp] theorem planeReferenceIsometry_apply_one (z : WithLp 2 (ℝ × ℝ)) :
    planeReferenceIsometry z 1 = z.snd := by
  simp [planeReferenceIsometry, euclideanPlaneProdEquiv_symm_apply]


def planeReferenceProductIsometry :
    WithLp 2 (ℝ × ℝ) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 2) × PUnit.{1}) :=
  planeReferenceIsometry.toIsometryEquiv.trans
    (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin 2)) PUnit.{1}).symm

variable {X : Type*} [MetricSpace X] {Q : X → WithLp 2 (ℝ × ℝ)}
  {p x : X} {Δ τ ν : ℝ}

theorem exists_planeReference_rankTwo_source (hΔ : 0 < Δ) (hν : 0 < ν) (hν1 : ν < 1)
    (hτ : τ ≤ 1 / 10000) (hradius : ν⁻¹ ≤ Δ / 20)
    (hanchors : Δ / 40 + 2 * (τ * Δ) < ν⁻¹) (herror : 4 * (τ * Δ) < ν)
    (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ →
      z.snd ∈ Icc 0 (100 * Δ) → ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd)
    (hhigh : (Q x).snd ≤ 102 / 10 * Δ) :
    ∃ F : KleinerLottApprox x
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), (PUnit.unit : PUnit.{1}))) ν,
      (∀ y, (F.toFun y).fst = planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y)) ∧
      ∃ A B : Fin 2 → X,
        (∀ j, A j ∈ ball p (20 * Δ) ∧ A j ∈ ball x ν⁻¹ ∧
          dist (Q (A j)) (Q x + planeReferenceIsometry.symm
            (EuclideanSpace.single j (Δ / 40))) ≤ τ * Δ ∧
          dist (F.toFun (A j)) (rankTwoAxisPoint j (Δ / 40) (PUnit.unit : PUnit.{1})) < 2 * ν) ∧
        ∀ j, B j ∈ ball p (20 * Δ) ∧ B j ∈ ball x ν⁻¹ ∧
          dist (Q (B j)) (Q x + planeReferenceIsometry.symm
            (EuclideanSpace.single j (-(Δ / 40)))) ≤ τ * Δ ∧
          dist (F.toFun (B j)) (rankTwoAxisPoint j (-(Δ / 40)) (PUnit.unit : PUnit.{1})) < 2 * ν
 := by
  obtain ⟨F₀, hF₀⟩ := exists_planeComparison_at_radius_unscaled
    hΔ hν hν1 hτ hradius herror hQp hdist hcover hx hlow hhigh
  let e := planeReferenceProductIsometry
  have he0 : e (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) =
      WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), (PUnit.unit : PUnit.{1})) := by
    change WithLp.toLp 2 (planeReferenceIsometry 0, (PUnit.unit : PUnit.{1})) = _
    rw [map_zero]
  let F := F₀.mapTargetIsometryAt e _ he0
  have hfst (y : X) : (F.toFun y).fst =
      planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y) := by
    change planeReferenceIsometry (F₀.toFun y) = _
    rw [hF₀]
  have hchoose (j : Fin 2) (t : ℝ) (ht : |t| = Δ / 40) :
      ∃ a ∈ ball p (20 * Δ), a ∈ ball x ν⁻¹ ∧
        dist (Q a) (Q x + planeReferenceIsometry.symm (EuclideanSpace.single j t)) ≤ τ * Δ ∧
        dist (F.toFun a) (rankTwoAxisPoint j t (PUnit.unit : PUnit.{1})) < 2 * ν := by
    let v := planeReferenceIsometry.symm (EuclideanSpace.single j t)
    have hv : ‖v‖ ≤ Δ / 40 := by
      simp only [v, LinearIsometryEquiv.norm_map, PiLp.norm_single,
        Real.norm_eq_abs, ht, le_refl]
    obtain ⟨a, ha, he, hs⟩ := exists_planeComparison_anchor_in_source (q := 1)
      hΔ zero_lt_one hτ (by simpa only [one_mul] using hanchors)
      hQp hdist hcover hx hlow hhigh hv
    have has : a ∈ ball x ν⁻¹ := by simpa only [Metric.mem_ball, inv_one, one_mul] using hs
    have ha200 := ball_subset_ball (by linarith : 20 * Δ ≤ 200 * Δ) ha
    have hfa : F.toFun a = e (Q a - Q x) := by
      change e (F₀.toFun a) = e (Q a - Q x)
      rw [hF₀ a, planeComparisonMap_of_mem ha200, inv_one, one_smul]
    have hea : e v = rankTwoAxisPoint j t (PUnit.unit : PUnit.{1}) := by
      change WithLp.toLp 2 (planeReferenceIsometry v, (PUnit.unit : PUnit.{1})) = _
      rw [LinearIsometryEquiv.apply_symm_apply]
      rfl
    have hc : dist (F.toFun a) (rankTwoAxisPoint j t (PUnit.unit : PUnit.{1})) ≤ τ * Δ := by
      rw [hfa, ← hea, e.dist_eq, dist_eq_norm]
      rw [dist_eq_norm] at he
      convert he using 1
      congr 1
      abel
    refine ⟨a, ha, has, he, hc.trans_lt ?_⟩
    linarith
  choose A hAp hAx hAQ hAF using fun j : Fin 2 =>
    hchoose j (Δ / 40) (abs_of_pos (by positivity))
  choose B hBp hBx hBQ hBF using fun j : Fin 2 =>
    hchoose j (-(Δ / 40)) (by rw [abs_neg, abs_of_pos (by positivity)])
  exact ⟨F, hfst, A, B, fun j => ⟨hAp j, hAx j, hAQ j, hAF j⟩,
    fun j => ⟨hBp j, hBx j, hBQ j, hBF j⟩⟩

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH uM

theorem exists_coarse_edge_reference_parameters {β ε R : ℝ}
    (hβ : 0 < β) (hβsmall : β < 1 / 100)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 400 < R) :
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
  obtain ⟨κ, hκ, hproduce⟩ := hparams (Δ / 40) hs
  let τ := min (1 / 100000 : ℝ) (min (ν / (8 * Δ)) (β / (8 * Δ)))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτbound : τ ≤ 1 / 10000 :=
    (min_le_left _ _).trans (by norm_num)
  have hτν : 4 * (τ * Δ) < ν := by
    have hh : τ ≤ ν / (8 * Δ) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at hh
    nlinarith
  have hτβ : 4 * (τ * Δ) < β := by
    have hh : τ ≤ β / (8 * Δ) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hh
    nlinarith
  have hinv : ν⁻¹ = Δ / 30 := by dsimp [ν]; field_simp
  have hradius : ν⁻¹ ≤ Δ / 20 := by rw [hinv]; linarith
  have hanchors : Δ / 40 + 2 * (τ * Δ) < ν⁻¹ := by
    rw [hinv]
    have hh : τ ≤ (1 / 100000 : ℝ) := min_le_left _ _
    nlinarith
  refine ⟨τ, hτ, κ, hκ, ?_⟩
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


section BufferedLipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem edgeReferenceCoordinates_lipschitz
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {f : Fin 2 → M → ℝ} {x : M} {a c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (ball x (3 * a)))
    (hgram : ∀ y ∈ ball x (3 * a), ∀ i j,
      |g.inner y (gradFun g (f i) y) (gradFun g (f j) y) -
        (if i = j then 1 else 0)| ≤ c)
    {y z : M} (hy : y ∈ ball x a) (hz : z ∈ ball x a) :
    ‖edgeReferenceCoordinates f y - edgeReferenceCoordinates f z‖ ≤
      Real.sqrt (1 + 4 * c) * dist y z := by
  have hχ := edgeReferenceCoordinates_smooth hf
  have hfAt (y : M) (hy : y ∈ ball x (3 * a)) (j : Fin 2) :=
    ((hf j).contMDiffAt (Metric.isOpen_ball.mem_nhds hy))
  apply norm_sub_le_of_gradFun_inner_le_on_ball g hEnorm ?_ ?_ hy hz
  · intro e he y hy
    exact ((innerSL ℝ e).contDiff.contMDiff.comp_contMDiffOn hχ).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hy) |>.mdifferentiableAt (by simp)
  · intro e he y hy
    rw [← norm_tangent_eq_sqrt_gInner hEnorm,
      edgeReferenceCoordinates_covector_gradient g hEnorm (hfAt y hy)]
    calc
      _ ≤ ‖(mvfderiv (I := I) (edgeReferenceCoordinates f) y).adjoint‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖mvfderiv (I := I) (edgeReferenceCoordinates f) y‖ := by
        rw [LinearIsometryEquiv.norm_map, he, mul_one]
      _ ≤ Real.sqrt (1 + 4 * c) :=
        edgeReferenceCoordinates_operator_bound g hEnorm hc (hfAt y hy) (hgram y hy)

end BufferedLipschitz

theorem edgeReference_image_clauses {X : Type*} [MetricSpace X] {x : X} {β γ : ℝ}
    (hβ : 0 < β) (hβγ : β < γ / 1000) (hγ : 0 < γ) (hγ1 : γ < 1 / 100)
    (F : KleinerLottApprox x (0 : EuclideanSpace ℝ (Fin 2)) β)
    (χ : X → EuclideanSpace ℝ (Fin 2)) (hχ0 : χ x = 0)
    (hclose : ∀ y ∈ ball x 100, ‖χ y - F.toFun y‖ < γ)
    (hLip : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100,
      ‖χ y - χ z‖ ≤ (1 + γ / 4) * dist y z) :
    (∀ y ∈ ball x 100, infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) < 25 * γ) ∧
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
        ∃ y ∈ ball x 100, ‖χ y - v‖ < 25 * γ
    := by
  have hβ1 : β < 1 / 1000 := by linarith
  have hbudget : (200 : ℝ) < β⁻¹ - β := by
    have hi : (1000 : ℝ) < β⁻¹ := (lt_inv_comm₀ (by norm_num) hβ).mpr (by linarith)
    linarith
  have hx : x ∈ ball x 100 := mem_ball_self (by norm_num)
  refine ⟨?_, ?_⟩
  · intro y hy
    let v := (1 + γ / 4)⁻¹ • χ y
    have hv : v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100 := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (by linarith : 0 < 1 + γ / 4))]
      have hh := hLip y hy x hx
      rw [hχ0, sub_zero] at hh
      rw [← div_eq_inv_mul]
      apply (div_lt_iff₀ (by linarith : 0 < 1 + γ / 4)).mpr
      nlinarith [Metric.mem_ball.mp hy]
    have he : ‖χ y - v‖ < 25 * γ := by
      have hid : χ y - v = (γ / 4) • v := by
        calc
          χ y - v = (1 - (1 + γ / 4)⁻¹) • χ y := by dsimp [v]; module
          _ = (γ / 4) • v := by
            dsimp [v]
            rw [smul_smul]
            congr 1
            field_simp
            ring
      rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < γ / 4)]
      have hn : ‖v‖ < 100 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
      nlinarith
    exact (infDist_le_dist_of_mem hv).trans_lt (by simpa only [dist_eq_norm] using he)
  · intro v hv
    have hvnorm : ‖v‖ < 100 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    let w := (1 - γ / 8) • v
    have hw0 : 0 < 1 - γ / 8 := by linarith
    have hwnorm : ‖w‖ < 100 * (1 - γ / 8) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hw0]
      nlinarith
    obtain ⟨y, hy, he⟩ := F.coverage_witness w (by
      rw [dist_zero_right]
      linarith)
    have hyr := (abs_le.mp (F.radial_error y hy)).1
    rw [dist_zero_right] at hyr
    have hnorm := norm_le_norm_sub_add (F.toFun y) w
    have hdist : ‖F.toFun y - w‖ < 2 * β := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using he
    have hy100 : y ∈ ball x 100 := by
      change dist y x < 100
      nlinarith
    refine ⟨y, hy100, ?_⟩
    have hshift : ‖w - v‖ < 25 * γ / 2 := by
      have hid : w - v = -(γ / 8) • v := by dsimp [w]; module
      rw [hid, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity : 0 < γ / 8)]
      nlinarith
    have htri := dist_triangle (χ y) (F.toFun y) v
    simp only [dist_eq_norm] at htri
    have htri' := dist_triangle (F.toFun y) w v
    simp only [dist_eq_norm] at htri'
    linarith [hclose y hy100]

end DifferentialGeometry.Geometry.Collapse

