import DifferentialGeometry.Geometry.Collapse.RankTwoAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.CirclePacketApplications
import DifferentialGeometry.Geometry.Collapse.CircleFiberCircle
import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.RealProductRescaling

/-!
# A circle packet from one actual splitting

The fixed 201 rescaling constructs the previously supplied coordinates on the original
200-ball. One choice is retained through enclosure, bundle, circle and cutoff construction.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private def circleProductRescale {Y : Type*} [mY : MetricSpace Y]
    (c : ℝ) (hc : 0 < c) :
    @IsometryEquiv (WithLp 2 (ℝ² × Y)) (WithLp 2 (ℝ² × Y))
      ((inferInstance : MetricSpace (WithLp 2 (ℝ² × Y))).rescale c hc).toPseudoEMetricSpace
      (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoEMetricSpace := by
  let e : WithLp 2 (ℝ² × Y) ≃ WithLp 2 (ℝ² × Y) :=
    { toFun := fun x => WithLp.toLp 2 (c • x.fst, x.snd)
      invFun := fun x => WithLp.toLp 2 (c⁻¹ • x.fst, x.snd)
      left_inv := by
        intro x
        apply (WithLp.equiv 2 _).injective
        change (c⁻¹ • (c • x.fst), x.snd) = (x.fst, x.snd)
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      right_inv := by
        intro x
        apply (WithLp.equiv 2 _).injective
        change (c • (c⁻¹ • x.fst), x.snd) = (x.fst, x.snd)
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] }
  refine @IsometryEquiv.mk (WithLp 2 (ℝ² × Y)) (WithLp 2 (ℝ² × Y))
    ((inferInstance : MetricSpace (WithLp 2 (ℝ² × Y))).rescale c hc).toPseudoEMetricSpace
    (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoEMetricSpace e ?_
  apply @Isometry.of_dist_eq (WithLp 2 (ℝ² × Y)) (WithLp 2 (ℝ² × Y))
    ((inferInstance : MetricSpace (WithLp 2 (ℝ² × Y))).rescale c hc).toPseudoMetricSpace
    (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoMetricSpace
  intro x y
  change @dist (WithLp 2 (ℝ² × Y))
    (MetricSpace.scaledProduct inferInstance mY c hc).toDist (e x) (e y) = c * dist x y
  rw [MetricSpace.scaledProduct_dist, WithLp.prod_dist_eq_sqrt_sq_add_sq]
  have hfirst : dist (e x).fst (e y).fst = c * dist x.fst y.fst := by
    change dist (c • x.fst) (c • y.fst) = _
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]
  rw [hfirst, mul_pow, ← mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rfl

theorem exists_large_ball_rankTwo_coordinate_parameters {γ : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1 / 10) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 1000 ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ {β : ℝ}, β ≤ β₀ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ², ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200) ∧ η q = 0 ∧
        (∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x)) ∧
        LipschitzOnWith 2 η (ball q 200) ∧
        ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ
 := by
  let ε : ℝ := min (γ / 201) (1 / 10000)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : ε < 1 / 10 := by
    have hh : ε ≤ γ / 201 := min_le_left _ _
    nlinarith
  have hR : max 2 ε⁻¹ < ε⁻¹ + 3 := by
    have hinv : 10 < ε⁻¹ := (lt_inv_comm₀ (by norm_num) hε).mpr (by simpa using hεsmall)
    rw [max_eq_right (by linarith)]
    linarith
  obtain ⟨ν₀, hν₀, hν₀small, hprod⟩ :=
    exists_rankTwo_adapted_coordinate_parameters.{uE, uH, u, w} hε hεsmall hR
  let β₀ : ℝ := min (ν₀ / 804) (1 / 1000)
  refine ⟨β₀, by dsimp [β₀]; positivity, min_le_right _ _, ?_⟩
  intro E instNorm instSpace instFinite instNe H instTop I instBoundary
    M m instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y mY q a β hβ F hsec
  have hβp : 0 < β := F.error_pos
  have hβsmall : β ≤ 1 / 1000 := hβ.trans (min_le_right _ _)
  let ν : ℝ := 804 * β
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνle : ν ≤ ν₀ := by
    have hh := hβ.trans (min_le_left _ _)
    dsimp [ν]
    linarith
  have hνone : ν < 1 := hνle.trans_lt ((hν₀small.trans_le (min_le_right _ _)).trans (by norm_num))
  have hbudget : 3 * (1 / 201 : ℝ) * β ≤ ν := by dsimp [ν]; nlinarith
  have hdomain : dist q q + ν⁻¹ / (1 / 201 : ℝ) + 2 * β ≤ β⁻¹ := by
    have hinv : 1 ≤ β⁻¹ := (one_le_inv₀ hβp).mpr (by linarith)
    have he : ν⁻¹ / (1 / 201 : ℝ) = β⁻¹ / 4 := by
      dsimp [ν]
      field_simp
      ring
    rw [dist_self, zero_add, he]
    linarith
  let original := F.toFun
  let Fc := F.recenterRescale q (by norm_num : (0 : ℝ) < 1 / 201)
    hbudget hνone hdomain
  let e := circleProductRescale (Y := Y) (1 / 201) (by norm_num)
  have hbase : e (F.toFun q) = WithLp.toLp 2 ((0 : ℝ²), a) := by
    rw [F.basepoint]
    change WithLp.toLp 2 ((1 / 201 : ℝ) • (0 : ℝ²), a) = _
    rw [smul_zero]
  let F' := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ² × Y))
    (WithLp 2 (ℝ² × Y)) (m.rescale (1 / 201) (by norm_num))
    ((inferInstance : MetricSpace (WithLp 2 (ℝ² × Y))).rescale (1 / 201) (by norm_num))
    (MetricSpace.scaledProduct inferInstance mY (1 / 201) (by norm_num))
    q (F.toFun q) ν Fc e (WithLp.toLp 2 ((0 : ℝ²), a)) hbase
  have hmetric : ∀ x y : M, riemannianEDistOf g x y = ENNReal.ofReal (dist x y) := by
    intro x y
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_dist]
  let : MetricSpace M := m.rescale (1 / 201) (by norm_num)
  let : CompleteSpace M := (m.rescale_completeSpace_iff (1 / 201) (by norm_num)).mpr
    instComplete
  let := radialScaledBundle g (1 / 201) (by norm_num)
  let := radialScaledContinuous g (1 / 201) (by norm_num)
  let := radialScaledManifold (m := m) g hmetric (1 / 201) (by norm_num)
  let gc := scaleMetric ((1 / 201 : ℝ) ^ 2) (by positivity) g
  have hn : IsMetricNorm gc := isMetricNorm_of_riemannianBundle gc
  let : MetricSpace Y := mY.rescale (1 / 201) (by norm_num)
  have hF' (x : M) : F'.toFun x =
      WithLp.toLp 2 ((1 / 201 : ℝ) • (original x).fst, (original x).snd) := rfl
  have hscaled : ∀ y ∈ ball q ν⁻¹, SectionalBoundedBelowAt gc y (-ν ^ 2) := by
    intro y hy
    have hball : y ∈ @ball M m.toPseudoMetricSpace q β⁻¹ := by
      change (1 / 201 : ℝ) * @dist M m.toDist y q < ν⁻¹ at hy
      have he : ν⁻¹ = (1 / 804 : ℝ) * β⁻¹ := by dsimp [ν]; rw [mul_inv_rev]; ring
      rw [he] at hy
      change @dist M m.toDist y q < β⁻¹
      linarith [inv_pos.mpr hβp]
    apply (sectionalBoundedBelowAt_scaleMetric_iff (by positivity)).mpr
    apply SectionalBoundedBelowAt.mono (hsec y hball)
    dsimp [ν]
    nlinarith [sq_nonneg β]
  obtain ⟨ηc, hc, hzero, hrank, hlip, hclose, himage, hcover, htests⟩ :=
    hprod ν hν hνle E H I M gc hn Y q a F' hscaled
  have h200 (x : M) (hx : x ∈ @ball M m.toPseudoMetricSpace q 200) : x ∈ ball q 1 := by
    change (1 / 201 : ℝ) * @dist M m.toDist x q < 1
    change @dist M m.toDist x q < 200 at hx
    linarith
  let η : M → ℝ² := fun x => (201 : ℝ) • ηc x
  have hsm : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (@ball M m.toPseudoMetricSpace q 200) :=
    ((show ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M => (201 : ℝ)) (ball q 3)
      from contMDiffOn_const).smul hc).mono (fun x hx =>
      ball_subset_ball (by norm_num) (h200 x hx))
  have hder (x : M) (hx : x ∈ @ball M m.toPseudoMetricSpace q 200) :
      mvfderiv (I := I) η x = (201 : ℝ) • mvfderiv (I := I) ηc x := by
    have hmd := (hc x (ball_subset_ball (by norm_num) (h200 x hx))).contMDiffAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by norm_num) (h200 x hx)))
      |>.mdifferentiableAt (by simp)
    simpa [η, mvfderiv_const] using
      (mvfderiv_fun_smul (I := I) (a := fun x : M => (201 : ℝ)) mdifferentiableAt_const hmd)
  refine ⟨η, hsm, ?_, ?_, ?_, ?_⟩
  · change (201 : ℝ) • ηc q = 0
    rw [hzero, smul_zero]
  · intro x hx
    have hsurj : Surjective (mvfderiv (I := I) η x) := by
      intro y
      obtain ⟨v, hv⟩ := hrank x (h200 x hx) ((201 : ℝ)⁻¹ • y)
      refine ⟨v, ?_⟩
      rw [hder x hx]
      simp only [smul_apply, hv, smul_smul,
        mul_inv_cancel₀ (by norm_num : (201 : ℝ) ≠ 0), one_smul]
    intro y
    obtain ⟨v, hv⟩ := hsurj ((NormedSpace.fromTangentSpace (η x)) y)
    refine ⟨v, (NormedSpace.fromTangentSpace (η x)).injective ?_⟩
    exact hv
  · apply @LipschitzOnWith.of_dist_le_mul M ℝ² m.toPseudoMetricSpace inferInstance
    intro x hx y hy
    change dist ((201 : ℝ) • ηc x) ((201 : ℝ) • ηc y) ≤
      (2 : ℝ) * @dist M m.toDist x y
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 201), dist_eq_norm]
    have hh := hlip x (h200 x hx) y (h200 y hy)
    change ‖ηc x - ηc y‖ ≤ (1 + ε) * ((1 / 201 : ℝ) * @dist M m.toDist x y) at hh
    have he : ε ≤ 1 / 10000 := min_le_right _ _
    nlinarith [@dist_nonneg M m.toPseudoMetricSpace x y]
  · intro x hx
    have hh := hclose x (h200 x hx)
    rw [hF'] at hh
    change ‖ηc x - (1 / 201 : ℝ) • (original x).fst‖ < ε / 8 at hh
    have he : η x - (original x).fst =
        (201 : ℝ) • (ηc x - (1 / 201 : ℝ) • (original x).fst) := by
      simp only [η, smul_sub, smul_smul]
      norm_num
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 201)]
    have heps : ε ≤ γ / 201 := min_le_left _ _
    nlinarith

theorem exists_early_simultaneous_circle_packet_parameters :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
          eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ → KleinerLottApprox q c σ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
      ∃ hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
        η q = 0 ∧ LipschitzOnWith 2 η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
        (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
        ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
          (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
          (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
          ∀ R (hR : 0 < R) (hRr : R < 100),
            let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
            letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            let U : TopologicalSpace.Opens
                (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
              ⟨f ⁻¹' planeBallInner 100 R,
                (planeBallInner 100 R).isOpen.preimage
                  (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
            ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                ({x // f x = y₀} × planeBallInner 100 R) U ∞),
              (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
        (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
          let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
          letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          Nonempty (Circle ≃ₘ⟮𝓡 1,
            𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
          ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9
 := by
  obtain ⟨a₀, ha₀, ha₀small, hres⟩ :=
    exists_simultaneous_circle_residual_threshold.{u, v, w}
  refine ⟨a₀, ha₀, ?_⟩
  intro γ hγ hγone
  obtain ⟨β₀, hβ₀, hsmall, hcoordinates⟩ :=
    exists_large_ball_rankTwo_coordinate_parameters.{uE, uH, u, w} hγ hγone
  refine ⟨min β₀ a₀, lt_min hβ₀ ha₀, min_le_right _ _, ?_⟩
  intro E instNorm instSpace instFinite instNe H instTop I instBoundary
    M m instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y mY q a C mC instC c hlen hdim hcomp σ β hσ hβ f F hsec
  obtain ⟨η, hη, hq, hrank, hlip, hclose⟩ :=
    hcoordinates E H I M g hEnorm Y q a (hβ.trans (min_le_left _ _)) F hsec
  have hres' : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1 := by
    intro x hx
    exact hres M q C c hlen hdim hcomp Y a σ β
      hσ (hβ.trans (min_le_right _ _)) f F x
      ((mem_ball.mp hx).le.trans (by norm_num))
  have hβsmall : β ≤ 1 / 200 := (hβ.trans (min_le_left _ _)).trans
    (hsmall.trans (by norm_num))
  have hclose' : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10 :=
    fun x hx => (hclose x hx).trans hγone
  obtain ⟨h102, h2, hbundle, ζ, hζ, hc, hζ01, hζ1, hsupp⟩ :=
    circlePacket_of_rank_two_coordinates g hEnorm F hβsmall hres' hη hrank hlip hq hclose'
  refine ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, hbundle, ?_,
    ζ, hζ, hc, hζ01, hζ1, hsupp⟩
  intro hdim3 z
  exact circleFiber_local_model_circle g hEnorm hdim3 hη hrank hlip hq h102 h2 z

theorem exists_simultaneous_circle_packet_parameters {γ : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1 / 10) :
    ∃ a₂ : ℝ, 0 < a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
          eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ {σ β : ℝ}, σ ≤ a₂ → β ≤ a₂ → KleinerLottApprox q c σ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
      ∃ hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
        η q = 0 ∧ LipschitzOnWith 2 η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
        (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
        ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
          (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
          (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
          ∀ R (hR : 0 < R) (hRr : R < 100),
            let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
            letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            let U : TopologicalSpace.Opens
                (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
              ⟨f ⁻¹' planeBallInner 100 R,
                (planeBallInner 100 R).isOpen.preimage
                  (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
            ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                ({x // f x = y₀} × planeBallInner 100 R) U ∞),
              (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
        (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
          let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
          letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          Nonempty (Circle ≃ₘ⟮𝓡 1,
            𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
          ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9
 := by
  obtain ⟨a₂, ha₂, hparameters⟩ :=
    exists_early_simultaneous_circle_packet_parameters.{uE, uH, u, v, w}
  obtain ⟨β₀, hβ₀, hβa, hproduction⟩ := hparameters γ hγ hγone
  refine ⟨min a₂ β₀, lt_min ha₂ hβ₀, ?_⟩
  intro E instNorm instSpace instFinite instNe H instTop I instBoundary
    M m instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y mY q a C mC instC c hlen hdim hcomp σ β hσ hβ f F hsec
  exact hproduction E H I M g hEnorm Y q a C c hlen hdim hcomp
    (hσ.trans (min_le_left _ _)) (hβ.trans (min_le_right _ _)) f F hsec

end DifferentialGeometry.Geometry.Collapse
