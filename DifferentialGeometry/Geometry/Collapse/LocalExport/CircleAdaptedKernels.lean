import DifferentialGeometry.Geometry.Collapse.SimultaneousCircleProduction
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart

/-!
# Circle charts with their original long derivative tests (review-42 packet (i), kernels)

`exists_large_ball_rankTwo_coordinate_parameters` (`SimultaneousCircleProduction.lean`, Codex X77)
builds the rank-two coordinate on `B(q, 200)` by rescaling with `1/201` and keeps only smoothness,
rank, a Lipschitz bound and the value error; the original long derivative tests of
`exists_rankTwo_adapted_coordinate_parameters` (RankTwoAdaptedCoordinates.lean) are dropped there.

* `rescaled_rankTwo_tests_LC87`: the tests of the coordinate `η_c` at the scale `201⁻¹ d` (metric
  `201⁻² g`) give, for `η = 201 η_c`, the tests at the original scale: for `x ∈ B(q, 200)`,
  `z ∈ B(q, 201R)`, `201 < d(x, z)` and a `g`-unit initial velocity `w` of a geodesic reaching `z`,
  `‖dη_x(w) - d(x, z)⁻¹ (F(z) - F(x))₁‖ < ε` (geodesics of `201⁻² g` are those of `g`,
  `intrinsicGeodesic_radialScaled_eq`, reparametrized by `intrinsicGeodesic_smul`).
* `exists_large_ball_rankTwo_coordinate_with_tests`: X77's large-ball coordinate (same proof, with
  the constant written `201⁻¹`) together with the `(1 + γ)`-Lipschitz bound and the original tests.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **The tests at scale `201⁻¹ d` give the tests at the original scale** (see the module
docstring). -/
theorem rescaled_rankTwo_tests_LC87 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {Y : Type*} [MetricSpace Y] {q : M} {y₀ : Y}
    {β : ℝ} (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), y₀)) β) (ηc : M → ℝ²)
    {ε R : ℝ}
    (htests :
      let Ff := F.toFun
      have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
      letI := m.rescale (201 : ℝ)⁻¹ (by norm_num)
      letI := radialScaledBundle g (201 : ℝ)⁻¹ (by norm_num)
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g (201 : ℝ)⁻¹ (by norm_num)
      letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric (201 : ℝ)⁻¹
        (by norm_num)
      letI : CompleteSpace M := (m.rescale_completeSpace_iff (201 : ℝ)⁻¹ (by norm_num)).mpr hM
      let gc : SmoothRiemannianMetric I M := scaleMetric ((201 : ℝ)⁻¹ ^ 2) (by positivity) g
      have hn : IsMetricNorm (I := I) (M := M) gc := isMetricNorm_of_riemannianBundle gc
      ∀ x ∈ ball q 1, ∀ z ∈ ball q R, 1 < dist x z →
        ∀ w : TangentSpace I x, gc.inner x w w = 1 →
        intrinsicGeodesic gc hn x w (dist x z) = z →
        ‖mvfderiv (I := I) ηc x w - (dist x z)⁻¹ •
          ((201 : ℝ)⁻¹ • (Ff z).fst - (201 : ℝ)⁻¹ • (Ff x).fst)‖ < ε)
    (hder : ∀ x ∈ ball q 200, mvfderiv (I := I) (fun y => (201 : ℝ) • ηc y) x =
      (201 : ℝ) • mvfderiv (I := I) ηc x) :
    ∀ x ∈ ball q 200, ∀ z ∈ ball q (201 * R), 201 < dist x z →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      ‖mvfderiv (I := I) (fun y => (201 : ℝ) • ηc y) x w -
        (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < ε := by
  intro x hx z hz hxz w hw hgeo
  have hgeoEq := intrinsicGeodesic_radialScaled_eq g hEnorm (show (0 : ℝ) < 201 by norm_num) x
    ((201 : ℝ) • w)
  have hs1 := intrinsicGeodesic_smul g hEnorm x ((201 : ℝ) • w) ((201 : ℝ)⁻¹ * dist x z)
  have hs2 := intrinsicGeodesic_smul g hEnorm x w (dist x z)
  have hd := hder x hx
  have hdpos : 0 < dist x z := by linarith
  have hx' : (201 : ℝ)⁻¹ * dist x q < 1 := by
    have := mem_ball.mp hx
    rw [inv_mul_lt_iff₀ (by norm_num)]
    linarith
  have hz' : (201 : ℝ)⁻¹ * dist z q < R := by
    have := mem_ball.mp hz
    rw [inv_mul_lt_iff₀ (by norm_num)]
    linarith
  have hxz' : 1 < (201 : ℝ)⁻¹ * dist x z := by
    rw [lt_inv_mul_iff₀ (by norm_num)]
    linarith
  have hw' : (scaleMetric ((201 : ℝ)⁻¹ ^ 2) (by positivity) g).inner x ((201 : ℝ) • w)
      ((201 : ℝ) • w) = 1 := by
    simp only [scaleMetric_inner, map_smul, smul_apply, smul_eq_mul, hw]
    norm_num
  have hsm : ((201 : ℝ)⁻¹ * dist x z) • ((201 : ℝ) • w) = dist x z • w := by
    rw [smul_smul]
    congr 1
    field_simp
  have h2 : intrinsicGeodesic g hEnorm x ((201 : ℝ) • w) ((201 : ℝ)⁻¹ * dist x z) = z := by
    rw [← hs1, hsm, hs2, hgeo]
  have h1 := congrFun hgeoEq ((201 : ℝ)⁻¹ * dist x z)
  have h := htests x hx' z hz' hxz' ((201 : ℝ) • w) hw' (h1.trans h2)
  have heq : mvfderiv (I := I) (fun y => (201 : ℝ) • ηc y) x w -
      (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst) =
      mvfderiv (I := I) ηc x ((201 : ℝ) • w) - ((201 : ℝ)⁻¹ * dist x z)⁻¹ •
        ((201 : ℝ)⁻¹ • (F.toFun z).fst - (201 : ℝ)⁻¹ • (F.toFun x).fst) := by
    rw [hd, map_smul, smul_apply, ← smul_sub, smul_smul]
    congr 2
    field_simp
  rw [heq]
  exact h

end Transport

def circleProductRescale_LC87 {Y : Type*} [mY : MetricSpace Y]
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

theorem exists_large_ball_rankTwo_coordinate_with_tests {γ : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1 / 10) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 1000 ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ {β : ℝ}, β ≤ β₀ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ², ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200) ∧ η q = 0 ∧
        (∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x)) ∧
        LipschitzOnWith (Real.toNNReal (1 + γ)) η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        ∀ x ∈ ball q 200, ∀ z ∈ ball q (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace I x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x z) = z →
          ‖mvfderiv (I := I) η x w - (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ := by
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
  have htransport := fun (ηc : M → ℝ²) (ε' R : ℝ) =>
    rescaled_rankTwo_tests_LC87 (I := I) g hEnorm F ηc (ε := ε') (R := R)
  have hβp : 0 < β := F.error_pos
  have hβsmall : β ≤ 1 / 1000 := hβ.trans (min_le_right _ _)
  let ν : ℝ := 804 * β
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνle : ν ≤ ν₀ := by
    have hh := hβ.trans (min_le_left _ _)
    dsimp [ν]
    linarith
  have hνone : ν < 1 := hνle.trans_lt ((hν₀small.trans_le (min_le_right _ _)).trans (by norm_num))
  have hbudget : 3 * (201 : ℝ)⁻¹ * β ≤ ν := by dsimp [ν]; nlinarith
  have hdomain : dist q q + ν⁻¹ / (201 : ℝ)⁻¹ + 2 * β ≤ β⁻¹ := by
    have hinv : 1 ≤ β⁻¹ := (one_le_inv₀ hβp).mpr (by linarith)
    have he : ν⁻¹ / (201 : ℝ)⁻¹ = β⁻¹ / 4 := by
      dsimp [ν]
      field_simp
      ring
    rw [dist_self, zero_add, he]
    linarith
  let original := F.toFun
  let Fc := F.recenterRescale q (by norm_num : (0 : ℝ) < (201 : ℝ)⁻¹)
    hbudget hνone hdomain
  let e := circleProductRescale_LC87 (Y := Y) (201 : ℝ)⁻¹ (by norm_num)
  have hbase : e (F.toFun q) = WithLp.toLp 2 ((0 : ℝ²), a) := by
    rw [F.basepoint]
    change WithLp.toLp 2 ((201 : ℝ)⁻¹ • (0 : ℝ²), a) = _
    rw [smul_zero]
  let F' := @KleinerLottApprox.mapTargetIsometryAt M (WithLp 2 (ℝ² × Y))
    (WithLp 2 (ℝ² × Y)) (m.rescale (201 : ℝ)⁻¹ (by norm_num))
    ((inferInstance : MetricSpace (WithLp 2 (ℝ² × Y))).rescale (201 : ℝ)⁻¹ (by norm_num))
    (MetricSpace.scaledProduct inferInstance mY (201 : ℝ)⁻¹ (by norm_num))
    q (F.toFun q) ν Fc e (WithLp.toLp 2 ((0 : ℝ²), a)) hbase
  have hmetric : ∀ x y : M, riemannianEDistOf g x y = ENNReal.ofReal (dist x y) := by
    intro x y
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_dist]
  let : MetricSpace M := m.rescale (201 : ℝ)⁻¹ (by norm_num)
  let : CompleteSpace M := (m.rescale_completeSpace_iff (201 : ℝ)⁻¹ (by norm_num)).mpr
    instComplete
  let := radialScaledBundle g (201 : ℝ)⁻¹ (by norm_num)
  let := radialScaledContinuous g (201 : ℝ)⁻¹ (by norm_num)
  let := radialScaledManifold (m := m) g hmetric (201 : ℝ)⁻¹ (by norm_num)
  let gc := scaleMetric ((201 : ℝ)⁻¹ ^ 2) (by positivity) g
  have hn : IsMetricNorm gc := isMetricNorm_of_riemannianBundle gc
  let : MetricSpace Y := mY.rescale (201 : ℝ)⁻¹ (by norm_num)
  have hF' (x : M) : F'.toFun x =
      WithLp.toLp 2 ((201 : ℝ)⁻¹ • (original x).fst, (original x).snd) := rfl
  have hscaled : ∀ y ∈ ball q ν⁻¹, SectionalBoundedBelowAt gc y (-ν ^ 2) := by
    intro y hy
    have hball : y ∈ @ball M m.toPseudoMetricSpace q β⁻¹ := by
      change (201 : ℝ)⁻¹ * @dist M m.toDist y q < ν⁻¹ at hy
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
    change (201 : ℝ)⁻¹ * @dist M m.toDist x q < 1
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
  refine ⟨η, hsm, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [Real.coe_toNNReal _ (by linarith)]
    change dist ((201 : ℝ) • ηc x) ((201 : ℝ) • ηc y) ≤
      (1 + γ) * @dist M m.toDist x y
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 201), dist_eq_norm]
    have hh := hlip x (h200 x hx) y (h200 y hy)
    change ‖ηc x - ηc y‖ ≤ (1 + ε) * ((201 : ℝ)⁻¹ * @dist M m.toDist x y) at hh
    have he : ε ≤ γ / 201 := min_le_left _ _
    nlinarith [@dist_nonneg M m.toPseudoMetricSpace x y]
  · intro x hx
    have hh := hclose x (h200 x hx)
    rw [hF'] at hh
    change ‖ηc x - (201 : ℝ)⁻¹ • (original x).fst‖ < ε / 8 at hh
    have he : η x - (original x).fst =
        (201 : ℝ) • (ηc x - (201 : ℝ)⁻¹ • (original x).fst) := by
      simp only [η, smul_sub, smul_smul]
      norm_num
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 201)]
    have heps : ε ≤ γ / 201 := min_le_left _ _
    nlinarith
  · have hRε : 10000 ≤ ε⁻¹ + 3 := by
      have he : ε ≤ 1 / 10000 := min_le_right _ _
      have hinv : 10000 ≤ ε⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hε]
        simpa using he
      linarith
    have hγε : ε ≤ γ := (min_le_left _ _).trans (by linarith)
    intro x hx z hz hxz w hw hgeo
    have hz' : z ∈ @ball M m.toPseudoMetricSpace q (201 * (ε⁻¹ + 3)) := by
      change @dist M m.toDist z q < 201 * (ε⁻¹ + 3)
      change @dist M m.toDist z q < 201 * 10000 at hz
      linarith
    exact (htransport ηc ε (ε⁻¹ + 3) htests hder x hx z hz' hxz w hw hgeo).trans_le hγε

/-- **A circle chart with its original tests (X77 level).** The constants of X77
(`exists_early_simultaneous_circle_packet_parameters`): `a₂` before `γ`, `β₀` from `γ`. For a
normalized point with an actual Kleiner–Lott map to a two-dimensional nonnegative length space and
an actual `(2, β)`-splitting `F` (with `sec ≥ -β²` on `B(q, β⁻¹)`) there is an LC83 circle chart
centred at `q` whose coordinate is `(1 + γ)`-Lipschitz on `B(q, 200)`, within `γ` of `F₁`, at most
`8` on `B(q, 2)`, and satisfies the original long derivative tests against the SAME `F`. -/
theorem exists_circleChart_with_tests :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
          eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ → KleinerLottApprox q c σ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ ch : CircleChart I M, ch.center = q ∧ (∀ x ∈ ball q 2, ‖ch.coord x‖ ≤ 8) ∧
        LipschitzOnWith (Real.toNNReal (1 + γ)) ch.coord (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖ch.coord x - (F.toFun x).fst‖ < γ) ∧
        ∀ x ∈ ball q 200, ∀ z ∈ ball q (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace I x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x z) = z →
          ‖mvfderiv (I := I) ch.coord x w -
            (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ := by
  obtain ⟨a₀, ha₀, ha₀small, hres⟩ :=
    exists_simultaneous_circle_residual_threshold.{u, v, w}
  refine ⟨min a₀ (1 / 4), lt_min ha₀ (by norm_num), ?_⟩
  intro γ hγ hγone
  obtain ⟨β₀, hβ₀, hsmall, hcoordinates⟩ :=
    exists_large_ball_rankTwo_coordinate_with_tests.{uE, uH, u, w} hγ hγone
  refine ⟨min β₀ (min a₀ (1 / 4)), lt_min hβ₀ (lt_min ha₀ (by norm_num)), min_le_right _ _, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ q a C _ _ c hlen hdim hcomp σ β hσ hβ f F
    hsec
  obtain ⟨η, hη, hq, hrank, hlip, hclose, htests⟩ :=
    hcoordinates E H I M g hEnorm Y q a (hβ.trans (min_le_left _ _)) F hsec
  have hβa : β ≤ a₀ := hβ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hβq : β ≤ 1 / 4 := hβ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hres' : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1 := by
    intro x hx
    exact hres M q C c hlen hdim hcomp Y a σ β
      (hσ.trans (min_le_left _ _)) hβa f F x ((mem_ball.mp hx).le.trans (by norm_num))
  have hβsmall : β ≤ 1 / 200 := (hβ.trans (min_le_left _ _)).trans
    (hsmall.trans (by norm_num))
  have hclose' : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10 :=
    fun x hx => (hclose x hx).trans hγone
  have hlip2 : LipschitzOnWith 2 η (ball q 200) := by
    refine hlip.weaken ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith)]
    push_cast
    linarith
  obtain ⟨h102, h2⟩ := circlePacket_enclosures F hβsmall hres' hclose'
  obtain ⟨-, -, hprop, hsurj, hfib, htriv⟩ :=
    circleFiber_local_model g hEnorm hη hrank hlip2 hq h102 h2
  refine ⟨{ center := q
            coord := η
            contMDiffOn_coord := hη
            rank := hrank
            lipschitz := hlip2
            coord_center := hq
            enclosure := h102
            zero_enclosure := h2
            isProperMap := hprop
            surjective := hsurj
            fibres := hfib
            trivial := htriv }, rfl, ?_, hlip, hclose, htests⟩
  intro x hx
  have hβpos : 0 < β := F.error_pos
  have hx2 : dist x q < 2 := hx
  have hxβ : x ∈ ball q β⁻¹ := by
    rw [mem_ball]
    have : (4 : ℝ) ≤ β⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hβpos]
      linarith
    linarith
  have hdist := F.distortion x hxβ q (mem_ball_self (inv_pos.mpr hβpos))
  rw [F.basepoint] at hdist
  have hfst : ‖(F.toFun x).fst‖ ≤ dist (F.toFun x) (WithLp.toLp 2 ((0 : ℝ²), a)) := by
    have h := WithLp.dist_fst_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ²), a))
    simpa [dist_zero_right] using h
  have hxq : x ∈ ball q 200 := mem_ball.mpr (by linarith)
  have hc := hclose x hxq
  have habs := (abs_le.mp hdist).2
  have htri : ‖η x‖ ≤ ‖(F.toFun x).fst‖ + ‖η x - (F.toFun x).fst‖ :=
    norm_le_insert' (η x) (F.toFun x).fst
  dsimp only
  linarith

end DifferentialGeometry.Geometry.Collapse
