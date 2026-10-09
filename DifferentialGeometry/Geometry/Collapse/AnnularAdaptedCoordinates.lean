import DifferentialGeometry.Geometry.Collapse.RadialAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.OriginalRadialSplitting
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts

/-!
# The prescribed radial adapted coordinate on every annular normalized ball

The original distance coordinate and the previously selected radial smoothing
are retained under genuine metric and tensor rescaling.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

private theorem enlarge_radial_splitting {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {p : X} {q : Y} {ν β : ℝ} (F : KleinerLottApprox p q ν)
    (hβ : 0 < β) (hβone : β < 1) (hνβ : ν < β / 4) :
    ∃ G : KleinerLottApprox p q β, G.toFun = F.toFun := by
  have hν := F.error_pos
  have hle : ν ≤ β := by linarith
  have hrad : β⁻¹ ≤ ν⁻¹ := inv_le_inv₀ hβ hν |>.mpr hle
  refine ⟨⟨hβ, hβone, F.toFun, F.basepoint, ?_, ?_⟩, rfl⟩
  · intro x hx y hy
    exact (F.distortion x (mem_ball.mpr ((mem_ball.mp hx).trans_le hrad))
      y (mem_ball.mpr ((mem_ball.mp hy).trans_le hrad))).trans hle
  · intro y hy
    obtain ⟨x, hx, hclose, hxrad⟩ := F.coverage_witness_radius y
      ((mem_ball.mp (show y ∈ ball q (β⁻¹ - β) from hy)).trans_le (by linarith))
    have hxβ : x ∈ ball p β⁻¹ := mem_ball.mpr (by linarith)
    exact (infDist_le_dist_of_mem (show F.toFun x ∈ F.toFun '' ball p β⁻¹ from
      ⟨x, hxβ, rfl⟩)).trans (by linarith)

private theorem real_splitting_coordinate {X Z : Type*} [MetricSpace X] [MetricSpace Z]
    {q : X} {z : Z} {ν : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) ν)
    (u : X → ℝ) (hF : ∀ x, (F.toFun x).fst = WithLp.toLp 2 (Function.const (Fin 1) (u x))) :
    ∃ G : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) ν,
      ∀ x, (G.toFun x).fst = u x := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let G := F.mapTargetIsometryAt
    (e.symm.toIsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Z))
    (WithLp.toLp 2 ((0 : ℝ), z)) (by
      change WithLp.toLp 2 (e.symm 0, z) = WithLp.toLp 2 ((0 : ℝ), z)
      exact congrArg (fun t : ℝ => WithLp.toLp 2 (t, z)) e.symm.map_zero)
  refine ⟨G, fun x => ?_⟩
  change e.symm (F.toFun x).fst = u x
  rw [hF]
  apply e.injective
  rw [e.apply_symm_apply]
  ext i
  change u x = ((OrthonormalBasis.singleton (Fin 1) ℝ).repr (u x)) i
  exact (OrthonormalBasis.singleton_repr (u x) i).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[instance_reducible]
def radialScaledBundle (g : SmoothRiemannianMetric I M) (lam : ℝ) (hlam : 0 < lam) :
    RiemannianBundle (fun x : M => TangentSpace I x) :=
  ⟨(scaleMetric (lam ^ 2) (pow_pos hlam 2) g).toRiemannianMetric⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem radialScaledContinuous (g : SmoothRiemannianMetric I M) (lam : ℝ) (hlam : 0 < lam) :
    let := radialScaledBundle g lam hlam
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := by
  let := radialScaledBundle g lam hlam
  let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) g
  exact ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem radialScaledManifold (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (lam : ℝ) (hlam : 0 < lam) :
    let := m.rescale lam hlam
    let := radialScaledBundle g lam hlam
    IsRiemannianManifold I M := by
  let := m.rescale lam hlam
  let := radialScaledBundle g lam hlam
  refine ⟨fun a b => ?_⟩
  let := radialScaledContinuous g lam hlam
  let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) g
  have hn : IsMetricNorm h := isMetricNorm_of_riemannianBundle h
  rw [← riemannianEDistOf_eq_riemannianEDist h hn, edistOf_scale, hmetric,
    Real.sqrt_sq hlam.le]
  rw [edist_dist]
  change ENNReal.ofReal (lam * @dist M m.toDist a b) = _
  exact ENNReal.ofReal_mul hlam.le

variable [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]

private theorem small_calibration_parameter {ζ : ℝ} (hζ : 0 < ζ) (hζone : ζ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 3 ∧ γ < 1 / 4 ∧ γ < ζ ∧
      γ + (Real.sqrt (4 * γ + γ ^ 2) + Real.sqrt (4 * γ + γ ^ 2)) ≤ ζ := by
  let γ := ζ ^ 2 / 10000
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hsq : ζ ^ 2 < ζ := by nlinarith
  have hγζ : γ < ζ / 4 := by dsimp [γ]; nlinarith
  have hsqrt : Real.sqrt (4 * γ + γ ^ 2) ≤ ζ / 4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    dsimp [γ]
    have hsq1 : ζ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (ζ ^ 2), mul_le_mul_of_nonneg_left hsq1 (sq_nonneg ζ)]
  exact ⟨γ, hγ, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_prescribed_annular_adapted_parameters {β ζ : ℝ}
    (hβ : 0 < β) (hβζ : β < ζ) (hζone : ζ < 1) :
    ∃ ε δstar Λstar : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δstar ∧ 0 < Λstar ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I M),
      ∀ (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)), ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δstar → ∀ η : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η {x | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} →
      (∀ x y, |(η x - dist p x) - (η y - dist p y)| ≤ ε * dist x y) →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
      let := m.rescale lam hlam
      letI := (m.rescale_completeSpace_iff lam hlam).mpr inferInstance
      letI := radialScaledBundle g lam hlam
      letI := radialScaledContinuous g lam hlam
      letI := radialScaledManifold (m := m) g hmetric lam hlam
      let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) g
      let ψ := fun x => lam * (η x - η q)
      ∃ hEnorm : IsMetricNorm h,
        ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
          ∃ (z : Z) (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) β),
          (∀ x, (α.toFun x).fst = lam *
            (@dist M m.toDist p x - @dist M m.toDist p q)) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
          (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
          (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
          ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
            ∀ w : TangentSpace I x, h.inner x w w = 1 →
            intrinsicGeodesic h hEnorm x w (dist x y) = y →
            |mvfderiv (I := I) ψ x w -
              ((α.toFun y).fst - (α.toFun x).fst) / dist x y| < ζ := by
  have hζ : 0 < ζ := hβ.trans hβζ
  obtain ⟨γ, hγ, hγthird, hγquarter, hγζ, hcal⟩ := small_calibration_parameter hζ hζone
  have hγone : γ < 1 := by linarith
  obtain ⟨ν₀, hν₀, hν₀bound, hadapt⟩ :=
    exists_rankOne_adapted_coordinate_parameters hγ hγone
  let ν := min ν₀ (β / 4) / 2
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνν₀ : ν ≤ ν₀ := by
    have hm := min_le_left ν₀ (β / 4)
    dsimp [ν]
    linarith
  have hνβ : ν < β / 4 := by
    have hm := min_le_right ν₀ (β / 4)
    dsimp [ν]
    linarith
  have hνone : ν < 1 := hνν₀.trans_lt (hν₀bound.trans_le (min_le_right _ _) |>.trans
    (by norm_num))
  obtain ⟨δstar, Λ₀, hδstar, hΛ₀, hsplit⟩ :=
    exists_original_radial_splitting_parameter_riemannian (E := E) (I := I) hν hνone
  let Λstar := max 80 (max ν⁻¹ Λ₀)
  refine ⟨γ, δstar, Λstar, hγ, ?_, hδstar, ?_, ?_⟩
  · exact hγquarter
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro M m hchart hmanifold hsigma hcomplete hconnected g hmetric p hsec C mC o hcone
      δ F hδ η hη herr q hqlo hqhi lam hlam hΛ
    have h80 : 80 ≤ lam := (le_max_left _ _).trans hΛ
    have hνlam : ν⁻¹ ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
    have hΛ₀lam : Λ₀ ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
    obtain ⟨Z, mZ, z, F₀, hF₀⟩ := hsplit M g hmetric p hsec C o hcone F hδ
      q hqlo hqhi lam hlam hΛ₀lam
    let := m.rescale lam hlam
    let : CompleteSpace M := (m.rescale_completeSpace_iff lam hlam).mpr inferInstance
    let := radialScaledBundle g lam hlam
    let := radialScaledContinuous g lam hlam
    let := radialScaledManifold (m := m) g hmetric lam hlam
    let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) g
    let ψ := fun x => lam * (η x - η q)
    have hEnorm : IsMetricNorm h := isMetricNorm_of_riemannianBundle h
    let := mZ
    obtain ⟨Freal, hreal⟩ := real_splitting_coordinate F₀
      (fun x => lam * (@dist M m.toDist p x - @dist M m.toDist p q)) hF₀
    have hscaledsec : ∀ y ∈ ball q ν⁻¹, SectionalBoundedBelowAt h y (-ν ^ 2) := by
      intro y hy
      have hyq : @dist M m.toDist y q < 1 := by
        change lam * @dist M m.toDist y q < ν⁻¹ at hy
        have hd := @dist_nonneg M m.toPseudoMetricSpace y q
        nlinarith
      have hyp : @dist M m.toDist y p < 400 := by
        have ht := @dist_triangle M m.toPseudoMetricSpace y q p
        have hqp : @dist M m.toDist q p ≤ 10 := by
          exact (@dist_comm M m.toPseudoMetricSpace q p).trans_le hqhi
        linarith
      apply (sectionalBoundedBelowAt_scaleMetric_iff (pow_pos hlam 2)).mpr
      apply SectionalBoundedBelowAt.mono (hsec y hyp)
      have hprod : 1 ≤ ν * lam := by
        have hi := mul_le_mul_of_nonneg_left hνlam hν.le
        rwa [mul_inv_cancel₀ hν.ne'] at hi
      nlinarith [sq_nonneg (ν * lam), sq_nonneg (ν * lam - 1)]
    obtain ⟨φ, hφ, hφq, hφlip, himage1, himage2, htest⟩ :=
      hadapt ν hν hνν₀ E H I M h hEnorm Z q z Freal hscaledsec
    have hψ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) := by
      apply contMDiffOn_const.mul
      apply (hη.mono ?_).sub contMDiffOn_const
      intro x hx
      change lam * @dist M m.toDist x q < 1 at hx
      have hsmall : @dist M m.toDist x q < 1 / 80 := by
        have hd := @dist_nonneg M m.toPseudoMetricSpace x q
        nlinarith
      have htri := @dist_triangle M m.toPseudoMetricSpace p x q
      have htri2 := @dist_triangle M m.toPseudoMetricSpace x q p
      have hsym1 := @dist_comm M m.toPseudoMetricSpace p x
      have hsym2 := @dist_comm M m.toPseudoMetricSpace q x
      have hsym3 := @dist_comm M m.toPseudoMetricSpace p q
      constructor <;> linarith
    have hψq : ψ q = 0 := by simp [ψ]
    have hpq : 3 < dist p q := by change 3 < lam * @dist M m.toDist p q; nlinarith
    have hdiff : ∀ x y, |(ψ x - (dist p x - dist p q)) -
        (ψ y - (dist p y - dist p q))| ≤ γ * dist x y := by
      intro x y
      change |(lam * (η x - η q) -
        (lam * @dist M m.toDist p x - lam * @dist M m.toDist p q)) -
        (lam * (η y - η q) -
        (lam * @dist M m.toDist p y - lam * @dist M m.toDist p q))| ≤
        γ * (lam * @dist M m.toDist x y)
      have he := mul_le_mul_of_nonneg_left (herr x y) hlam.le
      rw [← abs_of_pos hlam, ← abs_mul, abs_of_pos hlam] at he
      convert he using 1
      · congr 1
        ring
      · ring
    have htest' : ∀ x ∈ ball q 1, ∀ y ∈ ball q γ⁻¹, 1 < dist x y →
        ∀ w : TangentSpace I x, h.inner x w w = 1 →
        intrinsicGeodesic h hEnorm x w (dist x y) = y →
        |mvfderiv (I := I) φ x w -
          ((dist p y - dist p q) - (dist p x - dist p q)) / dist x y| < γ := by
      intro x hx y hy hd w hw he
      simpa only [hreal, MetricSpace.rescale_dist, mul_sub] using htest x hx y hy hd w hw he
    obtain ⟨hψlip, hψimage1, hψimage2, hψtest⟩ :=
      radial_smoothing_adapted_clauses h hEnorm hγ hγthird hγ.le hpq hcal
        hφ hψ hφq hψq hφlip himage1 himage2 htest' hdiff
    obtain ⟨α, hα⟩ := enlarge_radial_splitting Freal hβ (hβζ.trans hζone) hνβ
    have hcoord : ∀ x, (α.toFun x).fst =
        lam * (@dist M m.toDist p x - @dist M m.toDist p q) := by
      intro x
      rw [hα]
      exact hreal x
    refine ⟨hEnorm, Z, mZ, z, α, hcoord, hψ, hψq, hψlip, hψimage1, hψimage2, ?_⟩
    intro x hx y hy hd w hw he
    change |mvfderiv (I := I) ψ x w -
      ((α.toFun y).fst - (α.toFun x).fst) / dist x y| < ζ
    have hc : (α.toFun y).fst - (α.toFun x).fst =
        (dist p y - dist p q) - (dist p x - dist p q) := by
      rw [hcoord, hcoord]
      change _ = (lam * @dist M m.toDist p y - lam * @dist M m.toDist p q) -
        (lam * @dist M m.toDist p x - lam * @dist M m.toDist p q)
      ring
    rw [hc]
    exact hψtest x hx y hy hd w hw he

end DifferentialGeometry.Geometry.Collapse
