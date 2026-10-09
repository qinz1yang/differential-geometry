import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.ScaledRawAlignment
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation

/-!
Concrete Euclidean-product maps exercise reference normalization at a different raw scale
and centre. The residual factor is the real line, and its two rescalings cancel. The resulting
same map also supplies genuine closed-ball coverage through the existing MC11 conversion.
-/

set_option autoImplicit false

noncomputable section

open GC.MetricGeometry

namespace GC.MetricGeometry

theorem product_raw_half_scale_recentred (k : ℕ)
    (a : WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ))
    (ha : dist a (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), (0 : ℝ))) ≤ 1) :
    ∃ F : KleinerLottApprox a (WithLp.toLp 2 (0, a.snd)) (1 / 10),
      ∀ x, F.toFun x = WithLp.toLp 2 (x.fst - a.fst, x.snd) := by
  let mR : MetricSpace ℝ := inferInstance
  let mP : MetricSpace (WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ)) := inferInstance
  let e := IsometryEquiv.normedProdRescale (A := ℝ) (2⁻¹) (by norm_num) (0 :
    EuclideanSpace ℝ (Fin k))
  have he (x : WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ)) :
      e x = WithLp.toLp 2 (((2 : ℝ)⁻¹) • x.fst, x.snd) := by
    rw [IsometryEquiv.normedProdRescale_apply, sub_zero]
  let ε : ℝ := rawScaleQuality (1 / 10) 2 / 2
  have hε : 0 < ε := half_pos (rawScaleQuality_pos (by norm_num) (by norm_num))
  have hεone : ε < 1 := by
    have hh := min_le_left ((1 / 10 : ℝ) / 12) (1 / (2 * (2 + 2 * (1 / 10)⁻¹ + 2)))
    change rawScaleQuality (1 / 10) 2 ≤ (1 / 10 : ℝ) / 12 at hh
    dsimp only [ε]
    linarith
  let f := @IsometryEquiv.toKleinerLottApprox _ _ (mP.rescale (2⁻¹) (by norm_num))
    (MetricSpace.scaledProduct inferInstance mR (2⁻¹) (by norm_num)) e
    (WithLp.toLp 2 (0, 0)) (WithLp.toLp 2 (0, 0))
    (by rw [he]; simp) ε hε hεone
  have hεq : ε ≤ rawScaleQuality (1 / 10) (2 * 1) := by
    norm_num only [mul_one]
    exact half_le_self (rawScaleQuality_pos (by norm_num) (by norm_num)).le
  obtain ⟨F, hF⟩ := @exists_reference_scaled_raw_splitting _ _ mP
    (mR.rescale (2⁻¹) (by norm_num)) k (WithLp.toLp 2 (0, 0)) 0 ε (1 / 10) 2
    (by norm_num) f a (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    1 zero_le_one ha hεq
  have hmetric : MetricSpace.scaledProduct
      (inferInstance : MetricSpace (EuclideanSpace ℝ (Fin k)))
      (mR.rescale (2⁻¹) (by norm_num)) 2 (by norm_num) = mP := by
    unfold MetricSpace.scaledProduct
    have hR : (mR.rescale (2⁻¹) (by norm_num)).rescale 2 (by norm_num) = mR := by
      rw [MetricSpace.rescale_mul]
      norm_num
    rw [hR]
  have hmap : ∀ x, @KleinerLottApprox.toFun _ _ mP
      (MetricSpace.scaledProduct inferInstance (mR.rescale (2⁻¹) (by norm_num))
        2 (by norm_num))
      a (WithLp.toLp 2 (0, a.snd)) (1 / 10) F x =
        WithLp.toLp 2 (x.fst - a.fst, x.snd) := by
    intro x
    calc
      _ = WithLp.toLp 2 (2 • ((e x).fst - (e a).fst), (e x).snd) := hF x
      _ = _ := by
        simp only [he, WithLp.toLp_fst, WithLp.toLp_snd]
        rw [← smul_sub, smul_smul]
        norm_num
  have hresult : ∃ G : @KleinerLottApprox _ _ mP
      (MetricSpace.scaledProduct inferInstance (mR.rescale (2⁻¹) (by norm_num))
        2 (by norm_num)) a (WithLp.toLp 2 (0, a.snd)) (1 / 10),
      ∀ x, @KleinerLottApprox.toFun _ _ mP
        (MetricSpace.scaledProduct inferInstance (mR.rescale (2⁻¹) (by norm_num))
          2 (by norm_num)) a (WithLp.toLp 2 (0, a.snd)) (1 / 10) G x =
            WithLp.toLp 2 (x.fst - a.fst, x.snd) := ⟨F, hmap⟩
  rw [hmetric] at hresult
  exact hresult

theorem product_raw_half_scale_closed_ball (k : ℕ)
    (a : WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ))
    (ha : dist a (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), (0 : ℝ))) ≤ 1) :
    ∃ F : PointedBallApprox a (WithLp.toLp 2 (0, a.snd)) 1 (3 / 10),
      ∀ x, F.toFun x = WithLp.toLp 2 (x.val.fst - a.fst, x.val.snd) := by
  obtain ⟨F, hF⟩ := product_raw_half_scale_recentred k a ha
  have hnum : (3 * (1 / 10) : ℝ) = 3 / 10 := by ring
  rw [← hnum]
  exact ⟨F.toClosedBall (R := 1) (by norm_num) (by norm_num), fun x => hF x.val⟩

end GC.MetricGeometry
