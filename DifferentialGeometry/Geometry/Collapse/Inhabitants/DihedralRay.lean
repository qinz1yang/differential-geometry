import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralAxis
import DifferentialGeometry.Geometry.Metric.Approximation.RayZeroRank

/-!
Both real tips of the thin projective-sum metric have actual endpoint half-ray approximations.
The sphere scale and long axis are selected internally from the common distortion bound.
The original finite rank tolerances then give two genuine rank-zero points in the same metric;
this does not assert a selected zero-model family or its smooth model-chart obligations.
-/

set_option autoImplicit false

noncomputable section

open Metric Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open GC.Endpoint GC.Geometry.SphericalProduct GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u v

theorem exists_dihedralTips_rayApprox_scale (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
  ∃ (ε : ℝ) (hε : 0 < ε), ∀ (L : ℝ) (hL : 0 < L), δ⁻¹ < L →
    Nonempty (@KleinerLottApprox
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
      (Ici (0 : ℝ)) (inducedMetricSpace (dihedralMetric ε L hε hL)) inferInstance
      dihedralLeftTip (⟨0, by simp⟩ : Ici (0 : ℝ)) δ) ∧
    Nonempty (@KleinerLottApprox
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
      (Ici (0 : ℝ)) (inducedMetricSpace (dihedralMetric ε L hε hL)) inferInstance
      dihedralRightTip (⟨0, by simp⟩ : Ici (0 : ℝ)) δ) := by
  obtain ⟨D, hD, upper⟩ := exists_dihedralAxis_distortion.{u}
  let ε := δ / (D + 1) / 2
  have hD1 : 0 < D + 1 := by linarith
  have hε : 0 < ε := half_pos (div_pos hδ hD1)
  have hεeq : ε * (D + 1) = δ / 2 := by
    dsimp only [ε]
    field_simp
  have hεD : ε * D < δ := by nlinarith
  refine ⟨ε, hε, ?_⟩
  intro L hL hLbig
  let sourceMetric := inducedMetricSpace (dihedralMetric.{u} ε L hε hL)
  have hmetric := inducedMetricSpace_hmetric (dihedralMetric.{u} ε L hε hL)
  have band (x y : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :
      |dihedralAxis L x - dihedralAxis L y| ≤ dist x y ∧
      dist x y ≤ |dihedralAxis L x - dihedralAxis L y| + ε * D := by
    have lo := dihedralAxis_distance_le ε L hε hL x y
    have hi := upper ε L hε hL x y
    rw [hmetric x y] at lo hi
    exact ⟨(ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp lo,
      (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (abs_nonneg _) (mul_nonneg hε.le hD))).mp hi⟩
  have pointAxis (t : ℝ) (ht : 0 ≤ t) (htL : t ≤ L) :
      dihedralAxis.{u} L (dihedralProjection
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, t / (2 * L)))) =
      t := by
    rw [dihedralAxis_projection, sphereCylinderRechartDiffeomorph.symm_apply_apply]
    have hL2 : 0 < 2 * L := mul_pos (by norm_num) hL
    have htdiv : 0 ≤ t / (2 * L) := div_nonneg ht hL2.le
    have htdivhalf : t / (2 * L) ≤ 1 / 2 := by
      rw [div_le_iff₀ hL2]
      linarith
    have hn := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr
      (show |t / (2 * L)| ≤ |(1 : ℝ)| / 2 by
        simpa only [abs_of_nonneg htdiv, abs_one] using htdivhalf)
    change 2 * L * ‖((t / (2 * L) : ℝ) : AddCircle (1 : ℝ))‖ = t
    rw [hn, abs_of_nonneg htdiv]
    field_simp
  let center (b : Bool) := if b then dihedralRightTip.{u} else dihedralLeftTip
  let f (b : Bool) (x : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :=
    if b then L - dihedralAxis L x else dihedralAxis L x
  have f_nonneg (b : Bool) (x : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) : 0 ≤ f b x := by
    have hb := dihedralAxis_mem_Icc L hL x
    cases b
    · exact hb.1
    · exact sub_nonneg.mpr hb.2
  have f_center (b : Bool) : f b (center b) = 0 := by
    cases b
    · exact dihedralAxis_leftTip L
    · change L - dihedralAxis L dihedralRightTip = 0
      rw [dihedralAxis_rightTip, sub_self]
  have f_dist (b : Bool) (x y : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :
      |f b x - f b y| = |dihedralAxis L x - dihedralAxis L y| := by
    cases b
    · rfl
    · change |(L - dihedralAxis L x) - (L - dihedralAxis L y)| = _
      rw [show (L - dihedralAxis L x) - (L - dihedralAxis L y) =
        -(dihedralAxis L x - dihedralAxis L y) by ring, abs_neg]
  let build (b : Bool) : KleinerLottApprox (center b) (⟨0, by simp⟩ : Ici (0 : ℝ)) δ :=
    { error_pos := hδ
      error_lt_one := hδ1
      toFun := fun x => ⟨f b x, f_nonneg b x⟩
      basepoint := Subtype.ext (f_center b)
      distortion := fun x hx y hy => by
        rw [Subtype.dist_eq, Real.dist_eq, f_dist b x y]
        have hb := band x y
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      coverage := fun y hy => by
        have hy0 : 0 ≤ y.val := y.property
        have hy' : y.val < δ⁻¹ - δ := by
          simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hy0] using hy
        have hyL : y.val ≤ L := by linarith
        let t := if b then L - y.val else y.val
        have ht0 : 0 ≤ t := by
          cases b
          · exact hy0
          · exact sub_nonneg.mpr hyL
        have htL : t ≤ L := by
          cases b
          · exact hyL
          · change L - y.val ≤ L
            linarith
        let q := dihedralProjection (sphereCylinderRechartDiffeomorph
          (GC.GraphManifold.Assembly.northPole, t / (2 * L)))
        have hqaxis : dihedralAxis L q = t := pointAxis t ht0 htL
        have hfq : f b q = y.val := by
          cases b
          · exact hqaxis
          · change L - dihedralAxis L q = y.val
            rw [hqaxis]
            change L - (L - y.val) = y.val
            ring
        have hqdist := (band q (center b)).2
        have hfd := f_dist b q (center b)
        rw [hfq, f_center, sub_zero, abs_of_nonneg hy0] at hfd
        rw [← hfd] at hqdist
        have hqball : q ∈ Metric.ball (center b) δ⁻¹ := by
          change dist q (center b) < δ⁻¹
          linarith
        have himage : y ∈ (fun x => (⟨f b x, f_nonneg b x⟩ : Ici (0 : ℝ))) ''
            Metric.ball (center b) δ⁻¹ := ⟨q, hqball, Subtype.ext hfq⟩
        exact (Metric.infDist_le_dist_of_mem himage).trans
          (by simpa only [dist_self] using hδ.le) }
  exact ⟨⟨build false⟩, ⟨build true⟩⟩

theorem exists_dihedralTips_rayApprox (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
  ∃ (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L),
    Nonempty (@KleinerLottApprox
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
      (Ici (0 : ℝ)) (inducedMetricSpace (dihedralMetric ε L hε hL)) inferInstance
      dihedralLeftTip (⟨0, by simp⟩ : Ici (0 : ℝ)) δ) ∧
    Nonempty (@KleinerLottApprox
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
      (Ici (0 : ℝ)) (inducedMetricSpace (dihedralMetric ε L hε hL)) inferInstance
      dihedralRightTip (⟨0, by simp⟩ : Ici (0 : ℝ)) δ) := by
  obtain ⟨ε, hε, hmaps⟩ := exists_dihedralTips_rayApprox_scale.{u} δ hδ hδ1
  let L := δ⁻¹ + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hLbig : δ⁻¹ < L := by dsimp only [L]; linarith
  obtain ⟨left, right⟩ := hmaps L hL hLbig
  exact ⟨ε, L, hε, hL, left, right⟩

theorem exists_dihedral_zeroRankTips_scale (β : ℕ → ℝ)
    (hβ : ∀ k, 0 < k → k ≤ 3 → β k < 1 / 100) :
    ∃ (ε : ℝ) (hε : 0 < ε), ∀ (L : ℝ) (hL : 0 < L), 200 < L →
      @splittingRank.{u, v}
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)) dihedralLeftTip β 3 = 0 ∧
      @splittingRank.{u, v}
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)) dihedralRightTip β 3 = 0 ∧
      L ≤ @dist (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)).toDist
        dihedralLeftTip dihedralRightTip := by
  obtain ⟨ε, hε, hmaps⟩ :=
    exists_dihedralTips_rayApprox_scale.{u} (1 / 200) (by norm_num) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro L hL hsize
  obtain ⟨⟨left⟩, ⟨right⟩⟩ := hmaps L hL (by norm_num; exact hsize)
  let sourceMetric := inducedMetricSpace (dihedralMetric.{u} ε L hε hL)
  have leftZero := splittingRank_zero_of_endpoint_ray.{u, v} left (by norm_num) hβ
  have rightZero := splittingRank_zero_of_endpoint_ray.{u, v} right (by norm_num) hβ
  have hdistance := dihedralTips_distance_ge ε L hε hL
  rw [inducedMetricSpace_hmetric (dihedralMetric ε L hε hL)] at hdistance
  have hreal := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hdistance
  exact ⟨leftZero, rightZero, hreal⟩

theorem exists_dihedral_zeroRankTips (β : ℕ → ℝ)
    (hβ : ∀ k, 0 < k → k ≤ 3 → β k < 1 / 100) :
    ∃ (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L),
      @splittingRank.{u, v}
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)) dihedralLeftTip β 3 = 0 ∧
      @splittingRank.{u, v}
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)) dihedralRightTip β 3 = 0 ∧
      L ≤ @dist (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier
        (inducedMetricSpace (dihedralMetric ε L hε hL)).toDist
        dihedralLeftTip dihedralRightTip := by
  obtain ⟨ε, hε, hranks⟩ := exists_dihedral_zeroRankTips_scale.{u, v} β hβ
  exact ⟨ε, 201, hε, by norm_num, hranks 201 (by norm_num) (by norm_num)⟩

end DifferentialGeometry.Geometry.Collapse
