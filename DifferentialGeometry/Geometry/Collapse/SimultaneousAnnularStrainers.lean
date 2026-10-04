import DifferentialGeometry.Geometry.Collapse.ZeroStratumRiemannian
import DifferentialGeometry.Geometry.Metric.Approximation.ZeroStratumExport
import DifferentialGeometry.Geometry.Comparison.ModelSide
import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint

/-!
# Original annular constants and original-center prefix calibration

The selected outward point precedes every scaling factor. The project delta and Lambda are
literal formulas, and all actual prefixes retain their original center and proportional error.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Real Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal Topology

namespace GC.MetricGeometry

universe u v

private theorem original_annular_chord {σ θ : ℝ} (hσ : 0 < σ) (hσone : σ < 1)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hbudget : 4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2)) < 1 - cos σ) :
    modelSideNegCurvature σ σ⁻¹ σ⁻¹ (Real.pi - σ) < 2 * σ⁻¹ * cos (θ / 2) := by
  let L := σ⁻¹
  let c := 2 * L * cos (θ / 2)
  have hL : 0 < L := inv_pos.mpr hσ
  have hc : 0 ≤ c := by
    apply mul_nonneg (by positivity)
    exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [two_le_pi]⟩
  have hcmax : c ≤ L + L := by
    have := mul_le_mul_of_nonneg_left (cos_le_one (θ / 2)) (show 0 ≤ 2 * L by positivity)
    dsimp [c]
    linarith
  have hangle : Real.pi - σ < comparisonAngleNegCurvature σ L L c := by
    have he : cosh (sqrt σ * (L + L)) * (L + L - c) * (L + L) / (L * L) =
        4 * cosh (sqrt σ * (L + L)) * (1 - cos (θ / 2)) := by
      dsimp [c]
      field_simp [hL.ne']
      ring
    have hb : cosh (sqrt σ * (L + L)) * (L + L - c) * (L + L) / (L * L) <
        1 - cos σ := by
      rw [he]
      exact hbudget
    simpa only [sq_sqrt hσ.le] using pi_sub_lt_comparisonAngleNegCurvature_of_excess
      (sqrt_nonneg σ) hL hL (by simpa only [sub_self, abs_zero] using hc) hcmax hσ.le hb
  have hφ : Real.pi - σ ∈ Icc (0 : ℝ) Real.pi :=
    ⟨by linarith [two_le_pi], by linarith⟩
  have hle : modelSideNegCurvature σ L L (Real.pi - σ) ≤ c := by
    calc
      modelSideNegCurvature σ L L (Real.pi - σ) ≤
          modelSideNegCurvature σ L L (comparisonAngleNegCurvature σ L L c) :=
        modelSideNegCurvature_mono_angle hσ.le hL.le hL.le hφ.1
          (comparisonAngleNegCurvature_mem_Icc σ L L c).2 hangle.le
      _ = c := modelSideNegCurvature_comparisonAngle hσ.le hL hL
        (by simpa only [sub_self, abs_zero] using hc) hcmax
  apply lt_of_le_of_ne hle
  intro heq
  have h := comparisonAngleNegCurvature_modelSide hσ.le hL hL hφ
  rw [heq] at h
  linarith

theorem exists_original_annular_strainer_constants {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      modelSideNegCurvature σ σ⁻¹ σ⁻¹ (Real.pi - σ) < 2 * σ⁻¹ * cos (θ / 2) ∧
      let δσ := min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600))
      let Λσ := max (20 * σ⁻¹) (max ((1 / 60) / sqrt σ) 2)
      ∀ (X : Type u) (C : Type v) [MetricSpace X] [MetricSpace C],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X, Continuous f ∧
        f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (p : X) (o : C), RadialConeData o → ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < δσ → fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∃ z : X, dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        Real.pi - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2)
          (dist q p) (dist q z) (dist p z) ∧
        (∀ x : X, 0 < dist q x → dist q x + dist x z = dist q z →
          0 ≤ dist q p + dist q x - dist p x ∧
          dist q p + dist q x - dist p x < 2 * dist q x * (1 - cos θ) ∧
          ∀ μ : ℝ, 0 < μ → μ * dist q x - 2 * (μ * dist q x) * (1 - cos θ) <
            μ * dist p x - μ * dist p q ∧
            μ * dist p x - μ * dist p q ≤ μ * dist q x) ∧
        ∀ lam : ℝ, Λσ ≤ lam → ∃ a b : X,
          dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
          dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
          Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
            (lam * dist a b) := by
  obtain ⟨θ, hθ, hθone, hθbudget⟩ := exists_annular_strainer_angle hσ hσone
  have hcosθ : 0 < 1 - cos θ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hθ
    rw [cos_zero] at h
    linarith
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  refine ⟨θ, hθ, hθone, original_annular_chord hσ hσone hθ hθone hθbudget, ?_⟩
  dsimp only
  intro X C mX mC hsegments p o H δ φ hδ hcomp q hq1 hq2
  have hseg' : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
    intro x y
    obtain ⟨f, _, h0, h1, hd⟩ := hsegments x y
    exact ⟨f, h0, h1, hd⟩
  have hδpos := φ.error_pos
  have hδ1 : δ < 1 / 100 :=
    (hδ.trans_le (min_le_left _ _)).trans (by norm_num)
  have hδ2 : δ < (1 - cos θ) / 600 :=
    hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set D : ℝ := dist p q with hD
  have hDpos : 0 < D := by linarith
  -- LC25: the outward point at twice the radius.
  obtain ⟨q', hpq', hlow, hhigh⟩ := φ.exists_outward_point_on_annulus H hsegments
    (a := 1 / 10) (b := 10) (by norm_num) (by norm_num) (by linarith) (by linarith) ⟨hq1, hq2⟩
  -- The point `z` at distance `D` from `q` on a segment towards `q'`.
  obtain ⟨z, -, hqz, -, hzq', -, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q q' q' dist_nonneg hlow hlow
  have hpz_low : 2 * D - 15 * δ < dist p z := by
    have h := dist_triangle p z q'
    linarith
  have hpz_up : dist p z ≤ 2 * D := by
    have h := dist_triangle p q z
    linarith
  have hpz_nonneg : 0 ≤ dist p z := dist_nonneg
  have hqp : dist q p = D := dist_comm q p
  -- The angle at `q` of `(q; p, z)` at curvature `-(1/60)²`.
  have hangle0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist p z) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hDpos hpz_nonneg hpz_up
      (by nlinarith) hθ.le
    rw [div_lt_iff₀ hDpos]
    have : 4 * (2 * D - dist p z) < 60 * δ := by linarith
    nlinarith
  refine ⟨z, hqz, by linarith, by rw [hqp, hqz]; exact hangle0, ?_, ?_⟩
  · intro x hx hxz
    have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
    have hqB : q ∈ ball p 21 := by change dist q p < 21; rw [hqp]; linarith
    have hzB : z ∈ ball p 21 := by change dist z p < 21; rw [dist_comm]; linarith
    have hxB : x ∈ ball p 21 := by
      change dist x p < 21
      have h1 := dist_triangle x q p
      have h2 := dist_nonneg (x := x) (y := z)
      rw [dist_comm x q] at h1
      linarith
    have hκD : (1 / 60 : ℝ) * dist q p ≤ 1 := by rw [hqp]; linarith
    have hθpi : θ ≤ Real.pi / 2 := by linarith [two_le_pi]
    have hangle : Real.pi - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2)
        (dist q p) (dist q z) (dist p z) := by rw [hqp, hqz]; exact hangle0
    obtain ⟨hnonneg, herror⟩ := outward_prefix_calibration (by norm_num : (0 : ℝ) < 1 / 60)
      hcomp hpB hqB hzB hxB (by rw [hqz, hqp]) hκD hθ hθpi hangle hx hxz
    exact ⟨hnonneg, herror, fun μ hμ => outward_prefix_calibration_scaled
      (by norm_num : (0 : ℝ) < 1 / 60) hcomp hpB hqB hzB hxB
      (by rw [hqz, hqp]) hκD hθ hθpi hangle hx hxz hμ⟩
  · intro lam hΛ
    have hlam : 20 * L ≤ lam := (le_max_left _ _).trans hΛ
    -- Shortening to the exact length `s = L / λ`.
    set s : ℝ := L / lam with hs
    have hlampos : 0 < lam := lt_of_lt_of_le (by positivity) hlam
    have hspos : 0 < s := div_pos hLpos hlampos
    have hs20 : s ≤ 1 / 20 := by
      rw [hs, div_le_iff₀ hlampos]
      linarith
    have hsD : s ≤ D := by linarith
    obtain ⟨a, b, hqa, hqb, hap, hbz, -, -⟩ :=
      exists_equal_radius_endpoints_with_excess_le hseg' q p z hspos.le
        (by rw [hqp]; exact hsD) (by rw [hqz]; exact hsD)
    have hmem (x : X) (hx : dist x p < 21) : x ∈ ball p 21 := hx
    have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
    have hqB : q ∈ ball p 21 := hmem q (by rw [hqp]; linarith)
    have hzB : z ∈ ball p 21 := hmem z (by rw [dist_comm]; linarith)
    have haB : a ∈ ball p 21 := hmem a (by rw [hap, hqp]; linarith)
    have hbB : b ∈ ball p 21 := hmem b (by
      have h := dist_triangle b q p
      rw [dist_comm b q, hqb, hqp] at h
      linarith)
    have hzq : z ≠ q := by
      intro h
      rw [h, dist_self] at hqz
      linarith
    have haq : a ≠ q := by
      intro h
      rw [h, dist_self] at hqa
      linarith
    have hκ : (0 : ℝ) ≤ (1 / 60) ^ 2 := by positivity
    have hsh1 := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hqB haB hpB hzB
      (by rw [hqa]; exact hspos) hzq (by rw [hqa, hap]; ring)
    have hsh2 := comparisonAngleNegCurvature_le_of_shortening_right hκ hcomp hqB hbB hzB haB
      (by rw [hqb]; exact hspos) haq (by rw [hqb, hbz]; ring)
    have hangle_s : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) s s (dist a b) := by
      have h0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z)
          (dist p z) := by rw [hqp, hqz]; exact hangle0
      have h := (h0.trans_le hsh1).trans_le hsh2
      rwa [hqa, hqb] at h
    have hab_up : dist a b ≤ 2 * s := by
      have h := dist_triangle a q b
      rw [dist_comm a q, hqa, hqb] at h
      linarith
    have hchord := two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature hκ hspos
      dist_nonneg hab_up hθ.le (by linarith [two_le_pi]) hangle_s
    -- The comparison angle in the rescaled distance at curvature `-σ`.
    have hlams : lam * s = L := by
      rw [hs]
      field_simp
    have hc_up : lam * dist a b ≤ L + L := by nlinarith
    have hc_low : 2 * L * cos (θ / 2) < lam * dist a b := by nlinarith
    have hfinal : π - σ < comparisonAngleNegCurvature (sqrt σ ^ 2) L L (lam * dist a b) := by
      apply pi_sub_lt_comparisonAngleNegCurvature_of_excess (sqrt_nonneg σ) hLpos hLpos
        (by rw [sub_self, abs_zero]; positivity) hc_up hσ.le
      have hK : 0 < cosh (sqrt σ * (L + L)) := cosh_pos _
      rw [div_lt_iff₀ (by positivity)]
      have hexcess : L + L - lam * dist a b < 2 * L * (1 - cos (θ / 2)) := by linarith
      have h1 : cosh (sqrt σ * (L + L)) * (L + L - lam * dist a b) * (L + L) <
          cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) := by
        apply mul_lt_mul_of_pos_right _ (by positivity)
        exact mul_lt_mul_of_pos_left hexcess hK
      have h2 : cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) =
          (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) := by
        rw [hL]
        ring
      have h3 : (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) <
          (1 - cos σ) * (L * L) := mul_lt_mul_of_pos_right hθbudget (by positivity)
      linarith
    rw [sq_sqrt hσ.le] at hfinal
    refine ⟨a, b, hqa, hqb, by rw [hqa, hap]; ring, by rw [hqb, hbz]; ring, ?_⟩
    rw [hqa, hqb, hlams]
    exact hfinal

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v

open GC.MetricGeometry

theorem exists_simultaneous_original_annular_strainers {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      modelSideNegCurvature σ σ⁻¹ σ⁻¹ (Real.pi - σ) < 2 * σ⁻¹ * cos (θ / 2) ∧
      let δσ := min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600))
      let Λσ := max (20 * σ⁻¹) (max ((1 / 60) / sqrt σ) 2)
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M), IsMetricNorm g → ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δσ →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∃ z : M, dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        Real.pi - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2)
          (dist q p) (dist q z) (dist p z) ∧
        (∀ x : M, 0 < dist q x → dist q x + dist x z = dist q z →
          0 ≤ dist q p + dist q x - dist p x ∧
          dist q p + dist q x - dist p x < 2 * dist q x * (1 - cos θ) ∧
          ∀ μ : ℝ, 0 < μ → μ * dist q x - 2 * (μ * dist q x) * (1 - cos θ) <
            μ * dist p x - μ * dist p q ∧
            μ * dist p x - μ * dist p q ≤ μ * dist q x) ∧
        ∀ lam : ℝ, Λσ ≤ lam → ∃ hlam : 0 < lam,
          (∀ y ∈ riemannianBallOf (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) q σ⁻¹,
            SectionalBoundedBelowAt (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) y (-σ)) ∧
          ∃ a b : M,
          dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
          dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
          Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
            (lam * dist a b)
 := by
  obtain ⟨θ, hθ, hθone, hside, hkernel⟩ :=
    exists_original_annular_strainer_constants.{u, v} hσ hσone
  refine ⟨θ, hθ, hθone, hside, ?_⟩
  dsimp only at hkernel ⊢
  intro M mM cM sM scM cmM rM rmM crM g hEnorm p hsec C mC o H δ φ hδ q hq1 hq2
  have hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b) := by
    intro a b
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_dist]
  have hcomp : fourPointComparison ((1 / 60) ^ 2) (ball p 21) := by
    apply fourPointComparison_of_sectional_lower_bound_on_eight_ball g hmetric p (by positivity)
    intro y hy
    exact hsec y (ball_subset_ball (by norm_num) hy)
  obtain ⟨z, hz, he, ha, hpref, hanchors⟩ :=
    hkernel M C (exists_riemannian_metric_segment g hEnorm) p o H φ hδ hcomp q hq1 hq2
  refine ⟨z, hz, he, ha, hpref, ?_⟩
  intro lam hΛ
  have hL : σ⁻¹ ≤ lam := by
    have h := (le_max_left _ _).trans hΛ
    have hi : 0 < σ⁻¹ := inv_pos.mpr hσ
    linarith
  have hlam : 0 < lam := (inv_pos.mpr hσ).trans_le hL
  refine ⟨hlam, ?_, hanchors lam hΛ⟩
  intro y hy
  have hσlam : 1 ≤ σ * lam := by
    have h := mul_le_mul_of_nonneg_left hL hσ.le
    rwa [mul_inv_cancel₀ hσ.ne'] at h
  have hy' : y ∈ riemannianBallOf g q (σ⁻¹ / lam) := by
    have h := riemannianBallOf_scaleMetric (lam ^ 2) (pow_pos hlam 2) g q (σ⁻¹ / lam)
    rw [Real.sqrt_sq hlam.le, show lam * (σ⁻¹ / lam) = σ⁻¹ by field_simp] at h
    rwa [h] at hy
  have hs1 : σ⁻¹ / lam ≤ 1 := by
    rw [div_le_one hlam]
    exact hL
  have hyp : y ∈ ball p 400 := by
    rw [DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm
      g hEnorm] at hy'
    have h1 : dist y q < σ⁻¹ / lam := hy'
    change dist y p < 400
    linarith [dist_triangle y q p, dist_comm q p]
  have h := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric
    ((hsec y hyp).mono (show -(σ * lam ^ 2) ≤ -((1 / 60) ^ 2) by nlinarith))
    (lam ^ 2) (pow_pos hlam 2)
  rwa [show -(σ * lam ^ 2) / lam ^ 2 = -σ by field_simp] at h

end DifferentialGeometry.Geometry.Collapse
