import DifferentialGeometry.Geometry.Comparison.EightNestedRadial
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.RadialModel
import DifferentialGeometry.Topology.MetricSpace.RadialBall
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false


open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {R : ℝ} (hR : 0 < R)
variable [LocallyCompactSpace (ball o (8 * R))]
variable (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
  @IsOpen (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)

include hcurves hR hlocal

theorem radial_contraction_of_chosen_isometries_intrinsic_8_buffer
    {q : X} (hq : q ∈ ball o (R / 2)) {δ : ℝ} (hδ : δ ∈ Ioo 0 R)
    (t : unitInterval) (ht : (t : ℝ) = δ / (2 * R))
    (γ : ∀ x : closedBall o R, Icc (0 : ℝ) (dist q (x : X)) → X)
    (hγ : ∀ x, Isometry (γ x))
    (hγ0 : ∀ x, γ x ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hγend : ∀ x, γ x ⟨dist q (x : X), ⟨dist_nonneg, le_rfl⟩⟩ = x) :
    let h : closedBall o R → X := fun x => γ x
      ⟨(t : ℝ) * dist q (x : X), mul_nonneg t.property.1 dist_nonneg,
        mul_le_of_le_one_left dist_nonneg t.property.2⟩
    (∀ x, h x ∈ ball q δ) ∧
      ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y) := by
  let h : closedBall o R → X := fun x => γ x
    ⟨(t : ℝ) * dist q (x : X), mul_nonneg t.property.1 dist_nonneg,
      mul_le_of_le_one_left dist_nonneg t.property.2⟩
  change (∀ x, h x ∈ ball q δ) ∧
    ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y)
  have htpos : 0 < (t : ℝ) := by rw [ht]; exact div_pos hδ.1 (by positivity)
  have htR : (t : ℝ) * (2 * R) = δ := by rw [ht]; field_simp
  have hrad (x : closedBall o R) : dist q (x : X) < 2 * R := by
    have h := dist_triangle q o (x : X)
    rw [dist_comm o (x : X)] at h
    have hqo : dist q o < R / 2 := hq
    have hxo : dist (x : X) o ≤ R := x.property
    linarith
  have hqh (x : closedBall o R) : dist q (h x) = (t : ℝ) * dist q (x : X) := by
    have he := (hγ x).dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
      ⟨(t : ℝ) * dist q (x : X), mul_nonneg t.property.1 dist_nonneg,
        mul_le_of_le_one_left dist_nonneg t.property.2⟩
    simpa only [hγ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg t.property.1 dist_nonneg)] using he
  have hcoef : δ / sinh (2 * R) ≤ (t : ℝ) := by
    rw [← htR]
    apply (div_le_iff₀ (sinh_pos_iff.mpr (by positivity : 0 < 2 * R))).mpr
    exact mul_le_mul_of_nonneg_left (self_le_sinh_iff.mpr (by positivity : 0 ≤ 2 * R)) t.property.1
  constructor
  · intro x
    change dist (h x) q < δ
    rw [dist_comm, hqh]
    have h := mul_lt_mul_of_pos_left (hrad x) htpos
    rwa [htR] at h
  · intro x y
    by_cases hx : q = (x : X)
    · have hhx : h x = q := by
        have he := hqh x
        rw [← hx, dist_self, mul_zero] at he
        exact (dist_eq_zero.mp he).symm
      rw [hhx, ← hx, hqh]
      exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
    by_cases hy : q = (y : X)
    · have hhy : h y = q := by
        have he := hqh y
        rw [← hy, dist_self, mul_zero] at he
        exact (dist_eq_zero.mp he).symm
      rw [hhy, ← hy, dist_comm (h x) q, dist_comm (x : X) q, hqh]
      exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
    let θ := comparisonAngleNegCurvature 1 (dist q (x : X)) (dist q (y : X)) (dist (x : X) (y : X))
    have hmodel := modelSideNegCurvature_le_of_nested_radial_prefixes_intrinsic_8_buffer
      hcurves o (by norm_num : (0 : ℝ) < 1) hR hlocal hq x.property y.property
      (γ x) (γ y) (hγ x) (hγ y) (hγ0 x) (hγ0 y) (hγend x) (hγend y)
      (s := (t : ℝ) * dist q (x : X)) (u := dist q (x : X))
      (v := dist q (y : X)) (t := (t : ℝ) * dist q (y : X))
      (mul_nonneg t.property.1 dist_nonneg) (mul_le_of_le_one_left dist_nonneg t.property.2)
      le_rfl (mul_nonneg t.property.1 dist_nonneg)
      (mul_le_of_le_one_left dist_nonneg t.property.2) le_rfl
    rw [hγend, hγend] at hmodel
    change modelSideNegCurvature 1 ((t : ℝ) * dist q (x : X))
      ((t : ℝ) * dist q (y : X)) θ ≤ dist (h x) (h y) at hmodel
    have hbig : modelSideNegCurvature 1 (dist q (x : X)) (dist q (y : X)) θ = dist (x : X) (y : X) :=
      modelSideNegCurvature_comparisonAngle (by norm_num) (dist_pos.mpr hx) (dist_pos.mpr hy)
        (by simpa only [dist_comm q (x : X), dist_comm q (y : X)] using abs_dist_sub_le (x : X) (y : X) q)
        (dist_triangle_left (x : X) (y : X) q)
    have hbigLaw := cosh_sqrt_mul_modelSideNegCurvature (κ := (1 : ℝ)) (by norm_num)
      (a := dist q (x : X)) (b := dist q (y : X)) (θ := θ) dist_nonneg dist_nonneg
    simp only [sqrt_one, one_mul, hbig] at hbigLaw
    have hsmallLaw := cosh_sqrt_mul_modelSideNegCurvature (κ := (1 : ℝ)) (by norm_num)
      (a := (t : ℝ) * dist q (x : X)) (b := (t : ℝ) * dist q (y : X)) (θ := θ)
      (mul_nonneg t.property.1 dist_nonneg) (mul_nonneg t.property.1 dist_nonneg)
    simp only [sqrt_one, one_mul] at hsmallLaw
    have hlower := radial_side_lower_of_cosine_laws dist_nonneg dist_nonneg (hrad x).le (hrad y).le
      (c := dist (x : X) (y : X)) dist_nonneg
      (modelSideNegCurvature_nonneg (mul_nonneg t.property.1 dist_nonneg) (mul_nonneg t.property.1 dist_nonneg))
      (by positivity : 0 < 2 * R) t.property (cos_le_one θ) hbigLaw hsmallLaw.ge
    rw [htR] at hlower
    exact hlower.trans hmodel


theorem exists_radial_contraction_of_intrinsic_8_buffer
    {q : X} (hq : q ∈ ball o (R / 2)) {δ : ℝ} (hδ : δ ∈ Ioo 0 R) :
    ∃ h : closedBall o R → X, (∀ x, h x ∈ ball q δ) ∧
      ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y) := by
  classical
  have hsegments (x : closedBall o R) :
      ∃ γ : Icc (0 : ℝ) (dist q (x : X)) → X, Isometry γ ∧
        γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q ∧
        γ ⟨dist q (x : X), ⟨dist_nonneg, le_rfl⟩⟩ = x := by
    obtain ⟨f, _, hf0, hf1, _, hfd⟩ := exists_radial_metric_segment_in_two_ball
      hcurves o hR (L := 8 * R) (by linarith) hq x.property
    exact exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  choose γ hγ hγ0 hγend using hsegments
  let t : unitInterval := ⟨δ / (2 * R), by
    constructor
    · exact div_nonneg hδ.1.le (by positivity)
    · apply (div_le_one (by positivity : 0 < 2 * R)).mpr
      linarith [hδ.2]⟩
  exact ⟨_, radial_contraction_of_chosen_isometries_intrinsic_8_buffer
    hcurves o hR hlocal hq hδ t rfl γ hγ hγ0 hγend⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
