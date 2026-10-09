import DifferentialGeometry.Geometry.Comparison.IntrinsicEightRadialComparison

set_option autoImplicit false


open Set Metric Real Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (8 * R))]
variable (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
  @IsOpen (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem radial_point_on_side_of_intrinsic_8_buffer
    {q x z : X} (hq : q ∈ ball o (R / 2)) (hx : x ∈ closedBall o R)
    (hz : z ∈ closedBall o R)
    (σ : Icc (0 : ℝ) (dist q x) → X) (hσ : Isometry σ)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hσend : σ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (t : Icc (0 : ℝ) (dist q x)) :
    modelSideNegCurvature κ t.val (dist q z)
        (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤ dist (σ t) z := by
  have hσrad (u : Icc (0 : ℝ) (dist q x)) : dist q (σ u) = u.val := by
    have h := hσ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ u
    simpa only [hσ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1] using h
  by_cases ht0 : t.val = 0
  · have heq : t = ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := Subtype.ext ht0
    rw [heq, hσ0, modelSideNegCurvature_zero_left hκ.le dist_nonneg]
  have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have hA : 0 < dist q x := htpos.trans_le t.property.2
  by_cases hqz : q = z
  · subst z
    rw [dist_self, modelSideNegCurvature_zero_right hκ.le t.property.1]
    exact le_of_eq ((hσrad t).symm.trans (dist_comm q (σ t)))
  have hσmem (u : Icc (0 : ℝ) (dist q x)) : σ u ∈ closedBall o (3 * R / 2) := by
    have htail : dist (σ u) x = dist q x - u.val := by
      have h := hσ.dist_eq u ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩
      simpa only [hσend, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr u.property.2), neg_sub] using h
    have hleft := dist_triangle (σ u) q o
    rw [dist_comm (σ u) q, hσrad] at hleft
    have hright := dist_triangle (σ u) x o
    rw [htail] at hright
    have hAupper := dist_triangle q o x
    rw [dist_comm o x] at hAupper
    have hqo : dist q o < R / 2 := hq
    have hxo : dist x o ≤ R := hx
    change dist (σ u) o ≤ 3 * R / 2
    linarith
  have hzero : dist z (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) ≤ 2 * R := by
    rw [hσ0]
    have h := dist_triangle z o q
    rw [dist_comm o q] at h
    have hzo : dist z o ≤ R := hz
    have hqo : dist q o < R / 2 := hq
    linarith
  have hend : dist z (σ ⟨dist q x, ⟨hA.le, le_rfl⟩⟩) ≤ 2 * R := by
    rw [hσend]
    have h := dist_triangle z o x
    rw [dist_comm o x] at h
    have hzo : dist z o ≤ R := hz
    have hxo : dist x o ≤ R := hx
    linarith
  have hangle := comparisonAngleNegCurvature_le_of_intrinsic_8_buffer_segment
    hcurves o hκ hR hlocal hA σ hσ hσmem hz hzero hend (by rwa [hσ0])
    ⟨htpos, t.property.2⟩
  rw [hσ0, hσend] at hangle
  have hB : 0 < dist q z := dist_pos.mpr hqz
  have hlo : |t.val - dist q z| ≤ dist (σ t) z := by
    simpa only [dist_comm (σ t) q, dist_comm z q, hσrad] using abs_dist_sub_le (σ t) z q
  have hhi : dist (σ t) z ≤ t.val + dist q z := by
    simpa only [dist_comm (σ t) q, hσrad] using dist_triangle (σ t) q z
  calc
    _ ≤ modelSideNegCurvature κ t.val (dist q z)
        (comparisonAngleNegCurvature κ t.val (dist q z) (dist (σ t) z)) :=
      modelSideNegCurvature_mono_angle hκ.le htpos.le hB.le
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2 hangle
    _ = dist (σ t) z := modelSideNegCurvature_comparisonAngle hκ.le htpos hB hlo hhi

end DifferentialGeometry.Geometry.Comparison.Toponogov
