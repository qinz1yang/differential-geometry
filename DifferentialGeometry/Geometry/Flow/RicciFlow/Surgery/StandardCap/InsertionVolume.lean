import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionNorm
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Measure.OpenRestriction
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩
private local instance (U : Opens E3) : MeasurableSpace U := borel U
private local instance (U : Opens E3) : BorelSpace U := ⟨rfl⟩
private local instance (U : Opens E3) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

private theorem cap_volume_le_two_of_error_lt {B : ℝ} (hB : 0 < B)
    (g : SmoothRiemannianMetric (𝓡 3) (insertionBall B))
    (herr : metricDerivENormSupOn {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd} 0 g
      (metric.restrictOpen (insertionBall B)) (metric.restrictOpen (insertionBall B)) <
      ENNReal.ofReal (1 / 2 : ℝ)) :
    riemannianVolumeMeasure (𝓡 3) (insertionBall B) g {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
      2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  have hcomp (x : insertionBall B) (hx : ‖(x : E3)‖ ≤ transitionEnd) (v : TangentSpace (𝓡 3) x) :
      g.inner x v v ≤ (3 / 2 : ℝ) * (metric.restrictOpen (insertionBall B)).inner x v v := by
    have h := (inner_bounds_of_metricDerivENormSupOn_lt
      (metric.restrictOpen (insertionBall B)) g herr hx v).2
    norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at h
    exact h
  have hmeas : MeasurableSet {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd} :=
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet
  have hv := riemannianVolumeMeasure_apply_le_of_inner_le
    (metric.restrictOpen (insertionBall B)) g (C := 3 / 2) (by norm_num) hmeas hcomp
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hv
  have hrestriction := riemannianVolumeMeasure_restrictOpen_preimage metric (insertionBall B)
    (K := {x : E3 | ‖x‖ ≤ transitionEnd})
    ((isClosed_le continuous_norm continuous_const).measurableSet)
    (by intro x hx; change ‖x‖ < transitionEnd + B; change ‖x‖ ≤ transitionEnd at hx; linarith)
  have hfactor : ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) ≤ 2 := by
    have hs : Real.sqrt ((3 / 2 : ℝ) ^ 3) < 2 :=
      (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    exact (ENNReal.ofReal_le_ofReal hs.le).trans_eq (by norm_num)
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) *
        riemannianVolumeMeasure (𝓡 3) (insertionBall B) (metric.restrictOpen (insertionBall B))
          {x | ‖(x : E3)‖ ≤ transitionEnd} := hv
    _ = ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) *
        riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
          exact congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) * t) hrestriction
    _ ≤ _ := mul_le_mul' hfactor le_rfl

theorem exists_insertedMetric_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (B : ℝ) (hAB : 2 * A < B), 1 < B →
      ∀ (η : ℝ) (hη : 0 < η)
        (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
        metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) 0} 0 h
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
          ENNReal.ofReal |η - 1| < ENNReal.ofReal ε →
        riemannianVolumeMeasure (𝓡 3) (insertionBall B) (insertedMetric hA hAB hη h)
          {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
          2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  obtain ⟨C, hC, hb⟩ := exists_insertedMetric_ball_error_bound A hA 0 (by norm_num) 0
  let ε := (2 * C)⁻¹
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, ?_⟩
  intro B hAB hB η hη h hin
  apply cap_volume_le_two_of_error_lt (by linarith : 0 < B) (insertedMetric hA hAB hη h)
  have hbound := hb B hAB (by simpa using hB) η hη h
  simp only [add_zero] at hbound
  apply hbound.trans_lt
  have hm := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hin
  have he : C * ε = 1 / 2 := by dsimp [ε]; field_simp
  rw [← ENNReal.ofReal_mul hC.le, he] at hm
  exact hm

theorem exists_insertedMetric_scaled_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (B : ℝ) (hAB : 2 * A < B), 1 < B →
      ∀ (η : ℝ) (hη : 0 < η)
        (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
        metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) 0} 0 h
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
          ENNReal.ofReal |η - 1| < ENNReal.ofReal ε →
        ∀ (Q : ℝ) (hQ : 0 < Q),
          riemannianVolumeMeasure (𝓡 3) (insertionBall B)
            (scaleMetric Q⁻¹ (inv_pos.mpr hQ) (insertedMetric hA hAB hη h))
            {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
            ENNReal.ofReal (Real.sqrt Q⁻¹) ^ 3 *
              (2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨ε, hε, hb⟩ := exists_insertedMetric_cap_volume_bound A hA
  refine ⟨ε, hε, ?_⟩
  intro B hAB hB η hη h hin Q hQ
  rw [volume_scale_apply]
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim]
  exact mul_le_mul' le_rfl (hb B hAB hB η hη h hin)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
