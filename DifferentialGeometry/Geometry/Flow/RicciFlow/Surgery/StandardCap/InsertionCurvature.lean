import DifferentialGeometry.Geometry.Curvature.PositiveStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_insertedMetric_core_sectionalCurvature_pos (A : ℝ) (hA : 0 < A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (B : ℝ) (hAB : 2 * A < B) (η : ℝ) (hη : 0 < η)
      (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
      metricDerivENormSupOn
          {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) (-A)} 2
          h ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
            (DifferentialGeometry.Geometry.Neck.openCylinder B))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
            (DifferentialGeometry.Geometry.Neck.openCylinder B)) + ENNReal.ofReal |η - 1| < ENNReal.ofReal δ →
      ∀ x : insertionBall B, ‖(x : E3)‖ ≤ conformalRadius (-A) →
        ∀ u v : TangentSpace (𝓡 3) x,
        (insertedMetric hA hAB hη h).inner x u u * (insertedMetric hA hAB hη h).inner x v v -
          (insertedMetric hA hAB hη h).inner x u v ^ 2 ≠ 0 →
        0 < sectionalCurvature (insertedMetric hA hAB hη h) x u v := by
  have hK : IsCompact {x : E3 | ‖x‖ ≤ conformalRadius (-A)} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : E3) (conformalRadius (-A))
  have hpos : ∀ x ∈ {x : E3 | ‖x‖ ≤ conformalRadius (-A)},
      ∀ u v : TangentSpace (𝓡 3) x,
      metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0 →
      0 < sectionalCurvature metric x u v := by
    intro x hx u v hplane
    have hr : conformalRadius (-A) < transitionEnd := by
      simpa only [conformalRadius_zero] using strictMono_conformalRadius (neg_neg_of_pos hA)
    exact sectionalCurvature_pos (lt_of_le_of_lt hx hr) u v hplane
  obtain ⟨ε, hε, hstable⟩ := exists_pos_sectionalCurvature_of_small_metricDerivENormSupOn metric hK hpos
  obtain ⟨C, hC, hnorm⟩ := exists_insertedMetric_core_error_bound A hA 2
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro B hAB η hη h hsmall x hx u v hplane
  apply hstable (insertionBall B) (insertedMetric hA hAB hη h) ?_ x hx u v hplane
  apply (hnorm B hAB η hη h).trans_lt
  have hs := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
    ENNReal.ofReal_ne_top hsmall
  have he : ENNReal.ofReal C * ENNReal.ofReal (ε / C) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    field_simp
  exact hs.trans_eq he

end DifferentialGeometry.PDE.RicciFlow.StandardCap
