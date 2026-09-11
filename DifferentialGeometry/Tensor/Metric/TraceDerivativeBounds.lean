import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Product
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Tensor

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_iter_cov_metric_trace_first_two (r k : ℕ) :
    ∃ e : Fin ((r + 2) + k) ≃ Fin ((r + k) + 2),
      ∀ (G : SmoothRiemannianMetric I M)
        (T : Tensor0SField (I := I) (M := M) ∞ (r + 2)),
        iterCov G r (metricTraceFirstTwoField G T) k =
          metricTraceFirstTwoField G
            (Tensor0SField.domDomCongr ∞ e (iterCov G (r + 2) T k)) := by
  induction k with
  | zero =>
    refine ⟨Equiv.refl (Fin (r + 2)), ?_⟩
    intro G T
    change metricTraceFirstTwoField G T =
      metricTraceFirstTwoField G (Tensor0SField.domDomCongr ∞ (Equiv.refl _) T)
    rw [Tensor0SField.domDomCongr_refl]
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (r + k)), ?_⟩
    intro G T
    let cov := leviCivitaConnectionOfMetric G
    have hmc : IsMetricCompatible cov G :=
      leviCivitaConnectionOfMetric_isMetricCompatible G
    have hT := iterCov_realizes G T k
    have hreindex := totalNabla0SRealizes_domDomCongr cov e _ _ hT
    have htrace := nablaRealizes_metricTraceFirstTwo (s := r + k)
      cov G hmc _ _ hreindex
    rw [← he G T] at htrace
    have hactual := iterCov_realizes G (metricTraceFirstTwoField G T) k
    have hout := Tensor0SBundle.totalNabla0SRealizes_unique hactual htrace
    rw [← Tensor0SField.domDomCongr_trans]
    exact hout

theorem norm_sq_iter_cov_metric_trace_first_two_le
    (G : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (I := I) (M := M) ∞ (r + 2)) (k : ℕ) (q : M) :
    normSq0S G q (r + k) (iterCov G r (metricTraceFirstTwoField G T) k q) ≤
      (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) *
        normSq0S G q ((r + 2) + k) (iterCov G (r + 2) T k q) := by
  classical
  obtain ⟨e, he⟩ := exists_iter_cov_metric_trace_first_two (I := I) (M := M) r k
  rw [he G T]
  have htrace := trace_normSq_rank_le G
    ((Tensor0SField.domDomCongr ∞ e (iterCov G (r + 2) T k)) q)
  rw [Tensor0SField.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G q
  have hinv : MetricInverseInBasis G q basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I q)))) := by
    have h := metricInverseInBasis_of_orthonormal G basis hON
    intro a b
    simpa only [identityInvMetric, diagonalInvMetric] using h a b
  have hperm := normSq0S_domDomCongr G q basis hinv e
    (iterCov G (r + 2) T k q)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq (congrArg
    (fun z => (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) * z) hperm)

end Manifold

section Euclidean

open TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_iter_cov_metric_trace_first_two_bound_on_opens (r k : ℕ) :
    ∃ C > 0, ∀ (U : Opens E) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
      (T : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) ∞ (r + 2)) (q : U),
      Real.sqrt (normSq0S G q (r + k)
        (iterCov G r (metricTraceFirstTwoField G T) k q)) ≤
      C * Real.sqrt (normSq0S G q ((r + 2) + k)
        (iterCov G (r + 2) T k q)) := by
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2)
  refine ⟨1 + Real.sqrt D, by positivity, ?_⟩
  intro U G T q
  have h := Real.sqrt_le_sqrt (norm_sq_iter_cov_metric_trace_first_two_le G T k q)
  change _ ≤ Real.sqrt (D * normSq0S G q ((r + 2) + k)
    (iterCov G (r + 2) T k q)) at h
  rw [Real.sqrt_mul (by dsimp only [D]; positivity : 0 ≤ D)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg D])
    (Real.sqrt_nonneg _))

end Euclidean

end DifferentialGeometry.Geometry.Tensor
