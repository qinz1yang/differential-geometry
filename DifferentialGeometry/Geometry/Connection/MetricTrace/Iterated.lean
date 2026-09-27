import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem exists_iterCov_metricTrace
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (r + 2)) (k : ℕ) :
    ∃ e : Fin (r + 2 + k) ≃ Fin ((r + k) + 2),
      iterCov (I := I) g r (metricTraceFirstTwoField (I := I) g A) k =
        metricTraceFirstTwoField (I := I) g
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
            (iterCov (I := I) g (r + 2) A k)) := by
  classical
  induction k with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      refine DFunLike.ext _ _ fun x => ?_
      exact tensor0SSpace_ext (I := I) r x fun v => rfl
  | succ k ih =>
      obtain ⟨e, he⟩ := ih
      let cov := leviCivitaConnectionOfMetric (I := I) g
      have hmc : IsMetricCompatible (I := I) cov g :=
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
      have hA := iterCov_realizes (I := I) g A k
      have hreindex := totalNabla0SRealizes_domDomCongr (I := I) cov e _ _ hA
      have htrace := nablaRealizes_metricTraceFirstTwo (I := I)
        (s := r + k) cov g hmc _ _ hreindex
      rw [← he] at htrace
      have hbase := iterCov_realizes (I := I) g (metricTraceFirstTwoField (I := I) g A) k
      have hout := Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hbase htrace
      refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (r + k)), ?_⟩
      rw [← Tensor0SField.domDomCongr_trans]
      exact hout

theorem iterCov_metricTrace_normSq_le
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (r + 2)) (k : ℕ) (x : M) :
    normSq0S (I := I) g x (r + k)
        (iterCov (I := I) g r (metricTraceFirstTwoField (I := I) g A) k x) ≤
      (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) *
        normSq0S (I := I) g x (r + 2 + k) (iterCov (I := I) g (r + 2) A k x) := by
  classical
  obtain ⟨e, he⟩ := exists_iterCov_metricTrace (I := I) g A k
  rw [he]
  have htrace := trace_normSq_rank_le (I := I) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
      (iterCov (I := I) g (r + 2) A k) x)
  rw [Tensor0SField.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hperm := normSq0S_domDomCongr (I := I) g x basis hinv e
    (iterCov (I := I) g (r + 2) A k x)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq
    (congrArg (fun z => (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) * z) hperm)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
