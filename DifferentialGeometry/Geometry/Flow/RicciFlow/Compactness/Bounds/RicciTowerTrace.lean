import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeComponents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Connection.MetricTrace.NablaTraceGen
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle

open DifferentialGeometry.HCGCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]


omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_ric_trace
    (g : SmoothRiemannianMetric I M)
    (Rm : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (k : Nat) :
    ∃ e : Fin (4 + k) ≃ Fin ((2 + k) + 2),
      iterCov (I := I) g 2 (trace04Field (I := I) (M := M) g Rm) k =
        metricTraceFirstTwoField (I := I) (M := M) g
          (Tensor0SField.domDomCongr (I := I) (∞ : WithTop ℕ∞) e
            (iterCov (I := I) g 4 Rm k)) := by
  classical
  induction k with
  | zero =>
      exact ⟨trace04Perm, rfl⟩
  | succ k ih =>
      obtain ⟨e, he⟩ := ih
      let cov := leviCivitaConnectionOfMetric (I := I) g
      have hmc : IsMetricCompatibleGen (I := I) cov g := by
        exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
      have hRm := iterCov_realizes (I := I) g Rm k
      have hreindex := totalNabla0SRealizes_domDomCongr (I := I) cov e _ _ hRm
      have htrace := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
        (s := 2 + k) cov g hmc _ _ hreindex
      rw [← he] at htrace
      have hric := iterCov_realizes (I := I) g
        (trace04Field (I := I) (M := M) g Rm) k
      have hout := Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hric htrace
      refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (2 + k)), ?_⟩
      rw [← Tensor0SField.domDomCongr_trans]
      exact hout

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem iterRic_normSq_le
    (g : SmoothRiemannianMetric I M)
    (Rm : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (k : Nat) (x : M) :
    normSq0S (I := I) g x (2 + k)
        (iterCov (I := I) g 2 (trace04Field (I := I) (M := M) g Rm) k x) <=
      (Module.finrank Real E : Real) ^ ((2 + k) + 2) *
        normSq0S (I := I) g x (4 + k) (iterCov (I := I) g 4 Rm k x) := by
  classical
  obtain ⟨e, he⟩ := exists_ric_trace (I := I) g Rm k
  rw [he]
  have htrace := trace_normSq_rank_le (I := I) g
    ((Tensor0SField.domDomCongr (I := I) (∞ : WithTop ℕ∞) e
      (iterCov (I := I) g 4 Rm k)) x)
  rw [Tensor0SField.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have hperm :
      normSq0S (I := I) g x ((2 + k) + 2)
          ((iterCov (I := I) g 4 Rm k x).domDomCongr e) =
        normSq0S (I := I) g x (4 + k) (iterCov (I := I) g 4 Rm k x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv e
      (iterCov (I := I) g 4 Rm k x)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq
    (congrArg (fun z => (Module.finrank Real E : Real) ^ ((2 + k) + 2) * z) hperm)

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm_eq_iterCov
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : Nat) :
    nablaKRm04Field (I := I) S t k =
      iterCov (I := I) (S.base.metric t) 4 (S.base.rm04 t) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hleft := nablaKRm04Field_realizes (I := I) S t k
      have hleft' :
          TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (4 + k) (leviCivitaConnectionOfMetric (I := I) (S.base.metric t))
            (iterCov (I := I) (S.base.metric t) 4 (S.base.rm04 t) k)
            (nablaKRm04Field (I := I) S t (k + 1)) := by
        simpa [SolutionOn.family, SolutionFamily.connection, metricCov, ih] using hleft
      exact Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hleft'
        (iterCov_realizes (I := I) (S.base.metric t) (S.base.rm04 t) k)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricTower_normSq_le
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : Nat) (x : M) :
    normSq0S (I := I) (S.base.metric t) x (2 + k)
        (ricCovTower (I := I) (S.base.metric t) (S.base.metric t) k x) <=
      (Module.finrank Real E : Real) ^ ((2 + k) + 2) *
        normSq0S (I := I) (S.base.metric t) x (4 + k)
          (nablaKRm04Field (I := I) S t k x) := by
  have hbase :
      CovariantDerivative.ricciSection (I := I) (M := M)
          (leviCivitaConnectionOfMetric (I := I) (S.base.metric t))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) (S.base.metric t)) =
        trace04Field (I := I) (M := M) (S.base.metric t) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricRm04, metricCov] using
      (levi_civita_ricci_section_eq_riemann_trace (I := I) (M := M) (S.base.metric t))
  simpa [ricCovTower, hbase, nablaKRm_eq_iterCov] using
    (iterRic_normSq_le (I := I) (S.base.metric t) (S.base.rm04 t) k x)

end DifferentialGeometry.PDE.RicciFlow
