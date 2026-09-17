import DifferentialGeometry.Geometry.Connection.MetricTrace.Iterated
import DifferentialGeometry.Geometry.Operator.Hessian.IteratedCovariantDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation

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

variable [NeZero (Module.finrank ℝ E)]

theorem abs_laplacian_scalar_le_second_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x| ≤
      (Module.finrank ℝ E : ℝ) ^ 6 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) := by
  classical
  let g := S.base.metric t
  let Ric := metricRicci (I := I) g
  let A := metricTraceFirstTwoField (I := I) g Ric
  let f := metricScalarAt (I := I) g
  have hA : ∀ y, A y Fin.elim0 = f y := by
    intro y
    dsimp only [A, Ric, f]
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      traceFirstTwo_elim0, metricRicci_apply, metricScalarAt_def]
  have hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f := by
    let V : Fin 0 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := fun i => i.elim0
    have heval : (fun p => A p (fun a => V a p)) = f := by
      funext p
      exact (congrArg (A p) (Subsingleton.elim _ _)).trans (hA p)
    intro y
    rw [← heval]
    exact tensor0SField_eval_smooth_slots_contMDiffAt (I := I) A V y
  let Hess := hessianSec (I := I) (leviCivitaConnectionOfMetric (I := I) g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g) f hf
  have hHess : iterCov (I := I) g 0 A 2 = Hess :=
    iterCov_zeroTensor_two_eq_hessianSec (I := I) g A f hf hA
  have htrace : laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x =
      metricTracePair0SAt (I := I) g (Hess x) := by
    change laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g f x =
      metricTracePair0SAt (I := I) g (Hess x)
    have h := scalarLap_smooth (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
      g (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) f hf (x := x)
    simpa only [ScalarLaplacianRealizesTraceAt, traceFirstTwo_elim0] using h
  have hscalarBound := iterCov_metricTrace_normSq_le (I := I) g Ric 2 x
  change normSq0S (I := I) g x 2 (iterCov (I := I) g 0 A 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 4 *
      normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x) at hscalarBound
  rw [hHess] at hscalarBound
  have hricBound := ricTower_normSq_le (I := I) S t 2 x
  change normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 6 *
      nablaKRm04NormSqIntrinsic (I := I) S 2 t x at hricBound
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hlap := metricTracePair0SAt_sq_le_card_mul_normSq0S (I := I)
    g basis _ hinv (Hess x)
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  rw [Fintype.card_fin, hrank, ← htrace] at hlap
  have hn : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hn2 : (Module.finrank ℝ E : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
    nlinarith
  have hHessnonneg := normSq0S_nonneg (I := I) g x 2 (Hess x)
  have hsquared : laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 12 * nablaKRm04NormSqIntrinsic (I := I) S 2 t x := by
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) * normSq0S (I := I) g x 2 (Hess x) := hlap
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * normSq0S (I := I) g x 2 (Hess x) :=
        mul_le_mul_of_nonneg_right hn2 hHessnonneg
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 4 *
            normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x)) :=
        mul_le_mul_of_nonneg_left hscalarBound (sq_nonneg _)
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 4 *
            ((Module.finrank ℝ E : ℝ) ^ 6 * nablaKRm04NormSqIntrinsic (I := I) S 2 t x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hricBound (by positivity)) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ = Real.sqrt (laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 12 *
        nablaKRm04NormSqIntrinsic (I := I) S 2 t x) := Real.sqrt_le_sqrt hsquared
    _ = _ := by
      have hpow : (Module.finrank ℝ E : ℝ) ^ 12 = ((Module.finrank ℝ E : ℝ) ^ 6) ^ 2 :=
        by ring
      rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
