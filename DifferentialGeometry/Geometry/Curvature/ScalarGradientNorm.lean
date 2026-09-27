import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.Algebra.Order.Chebyshev
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem trace_gradient_normSq_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) (x : M) :
    g.inner x
        (gradientFun (I := I) g (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x)
        (gradientFun (I := I) g (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x) ≤
      (Module.finrank ℝ E : ℝ) *
        normSq0S (I := I) g x 3 (iterCov (I := I) g 2 A 1 x) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let A1 : Tensor0SSpace 3 I x := iterCov (I := I) g 2 A 1 x
  let c : Fin (Module.finrank ℝ (TangentSpace I x)) →
      Fin (Module.finrank ℝ (TangentSpace I x)) →
      Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ :=
    fun d a b ↦ component0S (I := I) basis A1
      (Fin.cons d (fun q : Fin 2 ↦ if q = 0 then a else b))
  have hc (d a b : Fin (Module.finrank ℝ (TangentSpace I x))) :
      c d a b = A1 (vec3 (I := I) (basis d) (basis a) (basis b)) := by
    dsimp only [c, component0S_apply]
    congr 1
    funext q
    fin_cases q <;> rfl
  have htrace (d : Fin (Module.finrank ℝ (TangentSpace I x))) :
      mvfderiv (I := I) (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x (basis d) =
        ∑ i, c d i i := by
    have hraw :
        mvfderiv (I := I) (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x (basis d) =
          ∑ i, ∑ j, identityInvMetric i j *
            A1 (vec3 (I := I) (basis d) (basis i) (basis j)) := by
      simpa only [differential1FormFun_apply_eq_mvfderiv, A1, iterCov_succ,
        show iterCov (I := I) g 2 A 0 = A from rfl, Nat.add_zero, covStep_apply] using
        (differential_metricTrace_eq_trace_totalNabla_inBasis (I := I) (leviCivitaConnectionOfMetric (I := I) g) g
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
          A basis identityInvMetric hinv (basis d))
    simpa [identityInvMetric, diagonalInvMetric, ← hc] using hraw
  have hnorm : normSq0S (I := I) g x 3 A1 = ∑ d, ∑ a, ∑ b, (c d a b) ^ 2 :=
    normSq0S_three_identity_eq_sum (I := I) g x basis hinv A1
  have hdiag : (∑ d, ∑ a, (c d a a) ^ 2) ≤ ∑ d, ∑ a, ∑ b, (c d a b) ^ 2 := by
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum
    intro a _
    exact Finset.single_le_sum (fun b _ ↦ sq_nonneg (c d a b)) (Finset.mem_univ a)
  calc
    g.inner x
        (gradientFun (I := I) g (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x)
        (gradientFun (I := I) g (fun y ↦ metricTracePair0SAt (I := I) g (A y)) x) =
        ∑ d, (mvfderiv (I := I) (fun y ↦ metricTracePair0SAt (I := I) g (A y))
          x (basis d)) ^ 2 :=
      DifferentialGeometry.Geometry.Operator.inner_gradFun_self_eq_sum_sq g _ x basis hON
    _ = ∑ d, (∑ i, c d i i) ^ 2 := by simp only [htrace]
    _ ≤ ∑ d, (Module.finrank ℝ E : ℝ) * ∑ i, (c d i i) ^ 2 := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Finset.card_univ, Fintype.card_fin,
        show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] using
        (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ) (f := fun i ↦ c d i i))
    _ = (Module.finrank ℝ E : ℝ) * ∑ d, ∑ i, (c d i i) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℝ E : ℝ) * ∑ d, ∑ a, ∑ b, (c d a b) ^ 2 :=
      mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)
    _ = (Module.finrank ℝ E : ℝ) *
        normSq0S (I := I) g x 3 (iterCov (I := I) g 2 A 1 x) := by
      rw [← hnorm]

theorem scalar_gradient_normSq_le_nablaRm
    (g : SmoothRiemannianMetric I M) (x : M) :
    g.inner x
        (gradientFun (I := I) g (metricScalarAt (I := I) g) x)
        (gradientFun (I := I) g (metricScalarAt (I := I) g) x) ≤
      (Module.finrank ℝ E : ℝ) ^ 6 *
        normSq0S (I := I) g x 5
          (iterCov (I := I) g 4 (metricRm04 (I := I) g) 1 x) := by
  have hRic : metricRicci (I := I) g =
      metricTraceCovariantFourField (I := I) g (metricRm04 (I := I) g) := by
    simpa only [metricRicci, metricRm04, metricCov] using
      (levi_civita_ricci_section_eq_riemann_trace (I := I) g)
  have hscalar : (fun y : M ↦ metricTracePair0SAt (I := I) g (metricRicci (I := I) g y)) =
      metricScalarAt (I := I) g := by
    funext y
    rw [metricRicci_apply, metricScalarAt_def]
  have hgrad := trace_gradient_normSq_le (I := I) g (metricRicci (I := I) g) x
  rw [hscalar] at hgrad
  have hRicNorm :
      normSq0S (I := I) g x 3 (iterCov (I := I) g 2 (metricRicci (I := I) g) 1 x) ≤
        (Module.finrank ℝ E : ℝ) ^ 5 *
          normSq0S (I := I) g x 5
            (iterCov (I := I) g 4 (metricRm04 (I := I) g) 1 x) := by
    rw [hRic]
    exact iterRic_normSq_le (I := I) g (metricRm04 (I := I) g) 1 x
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        normSq0S (I := I) g x 3 (iterCov (I := I) g 2 (metricRicci (I := I) g) 1 x) := hgrad
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 5 *
        normSq0S (I := I) g x 5
          (iterCov (I := I) g 4 (metricRm04 (I := I) g) 1 x)) :=
      mul_le_mul_of_nonneg_left hRicNorm (Nat.cast_nonneg _)
    _ = _ := by ring

theorem scalar_gradient_inner_le_nablaRm
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    |g.inner x (gradientFun (I := I) g (metricScalarAt (I := I) g) x) v| ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        Real.sqrt (normSq0S (I := I) g x 5
          (iterCov (I := I) g 4 (metricRm04 (I := I) g) 1 x)) *
        Real.sqrt (g.inner x v v) := by
  have hsqrt := Real.sqrt_le_sqrt (scalar_gradient_normSq_le_nablaRm (I := I) g x)
  have hpow : (Module.finrank ℝ E : ℝ) ^ 6 = ((Module.finrank ℝ E : ℝ) ^ 3) ^ 2 := by ring
  rw [hpow, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3)] at hsqrt
  exact (DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    (I := I) g x (gradientFun (I := I) g (metricScalarAt (I := I) g) x) v).trans
    (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry.Curvature

end
