import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannCurvature04At_eq_sum_metricRm04At
    (g₁ g₂ : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx ℝ (TangentSpace I x)) (gInv : Idx → Idx → ℝ)
    (hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv)
    (v : Fin 4 → TangentSpace I x) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x v =
      ∑ i, ∑ j, gInv i j * (metricRm04At (I := I) g₂ x
        (Function.update v (Fin.last 3) (basis i)) *
        g₁.inner x (basis j) (v (Fin.last 3))) := by
  classical
  let R := connectionRiemannCurvatureField (metricCov (I := I) g₂)
    (CovariantDerivative.tangentConstAt (I := I) x (v 0))
    (CovariantDerivative.tangentConstAt (I := I) x (v 1))
    (CovariantDerivative.tangentConstAt (I := I) x (v 2)) x
  have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v (Fin.last 3)) := by
    funext k
    fin_cases k <;> rfl
  have hleft : CovariantDerivative.riemannCurvature04At (I := I) g₁
      (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v =
      g₁.inner x (v (Fin.last 3)) R := by
    conv_lhs => rw [hv]
    exact CovariantDerivative.riemannCurvature04At_apply_const g₁
      (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) _ _ _ _
  have hright (i : Idx) : metricRm04At (I := I) g₂ x
      (Function.update v (Fin.last 3) (basis i)) = g₂.inner x (basis i) R := by
    have hu : Function.update v (Fin.last 3) (basis i) =
        vec4 (I := I) (v 0) (v 1) (v 2) (basis i) := by
      funext k
      fin_cases k <;> simp [vec4, Function.update]
    rw [hu]
    exact CovariantDerivative.riemannCurvature04At_apply_const g₂
      (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) _ _ _ _
  rw [hleft]
  simp_rw [hright]
  calc
    g₁.inner x (v (Fin.last 3)) R = g₁.inner x R (v (Fin.last 3)) :=
      g₁.symm x _ _
    _ = g₁.inner x (∑ j, basis.repr R j • basis j) (v (Fin.last 3)) := by
      rw [basis.sum_repr]
    _ = ∑ j, basis.repr R j * g₁.inner x (basis j) (v (Fin.last 3)) := by
      rw [map_sum, sum_apply]
      simp only [map_smul, smul_apply, smul_eq_mul]
    _ = ∑ j, ∑ i, gInv j i * g₂.inner x R (basis i) *
        g₁.inner x (basis j) (v (Fin.last 3)) := by
      simp_rw [basis_repr_eq_sum_inv_inner (I := I) g₂ x basis gInv hinv R,
        Finset.sum_mul]
    _ = ∑ i, ∑ j, gInv i j * (g₂.inner x (basis i) R *
        g₁.inner x (basis j) (v (Fin.last 3))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [MetricInverseInBasis.symmetric (I := I) g₂ x basis gInv hinv j i,
        g₂.symm x R (basis i), mul_assoc]

end DifferentialGeometry.Geometry.Curvature
