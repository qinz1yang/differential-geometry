import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false

/-!
# Scalar curvature bound from the Riemann norm

This file closes the trace estimate needed to turn a pointwise Riemann norm
bound into a scalar-curvature upper bound.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- The absolute scalar curvature is at most the square of the tangent
dimension times the fibre norm of the lowered Riemann tensor. -/
theorem scalar_abs_le_rm (g : SmoothRiemannianMetric I M) (x : M) :
    |metricScalarAt (I := I) (M := M) g x| ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have htrace : metricScalarAt (I := I) (M := M) g x =
      ∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricScalarAt_def (I := I) g x,
      metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x))))
        hinv (metricRicciAt (I := I) (M := M) g x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      have hij : i ≠ j := fun hij => hji hij.symm
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hij, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [htrace]
  calc
    |∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i, |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (Module.finrank ℝ (TangentSpace I x) : ℝ) *
          Real.sqrt (normSq0S (I := I) g x 4
            (metricRm04At (I := I) (M := M) g x)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fintype.card_fin] using
        metricRicciComp_le (I := I) (M := M) g basis hON i i
    _ = (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end DifferentialGeometry.Integral.Connection
