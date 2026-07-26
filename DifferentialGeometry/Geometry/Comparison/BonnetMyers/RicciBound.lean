import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity

/-!
# The "Ric ≥ κ · g" predicate

This file introduces the predicate `RicciBoundedBelow g κ`, asserting that
the Ricci tensor of a smooth Riemannian metric `g` is bounded below by
`κ · g` as bilinear forms: for every point `x` and tangent vector `v` at
`x`, one has `κ · ⟨v, v⟩_g ≤ Ric(v, v)`.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Lower Ricci bound predicate.** The metric `g` has Ricci curvature bounded
below by `κ` (interpreted as `Ric ≥ κ · g` as bilinear forms) iff for every
point `x : M` and every tangent vector `v : T_x M`,
`κ · g(v, v) ≤ Ric_g(v, v)`. -/
def RicciBoundedBelow (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

/-- A global bound on the norm of the lowered Riemann tensor gives a uniform
lower Ricci bound. The dimension-squared constant is deliberately coarse; it
matches the existing general-dimensional Ricci trace estimate. -/
theorem ricciLower_of_rm
    (g : SmoothRiemannianMetric I M) {Rm : ℝ}
    (hRm : ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x)) ≤ Rm) :
    RicciBoundedBelow (I := I) g
      (-((Module.finrank ℝ E : ℝ) ^ 2 * Rm)) := by
  classical
  intro x v
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  let A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
    (metricRm04At (I := I) (M := M) g x))
  have hcomp : ∀ i j,
      |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j))| ≤
        (Module.finrank ℝ E : ℝ) * A := by
    intro i j
    simpa [A] using metricRicciComp_le (I := I) g basis hON i j
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * A := by
    intro u hu
    have h := ricci_unitSphere_le_of_componentBound
      (I := I) g (metricRicciAt (I := I) (M := M) g x) basis hON
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hcomp u hu
    simpa [A, pow_two, mul_assoc] using h
  have hquad := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g x) hunit v
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g x v v] at hquad
  have hinner : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst v
      simp
    · exact (g.pos x v hv).le
  have hcoef :
      (Module.finrank ℝ E : ℝ) ^ 2 * A ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Rm :=
    mul_le_mul_of_nonneg_left (hRm x) (sq_nonneg _)
  have habs : |ricciTensor (I := I) g x v v| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner x v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hcoef hinner)
  simpa only [neg_mul] using (abs_le.mp habs).1

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
