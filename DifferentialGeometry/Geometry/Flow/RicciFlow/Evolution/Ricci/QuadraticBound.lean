import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Ricci quadratic bound from the lowered curvature norm

This file records the pointwise, arbitrary-dimensional estimate that converts
the norm of the canonical lowered Riemann tensor of a Ricci-flow family into a
quadratic-form bound for its Ricci tensor.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- The Ricci quadratic form of a solution-family metric is controlled
pointwise by the norm of its canonical lowered Riemann tensor. -/
theorem ricci_quad_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t C : Real} (x : M) (v : TangentSpace I x)
    (hcurv :
      normSq0S (I := I) (S.base.metric t) x 4
        (S.base.rm04 t x) ≤ C) :
    |ricciTensor (I := I) (S.base.metric t) x v v| ≤
      (Module.finrank Real E : Real) ^ 2 * Real.sqrt C *
        (S.base.metric t).inner x v v := by
  let n := Module.finrank Real (TangentSpace I x)
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis (I := I) (S.base.metric t) x
  have hcomp : ∀ i j : Fin n,
      |S.ricciAt t x (vec2 (I := I) (basis i) (basis j))| ≤
        (n : Real) * Real.sqrt C := by
    intro i j
    calc
      |S.ricciAt t x (vec2 (I := I) (basis i) (basis j))| =
          |metricRicciAt (I := I) (S.base.metric t) x
            (vec2 (I := I) (basis i) (basis j))| := rfl
      _ ≤ (n : Real) *
          Real.sqrt
            (normSq0S (I := I) (S.base.metric t) x 4
              (metricRm04At (I := I) (S.base.metric t) x)) :=
        by
          simpa only [n, Fintype.card_fin] using
            metricRicciComp_le (I := I) (S.base.metric t) basis hON i j
      _ ≤ (n : Real) * Real.sqrt C := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        apply Real.sqrt_le_sqrt
        simpa only [SolutionFamily.rm04, metricRm04_apply] using hcurv
  have hunit : ∀ u : TangentSpace I x,
      (S.base.metric t).inner x u u = 1 →
        |S.ricciAt t x (vec2 (I := I) u u)| ≤
          (n : Real) ^ 2 * Real.sqrt C := by
    intro u hu
    have h :=
      ricci_unitSphere_le_of_componentBound
        (I := I) (S.base.metric t) (S.ricciAt t x) basis hON
        (R := (n : Real) * Real.sqrt C)
        (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg C))
        hcomp u hu
    nlinarith
  have hray :=
    tensor02_quadForm_abs_le_of_unit_bound
      (I := I) (S.base.metric t) (S.ricciAt t x) hunit v
  change
    |S.ricciAt t x (vec2 (I := I) v v)| ≤
      (Module.finrank Real E : Real) ^ 2 * Real.sqrt C *
        (S.base.metric t).inner x v v at hray
  rw [← metricRicciAt_apply_eq_ricciTensor]
  exact hray

end DifferentialGeometry.PDE.RicciFlow
