import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem riemannOp_apply_eq_zero_of_covApply_eq_smul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {Z : (z : M) → TangentSpace I z}
    (hZ : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% Z))
    {c : Real}
    (hcovZ : ∀ (z : M) (u : TangentSpace I z),
      cov.toFun Z z u = c • u)
    (x : M) (v w : TangentSpace I x) :
    riemannOp cov x v w (Z x) = 0 := by
  let X : (z : M) → TangentSpace I z :=
    smoothExtensionTangent (I := I) x v
  let Y : (z : M) → TangentSpace I z :=
    smoothExtensionTangent (I := I) x w
  have hX : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% Y) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  have hcovYZ : covApply cov Y Z = c • Y := by
    funext z
    exact hcovZ z (Y z)
  have hcovXZ : covApply cov X Z = c • X := by
    funext z
    exact hcovZ z (X z)
  have hcovY :
      cov.toFun (c • Y) x = c • cov.toFun Y x := by
    exact cov.isCovariantDerivativeOn.smul_const c
      (hY.mdifferentiableAt (by simp))
  have hcovX :
      cov.toFun (c • X) x = c • cov.toFun X x := by
    exact cov.isCovariantDerivativeOn.smul_const c
      (hX.mdifferentiableAt (by simp))
  rw [← hXx, ← hYx]
  rw [riemannOp_apply_smooth cov hX hY hZ]
  rw [riemannSec_torsionFree_form htor
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))]
  rw [hcovYZ, hcovXZ, hcovY, hcovX,
    hcovZ x (cov.toFun Y x (X x)), hcovZ x (cov.toFun X x (Y x))]
  simp

end DifferentialGeometry.Geometry.Curvature
