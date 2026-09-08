import DifferentialGeometry.Geometry.Metric.Conformal.Operators
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDifferenceKoszul

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle
open Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] in
private theorem mfderiv_exp_two_mul_apply
    (u : C^∞⟮I, M; Real⟯) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => Real.exp (2 * u y)) x v =
      2 * Real.exp (2 * u x) * mvfderiv I (u : M → Real) x v := by
  have hu := (u.contMDiff.mdifferentiableAt (by simp) :
    MDifferentiableAt I 𝓘(Real) (u : M → Real) x).hasMFDerivAt
  have htwo : HasMFDerivAt I 𝓘(Real) (fun y : M => 2 * u y) x
      ((2 : Real) • mvfderiv I (u : M → Real) x) := hu.const_smul 2
  have hx := ((Real.hasDerivAt_exp (2 * u x)).hasFDerivAt.hasMFDerivAt.comp x htwo).mfderiv
  have happly := congrArg (fun F : TangentSpace I x →L[Real] Real => F v) hx
  change mvfderiv I (fun y => Real.exp (2 * u y)) x v =
    (2 * mvfderiv I (u : M → Real) x v) * Real.exp (2 * u x) at happly
  rw [happly]
  ring

private theorem metricCovDeriv_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    metricCovDeriv (conformalMetric g u) (LeviCivita g) X Y Z x =
      2 * Real.exp (2 * u x) * mvfderiv I (u : M → Real) x (X x) *
        g.inner x (Y x) (Z x) := by
  have hcoeff : ContMDiff I 𝓘(Real) ∞ (fun y : M => Real.exp (2 * u y)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff)
  have hpair := contMDiff_g_inner_of_smooth_sections g Y Z
  have hm := (LeviCivita_isMetricCompatible g).apply
    (x := x) Y.mdifferentiableAt Z.mdifferentiableAt (X x)
  unfold metricCovDeriv
  simp_rw [conformalMetric_inner]
  rw [directionalDeriv_eq]
  change mvfderiv I (fun y => Real.exp (2 * u y) * g.inner y (Y y) (Z y)) x (X x) - _ - _ = _
  rw [mvfderiv_mul_at (X x) (hcoeff.mdifferentiableAt (by simp))
    (hpair.mdifferentiableAt (by simp))]
  change mvfderiv I (fun y => g.inner y (Y y) (Z y)) x (X x) = _ at hm
  rw [mfderiv_exp_two_mul_apply, hm]
  ring

theorem connectionDifference_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (conformalMetric g u) g x w v =
      mvfderiv I (u : M → Real) x v • w + mvfderiv I (u : M → Real) x w • v -
        g.inner x v w • gradientFun g u x := by
  apply SmoothRiemannianMetric.eq_of_inner_eq (conformalMetric g u)
  intro z
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x w
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x z
  have hk := connectionDifference_koszul (conformalMetric g u) g
    (x := x) X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt
  rw [metricCovDeriv_conformalMetric, metricCovDeriv_conformalMetric,
    metricCovDeriv_conformalMetric, hX, hY, hZ] at hk
  simp only [conformalMetric_inner, map_sub, map_add, map_smul, sub_apply,
    add_apply, smul_apply, smul_eq_mul, inner_gradientFun]
  rw [conformalMetric_inner] at hk
  nlinarith [hk]

theorem LeviCivita_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    {Y : (x : M) → TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    LeviCivita (conformalMetric g u) Y x v = LeviCivita g Y x v +
      mvfderiv I (u : M → Real) x v • Y x + mvfderiv I (u : M → Real) x (Y x) • v -
        g.inner x v (Y x) • gradientFun g u x := by
  have h := connectionDifference_conformalMetric g u x v (Y x)
  rw [PDE.DeTurck.connectionDifference_apply _ _ hY] at h
  calc
    _ = LeviCivita g Y x v +
        (mvfderiv I (u : M → Real) x v • Y x +
          mvfderiv I (u : M → Real) x (Y x) • v -
          g.inner x v (Y x) • gradientFun g u x) := by
      rw [← h]
      abel
    _ = _ := by abel

end DifferentialGeometry.Geometry.Connection
