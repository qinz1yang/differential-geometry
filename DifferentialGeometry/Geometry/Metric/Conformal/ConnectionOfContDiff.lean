import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.Evaluation
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.DifferenceKoszul
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Connection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem mvfderiv_exp_two (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => Real.exp (2 * F y)) x v =
      2 * Real.exp (2 * F x) * mvfderiv I F x v := by
  have hG : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
      (Real.exp (2 * F x) * 2) (F x) := by
    simpa using ((hasDerivAt_id (F x)).const_mul 2).exp
  have hcomp := mvfderiv_comp x hG.differentiableAt.mdifferentiableAt
    (hF.mdifferentiable (by simp) x)
  have heval := congrArg (fun D : TangentSpace I x →L[ℝ] ℝ => D v) hcomp
  have hGD : mvfderiv 𝓘(ℝ) (fun t : ℝ => Real.exp (2 * t)) (F x) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (Real.exp (2 * F x) * 2) := by
    change mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => Real.exp (2 * t)) (F x) = _
    rw [mfderiv_eq_fderiv]
    exact hG.hasFDerivAt.fderiv
  rw [hGD] at heval
  change mvfderiv I (fun y => Real.exp (2 * F y)) x v =
    mvfderiv I F x v * (Real.exp (2 * F x) * 2) at heval
  exact heval.trans (by ring)

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M]

private theorem metricCovDeriv_conformalMetric
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    metricCovDeriv (conformalMetricOfContDiff g F hF) (LeviCivita g) X Y Z x =
      2 * Real.exp (2 * F x) * mvfderiv I F x (X x) * g.inner x (Y x) (Z x) := by
  have hscale : ContMDiff I 𝓘(ℝ) ∞ (fun y => Real.exp (2 * F y)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)
  have hmc := metricCovDeriv_self_eq_zero g
    (X := X) (Y := Y) (Z := Z)
    (Y.contMDiff.mdifferentiable (by simp) x) (Z.contMDiff.mdifferentiable (by simp) x)
  unfold metricCovDeriv at hmc ⊢
  simp only [directionalDeriv_eq, conformalMetricOfContDiff_inner] at hmc ⊢
  change mvfderiv I (fun b => Real.exp (2 * F b) * g.inner b (Y b) (Z b)) x (X x) -
      Real.exp (2 * F x) * g.inner x ((LeviCivita g) Y x (X x)) (Z x) -
      Real.exp (2 * F x) * g.inner x (Y x) ((LeviCivita g) Z x (X x)) = _
  rw [mvfderiv_mul_at (X x) (hscale.mdifferentiable (by simp) x)
    ((contMDiff_metric_inner g Y Z).mdifferentiable (by simp) x), mvfderiv_exp_two F hF]
  change mvfderiv I (fun b => g.inner b (Y b) (Z b)) x (X x) -
    g.inner x ((LeviCivita g) Y x (X x)) (Z x) -
    g.inner x (Y x) ((LeviCivita g) Z x (X x)) = 0 at hmc
  linear_combination Real.exp (2 * F x) * hmc

theorem connectionDifference_conformalMetricOfContDiff
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (u v : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g x u v =
      mvfderiv I F x v • u + mvfderiv I F x u • v -
        g.inner x u v • gradFun g F x := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq
    (conformalMetricOfContDiff g F hF)
  intro w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
  have hk := connectionDifference_koszul (conformalMetricOfContDiff g F hF) g
    (X.contMDiff.mdifferentiable (by simp) x)
    (Y.contMDiff.mdifferentiable (by simp) x)
    (Z.contMDiff.mdifferentiable (by simp) x)
  rw [metricCovDeriv_conformalMetric, metricCovDeriv_conformalMetric,
    metricCovDeriv_conformalMetric, hX, hY, hZ] at hk
  simp only [conformalMetricOfContDiff_inner, map_sub, map_add, map_smul, sub_apply,
    add_apply, smul_apply, smul_eq_mul, inner_gradFun] at hk ⊢
  rw [g.symm x v u] at hk
  change Real.exp (2 * F x) *
    g.inner x (PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g x u v) w =
      mvfderiv I F x v * (Real.exp (2 * F x) * g.inner x u w) +
        mvfderiv I F x u * (Real.exp (2 * F x) * g.inner x v w) -
          g.inner x u v * (Real.exp (2 * F x) * mvfderiv I F x w)
  linear_combination (1 / 2 : ℝ) * hk

theorem leviCivita_conformalMetricOfContDiff
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (Y : ∀ x : M, TangentSpace I x) (x : M)
    (hY : MDifferentiableAt I I.tangent (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    (LeviCivita (conformalMetricOfContDiff g F hF)) Y x v =
      (LeviCivita g) Y x v +
        (mvfderiv I F x v • Y x + mvfderiv I F x (Y x) • v -
          g.inner x (Y x) v • gradFun g F x) := by
  have h := connectionDifference_conformalMetricOfContDiff g F hF x (Y x) v
  rw [PDE.DeTurck.connectionDifference_apply _ _ hY v] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end DifferentialGeometry.Geometry.Connection
