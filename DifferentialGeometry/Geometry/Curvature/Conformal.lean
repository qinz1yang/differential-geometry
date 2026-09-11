import DifferentialGeometry.Geometry.Metric.Conformal.Connection
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.Curvature
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Metric.Conformal.ConnectionOfContDiff
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem quadratic_difference_inner
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (u v : TangentSpace I x) :
    let d := mvfderiv (I := I) F x
    let G := gradFun g F x
    let A := fun a b : TangentSpace I x => d b • a + d a • b - g.inner x a b • G
    g.inner x u (A (A v v) u - A (A v u) v) =
      (d u) ^ 2 * g.inner x v v + (d v) ^ 2 * g.inner x u u -
        2 * d u * d v * g.inner x u v -
        g.inner x G G * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  dsimp only
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul,
    gradFun_metricDual_mvfderiv, g.symm x u (gradFun g F x),
    g.symm x v u]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem metric_pair_smooth (g : SmoothRiemannianMetric I M)
    (Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x => g.inner x (Y x) (Z x)) := by
  intro x
  exact CovariantDerivative.metric_inner_contMDiffAt g (Y.contMDiff x) (Z.contMDiff x) le_rfl

private theorem differential_field_derivative
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M)
    (u : TangentSpace I x) :
    mvfderiv (I := I) (fun y => mvfderiv (I := I) F y (Y y)) x u =
      hessFun g F x u (Y x) +
        mvfderiv (I := I) F x ((LeviCivita g).toFun Y x u) := by
  have hG := (gradFun_contMDiff_total g hF x).mdifferentiableAt (by simp)
  have hY := Y.mdifferentiableAt (x := x)
  have heq : (fun y => mvfderiv (I := I) F y (Y y)) =
      (fun y => g.inner y (gradFun g F y) (Y y)) := by
    funext y
    exact (gradFun_metricDual_mvfderiv g F y (Y y)).symm
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [heq]
  change mfderiv I 𝓘(ℝ) (fun y => g.inner y (gradFun g F y) (Y y)) x u = _
  rw [(LeviCivita_isMetricCompatible g).apply hG hY u,
    ← hessFun_eq_cov_grad g hF x u (Y x)]
  congr 1
  exact gradFun_metricDual_mvfderiv g F x ((LeviCivita g).toFun Y x u)

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem inner_cov_smul
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (hf : MDifferentiableAt I 𝓘(ℝ) f x) (u w : TangentSpace I x) :
    g.inner x w ((LeviCivita g).toFun (f • (fun y => Y y)) x u) =
      f x * g.inner x w ((LeviCivita g).toFun Y x u) +
        mvfderiv (I := I) f x u * g.inner x w (Y x) := by
  rw [(LeviCivita g).isCovariantDerivativeOnUniv.leibniz Y.mdifferentiableAt hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul]

omit [T2Space M] [BoundarylessManifold I M] in
private theorem differential_field_smooth
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(ℝ) ∞ (fun y => mvfderiv (I := I) F y (Y y)) := by
  let G : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨gradFun g F, gradFun_contMDiff_total g hF⟩
  apply (metric_pair_smooth g G Y).congr
  intro y
  exact (gradFun_metricDual_mvfderiv g F y (Y y)).symm

private theorem inner_cov_difference_field
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (u w : TangentSpace I x) :
    g.inner x w ((LeviCivita g).toFun (fun y =>
      mvfderiv (I := I) F y (Y y) • Z y + mvfderiv (I := I) F y (Z y) • Y y -
        g.inner y (Y y) (Z y) • gradFun g F y) x u) =
      mvfderiv (I := I) F x (Y x) * g.inner x w ((LeviCivita g).toFun Z x u) +
      mvfderiv (I := I) F x (Z x) * g.inner x w ((LeviCivita g).toFun Y x u) +
      (hessFun g F x u (Y x) + mvfderiv (I := I) F x ((LeviCivita g).toFun Y x u)) *
        g.inner x w (Z x) +
      (hessFun g F x u (Z x) + mvfderiv (I := I) F x ((LeviCivita g).toFun Z x u)) *
        g.inner x w (Y x) -
      g.inner x (Y x) (Z x) * hessFun g F x u w -
      (g.inner x ((LeviCivita g).toFun Y x u) (Z x) +
        g.inner x (Y x) ((LeviCivita g).toFun Z x u)) * mvfderiv (I := I) F x w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let G : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨gradFun g F, gradFun_contMDiff_total g hF⟩
  let dY := fun y => mvfderiv (I := I) F y (Y y)
  let dZ := fun y => mvfderiv (I := I) F y (Z y)
  let mYZ := fun y => g.inner y (Y y) (Z y)
  have hdY : MDifferentiableAt I 𝓘(ℝ) dY x :=
    ((differential_field_smooth g F hF Y) x).mdifferentiableAt (by simp)
  have hdZ : MDifferentiableAt I 𝓘(ℝ) dZ x :=
    ((differential_field_smooth g F hF Z) x).mdifferentiableAt (by simp)
  have hmYZ : MDifferentiableAt I 𝓘(ℝ) mYZ x :=
    ((metric_pair_smooth g Y Z) x).mdifferentiableAt (by simp)
  have ha := hdY.smul_section Z.mdifferentiableAt
  have hb := hdZ.smul_section Y.mdifferentiableAt
  have hc := hmYZ.neg.smul_section G.mdifferentiableAt
  have hfield : (fun y =>
      mvfderiv (I := I) F y (Y y) • Z y + mvfderiv (I := I) F y (Z y) • Y y -
        g.inner y (Y y) (Z y) • gradFun g F y) =
      (dY • (fun y => Z y) + dZ • (fun y => Y y)) + (-mYZ) • (fun y => G y) := by
    funext y
    simp only [Pi.add_apply, Pi.neg_apply, neg_smul, sub_eq_add_neg]
    rfl
  rw [hfield, (LeviCivita g).isCovariantDerivativeOnUniv.add (mdifferentiableAt_add_section ha hb) hc,
    (LeviCivita g).isCovariantDerivativeOnUniv.add ha hb]
  simp only [add_apply, map_add]
  rw [inner_cov_smul g dY Z x hdY u w, inner_cov_smul g dZ Y x hdZ u w,
    inner_cov_smul g (-mYZ) G x hmYZ.neg u w]
  have hneg : mvfderiv (I := I) (-mYZ) x u = -mvfderiv (I := I) mYZ x u := by
    rw [mvfderiv_neg, neg_apply]
  have hmetric : mvfderiv (I := I) mYZ x u =
      g.inner x ((LeviCivita g).toFun Y x u) (Z x) +
        g.inner x (Y x) ((LeviCivita g).toFun Z x u) :=
    (LeviCivita_isMetricCompatible g).apply Y.mdifferentiableAt Z.mdifferentiableAt u
  rw [hneg, hmetric]
  dsimp only [dY, dZ, mYZ, Pi.neg_apply]
  rw [differential_field_derivative g F hF Y x u,
    differential_field_derivative g F hF Z x u]
  have hGcov : g.inner x w ((LeviCivita g).toFun G x u) = hessFun g F x u w := by
    rw [g.symm]
    exact (hessFun_eq_cov_grad g hF x u w).symm
  have hGw : g.inner x w (G x) = mvfderiv (I := I) F x w := by
    rw [g.symm]
    exact gradFun_metricDual_mvfderiv g F x w
  rw [hGcov, hGw]
  ring

omit [I.Boundaryless] in
private theorem conformal_diffSec
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (Y Z : ∀ y : M, TangentSpace I y) :
    diffSec (LeviCivita g) (LeviCivita (conformalMetricOfContDiff g F hF)) Y Z = fun y =>
      mvfderiv (I := I) F y (Y y) • Z y + mvfderiv (I := I) F y (Z y) • Y y -
        g.inner y (Y y) (Z y) • gradFun g F y := by
  funext y
  change PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g y (Z y) (Y y) = _
  rw [connectionDifference_conformalMetricOfContDiff, g.symm y (Z y) (Y y)]

private theorem inner_covDerivDiff_conformalMetric
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (X : ∀ y : M, TangentSpace I y)
    (Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (w : TangentSpace I x) :
    g.inner x w (covDerivDiff (LeviCivita g) (LeviCivita (conformalMetricOfContDiff g F hF)) X Y Z x) =
      hessFun g F x (X x) (Y x) * g.inner x w (Z x) +
      hessFun g F x (X x) (Z x) * g.inner x w (Y x) -
      g.inner x (Y x) (Z x) * hessFun g F x (X x) w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA : CovariantDerivative.difference (LeviCivita (conformalMetricOfContDiff g F hF)) (LeviCivita g) =
      PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g := rfl
  rw [covDerivDiff, conformal_diffSec]
  simp only [hA, connectionDifference_conformalMetricOfContDiff, map_sub]
  rw [inner_cov_difference_field g F hF Y Z x (X x) w]
  have hGw : g.inner x w (gradFun g F x) = mvfderiv (I := I) F x w := by
    rw [g.symm]
    exact gradFun_metricDual_mvfderiv g F x w
  simp only [covApply, map_add, map_smul, smul_eq_mul, hGw]
  rw [g.symm x (Z x) ((LeviCivita g).toFun Y x (X x)),
    g.symm x ((LeviCivita g).toFun Z x (X x)) (Y x)]
  ring

theorem metricRm04StdAt_conformalMetric_plane
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (u v : TangentSpace I x) :
    metricRm04StandardAt (conformalMetricOfContDiff g F hF) x u v v u =
      Real.exp (2 * F x) *
        (metricRm04StandardAt g x u v v u -
          hessFun g F x u u * g.inner x v v - hessFun g F x v v * g.inner x u u +
          2 * hessFun g F x u v * g.inner x u v +
          (mvfderiv (I := I) F x u) ^ 2 * g.inner x v v +
          (mvfderiv (I := I) F x v) ^ 2 * g.inner x u u -
          2 * mvfderiv (I := I) F x u * mvfderiv (I := I) F x v * g.inner x u v -
          g.inner x (gradFun g F x) (gradFun g F x) *
            (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨U, hU⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hr := riemannSec_difference (LeviCivita g) (LeviCivita (conformalMetricOfContDiff g F hF))
    U.contMDiff V.contMDiff V.contMDiff (LeviCivita_torsion_eq_zero g) x
  rw [← riemannOp_apply_smooth (cov := LeviCivita (conformalMetricOfContDiff g F hF)) U.contMDiff V.contMDiff V.contMDiff,
    ← riemannOp_apply_smooth (cov := LeviCivita g) U.contMDiff V.contMDiff V.contMDiff] at hr
  have hi := congrArg (fun a : TangentSpace I x => g.inner x u a) hr
  simp only [map_add, map_sub] at hi
  rw [inner_covDerivDiff_conformalMetric g F hF U V V x u,
    inner_covDerivDiff_conformalMetric g F hF V U V x u] at hi
  have hA : CovariantDerivative.difference (LeviCivita (conformalMetricOfContDiff g F hF)) (LeviCivita g) =
      PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g := rfl
  simp only [diffSec, hA, connectionDifference_conformalMetricOfContDiff, hU, hV] at hi
  have hq := quadratic_difference_inner g F x u v
  dsimp only at hq
  simp only [map_sub] at hq hi
  rw [hq] at hi
  rw [rm04_eq_inner_riem, conformalMetricOfContDiff_inner, rm04_eq_inner_riem, hi]
  ring

theorem sectionalCurvature_conformalMetric_of_unit_orthogonal
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (u v : TangentSpace I x)
    (hu : g.inner x u u = 1) (hv : g.inner x v v = 1) (huv : g.inner x u v = 0) :
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvature
        (conformalMetricOfContDiff g F hF) x (Real.exp (-F x) • u) (Real.exp (-F x) • v) =
      Real.exp (-(2 * F x)) *
        (DifferentialGeometry.Geometry.Riemannian.sectionalCurvature g x u v -
          hessFun g F x u u - hessFun g F x v v +
          (mvfderiv (I := I) F x u) ^ 2 + (mvfderiv (I := I) F x v) ^ 2 -
          g.inner x (gradFun g F x) (gradFun g F x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_smul _ _
    (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    metricRm04StdAt_conformalMetric_plane]
  simp only [conformalMetricOfContDiff_inner, hu, hv, huv, mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, add_zero]
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal
    g x u v hu hv huv, Real.exp_neg]
  field_simp

end DifferentialGeometry.Geometry.Curvature
