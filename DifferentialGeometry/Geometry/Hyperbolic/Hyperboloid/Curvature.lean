import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Connection
import DifferentialGeometry.Geometry.Connection.ConnectionForm
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import Mathlib.Tactic.Module

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def radialVectorField (x : Hyperboloid E) : TangentSpace 𝓘(ℝ, E) x :=
  spaceVectorField x.space x

private theorem tangent_trivializationAt_apply (p x : Hyperboloid E)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ x v =
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x v := by
  have hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_eq_spaceHomeomorph]
    trivial
  have h := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt_symmL (R := ℝ) hx
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x v)
  rw [tangent_trivializationAt_symmL] at h
  exact h

private theorem mdifferentiableAt_radialVectorField (x : Hyperboloid E) :
    MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y : Hyperboloid E => (⟨y, radialVectorField y⟩ : TangentBundle 𝓘(ℝ, E) (Hyperboloid E))) x := by
  rw [mdifferentiableAt_section]
  have h := (contMDiff_space (E := E) (n := ∞)).mdifferentiableAt (by decide) (x := x)
  convert h using 1
  ext y
  have hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_eq_spaceHomeomorph]
    trivial
  rw [← (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearMapAt_apply_of_mem ℝ hy,
    tangent_trivializationAt_apply]
  rfl

variable [FiniteDimensional ℝ E]

private abbrev metricConnection :=
  Geometry.Connection.leviCivitaConnectionOfMetric (riemannianMetric (E := E))

private theorem cov_spaceVectorField (x : Hyperboloid E) (v w : E) :
    metricConnection (spaceVectorField w) x (spaceVectorField v x) =
      -(riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x)) •
        radialVectorField x := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).injective
  have h := leviCivita_tangentConstAt x (spaceVectorField v x) (spaceVectorField w x)
  rw [tangentConstAt_spaceVectorField, mfderiv_spaceDiffeomorph] at h
  rw [map_smul]
  exact h

private theorem cov_radialVectorField (x : Hyperboloid E) (v : E) :
    metricConnection radialVectorField x (spaceVectorField v x) =
      spaceVectorField v x -
        riemannianMetric.inner x (spaceVectorField v x) (radialVectorField x) • radialVectorField x := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (origin : Hyperboloid E)
  have hx : x ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_eq_spaceHomeomorph]
    trivial
  have hcoord : (fun y : Hyperboloid E => e.continuousLinearMapAt ℝ y (radialVectorField y)) = space := by
    funext y
    rw [tangent_trivializationAt_apply]
    rfl
  have hconst (w : E) : (fun y : Hyperboloid E => e.symmL ℝ y w) = spaceVectorField w := by
    funext y
    rw [tangent_trivializationAt_symmL]
    rfl
  have h := metricConnection.covariant_derivative_coord e hx
    (mdifferentiableAt_radialVectorField x) (spaceVectorField v x)
  rw [hcoord, _root_.CovariantDerivative.connectionForm_apply metricConnection e hx] at h
  have hval : e.continuousLinearMapAt ℝ x (radialVectorField x) = x.space := by
    rw [tangent_trivializationAt_apply]
    rfl
  rw [hval, hconst, cov_spaceVectorField] at h
  have hd : mvfderiv 𝓘(ℝ, E) (space : Hyperboloid E → E) x (spaceVectorField v x) = v := by
    change NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x (spaceVectorField v x)) = v
    rw [mfderiv_spaceDiffeomorph]
    rfl
  rw [hd, map_smul, hval] at h
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).injective
  rw [map_sub, map_smul]
  rw [tangent_trivializationAt_apply] at h
  have heval (w : E) :
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x (spaceVectorField w x) = w :=
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).apply_symm_apply w
  simpa only [radialVectorField, heval, neg_smul, sub_eq_add_neg] using h

omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_metric_pair (x : Hyperboloid E) (v w : E) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun y : Hyperboloid E => riemannianMetric.inner y (spaceVectorField v y) (spaceVectorField w y)) x := by
  have hg := riemannianMetric.contMDiff.mdifferentiableAt (by decide) (x := x)
  have h := MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg
    (mdifferentiableAt_spaceVectorField x v) (mdifferentiableAt_spaceVectorField x w)
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

private theorem cov_neg_metric_radial (x : Hyperboloid E) (u v w : E) :
    metricConnection
      (fun y : Hyperboloid E =>
        -(riemannianMetric.inner y (spaceVectorField v y) (spaceVectorField w y)) • radialVectorField y)
      x (spaceVectorField u x) =
      -(riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x)) •
          (spaceVectorField u x -
            riemannianMetric.inner x (spaceVectorField u x) (radialVectorField x) • radialVectorField x) -
        (riemannianMetric.inner x
            (metricConnection (spaceVectorField v) x (spaceVectorField u x)) (spaceVectorField w x) +
          riemannianMetric.inner x (spaceVectorField v x)
            (metricConnection (spaceVectorField w) x (spaceVectorField u x))) • radialVectorField x := by
  have hm := (Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible riemannianMetric).mvfderiv_inner
    (spaceVectorField u x) (mdifferentiableAt_spaceVectorField x v)
      (mdifferentiableAt_spaceVectorField x w)
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x =>
      L (spaceVectorField u x))
    (metricConnection.isCovariantDerivativeOnUniv.leibniz
      (mdifferentiableAt_radialVectorField x) (mdifferentiableAt_metric_pair x v w).neg)
  change metricConnection
    (fun y : Hyperboloid E =>
      -(riemannianMetric.inner y (spaceVectorField v y) (spaceVectorField w y)) • radialVectorField y)
    x (spaceVectorField u x) = _ at h
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, Pi.neg_apply] at h
  rw [mvfderiv_neg, neg_apply, hm, cov_radialVectorField] at h
  simpa only [neg_smul, sub_eq_add_neg] using h

private theorem bracket_spaceVectorField (x : Hyperboloid E) (v w : E) :
    VectorField.mlieBracket 𝓘(ℝ, E) (spaceVectorField v) (spaceVectorField w) x = 0 := by
  have h := Geometry.Connection.torsion_free_apply
    (Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree riemannianMetric)
    (mdifferentiableAt_spaceVectorField x v) (mdifferentiableAt_spaceVectorField x w)
  rw [cov_spaceVectorField, cov_spaceVectorField,
    riemannianMetric.symm x (spaceVectorField w x) (spaceVectorField v x), sub_self] at h
  exact h.symm

private theorem curvature_spaceVectorField (x : Hyperboloid E) (u v w : E) :
    Geometry.Curvature.connectionRiemannCurvatureField metricConnection
      (spaceVectorField u) (spaceVectorField v) (spaceVectorField w) x =
      -(riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x)) • spaceVectorField u x +
        riemannianMetric.inner x (spaceVectorField u x) (spaceVectorField w x) • spaceVectorField v x := by
  have hcov (a b : E) :
      (fun y : Hyperboloid E => metricConnection (spaceVectorField b) y (spaceVectorField a y)) =
        fun y : Hyperboloid E =>
          -(riemannianMetric.inner y (spaceVectorField a y) (spaceVectorField b y)) • radialVectorField y :=
    funext fun y => cov_spaceVectorField y a b
  rw [Geometry.Curvature.connectionRiemannCurvatureField, hcov, hcov,
    bracket_spaceVectorField, map_zero, sub_zero, cov_neg_metric_radial, cov_neg_metric_radial]
  rw [cov_spaceVectorField, cov_spaceVectorField, cov_spaceVectorField, cov_spaceVectorField]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [riemannianMetric.symm x (spaceVectorField v x) (spaceVectorField u x)]
  module

theorem metricRm04StandardAt_riemannianMetric (x : Hyperboloid E)
    (X Y Z W : TangentSpace 𝓘(ℝ, E) x) :
    Geometry.Curvature.metricRm04StandardAt riemannianMetric x X Y Z W =
      riemannianMetric.inner x X Z * riemannianMetric.inner x Y W -
        riemannianMetric.inner x Y Z * riemannianMetric.inner x X W := by
  rw [Geometry.Curvature.metricRm04StandardAt_apply,
    show Geometry.Curvature.metricRm04At riemannianMetric x =
      Geometry.Curvature.CovariantDerivative.riemannCurvature04At riemannianMetric
        (Geometry.Curvature.metricCov riemannianMetric)
        (Geometry.Curvature.metricCov_smooth riemannianMetric) x from rfl,
    Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const]
  change riemannianMetric.inner x W
    (Geometry.Curvature.connectionRiemannCurvatureField metricConnection
      (Geometry.Connection.tangentConstAt x X) (Geometry.Connection.tangentConstAt x Y)
      (Geometry.Connection.tangentConstAt x Z) x) = _
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
  have hvec (V : TangentSpace 𝓘(ℝ, E) x) : spaceVectorField (e V) x = V :=
    e.symm_apply_apply V
  have hconst (V : TangentSpace 𝓘(ℝ, E) x) :
      Geometry.Connection.tangentConstAt x V = spaceVectorField (e V) := by
    have h := tangentConstAt_spaceVectorField x (e V)
    rw [hvec] at h
    exact h
  rw [hconst X, hconst Y, hconst Z, curvature_spaceVectorField]
  simp only [hvec, map_add, map_smul, smul_eq_mul]
  rw [riemannianMetric.symm x W X, riemannianMetric.symm x W Y]
  ring

theorem sectionalCurvature_eq_neg_one (x : Hyperboloid E)
    (v w : TangentSpace 𝓘(ℝ, E) x) (hvw : LinearIndependent ℝ ![v, w]) :
    Geometry.Riemannian.sectionalCurvature riemannianMetric x v w = -1 := by
  let _ : T2Space (Hyperboloid E) := (spaceHomeomorph (E := E)).symm.t2Space
  have hden : riemannianMetric.inner x v v * riemannianMetric.inner x w w -
      (riemannianMetric.inner x v w) ^ 2 ≠ 0 := by
    apply ne_of_gt
    simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
      Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
        riemannianMetric x v w hvw
  rw [Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    metricRm04StandardAt_riemannianMetric, riemannianMetric.symm x w v]
  apply (div_eq_iff hden).2
  ring

end DifferentialGeometry.Hyperboloid
