import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Geometry.Curvature.PullbackNaturality
import DifferentialGeometry.Geometry.Metric.Sphere.RoundShape
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Curvature.MetricSectional

/-!
# The round sphere has constant positive sectional curvature

Combining the homogeneity of the round metric (the orthogonal group acts transitively
by isometries) with the naturality of the Riemann tensor under isometries, a curvature
identity proved at one point spreads to the whole sphere.  Here we record the
**curvature-invariance** half (Step 5A): the metric `(0,4)` Riemann tensor of the round
metric is invariant under `sphereDiffeo e`.

The remaining one-point computation (the explicit chart-Christoffel value at a pole) is
the `ConstPosSecMetric roundMetric` capstone, still ahead.

## Main result

* `metricRm04_round_invariant` — Riemann-tensor invariance under the orthogonal action.
-/

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

/-- **Curvature invariance under the orthogonal action.**  The metric `(0,4)` Riemann
tensor of the round metric at `x` equals its value at `sphereDiffeo e x` on the
pushed-forward vectors — because `sphereDiffeo e` is an isometry of the round metric
(`pullbackMetric_round_eq`) and the Riemann tensor is natural (`metricRm04Std_pullback`). -/
theorem metricRm04_round_invariant (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1)
    (X Y Z W : TangentSpace (𝓡 n) x) :
    metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Z W
      = metricRm04StdAt (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e x)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x X)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Y)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Z)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x W) := by
  haveI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  haveI : IsManifold (𝓡 n) 1 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have h := metricRm04Std_pullback (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e)
    x X Y Z W
  rwa [pullbackMetric_round_eq] at h

set_option maxHeartbeats 800000 in
omit [NeZero n] in
/-- **The round sphere's sectional-curvature numerator is the Gram determinant** (constant curvature
`c = 1`): `Rm04(X,Y,Y,X) = g(X,X)g(Y,Y) − g(X,Y)²` at every point.  This is the curvature content of
`ConstPosSecMetric roundMetric`; the `∃ c, …` wrapper is assembled where `ConstPosSecMetric` is in
scope (the Hamilton space-form file).  The curvature operator on the chart-constant extensions is
reduced to genuinely smooth sections by germ congruence
(`connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst`), then evaluated by the Gauss
equation `dIncl_curv_inner`. -/
theorem roundMetric_sec_value (x : sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x) :
    metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Y X
      = (roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x Y Y
        - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x X Y := by
  haveI : IsManifold (𝓡 n) ∞ (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x Y
  rw [metricRm04StdAt_apply,
    show metricRm04At (roundMetric (E := E) (n := n)) x
        = riemannCurvature04At (roundMetric (E := E) (n := n))
            (metricCov (roundMetric (E := E) (n := n)))
            (metricCov_smooth (roundMetric (E := E) (n := n))) x from rfl,
    riemannCurvature04At_apply_const,
    show CovariantDerivative.riemannCurvatureAux (metricCov (roundMetric (E := E) (n := n)))
          (CovariantDerivative.tangentConstAt x X) (CovariantDerivative.tangentConstAt x Y)
          (CovariantDerivative.tangentConstAt x Y) x
        = CovariantDerivative.riemannCurvatureAux (metricCov (roundMetric (E := E) (n := n)))
            (⇑Xc) (⇑Yc) (⇑Yc) x from by
        simp only [riemannCurvatureAux_eq_connectionRiemannCurvatureField]
        exact connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
          (metricCov (roundMetric (E := E) (n := n)))
          (metricCov_smooth (roundMetric (E := E) (n := n))) X Y Y Xc Yc Yc hXc hYc hYc,
    roundMetric_inner, real_inner_comm,
    dIncl_curv_inner Yc Xc Yc x X
      (ambDeriv_section_mdiffAt Yc Yc x) (ambDeriv_section_mdiffAt Yc Xc x),
    hXcx, hYcx]
  simp only [roundInner_apply, roundMetric_inner,
    real_inner_comm (dIncl (n := n) x Y) (dIncl (n := n) x X)]
  ring

omit [NeZero n] in
/-- **The round metric has constant positive sectional curvature (`c = 1`).**  This is precisely the
unfolding of `ConstPosSecMetric roundMetric` (defined in the Hamilton space-form file, which cannot be
imported here): `∃ c > 0, ∀ x X Y, Rm04(X,Y,Y,X) = c·(g(X,X)g(Y,Y) − g(X,Y)²)`.  It is therefore usable
directly wherever `ConstPosSecMetric roundMetric` is expected (definitional equality), feeding the
spherical-space-form quotient descent. -/
theorem roundMetric_constPosSec :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x),
      metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Y X
        = c * ((roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x Y Y
            - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x X Y) :=
  ⟨1, one_pos, fun x X Y => by rw [one_mul]; exact roundMetric_sec_value x X Y⟩

private instance sphereModel_neZero :
    NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

/-- The round metric has the curvature-one Riemann-operator formula. -/
theorem round_riemann_one (x : sphere (0 : E) 1)
    (X Y Z : TangentSpace (𝓡 n) x) :
    riemannOp (LeviCivita (I := 𝓡 n) (roundMetric (E := E) (n := n))) x X Y Z =
      (roundMetric (E := E) (n := n)).inner x Y Z • X -
        (roundMetric (E := E) (n := n)).inner x X Z • Y := by
  haveI : IsManifold (𝓡 n) 1 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) 2 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) 3 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have hRm :
      ∀ A B C D : TangentSpace (𝓡 n) x,
        metricRm04StdAt (roundMetric (E := E) (n := n)) x A B C D =
          1 * ((roundMetric (E := E) (n := n)).inner x B C *
              (roundMetric (E := E) (n := n)).inner x A D -
            (roundMetric (E := E) (n := n)).inner x A C *
              (roundMetric (E := E) (n := n)).inner x B D) := by
    exact metricRm_of_sec (I := 𝓡 n)
      (M := sphere (0 : E) 1) (roundMetric (E := E) (n := n)) x 1
        (fun A B => by
          simpa only [one_mul] using roundMetric_sec_value (E := E) (n := n) x A B)
  simpa only [one_smul] using
    riemannOp_of_rm (I := 𝓡 n)
      (M := sphere (0 : E) 1) (roundMetric (E := E) (n := n)) x 1 hRm X Y Z

end Geometry
end DifferentialGeometry
