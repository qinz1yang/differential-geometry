import DifferentialGeometry.Geometry.Curvature.Conformal
import DifferentialGeometry.Geometry.Curvature.Cylinder.ProductMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Operator.Cylinder
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
local notation "gC" => (roundCylinderMetric (E := E3) (n := 2))
local notation "gS" => (roundMetric (E := E3) (n := 2))
private abbrev gS2 := scaleMetric 2 (by norm_num) gS

private theorem axis_inner (q : S2 × ℝ) (v : TangentSpace IC q) :
    (gC).inner q (cylinderAxis q) v = v.2 := by
  erw [roundCylinderMetric, cylinderMetric_inner]
  change gS2.inner q.1 0 v.1 + (1 : ℝ) * v.2 = v.2
  erw [map_zero]
  change 0 + 1 * v.2 = v.2
  ring

private theorem metricRm04_tangential_base (q : S2 × ℝ)
    (u v : TangentSpace IC q) :
    metricRm04StandardAt gC q u v v u =
      metricRm04StandardAt gS2 q.1 u.1 v.1 v.1 u.1 := by
  erw [rm04_eq_inner_riem, roundCylinderMetric, inner_riemannOp_cylinderMetric,
    rm04_eq_inner_riem]

private theorem roundCylinder_inner_tangential (q : S2 × ℝ)
    (u v : TangentSpace IC q) (hvz : v.2 = 0) :
    (gC).inner q u v = 2 * (gS).inner q.1 u.1 v.1 := by
  erw [roundCylinderMetric, cylinderMetric_inner, hvz, mul_zero, add_zero, scaleMetric_inner]

private theorem metricRm04_tangential (q : S2 × ℝ) (u v : TangentSpace IC q)
    (huz : u.2 = 0) (hvz : v.2 = 0) :
    metricRm04StandardAt gC q u v v u =
      (1 / 2 : ℝ) * ((gC).inner q u u * (gC).inner q v v - ((gC).inner q u v) ^ 2) := by
  calc
    metricRm04StandardAt gC q u v v u =
        metricRm04StandardAt gS2 q.1 u.1 v.1 v.1 u.1 :=
      metricRm04_tangential_base q u v
    _ = 2 * metricRm04StandardAt gS q.1 u.1 v.1 v.1 u.1 :=
      metricRmStandard_scale 2 (by norm_num) gS q.1 u.1 v.1 v.1 u.1
    _ = 2 * ((gS).inner q.1 u.1 u.1 * (gS).inner q.1 v.1 v.1 -
        (gS).inner q.1 u.1 v.1 * (gS).inner q.1 u.1 v.1) := by
      rw [roundMetric_sec_value (E := E3) (n := 2) q.1 u.1 v.1]
    _ = (1 / 2 : ℝ) *
        ((gC).inner q u u * (gC).inner q v v - ((gC).inner q u v) ^ 2) := by
      rw [roundCylinder_inner_tangential q u u huz,
        roundCylinder_inner_tangential q v v hvz,
        roundCylinder_inner_tangential q u v hvz]
      ring

theorem sectionalCurvature_roundCylinder_radial (q : S2 × ℝ) (v : TangentSpace IC q)
    (hv : (gC).inner q v v = 1) (hvz : v.2 = 0) :
    sectionalCurvature gC q (cylinderAxis q) v = 0 := by
  have haxis : (gC).inner q (cylinderAxis q) (cylinderAxis q) = 1 :=
    cylinderMetric_axis_unit gS2 q
  have horth : (gC).inner q (cylinderAxis q) v = 0 := (axis_inner q v).trans hvz
  erw [sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal _ _ _ _ haxis hv horth,
    rm04_eq_inner_riem, roundCylinderMetric, riemannOp_cylinderAxis_left, map_zero]

theorem sectionalCurvature_roundCylinder_tangential (q : S2 × ℝ) (u v : TangentSpace IC q)
    (hu : (gC).inner q u u = 1) (hv : (gC).inner q v v = 1) (huv : (gC).inner q u v = 0)
    (huz : u.2 = 0) (hvz : v.2 = 0) :
    sectionalCurvature gC q u v = 1 / 2 := by
  erw [sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal _ _ _ _ hu hv huv,
    metricRm04_tangential q u v huz hvz, hu, hv, huv]
  norm_num

private theorem differential_comp_height {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (q : S2 × ℝ) (v : TangentSpace IC q) :
    mvfderiv IC (fun y : S2 × ℝ => f y.2) q v = deriv f q.2 * v.2 := by
  erw [← gradFun_metricDual_mvfderiv gC, gradFun_comp_height_cylinderMetric gS2 hf,
    map_smul, smul_apply, smul_eq_mul, axis_inner]

theorem sectionalCurvature_conformal_roundCylinder_radial {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (q : S2 × ℝ) (v : TangentSpace IC q)
    (hv : (gC).inner q v v = 1) (hvz : v.2 = 0) :
    sectionalCurvature
      (conformalMetricOfContDiff gC (fun y : S2 × ℝ => f y.2) (hf.contMDiff.comp contMDiff_snd)) q
      (Real.exp (-f q.2) • cylinderAxis q) (Real.exp (-f q.2) • v) =
        -Real.exp (-(2 * f q.2)) * deriv (deriv f) q.2 := by
  have haxis : (gC).inner q (cylinderAxis q) (cylinderAxis q) = 1 :=
    cylinderMetric_axis_unit gS2 q
  have horth : (gC).inner q (cylinderAxis q) v = 0 := (axis_inner q v).trans hvz
  erw [sectionalCurvature_conformalMetric_of_unit_orthogonal _ _ _ _ _ _ haxis hv horth,
    sectionalCurvature_roundCylinder_radial q v hv hvz,
    hessFun_comp_height_cylinderMetric gS2 hf, hessFun_comp_height_cylinderMetric gS2 hf,
    differential_comp_height hf, differential_comp_height hf,
    inner_gradFun_comp_height_cylinderMetric gS2 hf, hvz]
  change Real.exp (-(2 * f q.2)) *
    (0 - deriv (deriv f) q.2 * 1 * 1 - deriv (deriv f) q.2 * 0 * 0 +
      (deriv f q.2 * 1) ^ 2 + (deriv f q.2 * 0) ^ 2 - (deriv f q.2) ^ 2) = _
  ring

theorem sectionalCurvature_conformal_roundCylinder_tangential {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (q : S2 × ℝ) (u v : TangentSpace IC q)
    (hu : (gC).inner q u u = 1) (hv : (gC).inner q v v = 1) (huv : (gC).inner q u v = 0)
    (huz : u.2 = 0) (hvz : v.2 = 0) :
    sectionalCurvature
      (conformalMetricOfContDiff gC (fun y : S2 × ℝ => f y.2) (hf.contMDiff.comp contMDiff_snd)) q
      (Real.exp (-f q.2) • u) (Real.exp (-f q.2) • v) =
        Real.exp (-(2 * f q.2)) * (1 / 2 - (deriv f q.2) ^ 2) := by
  erw [sectionalCurvature_conformalMetric_of_unit_orthogonal _ _ _ _ _ _ hu hv huv,
    sectionalCurvature_roundCylinder_tangential q u v hu hv huv huz hvz,
    hessFun_comp_height_cylinderMetric gS2 hf, hessFun_comp_height_cylinderMetric gS2 hf,
    differential_comp_height hf, differential_comp_height hf,
    inner_gradFun_comp_height_cylinderMetric gS2 hf, huz, hvz]
  ring

end DifferentialGeometry.Geometry.Curvature
