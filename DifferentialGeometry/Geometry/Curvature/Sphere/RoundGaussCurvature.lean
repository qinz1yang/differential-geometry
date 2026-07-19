import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.Riemann.ConstantCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry
open Metric
open scoped Manifold ContDiff

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : NeZero (Module.finrank Real (EuclideanSpace Real (Fin 2))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩

theorem roundMetric_gaussCurvature_eq_one
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x = 1 := by
  set g := roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) with hg
  have hsec : ∀ (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (v w : TangentSpace (𝓡 2) p),
      Riemannian.sectionalCurvatureDenominator (I := 𝓡 2) g p v w ≠ 0 →
        Riemannian.sectionalCurvature (I := 𝓡 2) g p v w = 1 := by
    intro p v w hden
    have hrsv := roundMetric_sec_value (E := EuclideanSpace Real (Fin 3)) (n := 2) p v w
    rw [← hg] at hrsv
    have hnum : Riemannian.sectionalCurvatureNumerator (I := 𝓡 2) g p v w
        = Riemannian.sectionalCurvatureDenominator (I := 𝓡 2) g p v w := by
      rw [← Riemannian.metricRm04Std_eq_sectionalNumerator (I := 𝓡 2) g p v w, hrsv,
          Riemannian.sectionalCurvatureDenominator_def]
      ring
    rw [Riemannian.sectionalCurvature_def, hnum]
    exact div_self hden
  have hE : IsEinsteinMetric (I := 𝓡 2) g 1 := by
    have h := Riemannian.einstein_of_constant_sectionalCurvature (I := 𝓡 2) g 1 hsec
    rwa [show (1 : Real) * ((Module.finrank Real (EuclideanSpace Real (Fin 2)) : Real) - 1) = 1 by
      rw [finrank_euclideanSpace_fin]; norm_num] at h
  haveI hntE : Nontrivial (EuclideanSpace Real (Fin 2)) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; norm_num)
  haveI : Nontrivial (TangentSpace (𝓡 2) x) := hntE
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : TangentSpace (𝓡 2) x)
  have hpos : 0 < g.inner x v₀ v₀ := g.pos x v₀ hv₀
  have hne : g.inner x v₀ v₀ ≠ 0 := ne_of_gt hpos
  have hRicci : metricRicciAt (I := 𝓡 2) g x (vec2 (I := 𝓡 2) v₀ v₀)
      = gaussCurvature (I := 𝓡 2) g x * g.inner x v₀ v₀ :=
    ricci_eq_gaussCurvature_smul_metric_twoDim (I := 𝓡 2) finrank_euclideanSpace_fin g x v₀ v₀
  have hEinstein : metricRicciAt (I := 𝓡 2) g x (vec2 (I := 𝓡 2) v₀ v₀)
      = 1 * g.inner x v₀ v₀ := hE x v₀ v₀
  have hfin : gaussCurvature (I := 𝓡 2) g x * g.inner x v₀ v₀
      = 1 * g.inner x v₀ v₀ := by rw [← hRicci, hEinstein]
  exact mul_right_cancel₀ hne hfin

end DifferentialGeometry.Integral.Connection
