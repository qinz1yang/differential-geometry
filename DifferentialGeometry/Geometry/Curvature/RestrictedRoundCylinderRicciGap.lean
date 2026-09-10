import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinder
import DifferentialGeometry.Geometry.Metric.RestrictedCylinderAxis
import DifferentialGeometry.Geometry.Metric.AxisOperatorPerturbation
import DifferentialGeometry.Geometry.Metric.NormalizedAxisPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciSharp_restricted_roundCylinder_normalized_axis_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U)
    (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε) :
    let e : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x :=
      (Real.sqrt (g.inner x (restrictedCylinderAxis U x) (restrictedCylinderAxis U x)))⁻¹ • restrictedCylinderAxis U x
    g.inner x e e = 1 ∧ ∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
      let d := ricciSharp g x z - (1 / 2 : ℝ) • (z - (g.inner x e z) • e)
      Real.sqrt (g.inner x d d) ≤ 5772 * ε * Real.sqrt (g.inner x z z) := by
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let v : TangentSpace IC x := restrictedCylinderAxis U x
  have hv : gRef.inner x v v = 1 := restrictedCylinderAxis_unit gS U x
  have hmodel (z : TangentSpace IC x) :
      ricciSharp gRef x z = (1 / 2 : ℝ) • (z - (gRef.inner x v z) • v) := by
    have haxis : gRef.inner x v z = z.2 := by
      change (cylinderMetric gS).inner (x : Metric.sphere (0 : E) 1 × ℝ)
        (cylinderAxis (x : Metric.sphere (0 : E) 1 × ℝ))
        (show TangentSpace IC (x : Metric.sphere (0 : E) 1 × ℝ) from z) = z.2
      rw [cylinderMetric_inner]
      change gS.inner (x : Metric.sphere (0 : E) 1 × ℝ).1 0 z.1 + (1 : ℝ) * z.2 = z.2
      rw [map_zero]
      change (0 : ℝ) + 1 * z.2 = z.2
      ring
    rw [haxis]
    refine (ricciSharp_restricted_roundCylinder (E := E) (n := 2) U x z).trans ?_
    apply Prod.ext
    · change (((2 : ℝ) - 1) / 2) • z.1 = (1 / 2 : ℝ) •
        (z.1 - z.2 • (0 : EuclideanSpace ℝ (Fin 2)))
      norm_num
    · change (0 : ℝ) = (1 / 2 : ℝ) * (z.2 - z.2 * 1)
      ring
  have hreference (z : TangentSpace IC x) :
      let d := ricciSharp g x z - (1 / 2 : ℝ) • (z - (gRef.inner x v z) • v)
      Real.sqrt (gRef.inner x d d) ≤ 1441 * ε * Real.sqrt (gRef.inner x z z) := by
    dsimp only
    rw [← hmodel z]
    exact ricciSharp_restricted_roundCylinder_difference_bound U g x ε hε hsmall z
  obtain ⟨heunit, heproj, _⟩ :=
    normalized_axis_for_perturbed_metric g gRef x ε hε (hsmall 0 (by norm_num)) v hv
  refine ⟨heunit, ?_⟩
  intro z
  dsimp only
  rw [heproj]
  have h := axis_operator_error_for_perturbed_metric g gRef x ε (1441 * ε) (1 / 2)
    hε (hsmall 0 (by norm_num)) v hv (ricciSharp g x).toLinearMap hreference z
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  convert h using 1 <;> first | rfl | ring

end DifferentialGeometry.Geometry.Curvature
