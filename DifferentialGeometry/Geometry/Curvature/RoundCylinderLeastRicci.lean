import DifferentialGeometry.Geometry.Curvature.RoundCylinderPerturbation
import DifferentialGeometry.Geometry.Curvature.LeastRicciDirection
import DifferentialGeometry.Geometry.Metric.AxisOperatorPerturbation
import DifferentialGeometry.Geometry.Metric.NormalizedAxisPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_least_ricci_direction_on_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    (x : Metric.sphere (0 : E) 1 × ℝ) (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g (roundCylinderMetric (E := E) (n := 2))
        (roundCylinderMetric (E := E) (n := 2)) x ≤ ε) :
    ∃ (μ : ℝ) (w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
      g.inner x w w = 1 ∧ ricciSharp g x w = μ • w ∧
      (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
        g.inner x z z = 1 → μ ≤ ricciTensor g x z z) ∧
      |μ| ≤ 5772 * ε ∧
      Module.End.eigenspace (ricciSharp g x).toLinearMap μ = Submodule.span ℝ {w} ∧
      0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) Prod.snd x w ∧
      Real.sqrt ((roundCylinderMetric (E := E) (n := 2)).inner x
        (w - cylinderAxis x) (w - cylinderAxis x)) ≤ 92354 * ε := by
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  let gRef := roundCylinderMetric (E := E) (n := 2)
  let v : TangentSpace IC x := cylinderAxis x
  have hv : gRef.inner x v v = 1 := cylinderMetric_axis_unit gS x
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hεhalf : ε ≤ 1 / 2 := by linarith
  have hmodel (z : TangentSpace IC x) :
      ricciSharp gRef x z = (1 / 2 : ℝ) • (z - (gRef.inner x v z) • v) := by
    have haxis : gRef.inner x v z = z.2 := by
      change (cylinderMetric gS).inner x (cylinderAxis x) z = z.2
      rw [cylinderMetric_inner]
      change gS.inner x.1 0 z.1 + (1 : ℝ) * z.2 = z.2
      rw [map_zero]
      change (0 : ℝ) + 1 * z.2 = z.2
      ring
    rw [haxis]
    refine (ricciSharp_roundCylinder (E := E) (n := 2) x z).trans ?_
    apply Prod.ext
    · change (((2 : ℝ) - 1) / 2) • z.1 = (1 / 2 : ℝ) • (z.1 - z.2 • (0 : EuclideanSpace ℝ (Fin 2)))
      norm_num
    · change (0 : ℝ) = (1 / 2 : ℝ) * (z.2 - z.2 * 1)
      ring
  have hreference (z : TangentSpace IC x) :
      let d := ricciSharp g x z - (1 / 2 : ℝ) • (z - (gRef.inner x v z) • v)
      Real.sqrt (gRef.inner x d d) ≤ 1441 * ε * Real.sqrt (gRef.inner x z z) := by
    dsimp only
    rw [← hmodel z]
    exact ricciSharp_roundCylinder_difference_bound g x ε hεhalf hsmall z
  let e : TangentSpace IC x := (Real.sqrt (g.inner x v v))⁻¹ • v
  obtain ⟨heunit, heproj, heclose⟩ :=
    normalized_axis_for_perturbed_metric g gRef x ε hεhalf (hsmall 0 (by norm_num)) v hv
  have hactual (z : TangentSpace IC x) :
      let d := ricciSharp g x z - (1 / 2 : ℝ) • (z - (g.inner x e z) • e)
      Real.sqrt (g.inner x d d) ≤ 5772 * ε * Real.sqrt (g.inner x z z) := by
    dsimp only
    rw [heproj]
    have h := axis_operator_error_for_perturbed_metric g gRef x ε (1441 * ε) (1 / 2)
      hεhalf (hsmall 0 (by norm_num)) v hv (ricciSharp g x).toLinearMap hreference z
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    convert h using 1 <;> first | rfl | ring
  obtain ⟨μ, w, hw, heig, hmin, hμ, _, hdist, hspace⟩ :=
    exists_least_ricci_direction_of_axis_error g x e heunit (1 / 2) (5772 * ε)
      (by norm_num) (by linarith) hactual
  have hdist' : Real.sqrt (g.inner x (w - e) (w - e)) ≤ 46176 * ε := by
    convert hdist using 1
    ring
  have hrefdist : Real.sqrt (gRef.inner x (w - e) (w - e)) ≤ 92352 * ε := by
    have hlen := (sqrt_inner_comparison_of_metric_difference g gRef x ε (by linarith)
      (hsmall 0 (by norm_num)) (w - e)).1
    have hhalf : 1 / 2 ≤ Real.sqrt (1 - ε) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    have hb := mul_le_mul_of_nonneg_right hhalf
      (Real.sqrt_nonneg (gRef.inner x (w - e) (w - e)))
    nlinarith only [hlen, hb, hdist']
  have hclose : Real.sqrt (gRef.inner x (w - v) (w - v)) ≤ 92354 * ε := by
    have ht := sqrt_inner_add_le gRef x (w - e) (e - v)
    rw [sub_add_sub_cancel] at ht
    change Real.sqrt (gRef.inner x (e - v) (e - v)) ≤ 2 * ε at heclose
    linarith only [ht, hrefdist, heclose]
  have hpos : 0 < gRef.inner x v w := by
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic gRef x v (w - v)
    rw [hv, Real.sqrt_one, one_mul, map_sub, hv] at hcs
    have hl := (abs_le.mp (hcs.trans hclose)).1
    linarith only [hl, hε]
  refine ⟨μ, w, hw, heig, hmin, hμ, hspace, ?_, hclose⟩
  exact (cylinderMetric_axis_inner gS x w) ▸ hpos

end DifferentialGeometry.Geometry.Curvature
