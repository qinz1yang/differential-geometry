import DifferentialGeometry.Geometry.Curvature.RoundCylinderRicciGap
import DifferentialGeometry.Geometry.Curvature.LeastRicciDirection
import DifferentialGeometry.Geometry.Metric.AxisOperatorPerturbation
import DifferentialGeometry.Geometry.Metric.NormalizedAxisPerturbation

open DifferentialGeometry.SmoothRiemannianMetric
  (abs_metric_inner_le_sqrt_metric_quadratic)

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

set_option backward.isDefEq.respectTransparency false in
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
  let e : TangentSpace IC x := (Real.sqrt (g.inner x v v))⁻¹ • v
  obtain ⟨heunit, _, heclose⟩ :=
    normalized_axis_for_perturbed_metric g gRef x ε hεhalf (hsmall 0 (by norm_num)) v hv
  have hactual :=
    (ricciSharp_roundCylinder_normalized_axis_bound g x ε hεhalf hsmall).2
  obtain ⟨μ, w, hw, heig, hmin, hμ, _, hdist, hspace⟩ :=
    exists_least_ricci_direction_of_axis_error g x e heunit (1 / 2) (5772 * ε)
      (by norm_num) (by linarith) hactual
  have hdist' : Real.sqrt (g.inner x (w - e) (w - e)) ≤ 46176 * ε := by
    exact hdist.trans_eq (by ring)
  have hrefdist : Real.sqrt (gRef.inner x (w - e) (w - e)) ≤ 92352 * ε := by
    have hlen := (sqrt_inner_comparison_of_metric_difference g gRef x ε (by linarith)
      (hsmall 0 (by norm_num)) (w - e)).1
    have hhalf : 1 / 2 ≤ Real.sqrt (1 - ε) :=
      (Real.le_sqrt (by norm_num) (by linarith only [hεhalf])).mpr
        (by nlinarith only [hεhalf])
    have hb := mul_le_mul_of_nonneg_right hhalf
      (Real.sqrt_nonneg (gRef.inner x (w - e) (w - e)))
    nlinarith only [hlen, hb, hdist']
  have hclose : Real.sqrt (gRef.inner x (w - v) (w - v)) ≤ 92354 * ε := by
    let a : TangentSpace IC x := w - e
    let b : TangentSpace IC x := e - v
    have ht := sqrt_inner_add_le gRef x a b
    dsimp only [a, b] at ht
    rw [sub_add_sub_cancel] at ht
    linarith only [ht, hrefdist, heclose]
  have hpos : 0 < gRef.inner x v w := by
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic gRef x v (w - v)
    have hinner : gRef.inner x v (w - v) = gRef.inner x v w - 1 := by
      rw [map_sub, hv]
    rw [hinner, hv, Real.sqrt_one, one_mul] at hcs
    have hcs' : |gRef.inner x v w - 1| ≤ 92354 * ε := hcs.trans hclose
    have hl := (abs_le.mp hcs').1
    linarith only [hl, hε]
  refine ⟨μ, w, hw, heig, hmin, hμ, hspace, ?_, hclose⟩
  exact (cylinderMetric_axis_inner gS x w) ▸ hpos

end DifferentialGeometry.Geometry.Curvature
