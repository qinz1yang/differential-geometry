import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderRicciGap
import DifferentialGeometry.Geometry.Curvature.LeastRicciDirection
import DifferentialGeometry.Geometry.Metric.AxisOperatorPerturbation
import DifferentialGeometry.Geometry.Metric.NormalizedAxisPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

theorem exists_least_ricci_direction_on_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U)
    (x : U) (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε) :
    ∃ (μ : ℝ) (w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
      g.inner x w w = 1 ∧ ricciSharp g x w = μ • w ∧
      (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
        g.inner x z z = 1 → μ ≤ ricciTensor g x z z) ∧
      |μ| ≤ 5772 * ε ∧
      Module.End.eigenspace (ricciSharp g x).toLinearMap μ = Submodule.span ℝ {w} ∧
      0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : U ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x w ∧
      Real.sqrt (((roundCylinderMetric (E := E) (n := 2)).restrictOpen U).inner x
        (w - restrictedCylinderAxis U x) (w - restrictedCylinderAxis U x)) ≤ 92354 * ε := by
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let v : TangentSpace IC x := restrictedCylinderAxis U x
  have hv : gRef.inner x v v = 1 := restrictedCylinderAxis_unit gS U x
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hεhalf : ε ≤ 1 / 2 := by linarith
  let e : TangentSpace IC x := (Real.sqrt (g.inner x v v))⁻¹ • v
  obtain ⟨heunit, _, heclose⟩ :=
    normalized_axis_for_perturbed_metric g gRef x ε hεhalf (hsmall 0 (by norm_num)) v hv
  have hactual := (ricciSharp_restricted_roundCylinder_normalized_axis_bound U g x ε hεhalf hsmall).2
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
  exact (restrictedCylinderAxis_inner gS U x w) ▸ hpos

end Poincare.Geometry.Curvature
