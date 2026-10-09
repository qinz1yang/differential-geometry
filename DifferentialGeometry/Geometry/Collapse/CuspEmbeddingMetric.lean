import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Tensor0SBundle GC.Endpoint Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- Zeroth cusp error bounds the actual differential in the original reference metric. -/
theorem CuspEmbedding.inner_mfderiv_self_le
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X)
    (p : CuspHalfSpace) (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v) ≤
        (1 + δ) * e.cusp.metric.inner p v v := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis e.cusp.metric p
  have herr := e.metric_error 0 (Nat.zero_le K) p hp
  change Real.sqrt (normSq0S e.cusp.metric p 2
    (cuspMetricError g e.cusp e.toFun p)) ≤ δ at herr
  have hbound := abs_apply_le_sqrt_normSq0S e.cusp.metric p 2 basis hON
    (cuspMetricError g e.cusp e.toFun p) (fun _ => v)
  have heval : cuspMetricError g e.cusp e.toFun p (fun _ => v) =
      g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) -
          e.cusp.metric.inner p v v := rfl
  have hprod : (∏ _a : Fin 2, Real.sqrt (e.cusp.metric.inner p v v)) =
      e.cusp.metric.inner p v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)]
  rw [heval, hprod] at hbound
  have habs := hbound.trans
    (mul_le_mul_of_nonneg_right herr (metric_inner_self_nonneg _ _ _))
  have hu := (abs_le.mp habs).2
  linarith

theorem CuspEmbedding.height_component_sq_le
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    (p : CuspHalfSpace) (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    (v.2 0) ^ 2 ≤ (1 - δ)⁻¹ *
      g.inner (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis e.cusp.metric p
  have herr := e.metric_error 0 (Nat.zero_le K) p hp
  change Real.sqrt (normSq0S e.cusp.metric p 2
    (cuspMetricError g e.cusp e.toFun p)) ≤ δ at herr
  have hbound := abs_apply_le_sqrt_normSq0S e.cusp.metric p 2 basis hON
    (cuspMetricError g e.cusp e.toFun p) (fun _ => v)
  have heval : cuspMetricError g e.cusp e.toFun p (fun _ => v) =
      g.inner (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) -
      e.cusp.metric.inner p v v := by
    rfl
  have hprod : (∏ _a : Fin 2, Real.sqrt (e.cusp.metric.inner p v v)) =
      e.cusp.metric.inner p v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)]
  rw [heval, hprod] at hbound
  have habs := hbound.trans
    (mul_le_mul_of_nonneg_right herr (metric_inner_self_nonneg _ _ _))
  have hlower : (1 - δ) * e.cusp.metric.inner p v v ≤
      g.inner (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
    have h := (abs_le.mp habs).1
    linarith
  have hheight : (v.2 0) ^ 2 ≤ e.cusp.metric.inner p v v := by
    rw [e.cusp.metric_formula]
    have htorus := mul_nonneg (Real.exp_pos (-p.2.val 0)).le
      (metric_inner_self_nonneg e.cusp.torusMetric p.1 v.1)
    nlinarith
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ
  have hscaled := (mul_le_mul_of_nonneg_left hheight hpos.le).trans hlower
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  simpa only [mul_comm] using hscaled

end DifferentialGeometry.Geometry.Collapse
