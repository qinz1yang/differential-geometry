import DifferentialGeometry.Geometry.Hyperbolic.Cusp

/-!
# Frozen-warp comparison on the cusp model (foundation F-f, BCP02.b at the metric level)

On the model cusp `H = dz² + e^{-z} q` (`HyperbolicCusp`), at a point of height `z` with
`|z - z₀| ≤ a` the metric is within the factor `e^{±a}` of the frozen product metric
`dz² + e^{-z₀} q` (blueprint 207B, BCP02.b, `B:8234–8321`): `HyperbolicCusp.inner_le_exp_frozen`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- F-f.M: at height `z` with `|z - z₀| ≤ a` the cusp metric lies between `e^{-a}` and `e^{a}`
times the frozen product metric `dz² + e^{-z₀} q`. -/
theorem HyperbolicCusp.inner_le_exp_frozen (Hc : HyperbolicCusp) {p : CuspHalfSpace}
    {z₀ a : ℝ} (hz : |p.2.val 0 - z₀| ≤ a) (v : TangentSpace halfCollarModel p) :
    Real.exp (-a) * (v.2 0 ^ 2 + Real.exp (-z₀) * Hc.torusMetric.inner p.1 v.1 v.1) ≤
        Hc.metric.inner p v v ∧
      Hc.metric.inner p v v ≤
        Real.exp a * (v.2 0 ^ 2 + Real.exp (-z₀) * Hc.torusMetric.inner p.1 v.1 v.1) := by
  have hq : 0 ≤ Hc.torusMetric.inner p.1 v.1 v.1 := metric_inner_self_nonneg _ _ _
  have hv : 0 ≤ v.2 0 ^ 2 := sq_nonneg _
  have ha : 0 ≤ a := (abs_nonneg _).trans hz
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hlow : Real.exp (-a) * Real.exp (-z₀) ≤ Real.exp (-p.2.val 0) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hup : Real.exp (-p.2.val 0) ≤ Real.exp a * Real.exp (-z₀) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [Hc.metric_formula]
  constructor
  · have h1 : Real.exp (-a) * v.2 0 ^ 2 ≤ v.2 0 * v.2 0 := by nlinarith
    have h2 : Real.exp (-a) * Real.exp (-z₀) * Hc.torusMetric.inner p.1 v.1 v.1 ≤
        Real.exp (-p.2.val 0) * Hc.torusMetric.inner p.1 v.1 v.1 :=
      mul_le_mul_of_nonneg_right hlow hq
    nlinarith
  · have h1 : v.2 0 * v.2 0 ≤ Real.exp a * v.2 0 ^ 2 := by nlinarith
    have h2 : Real.exp (-p.2.val 0) * Hc.torusMetric.inner p.1 v.1 v.1 ≤
        Real.exp a * Real.exp (-z₀) * Hc.torusMetric.inner p.1 v.1 v.1 :=
      mul_le_mul_of_nonneg_right hup hq
    nlinarith

end DifferentialGeometry.Geometry.Collapse
