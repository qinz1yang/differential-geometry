import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallBoundaryGeometry
import DifferentialGeometry.Geometry.Metric.Distance.CompactImage

/-!
# The unconditional boundary instance, level 1 (lane BDRY-INST, review 54 §4)

Review 54 §4 asks for an instance of `NearlyCuspidalBoundary` that does not come from the
"no threshold" counterfactual. The model of the review, `W = T² × [0, L]` with
`g_a = dt² + a² h(t) g_T`, `h = e^{-t}` near `0` and `h = e^{-(L - t)}` near `L`, is the double
cusp of the X119 inhabitants (`L = 240`): the carrier `annulusCircleCarrier`, the metric
`doubleCuspMetric a ha`, the two collars `doubleCuspEmbedding` with metric error exactly zero.

* `exists_standardCuspTorus_diameter_INST`: the flat reference torus has finite diameter;
* `exists_doubleCuspNearlyCuspidalBoundary_INST`: for every `δ > 0` a scale `0 < a ≤ 1` and an
  actual `NearlyCuspidalBoundary` of the double cusp at ratio `δ`, with two boundary components,
  the reference cusps `doubleCuspReference a ha` and identically vanishing metric error.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection
open GC.Seifert GC.GraphManifold GC.Endpoint Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The flat reference torus `standardCuspTorusMetric` has finite diameter. -/
theorem exists_standardCuspTorus_diameter_INST :
    ∃ D : ℝ, 0 < D ∧ ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hd⟩ := exists_uniform_riemannianEDistOf_bound_of_compact_preconnected
    standardCuspTorusMetric (ContinuousMap.id Torus) (1, 1)
  refine ⟨D + D + 1, by linarith, fun x y => ?_⟩
  have hy : riemannianEDistOf standardCuspTorusMetric (1, 1) y ≤ ENNReal.ofReal D := by
    rw [riemannianEDistOf_comm]
    exact hd y
  refine (riemannianEDistOf_triangle standardCuspTorusMetric x (1, 1) y).trans
    ((add_le_add (hd x) hy).trans ?_)
  rw [← ENNReal.ofReal_add hD hD]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A scale `0 < a ≤ 1` with `a * D ≤ δ`. -/
theorem exists_doubleCuspScale_INST {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a * D ≤ δ := by
  refine ⟨min 1 (δ / D), lt_min one_pos (div_pos hδ hD), min_le_left _ _, ?_⟩
  calc min 1 (δ / D) * D ≤ δ / D * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
    _ = δ := div_mul_cancel₀ δ hD.ne'

/-- **Level 1 (review 54 §4).** For every `δ > 0` the double cusp `T² × [0, 240]` at a small torus
scale `a` carries an actual `NearlyCuspidalBoundary` at ratio `δ`: two boundary components (the two
ends), the reference cusps `dz² + e^{-z}(a² g_T)` and metric error identically zero on the depth
`100` collars. No counterfactual and no premise beyond `δ > 0`. -/
theorem exists_doubleCuspNearlyCuspidalBoundary_INST (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℝ, ∃ ha : 0 < a, a ≤ 1 ∧
      ∃ B : NearlyCuspidalBoundary annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K δ,
        ∃ hc : B.count = 2, (∀ i, B.component i = doubleCuspBoundary.{u} (Fin.cast hc i)) ∧
        (∀ i, (B.collar i).cusp = doubleCuspReference a ha) ∧
        ∀ i (k : ℕ) (p : CuspHalfSpace), p ∈ cuspDomain →
          iteratedMetricCovariantDerivative (B.collar i).cusp.metric 2
            (cuspMetricError (W := annulusCircleCarrier.{u}) (doubleCuspMetric.{u} a ha)
              (B.collar i).cusp (B.collar i).toFun) k p = 0 := by
  obtain ⟨D, hD, hdiam⟩ := exists_standardCuspTorus_diameter_INST
  obtain ⟨a, ha, ha1, haD⟩ := exists_doubleCuspScale_INST hD hδ
  refine ⟨a, ha, ha1, doubleCuspNearlyCuspidalBoundaryAt.{u} a ha D hD.le hdiam K δ haD, rfl,
    fun _ => rfl, fun _ => rfl, fun i k p hp => ?_⟩
  exact doubleCuspMetricError_iterated_zero.{u} a ha i k hp

end DifferentialGeometry.Geometry.Collapse
