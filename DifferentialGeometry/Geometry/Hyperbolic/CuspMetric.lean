/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Curvature.Product

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

def HyperbolicCusp.ofFlatMetric (q : SmoothRiemannianMetric torusModel Torus)
    (hq : ∀ (p : Torus) (v w : TangentSpace torusModel p),
      metricRm04StandardAt q p v w w v = 0) : HyperbolicCusp where
  torusMetric := q
  torus_flat := hq
  metric := q.exponentialWarpedEnd (1 / 2)
  metric_formula p v w := by
    rw [SmoothRiemannianMetric.exponentialWarpedEnd_inner]
    norm_num

@[simp] theorem HyperbolicCusp.ofFlatMetric_torusMetric
    (q : SmoothRiemannianMetric torusModel Torus)
    (hq : ∀ (p : Torus) (v w : TangentSpace torusModel p),
      metricRm04StandardAt q p v w w v = 0) :
    (HyperbolicCusp.ofFlatMetric q hq).torusMetric = q := rfl

theorem HyperbolicCusp.metric_eq_exponentialWarpedEnd (H : HyperbolicCusp) :
    H.metric = H.torusMetric.exponentialWarpedEnd (1 / 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [H.metric_formula, SmoothRiemannianMetric.exponentialWarpedEnd_inner]
  norm_num

private theorem circle_product_flat
    (g h : SmoothRiemannianMetric (𝓡 1) Circle) (p : Torus)
    (v w : TangentSpace torusModel p) :
    metricRm04StandardAt (g.prod h) p v w w v = 0 := by
  change metricRm04At (g.prod h) p (vec4 v w w v) = 0
  rw [metricRm04At_productMetric_apply,
    metricRm04At_eq_zero_of_finrank_le_one g (by simp),
    metricRm04At_eq_zero_of_finrank_le_one h (by simp)]
  change (0 : ℝ) + 0 = 0
  simp

def HyperbolicCusp.ofCircleMetrics
    (g h : SmoothRiemannianMetric (𝓡 1) Circle) : HyperbolicCusp :=
  HyperbolicCusp.ofFlatMetric (g.prod h) (circle_product_flat g h)

@[simp] theorem HyperbolicCusp.ofCircleMetrics_torusMetric
    (g h : SmoothRiemannianMetric (𝓡 1) Circle) :
    (HyperbolicCusp.ofCircleMetrics g h).torusMetric = g.prod h := rfl

def standardCusp : HyperbolicCusp :=
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
  HyperbolicCusp.ofCircleMetrics
    (DifferentialGeometry.Geometry.roundMetric (E := ℂ) (n := 1))
    (DifferentialGeometry.Geometry.roundMetric (E := ℂ) (n := 1))

end DifferentialGeometry.Geometry.Hyperbolic
