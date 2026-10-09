/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.UniversalCover.Flat
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
noncomputable section

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp

theorem torus_rm04_eq_zero (C : HyperbolicCusp) (p : Torus)
    (X Y Z W : TangentSpace torusModel p) :
    metricRm04StandardAt C.torusMetric p X Y Z W = 0 := by
  let B := fun X Y Z W : TangentSpace torusModel p =>
    metricRm04StandardAt C.torusMetric p X Y Z W
  have hB : IsAlgCurvForm B :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule C.torusMetric p)
  have hdiag (U V : TangentSpace torusModel p) : B U V U V = 0 := by
    calc
      B U V U V = -B U V V U := hB.anti_last U V U V
      _ = 0 := by
        change -metricRm04StandardAt C.torusMetric p U V V U = 0
        rw [C.torus_flat, neg_zero]
  exact hB.zero_of_diag hdiag X Y Z W

theorem torus_riemannOp_eq_zero (C : HyperbolicCusp) (p : Torus)
    (X Y Z : TangentSpace torusModel p) :
    riemannOp (LeviCivita C.torusMetric) p X Y Z = 0 := by
  let W := riemannOp (LeviCivita C.torusMetric) p X Y Z
  have hz := C.torus_rm04_eq_zero p X Y Z W
  rw [CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp] at hz
  change C.torusMetric.inner p W W = 0 at hz
  by_contra hW
  exact (ne_of_gt (C.torusMetric.pos p W hW)) hz

theorem torus_hasEuclideanUniversalCover (C : HyperbolicCusp) :
    Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover C.torusMetric := by
  let : NeZero (Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) := ⟨by simp⟩
  exact Riemannian.Topology.UniversalCover.hasEuclideanUniversalCover_of_riemannOp_eq_zero
    C.torusMetric (RiemannianMetricComplete.of_compact C.torusMetric)
    C.torus_riemannOp_eq_zero

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp
