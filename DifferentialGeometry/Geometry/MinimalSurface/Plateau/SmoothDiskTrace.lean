import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Mathlib.Analysis.Complex.RealDeriv



noncomputable section

open Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


theorem DiskSmoothUpToBoundary.interior {u : C(closedDisk, M)}
    (h : DiskSmoothUpToBoundary (E := E) u) : DiskSmoothInterior (E := E) u :=
  h.mono Metric.ball_subset_closedBall


theorem diskBoundary_lift_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => (diskBoundary (t : loopCircle) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) := by
    have hreal : ContDiff ℝ ∞ (fun t : ℝ => (2 * Real.pi * t : ℝ)) := by fun_prop
    have hcomplex := Complex.ofRealCLM.contDiff.comp hreal
    exact Complex.contDiff_exp.comp (hcomplex.mul contDiff_const)
  exact h.contMDiff.congr (fun t => diskBoundary_coe t)



theorem DiskSmoothUpToBoundary.trace {u : C(closedDisk, M)}
    (h : DiskSmoothUpToBoundary (E := E) u) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => diskTrace u (t : loopCircle)) := by
  have hb := diskBoundary_lift_contMDiff
  have hc := h.comp_contMDiff hb (fun t => (diskBoundary (t : loopCircle)).property)
  apply hc.congr
  intro t
  exact (diskExtension_coe u (diskBoundary (t : loopCircle))).symm

end DifferentialGeometry.Geometry
