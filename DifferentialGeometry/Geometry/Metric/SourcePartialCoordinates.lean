import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem chartCoord_source_mfderiv {U : V → M} {z : V}
    (hU : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) U z) (p : M)
    (hp : U z ∈ (chartAt E p).source) :
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)).comp
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) U z) =
      fderiv ℝ ((extChartAt 𝓘(ℝ, E) p) ∘ U) z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp,
    ← mfderiv_comp z (mdifferentiableAt_extChartAt hp) hU, mfderiv_eq_fderiv]
  ext v
  rfl

end DifferentialGeometry.Geometry
