import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.Geometry.Manifold.VectorBundle.Basic



noncomputable section

open Set Function Bundle Manifold Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem contDiffAt_chartRepAt_of_section
    {γ : ℝ → M} {V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)} {t : ℝ} {n : WithTop ℕ∞}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) n
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    ContDiffAt ℝ n (chartRepAt γ V t) t := by
  have hs := contMDiffAt_totalSpace.mp hV
  have hb : γ t ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)
  have heq : chartRepAt γ V t =ᶠ[𝓝 t]
      (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)
        (TotalSpace.mk' E (γ s) (V s))).2) := by
    filter_upwards [hs.1.continuousAt
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).open_baseSet.mem_nhds hb)] with s hmem
    rw [chartRepAt_apply,
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt_apply (R := ℝ),
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).coe_linearMapAt_of_mem hmem]
  exact hs.2.contDiffAt.congr_of_eventuallyEq heq

end DifferentialGeometry.Geometry
