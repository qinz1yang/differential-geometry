import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.CompactConvergence

open Filter
open scoped Topology

namespace ContinuousMap

variable {X F ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_comp_of_tendsto {l : Filter ι} [NeBot l]
    {f g : ι → C(X, F)} {u v : C(X, F)} {q : ℝ → X}
    (hf : Tendsto f l (𝓝 u)) (hg : Tendsto g l (𝓝 v))
    (hd : ∀ᶠ i in l, ∀ x : ℝ, HasDerivAt (fun t => f i (q t)) (g i (q x)) x)
    (x : ℝ) : HasDerivAt (fun t => u (q t)) (v (q x)) x := by
  apply hasDerivAt_of_tendstoUniformly
    ((tendsto_iff_tendstoUniformly.mp hg).comp q) hd
  intro t
  exact (tendsto_iff_tendstoUniformly.mp hf).tendsto_at (q t)

end ContinuousMap
