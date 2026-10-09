import DifferentialGeometry.Topology.LoopSpace.RegularTopology



noncomputable section

open Function ContinuousMap Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace V N]


def regularLoopPostcompose (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) 1 f)
    (γ : regularLoop E M) : regularLoop V N :=
  ⟨(⟨f, hf.continuous⟩ : C(M, N)).comp γ.val, hf.comp γ.property⟩

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



theorem continuous_regularLoopPostcompose (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (a : N → G) (ha : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, G) 1 a)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) 1 f) :
    Continuous[regularLoopTopology e (he.of_le (by exact_mod_cast le_top)),
      regularLoopTopology a ha] (regularLoopPostcompose f hf) := by
  have h := continuous_induced_rng.mp
    (continuous_regularLoopTopology_change e he hemb hi (a ∘ f) (ha.comp hf))
  apply continuous_induced_rng.mpr
  exact h

end DifferentialGeometry.Topology
