import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

open Set Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace Metric

theorem exists_subsequence_tendstoUniformly_of_lipschitz
    {T X : Type*} [MetricSpace T] [CompactSpace T] [MetricSpace X]
    {K : Set X} (hK : IsCompact K) {C : ℝ≥0} (f : ℕ → T → X)
    (hf : ∀ n, LipschitzWith C (f n)) (hmem : ∀ n t, f n t ∈ K) :
    ∃ (φ : ℕ → ℕ) (g : T → X), StrictMono φ ∧ LipschitzWith C g ∧
      (∀ t, g t ∈ K) ∧ TendstoUniformly (fun n => f (φ n)) g atTop := by
  let F (n : ℕ) : T →ᵇ X :=
    BoundedContinuousFunction.mkOfCompact ⟨f n, (hf n).continuous⟩
  let A := range F
  have hEA : Equicontinuous (fun g : A => ((g : T →ᵇ X) : T → X)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    intro g
    obtain ⟨n, hn⟩ := g.property
    rw [← hn]
    exact hf n
  have hcompact : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli K hK A
    · intro g t hg
      obtain ⟨n, rfl⟩ := hg
      exact hmem n t
    · exact hEA
  obtain ⟨g, _, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have heval (t : T) : Tendsto (fun n => f (φ n) t) atTop (𝓝 (g t)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto g).comp hlim
  refine ⟨φ, g, hφ, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    exact le_of_tendsto ((heval s).dist (heval t))
      (Eventually.of_forall (fun n => (hf (φ n)).dist_le_mul s t))
  · intro t
    exact hK.isClosed.mem_of_tendsto (heval t) (Eventually.of_forall (fun n => hmem (φ n) t))
  · exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

end Metric
