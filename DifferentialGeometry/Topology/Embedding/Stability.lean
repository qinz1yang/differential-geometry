import DifferentialGeometry.Analysis.Calculus.LipschitzFamily
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Diffeomorph.Perturbation

open scoped Manifold Topology NNReal

namespace Manifold

open Set

theorem eventually_isSmoothEmbedding
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p, x)) := by
  let f : P × M → P × V := fun q => (q.1, e (p₀, q.2))
  have hf : IsSmoothEmbedding (𝓘(ℝ, P).prod I) 𝓘(ℝ, P × V) n f := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, P)) (M := P) (n := n)).prodMap hf₀
  have hK : IsCompact (Metric.closedBall p₀ 1 ×ˢ (univ : Set M)) :=
    (isCompact_closedBall p₀ 1).prod isCompact_univ
  obtain ⟨G, hG, hGc, -, hGe⟩ := hf.exists_contDiff_compact_extension
    he hK isOpen_univ (subset_univ _)
  have hlip : ∀ᶠ p in 𝓝 p₀,
      LipschitzWith (1 / 2 : ℝ≥0) (fun y => G (p, y) - G (p₀, y)) :=
    ContDiff.eventually_lipschitzWith_sub_slice
      (hG.of_le (WithTop.coe_le_coe.mpr hn)) hGc p₀ (by norm_num)
  have hnear : Metric.closedBall p₀ 1 ∈ 𝓝 p₀ :=
    Metric.closedBall_mem_nhds p₀ zero_lt_one
  filter_upwards [hlip, hnear] with p hp hpnear
  have hslice : ContDiff ℝ n (fun y => G (p, y) - G (p₀, y)) :=
    (hG.comp (contDiff_const.prodMk contDiff_id)).sub
      (hG.comp (contDiff_const.prodMk contDiff_id))
  let Φ : Diffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) V V n :=
    Diffeomorph.addLipschitz hslice hp (by norm_num)
  have hmap : Φ ∘ (fun x => e (p₀, x)) = fun x => e (p, x) := by
    funext x
    change e (p₀, x) + (G (p, e (p₀, x)) - G (p₀, e (p₀, x))) = e (p, x)
    rw [show G (p, e (p₀, x)) = e (p, x) from
      hGe (x := (p, x)) ⟨hpnear, mem_univ x⟩]
    rw [show G (p₀, e (p₀, x)) = e (p₀, x) from
      hGe (x := (p₀, x)) ⟨Metric.mem_closedBall_self zero_le_one, mem_univ x⟩]
    abel
  exact hmap ▸ hf₀.diffeomorph_comp Φ

end Manifold
