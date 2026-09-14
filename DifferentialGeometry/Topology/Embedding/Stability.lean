import DifferentialGeometry.Analysis.Calculus.LipschitzFamily
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Diffeomorph.Perturbation

open scoped Manifold Topology NNReal

namespace Manifold

open Set

private theorem eventually_isSmoothEmbedding_of_compact_extension
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {e : P × M → V} {p₀ : P}
    (hf₀ : IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n)
    {G : P × V → V} (hG : ContDiff ℝ n G) (hGc : HasCompactSupport G)
    (hGe : EqOn (fun q : P × M => G (q.1, e (p₀, q.2))) e
      (Metric.closedBall p₀ 1 ×ˢ univ)) :
    ∀ᶠ p in 𝓝 p₀, IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p, x)) := by
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
  exact eventually_isSmoothEmbedding_of_compact_extension hf₀ hn hG hGc hGe

section

open scoped ContDiff

theorem eventually_isSmoothEmbedding_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf₀ : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (p₀, x))) :
    ∀ᶠ p in 𝓝 p₀, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞
      (fun x => e (p, x)) := by
  let f : P × M → P × V := fun q => (q.1, e (p₀, q.2))
  have hf : IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, P × V) ∞ f := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, P)) (M := P) (n := ∞)).prodMap hf₀
  have hK : IsCompact (Metric.closedBall p₀ 1 ×ˢ (univ : Set M)) :=
    (isCompact_closedBall p₀ 1).prod isCompact_univ
  obtain ⟨G, hG, hGc, -, hGe⟩ :=
    hf.exists_contDiff_compact_extension_prod_halfspace_of_tsupport_image_subset
      he hK isOpen_univ (subset_univ _)
  exact eventually_isSmoothEmbedding_of_compact_extension
    (n := (⊤ : ℕ∞)) hf₀ (by simp) hG hGc hGe

end

end Manifold
