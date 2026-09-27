import DifferentialGeometry.Analysis.Calculus.LipschitzFamily
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Diffeomorph.Perturbation

open scoped Manifold Topology NNReal

namespace Manifold

open Set

private theorem eventually_exists_lipschitz_perturbation_of_compact_extension
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {M : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : P × M → V} {p₀ : P}
    (hn : 1 ≤ n)
    {G : P × V → V} (hG : ContDiff ℝ n G) (hGc : HasCompactSupport G)
    (hGe : EqOn (fun q : P × M => G (q.1, e (p₀, q.2))) e
      (Metric.closedBall p₀ 1 ×ˢ univ)) :
    ∀ᶠ p in 𝓝 p₀, ∃ g : V → V, ContDiff ℝ n g ∧ HasCompactSupport g ∧
      LipschitzWith (1 / 2 : ℝ≥0) g ∧ ∀ x, e (p₀, x) + g (e (p₀, x)) = e (p, x) := by
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
  have hsupp : HasCompactSupport (fun y => G (p, y) - G (p₀, y)) := by
    apply HasCompactSupport.intro (hGc.image continuous_snd)
    intro y hy
    have hzero (q : P) : G (q, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hqy => hy ⟨(q, y), hqy, rfl⟩)
    rw [hzero p, hzero p₀, sub_self]
  refine ⟨_, hslice, hsupp, hp, fun x => ?_⟩
  rw [show G (p, e (p₀, x)) = e (p, x) from
    hGe (x := (p, x)) ⟨hpnear, mem_univ x⟩]
  rw [show G (p₀, e (p₀, x)) = e (p₀, x) from
    hGe (x := (p₀, x)) ⟨Metric.mem_closedBall_self zero_le_one, mem_univ x⟩]
  abel

private theorem eventually_exists_lipschitz_perturbation
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, ∃ g : V → V, ContDiff ℝ n g ∧ HasCompactSupport g ∧
      LipschitzWith (1 / 2 : ℝ≥0) g ∧ ∀ x, e (p₀, x) + g (e (p₀, x)) = e (p, x) := by
  let f : P × M → P × V := fun q => (q.1, e (p₀, q.2))
  have hf : IsSmoothEmbedding (𝓘(ℝ, P).prod I) 𝓘(ℝ, P × V) n f := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, P)) (M := P) (n := n)).prodMap hf₀
  have hK : IsCompact (Metric.closedBall p₀ 1 ×ˢ (univ : Set M)) :=
    (isCompact_closedBall p₀ 1).prod isCompact_univ
  obtain ⟨G, hG, hGc, -, hGe⟩ := hf.exists_contDiff_compact_extension
    he hK isOpen_univ (subset_univ _)
  exact eventually_exists_lipschitz_perturbation_of_compact_extension hn hG hGc hGe

theorem eventually_exists_diffeomorph_comp_eq
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, ∃ Φ : Diffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) V V n,
      ∀ x, Φ (e (p₀, x)) = e (p, x) := by
  filter_upwards [eventually_exists_lipschitz_perturbation he hf₀ hn] with p hp
  obtain ⟨g, hg, _, hglip, hge⟩ := hp
  exact ⟨Diffeomorph.addLipschitz hg hglip (by norm_num), hge⟩

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
  filter_upwards [eventually_exists_diffeomorph_comp_eq he hf₀ hn] with p hp
  obtain ⟨Φ, hΦ⟩ := hp
  exact (funext hΦ) ▸ hf₀.diffeomorph_comp Φ

section

open scoped ContDiff

theorem eventually_exists_contDiff_ambient_isotopy
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) ∞ e)
    (hf₀ : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (p₀, x))) :
    ∀ᶠ p in 𝓝 p₀, ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ x, Φ 1 (e (p₀, x)) = e (p, x)) ∧
      ∃ K : Set V, IsCompact K ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  filter_upwards [eventually_exists_lipschitz_perturbation he hf₀ (by simp)] with p hp
  obtain ⟨g, hg, hgc, hglip, hge⟩ := hp
  refine ⟨Diffeomorph.addLipschitzIsotopy hg hglip (by norm_num),
    Diffeomorph.contDiff_addLipschitzIsotopy hg hglip (by norm_num),
    Diffeomorph.contDiff_addLipschitzIsotopy_symm hg hglip (by norm_num),
    Diffeomorph.addLipschitzIsotopy_zero hg hglip (by norm_num), ?_,
    Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy hg hglip (by norm_num) hgc⟩
  intro x
  simpa only [Diffeomorph.addLipschitzIsotopy_one, Diffeomorph.addLipschitz_apply]
    using hge x

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
  filter_upwards [eventually_exists_lipschitz_perturbation_of_compact_extension
    (n := (⊤ : ℕ∞)) (by simp) hG hGc hGe] with p hp
  obtain ⟨g, hg, _, hglip, hge⟩ := hp
  exact (funext hge) ▸ hf₀.diffeomorph_comp
    (Diffeomorph.addLipschitz hg hglip (by norm_num))

end

end Manifold
