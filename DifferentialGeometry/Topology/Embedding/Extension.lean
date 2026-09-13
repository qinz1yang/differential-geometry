import DifferentialGeometry.Topology.Embedding.Retraction
import DifferentialGeometry.Analysis.Calculus.CompactCutoff

open scoped ContDiff Manifold Topology

namespace Manifold

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M}

theorem IsSmoothEmbedding.exists_contDiff_extension_of_isClosed_image
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsClosed (f '' K)) :
    ∃ G : V → F, ContDiff ℝ n G ∧ EqOn (G ∘ f) g K := by
  let C : V → Set F := fun z => {v | ∀ x ∈ K, f x = z → v = g x}
  have hC (z : V) : Convex ℝ (C z) := by
    rw [convex_iff_add_mem]
    intro a ha b hb s t _ _ hsum x hx hfx
    rw [ha x hx hfx, hb x hx hfx, ← add_smul, hsum, one_smul]
  have hlocal (z : V) : ∃ U ∈ 𝓝 z, ∃ G : V → F,
      ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, F) n G U ∧ ∀ y ∈ U, G y ∈ C y := by
    by_cases hz : z ∈ f '' K
    · obtain ⟨x, _, rfl⟩ := hz
      obtain ⟨U, hxU, r, hr, _, hfix⟩ := hf.exists_contMDiff_local_retraction x
      let G : V → F := Subtype.val.extend (fun q : U => g (r q)) 0
      have hG (q : U) : G q = g (r q) :=
        Subtype.val_injective.extend_apply (fun q : U => g (r q)) 0 q
      have hGU : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, F) n (fun q : U => G q) :=
        (hg.comp hr).congr hG
      refine ⟨U, U.isOpen.mem_nhds hxU, G, ?_, ?_⟩
      · intro y hy
        exact (contMDiffAt_subtype_iff.mp (hGU ⟨y, hy⟩)).contMDiffWithinAt
      · intro y hy x' _ hxy
        subst y
        rw [hG ⟨f x', hy⟩, hfix x' hy]
    · refine ⟨(f '' K)ᶜ, hK.isOpen_compl.mem_nhds hz, 0, contMDiffOn_const, ?_⟩
      intro y hy x hx hxy
      exact False.elim (hy ⟨x, hx, hxy⟩)
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, V)) (n := n) hC hlocal
  exact ⟨G, G.contMDiff.contDiff, fun x hx => hG (f x) x hx rfl⟩

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_of_tsupport_image_subset
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  have himage : IsCompact (f '' K) := hK.image hf.isEmbedding.continuous
  obtain ⟨G, hG, hGf⟩ := hf.exists_contDiff_extension_of_isClosed_image hg himage.isClosed
  have hA : IsCompact (f '' (K ∩ tsupport g)) :=
    (hK.inter_right (isClosed_tsupport g)).image hf.isEmbedding.continuous
  obtain ⟨χ, hχ, hχc, hχone, hχO, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hA hO hKO
  have hχn : ContDiff ℝ n χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun z => χ z • G z, hχn.smul hG, hχc.smul_right,
    (tsupport_smul_subset_left χ G).trans hχO, ?_⟩
  intro x hx
  change χ (f x) • G (f x) = g x
  rw [show G (f x) = g x from hGf hx]
  by_cases hxg : x ∈ tsupport g
  · rw [hχone.self_of_nhdsSet (mem_image_of_mem f ⟨hx, hxg⟩), Pi.one_apply, one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hxg, smul_zero]

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_eq_zero_nhds
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O)
    {D : Set V} (hD : IsClosed D) (hDA : Disjoint D (f '' (K ∩ tsupport g))) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧ tsupport G ⊆ O ∧
      EqOn (G ∘ f) g K ∧ ∃ W : Set V, IsOpen W ∧ D ⊆ W ∧ EqOn G 0 W := by
  have hAO : f '' (K ∩ tsupport g) ⊆ O ∩ Dᶜ := by
    intro z hz
    exact ⟨hKO hz, fun hzD => Set.disjoint_left.mp hDA hzD hz⟩
  obtain ⟨G, hG, hGc, hGO, hGf⟩ :=
    hf.exists_contDiff_compact_extension_of_tsupport_image_subset hg hK
      (hO.inter hD.isOpen_compl) hAO
  refine ⟨G, hG, hGc, hGO.trans inter_subset_left, hGf,
    (tsupport G)ᶜ, (isClosed_tsupport G).isOpen_compl, ?_, ?_⟩
  · intro z hz hzG
    exact (hGO hzG).2 hz
  · exact fun z hz => image_eq_zero_of_notMem_tsupport hz

theorem IsSmoothEmbedding.exists_contDiff_compact_extension
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O) (hKO : f '' K ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K :=
  hf.exists_contDiff_compact_extension_of_tsupport_image_subset hg hK hO
    ((image_mono inter_subset_left).trans hKO)

end Manifold
