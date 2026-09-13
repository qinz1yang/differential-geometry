import DifferentialGeometry.Topology.Embedding.Retraction
import Mathlib.Geometry.Manifold.PartitionOfUnity

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

theorem IsSmoothEmbedding.exists_contDiff_compact_extension
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O) (hKO : f '' K ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  have himage : IsCompact (f '' K) := hK.image hf.isEmbedding.continuous
  obtain ⟨G, hG, hGf⟩ := hf.exists_contDiff_extension_of_isClosed_image hg himage.isClosed
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between himage hO hKO
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, V)) (n := n) himage.isClosed hKL
  have hχL : tsupport (χ : V → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro z hz
    by_contra hn
    exact hz (hχzero z hn)
  let G' : V → F := fun z => χ z • G z
  have hG'L : tsupport G' ⊆ L := (tsupport_smul_subset_left χ G).trans hχL
  refine ⟨G', χ.contMDiff.contDiff.smul hG,
    hL.of_isClosed_subset (isClosed_tsupport G') hG'L, hG'L.trans hLO, ?_⟩
  intro x hx
  change χ (f x) • G (f x) = g x
  rw [hχone.self_of_nhdsSet (f x) (mem_image_of_mem f hx), one_smul]
  exact hGf hx

end Manifold
