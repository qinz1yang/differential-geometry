import DifferentialGeometry.Topology.Embedding.Factor
import Mathlib.Topology.Homeomorph.Lemmas

open scoped ContDiff

namespace Manifold

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} {f : M → N} {g : P → N}

noncomputable def IsSmoothEmbedding.lift (hf : IsSmoothEmbedding I J n f)
    (g : P → N) (hgf : Set.range g ⊆ Set.range f) : P → M :=
  fun x => hf.isEmbedding.toHomeomorph.symm ⟨g x, hgf (Set.mem_range_self x)⟩

omit [TopologicalSpace P] in
theorem IsSmoothEmbedding.comp_lift (hf : IsSmoothEmbedding I J n f)
    (hgf : Set.range g ⊆ Set.range f) (x : P) :
    f (hf.lift g hgf x) = g x := by
  exact congrArg Subtype.val
    (hf.isEmbedding.toHomeomorph.apply_symm_apply ⟨g x, hgf (Set.mem_range_self x)⟩)

theorem IsSmoothEmbedding.contMDiff_lift (hf : IsSmoothEmbedding I J n f)
    (hg : ContMDiff K J n g) (hgf : Set.range g ⊆ Set.range f) :
    ContMDiff K I n (hf.lift g hgf) := by
  apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
  refine ⟨?_, hg.congr (hf.comp_lift hgf)⟩
  exact hf.isEmbedding.toHomeomorph.symm.continuous.comp
    (hg.continuous.subtype_mk (fun x => hgf (Set.mem_range_self x)))

end

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''} [I.Boundaryless] [K.Boundaryless]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold K n P] {f : M → N} {g : P → N}

theorem IsSmoothEmbedding.isSmoothEmbedding_lift (hf : IsSmoothEmbedding I J n f)
    (hg : IsSmoothEmbedding K J n g) (hn : n ≠ 0) (hgf : Set.range g ⊆ Set.range f) :
    IsSmoothEmbedding K I n (hf.lift g hgf) := by
  have hcomp : IsSmoothEmbedding K J n (f ∘ hf.lift g hgf) := by
    rw [show f ∘ hf.lift g hgf = g from funext (hf.comp_lift hgf)]
    exact hg
  exact hcomp.of_comp hn (hf.contMDiff_lift hg.contMDiff hgf) hf.contMDiff

end Manifold
