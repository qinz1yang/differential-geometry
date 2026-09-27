import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

open Function Set
open scoped Manifold ContDiff Topology

namespace Manifold

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type u} {N' : Type v} [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
  {f : M → N}

namespace IsImmersionOfComplement

theorem postcomp_diffeomorph
    (hf : IsImmersionOfComplement F I J n f)
    (ψ : Diffeomorph J J N N' n) :
    IsImmersionOfComplement F I J n (ψ ∘ f) := by
  intro x
  let h := hf x
  let c : OpenPartialHomeomorph N' G :=
    ψ.symm.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ IsManifold.maximalAtlas J n N' := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        ψ.symm.contMDiff.contMDiffOn (by
          intro y hy
          simpa [c] using hy.2)
    · have hsub : c.target ⊆ h.codChart.target := by
        intro y hy
        simpa [c] using hy
      have hsmooth := ψ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas
          h.codChart_mem_maximalAtlas).mono hsub)
      simpa [c, Function.comp_def] using hsmooth
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (ψ.continuous.continuousAt.comp h.continuousAt) h.equiv
    h.domChart c h.mem_domChart_source
  · simp [c, h.mem_codChart_source]
  · exact h.domChart_mem_maximalAtlas
  · exact hc
  · intro y hy
    simpa [c, Function.comp_def] using h.writtenInCharts hy

end IsImmersionOfComplement

namespace IsImmersion

theorem postcomp_diffeomorph
    (hf : IsImmersion I J n f) (ψ : Diffeomorph J J N N' n) :
    IsImmersion I J n (ψ ∘ f) := by
  rcases hf with ⟨F, hFgroup, hFspace, hf⟩
  let _ := hFgroup
  let _ := hFspace
  exact ⟨F, inferInstance, inferInstance, hf.postcomp_diffeomorph ψ⟩

end IsImmersion

namespace IsSmoothEmbedding

theorem postcomp_diffeomorph
    (hf : IsSmoothEmbedding I J n f) (ψ : Diffeomorph J J N N' n) :
    IsSmoothEmbedding I J n (ψ ∘ f) :=
  ⟨hf.isImmersion.postcomp_diffeomorph ψ,
    ψ.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

end IsSmoothEmbedding

end Manifold
