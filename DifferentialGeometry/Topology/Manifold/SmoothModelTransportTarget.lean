import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

variable {𝕜 E F E₀ H H' H₀ M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H₀]
  [TopologicalSpace M] [ChartedSpace H₀ M]
  [TopologicalSpace N] [ChartedSpace H N]

variable (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
  (e : H ≃ₜ H') (L : E ≃L[𝕜] F) (hc : ∀ y, J (e y) = L (I y))
  (I₀ : ModelWithCorners 𝕜 E₀ H₀)

include hc in
theorem isImmersion_chartedSpaceTransHomeomorph_target {n : ℕ∞ω} {f : M → N}
    (hf : IsImmersion I₀ I n f) :
    letI := chartedSpaceTransHomeomorph (M := N) e
    IsImmersion I₀ J n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  apply IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  let h := hf.isImmersionOfComplement_complement x
  let c := h.codChart.trans e.toOpenPartialHomeomorph
  have hs : c.source = h.codChart.source := by simp [c]
  apply IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans L) h.domChart c
    h.mem_domChart_source (hs.symm ▸ h.mem_codChart_source)
    h.domChart_mem_maximalAtlas
    ((mem_maximalAtlas_chartedSpaceTransHomeomorph I J e L hc).mpr
      h.codChart_mem_maximalAtlas)
  · intro y hy
    rw [Set.mem_preimage, hs]
    exact h.source_subset_preimage_source hy
  · intro y hy
    change J (e (h.codChart (f ((h.domChart.extend I₀).symm y)))) = L (h.equiv (y, 0))
    rw [hc]
    exact congrArg L (h.writtenInCharts hy)

include hc in
theorem isSmoothEmbedding_chartedSpaceTransHomeomorph_target {n : ℕ∞ω} {f : M → N}
    (hf : IsSmoothEmbedding I₀ I n f) :
    letI := chartedSpaceTransHomeomorph (M := N) e
    IsSmoothEmbedding I₀ J n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  exact ⟨isImmersion_chartedSpaceTransHomeomorph_target I J e L hc I₀ hf.isImmersion,
    hf.isEmbedding⟩

end DifferentialGeometry.Manifold
