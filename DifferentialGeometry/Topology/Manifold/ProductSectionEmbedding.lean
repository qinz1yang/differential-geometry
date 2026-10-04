import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 E F H M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace F N]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [IsManifold I n M] [IsManifold 𝓘(𝕜, F) n N]

theorem isImmersion_prodMk_const (y : N) :
    IsImmersion I (I.prod 𝓘(𝕜, F)) n (fun x : M => (x, y)) := by
  apply IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let c₀ := chartAt F y
  let a := c₀ y
  let c := c₀.trans (Homeomorph.addRight (-a)).toOpenPartialHomeomorph
  have hs : c.source = c₀.source := by simp [c]
  have hy : y ∈ c.source := hs.symm ▸ mem_chart_source F y
  have hz : c y = 0 := by simp [c, a]
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) n N := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn 𝓘(𝕜, F) 𝓘(𝕜, F) n (fun z => c₀ z + -a) c.source
      rw [hs]
      exact (contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)).add
        contMDiffOn_const
    · change ContMDiffOn 𝓘(𝕜, F) 𝓘(𝕜, F) n (fun z => c₀.symm (z + -(-a))) c.target
      exact (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas y)).comp
        (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ hz => hz.2)
  let d := chartAt H x
  apply IsImmersionAtOfComplement.mk_of_charts
    (I := I) (J := I.prod 𝓘(𝕜, F)) (f := fun z : M => (z, y)) (x := x)
    (ContinuousLinearEquiv.refl 𝕜 (E × F))
    d (d.prod c) (mem_chart_source H x) ⟨mem_chart_source H x, hy⟩
    (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas x) hc)
  · intro z hz
    exact ⟨hz, hy⟩
  · intro z hz'
    change ((d.extend I) ((d.extend I).symm z), c y) = (z, 0)
    rw [(d.extend I).right_inv hz', hz]

theorem isSmoothEmbedding_prodMk_const (y : N) :
    IsSmoothEmbedding I (I.prod 𝓘(𝕜, F)) n (fun x : M => (x, y)) :=
  ⟨isImmersion_prodMk_const y, isEmbedding_prodMkLeft y⟩

end Manifold
