import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 E F H K M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F K} {n : ℕ∞ω}
  [IsManifold I n M] [IsManifold J n N]


theorem isImmersion_prodMk_const_of_centered_chart (y : N)
    (c : OpenPartialHomeomorph N K) (hy : y ∈ c.source)
    (hc : c ∈ IsManifold.maximalAtlas J n N) (hz : J (c y) = 0) :
    IsImmersion I (I.prod J) n (fun x : M => (x, y)) := by
  apply IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let d := chartAt H x
  apply IsImmersionAtOfComplement.mk_of_charts
    (I := I) (J := I.prod J) (f := fun z : M => (z, y)) (x := x)
    (ContinuousLinearEquiv.refl 𝕜 (E × F))
    d (d.prod c) (mem_chart_source H x) ⟨mem_chart_source H x, hy⟩
    (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas x) hc)
  · intro z hz'
    exact ⟨hz', hy⟩
  · intro z hz'
    change ((d.extend I) ((d.extend I).symm z), J (c y)) = (z, 0)
    rw [(d.extend I).right_inv hz', hz]

theorem isSmoothEmbedding_prodMk_const_of_centered_chart (y : N)
    (c : OpenPartialHomeomorph N K) (hy : y ∈ c.source)
    (hc : c ∈ IsManifold.maximalAtlas J n N) (hz : J (c y) = 0) :
    IsSmoothEmbedding I (I.prod J) n (fun x : M => (x, y)) :=
  ⟨isImmersion_prodMk_const_of_centered_chart y c hy hc hz, isEmbedding_prodMkLeft y⟩


theorem isImmersion_const_prodMk_of_centered_chart (y : N)
    (c : OpenPartialHomeomorph N K) (hy : y ∈ c.source)
    (hc : c ∈ IsManifold.maximalAtlas J n N) (hz : J (c y) = 0) :
    IsImmersion I (J.prod I) n (fun x : M => (y, x)) := by
  apply IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let d := chartAt H x
  apply IsImmersionAtOfComplement.mk_of_charts
    (I := I) (J := J.prod I) (f := fun z : M => (y, z)) (x := x)
    (ContinuousLinearEquiv.prodComm 𝕜 E F)
    d (c.prod d) (mem_chart_source H x) ⟨hy, mem_chart_source H x⟩
    (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.mem_maximalAtlas_prod hc (IsManifold.chart_mem_maximalAtlas x))
  · intro z hz'
    exact ⟨hy, hz'⟩
  · intro z hz'
    change (J (c y), (d.extend I) ((d.extend I).symm z)) = (0, z)
    rw [(d.extend I).right_inv hz', hz]

theorem isSmoothEmbedding_const_prodMk_of_centered_chart (y : N)
    (c : OpenPartialHomeomorph N K) (hy : y ∈ c.source)
    (hc : c ∈ IsManifold.maximalAtlas J n N) (hz : J (c y) = 0) :
    IsSmoothEmbedding I (J.prod I) n (fun x : M => (y, x)) :=
  ⟨isImmersion_const_prodMk_of_centered_chart y c hy hc hz, isEmbedding_prodMkRight y⟩

end Manifold
