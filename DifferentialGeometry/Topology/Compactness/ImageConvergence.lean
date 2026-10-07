import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.Separation

open Filter Set

namespace TendstoUniformlyOn

variable {X Y ι : Type*} [UniformSpace Y]
  {F : ι → X → Y} {f : X → Y} {l : Filter ι} {K : Set X} {y : Y}

theorem mem_closure_image
    (hF : TendstoUniformlyOn F f l K)
    (hy : ∃ᶠ i in l, y ∈ F i '' K) : y ∈ closure (f '' K) := by
  apply UniformSpace.mem_closure_iff_symm_ball.mpr
  intro V hV hsymm
  obtain ⟨i, ⟨x, hx, hxy⟩, hi⟩ := (hy.and_eventually (hF V hV)).exists
  refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
  change (y, f x) ∈ V
  rw [← hxy]
  exact hsymm.symm _ _ (hi x hx)

theorem mem_image_of_isClosed_image
    (hF : TendstoUniformlyOn F f l K) (hK : IsClosed (f '' K))
    (hy : ∃ᶠ i in l, y ∈ F i '' K) : y ∈ f '' K := by
  rw [← hK.closure_eq]
  exact hF.mem_closure_image hy

end TendstoUniformlyOn

theorem surjective_of_tendstoUniformlyOn_of_compact_preimages
    {X Y ι : Type*} [TopologicalSpace X] [UniformSpace Y] [T0Space Y]
    {F : ι → X → Y} {f : X → Y} {l : Filter ι}
    (hf : Continuous f)
    (hF : ∀ K : Set X, IsCompact K → TendstoUniformlyOn F f l K)
    (hpre : ∀ y : Y, ∃ K : Set X, IsCompact K ∧ ∃ᶠ i in l, y ∈ F i '' K) :
    Function.Surjective f := by
  intro y
  obtain ⟨K, hK, hy⟩ := hpre y
  obtain ⟨x, _, hxy⟩ :=
    (hF K hK).mem_image_of_isClosed_image (hK.image hf).isClosed hy
  exact ⟨x, hxy⟩
