import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false

open Filter Set

namespace DifferentialGeometry

theorem eventually_mapsTo_of_tendstoUniformly
    {X Y ι : Type*} [TopologicalSpace X] [UniformSpace Y]
    {A : Set X} {f : X → Y} {U : Set Y} {F : ι → X → Y} {p : Filter ι}
    (hconv : TendstoUniformly F f p) (hA : IsCompact A)
    (hf : ContinuousOn f A) (hU : IsOpen U) (hmap : MapsTo f A U) :
    ∀ᶠ n in p, MapsTo (F n) A U := by
  obtain ⟨V, hV, _hVopen, hball⟩ :=
    lebesgue_number_of_compact_open
      (hA.image_of_continuousOn hf) hU (mapsTo_iff_image_subset.mp hmap)
  filter_upwards [hconv V hV] with n hn
  intro x hx
  exact hball (f x) (mem_image_of_mem f hx) (hn x)

end DifferentialGeometry

theorem TendstoUniformlyOn.comp_tendstoUniformly
    {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {s : Set β} {F : ι → β → γ} {f : β → γ}
    {u : ι → α → β} {v : α → β}
    (hF : TendstoUniformlyOn F f l s) (hf : UniformContinuousOn f s)
    (hu : TendstoUniformly u v l)
    (hus : ∀ᶠ i in l, ∀ x, u i x ∈ s) (hvs : ∀ x, v x ∈ s) :
    TendstoUniformly (fun i x => F i (u i x)) (fun x => f (v x)) l := by
  have hcomp := hf.comp_tendstoUniformly_eventually hus hvs hu
  intro V hV
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  filter_upwards [hF W hW, hcomp W hW, hus] with i hi hci hsi
  intro x
  exact hWV (SetRel.prodMk_mem_comp (hci x) (hi _ (hsi x)))
