import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence

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
