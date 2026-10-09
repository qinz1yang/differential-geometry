import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

open Set

namespace eVariationOn

theorem le_of_edist_le {α X Y : Type*} [LinearOrder α] [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {f : α → X} {g : α → Y} {s : Set α}
    (h : ∀ a ∈ s, ∀ b ∈ s, edist (f a) (f b) ≤ edist (g a) (g b)) :
    eVariationOn f s ≤ eVariationOn g s := by
  apply iSup_le
  intro p
  apply le_iSup_of_le p
  exact Finset.sum_le_sum fun i hi => h _ (p.2.property.2 (i + 1)) _ (p.2.property.2 i)

theorem eq_of_edist_eq {α X Y : Type*} [LinearOrder α] [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {f : α → X} {g : α → Y} {s : Set α}
    (h : ∀ a ∈ s, ∀ b ∈ s, edist (f a) (f b) = edist (g a) (g b)) :
    eVariationOn f s = eVariationOn g s :=
  le_antisymm (le_of_edist_le fun a ha b hb => (h a ha b hb).le)
    (le_of_edist_le fun a ha b hb => (h a ha b hb).ge)

end eVariationOn

namespace Isometry

theorem comp_eVariationOn {α X Y : Type*} [LinearOrder α] [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {f : X → Y} (hf : Isometry f) (g : α → X) (s : Set α) :
    eVariationOn (f ∘ g) s = eVariationOn g s :=
  eVariationOn.eq_of_edist_eq fun a _ b _ => hf.edist_eq (g a) (g b)

end Isometry
