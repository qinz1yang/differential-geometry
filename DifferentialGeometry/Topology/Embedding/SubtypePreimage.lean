import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.Compact

section

noncomputable section
open Set Topology
universe u
namespace Topology.IsInducing

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem isCompact_image_subtype_preimage {U : Set E} {e : U → X}
    (he : IsInducing e) {L : Set X} (hL : IsCompact L) (hLe : L ⊆ range e) :
    IsCompact (Subtype.val '' (e ⁻¹' L)) :=
  (he.isCompact_preimage' hL hLe).image continuous_subtype_val

end Topology.IsInducing

namespace Function.Injective

variable {E X : Type*}

theorem image_subtype_preimage_subset {U W : Set E} {e : U → X}
    (he : Injective e) {L : Set X}
    (hLe : L ⊆ e '' {z : U | (z : E) ∈ W}) :
    Subtype.val '' (e ⁻¹' L) ⊆ W := by
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨v, hv, huv⟩ := hLe hu
  exact (he huv) ▸ hv

end Function.Injective

end

end
