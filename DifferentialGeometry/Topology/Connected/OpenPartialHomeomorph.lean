import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem image_eq_connectedComponent
    (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hconnected : IsPreconnected s) (hopen : IsOpen s)
    (hclosed : IsClosed (e '' s)) (hsource : s ⊆ e.source)
    {x : X} (hx : x ∈ s) : e '' s = connectedComponent (e x) := by
  have hcont := e.continuousOn.mono hsource
  have hconn := hconnected.image e hcont
  have hopen' := e.isOpen_image_of_subset_source hopen hsource
  have hmem : e x ∈ e '' s := mem_image_of_mem e hx
  exact subset_antisymm (hconn.subset_connectedComponent hmem)
    ((show IsClopen (e '' s) from ⟨hclosed, hopen'⟩).connectedComponent_subset hmem)

theorem image_eq_connectedComponent_of_isCompact [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hcompact : IsCompact s) (hconnected : IsPreconnected s) (hopen : IsOpen s)
    (hsource : s ⊆ e.source) {x : X} (hx : x ∈ s) :
    e '' s = connectedComponent (e x) :=
  e.image_eq_connectedComponent hconnected hopen
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed hsource hx

end OpenPartialHomeomorph
