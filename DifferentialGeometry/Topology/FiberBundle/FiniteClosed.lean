import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Maps.Basic

noncomputable section
open Bundle Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.FiberBundle

theorem isClosedMap_projection_of_finite {J B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [Finite F] (Z : FiberBundleCore J B F) : IsClosedMap Z.proj := by
  intro K hK
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let T := Z.localTriv (Z.indexAt x)
  let e := T.toOpenPartialHomeomorph
  have hxbase : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
  have hall (q : F) : ∀ᶠ y in 𝓝 x, e.symm (y, q) ∉ K := by
    have hc : ContinuousAt (fun y : B => e.symm (y, q)) x :=
      ContinuousAt.comp (f := fun y : B => (y, q)) (x := x)
        (e.symm.continuousAt ⟨hxbase, mem_univ _⟩)
        (continuous_id.prodMk continuous_const).continuousAt
    apply hc (hK.isOpen_compl.mem_nhds ?_)
    intro hmem
    exact hx ⟨e.symm (x, q), hmem, rfl⟩
  have ha : ∀ᶠ y in 𝓝 x, ∀ q : F, e.symm (y, q) ∉ K :=
    eventually_all.mpr hall
  filter_upwards [(Z.isOpen_baseSet _).mem_nhds hxbase, ha] with y hy hforall
  rintro ⟨z, hz, hp⟩
  have hsrc : z ∈ e.source := by
    change Z.proj z ∈ Z.baseSet (Z.indexAt x)
    rwa [hp]
  have hfst : (e z).1 = y := (T.coe_fst hsrc).trans hp
  have hval : e.symm (y, (e z).2) = z := by
    rw [← hfst]
    exact e.left_inv hsrc
  exact hforall (e z).2 (hval.symm ▸ hz)

end DifferentialGeometry.Topology.FiberBundle
