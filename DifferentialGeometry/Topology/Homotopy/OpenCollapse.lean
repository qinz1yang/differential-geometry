import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Maps.Proper.Basic







noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Y : Type*}


def openCollapse (U : Set Y) (y : Y) : OnePoint U :=
  by
    classical
    exact if h : y ∈ U then (⟨y, h⟩ : U) else OnePoint.infty

theorem openCollapse_of_mem (U : Set Y) (y : U) : openCollapse U y = (y : OnePoint U) := by
  simp only [openCollapse, dite_eq_left y.property]

theorem openCollapse_of_notMem (U : Set Y) {y : Y} (hy : y ∉ U) :
    openCollapse U y = OnePoint.infty := by
  simp only [openCollapse, dite_eq_right hy]



theorem continuous_openCollapse [TopologicalSpace Y] [T2Space Y] (U : Set Y) (hU : IsOpen U) :
    Continuous (openCollapse U) := by
  classical
  rw [continuous_def]
  intro V hV
  by_cases hinf : OnePoint.infty ∈ V
  · have hc : IsCompact ((fun u : U => (u : OnePoint U)) ⁻¹' V)ᶜ :=
      ((OnePoint.isOpen_iff_of_mem' hinf).mp hV).1
    have heq : (openCollapse U ⁻¹' V)ᶜ =
        Subtype.val '' ((fun u : U => (u : OnePoint U)) ⁻¹' V)ᶜ := by
      ext y
      by_cases hy : y ∈ U
      · simp only [mem_compl_iff, mem_preimage, openCollapse, dite_eq_left hy, mem_image]
        constructor
        · intro h
          exact ⟨⟨y, hy⟩, h, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact hu
      · simp only [mem_compl_iff, mem_preimage, openCollapse, dite_eq_right hy, hinf, not_true_eq_false,
          mem_image]
        refine ⟨False.elim, ?_⟩
        rintro ⟨u, _, hu⟩
        exact hy (hu ▸ u.property)
    rw [← isClosed_compl_iff, heq]
    exact (hc.image continuous_subtype_val).isClosed
  · have heq : openCollapse U ⁻¹' V =
        Subtype.val '' ((fun u : U => (u : OnePoint U)) ⁻¹' V) := by
      ext y
      by_cases hy : y ∈ U
      · simp only [mem_preimage, openCollapse, dite_eq_left hy, mem_image]
        constructor
        · intro h
          exact ⟨⟨y, hy⟩, h, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact hu
      · simp only [mem_preimage, openCollapse, dite_eq_right hy, hinf, mem_image]
        refine ⟨False.elim, ?_⟩
        rintro ⟨u, _, hu⟩
        exact hy (hu ▸ u.property)
    rw [heq]
    exact hU.isOpenMap_subtype_val _ ((OnePoint.isOpen_iff_of_notMem hinf).mp hV)


theorem openCollapse_surjective (U : Set Y) (hU : Uᶜ.Nonempty) : Surjective (openCollapse U) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨y, hy⟩ := hU
    exact ⟨y, openCollapse_of_notMem U hy⟩
  | coe y => exact ⟨y, openCollapse_of_mem U y⟩



theorem openCollapse_prod_quotient [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap (Prod.map (id : K → K) (openCollapse U)) := by
  let := hU.locallyCompactSpace
  have hp : IsProperMap (Prod.map (id : K → K) (openCollapse U)) :=
    isProperMap_id.prodMap (continuous_openCollapse U hU).isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((surjective_id : Surjective (id : K → K)).prodMap (openCollapse_surjective U hne))

end DifferentialGeometry.Topology
