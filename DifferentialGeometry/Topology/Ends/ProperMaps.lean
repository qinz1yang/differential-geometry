import DifferentialGeometry.Topology.Ends.FiniteEnds
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem not_isCompact_closure_of_range_proper_map
    [NoncompactSpace Y] {f : Y → X} (hf : IsProperMap f)
    {S : Set X} (hS : range f ⊆ S) : ¬ IsCompact (closure S) := by
  intro hcompact
  have hpre : f ⁻¹' closure S = univ := by
    apply eq_univ_of_forall
    intro y
    exact subset_closure (hS (mem_range_self y))
  exact noncompact_univ Y (hpre ▸ hf.isCompact_preimage hcompact)

theorem hasAtLeastEnds_of_proper_maps
    {k : ℕ} [PreconnectedSpace Y] [NoncompactSpace Y]
    (K : Set X) (hK : IsCompact K) (f : Fin k → Y → X)
    (hf : ∀ i, IsProperMap (f i)) (p : Fin k → Y)
    (havoid : ∀ i y, f i y ∉ K)
    (hdistinct : Function.Injective (fun i => connectedComponentIn Kᶜ (f i (p i)))) :
    HasAtLeastEnds X k := by
  refine ⟨K, hK, fun i => f i (p i), fun i => havoid i (p i), hdistinct, ?_⟩
  intro i
  apply not_isCompact_closure_of_range_proper_map (hf i)
  exact (isPreconnected_range (hf i).continuous).subset_connectedComponentIn
    (mem_range_self (p i)) (by rintro _ ⟨y, rfl⟩; exact havoid i y)

theorem hasAtLeastEnds_two_of_proper_maps_into_separated_sets
    [PreconnectedSpace Y] [NoncompactSpace Y]
    {K B E : Set X} (hK : IsCompact K) (hB : IsOpen B) (hE : IsOpen E)
    (hdisjoint : Disjoint B E) (hcover : B ∪ E = Kᶜ)
    (f g : Y → X) (hf : IsProperMap f) (hg : IsProperMap g) (p q : Y)
    (hfst : range f ⊆ B) (hsnd : range g ⊆ E) :
    HasAtLeastEnds X 2 := by
  have hBK : B ⊆ Kᶜ := by rw [← hcover]; exact subset_union_left
  have hEK : E ⊆ Kᶜ := by rw [← hcover]; exact subset_union_right
  have hp : f p ∈ B := hfst (mem_range_self p)
  have hq : g q ∈ E := hsnd (mem_range_self q)
  have hcompE : connectedComponentIn Kᶜ (g q) ⊆ E :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hE hB hdisjoint.symm
      (((union_comm E B).trans hcover).symm ▸ connectedComponentIn_subset Kᶜ (g q))
      ⟨g q, mem_connectedComponentIn (hEK hq), hq⟩
  have hne : connectedComponentIn Kᶜ (f p) ≠ connectedComponentIn Kᶜ (g q) := by
    intro heq
    exact disjoint_left.mp hdisjoint hp
      (hcompE (heq ▸ mem_connectedComponentIn (hBK hp)))
  let a : Fin 2 → Y → X := fun i => if i = 0 then f else g
  let b : Fin 2 → Y := fun i => if i = 0 then p else q
  refine hasAtLeastEnds_of_proper_maps K hK a ?_ b ?_ ?_
  · intro i
    by_cases hi : i = 0
    · simpa only [a, hi, ite_true] using hf
    · simpa only [a, hi, ite_false] using hg
  · intro i y
    by_cases hi : i = 0
    · simpa only [a, hi, ite_true, mem_compl_iff] using hBK (hfst (mem_range_self y))
    · simpa only [a, hi, ite_false, mem_compl_iff] using hEK (hsnd (mem_range_self y))
  · intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · exact hi.trans hj.symm
      · exact (hne (by simpa only [a, b, hi, hj, ite_true, ite_false] using hij)).elim
    · by_cases hj : j = 0
      · exact (hne (by simpa only [a, b, hi, hj, ite_true, ite_false] using hij.symm)).elim
      · exact (Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj).symm

end DifferentialGeometry.Geometry.Topology
