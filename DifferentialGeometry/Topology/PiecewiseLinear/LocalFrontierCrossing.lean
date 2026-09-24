import Mathlib.Topology.Closure

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem interior_inter_eq_of_inter_eq {X : Type*} [TopologicalSpace X]
    {A B V : Set X} (hV : IsOpen V) (heq : A ∩ V = B ∩ V) :
    interior A ∩ V = interior B ∩ V := by
  simpa only [interior_inter, hV.interior_eq] using congrArg interior heq

theorem frontier_inter_eq_of_inter_eq {X : Type*} [TopologicalSpace X]
    {A B V : Set X} (hA : IsClosed A) (hB : IsClosed B) (hV : IsOpen V)
    (heq : A ∩ V = B ∩ V) : frontier A ∩ V = frontier B ∩ V := by
  have hi := interior_inter_eq_of_inter_eq hV heq
  rw [hA.frontier_eq, hB.frontier_eq]
  ext x
  have h := Set.ext_iff.mp heq x
  have h' := Set.ext_iff.mp hi x
  simp only [mem_inter_iff, mem_sdiff] at *
  tauto

theorem closure_subset_of_inter_eq {X : Type*} [TopologicalSpace X]
    {C S T V : Set X} (hV : IsOpen V) (hCV : C ⊆ V) (heq : S ∩ V = T ∩ V)
    (hCS : C ⊆ closure S) : C ⊆ closure T := by
  intro x hx
  apply mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨y, ⟨hyO, hyV⟩, hyS⟩ :=
    mem_closure_iff.mp (hCS hx) (O ∩ V) (hO.inter hV) ⟨hxO, hCV hx⟩
  exact ⟨y, hyO, (heq.subset ⟨hyS, hyV⟩).1⟩

theorem frontier_sides_of_inter_eq {X : Type*} [TopologicalSpace X]
    {C A B A' B' V : Set X} (hA : IsClosed A) (hA' : IsClosed A')
    (hV : IsOpen V) (hCV : C ⊆ V)
    (heA : A ∩ V = A' ∩ V) (heB : B ∩ V = B' ∩ V)
    (hin : C ⊆ closure (frontier A ∩ interior B))
    (hout : C ⊆ closure (frontier A \ B)) :
    (C ⊆ closure (frontier A' ∩ interior B')) ∧ C ⊆ closure (frontier A' \ B') := by
  have hAf := frontier_inter_eq_of_inter_eq hA hA' hV heA
  have hBi := interior_inter_eq_of_inter_eq hV heB
  constructor
  · apply closure_subset_of_inter_eq hV hCV _ hin
    ext x
    have hf := Set.ext_iff.mp hAf x
    have hi := Set.ext_iff.mp hBi x
    simp only [mem_inter_iff] at *
    tauto
  · apply closure_subset_of_inter_eq hV hCV _ hout
    ext x
    have hf := Set.ext_iff.mp hAf x
    have hb := Set.ext_iff.mp heB x
    simp only [mem_inter_iff, mem_sdiff] at *
    tauto

end DifferentialGeometry.Topology.PiecewiseLinear
