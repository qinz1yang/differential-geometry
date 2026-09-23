import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Topology

namespace DifferentialGeometry.Topology

theorem exists_finite_compact_component_union
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {U P : Set X} (hU : IsOpen U) (hP : IsCompact P) (hPU : P ⊆ U)
    (hcomp : ∀ x ∈ P, IsCompact (closure (connectedComponentIn U x))) :
    ∃ V : Finset (Set X),
      (∀ C, C ∈ V ↔ ∃ x ∈ P, C = connectedComponentIn U x) ∧
      (∀ C ∈ V, IsOpen C ∧ IsConnected C ∧
        IsCompact (closure C) ∧ frontier C ⊆ frontier U) ∧
      let L := ⋃ C ∈ V, closure C
      IsCompact L ∧ P ⊆ interior L ∧ closure (interior L) = L ∧
        frontier L ⊆ frontier U := by
  classical
  let C : X → Set X := fun x => connectedComponentIn U x
  have hCop (x : X) : IsOpen (C x) := hU.connectedComponentIn
  have hCconn : ∀ x ∈ P, IsConnected (C x) := by
    intro x hx
    exact isConnected_connectedComponentIn_iff.mpr (hPU hx)
  have hCfront (x : X) : frontier (C x) ⊆ frontier U := by
    intro z hz
    refine ⟨closure_mono (connectedComponentIn_subset U x) hz.1, ?_⟩
    intro hzU
    have hzC : z ∈ C z := mem_connectedComponentIn (interior_subset hzU)
    obtain ⟨w, hw, hwC⟩ := mem_closure_iff.mp hz.1 (C z) (hCop z) hzC
    have hEq : C x = C z := (connectedComponentIn_eq hwC).trans
      (connectedComponentIn_eq hw).symm
    apply hz.2
    rw [hEq]
    exact (hCop z).interior_eq.symm ▸ hzC
  have hcov : P ⊆ ⋃ x : P, interior (C x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hCop x).interior_eq.symm ▸ (mem_connectedComponentIn (hPU hx))⟩
  obtain ⟨s, hs⟩ := hP.elim_finite_subcover (fun x : P => interior (C x))
    (fun x => isOpen_interior) (by
      intro x hx
      exact hcov hx)
  let V : Finset (Set X) := s.image (fun x : P => C x)
  have hVmem (D : Set X) : D ∈ V ↔ ∃ x ∈ P, D = C x := by
    simp only [V, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
      exact ⟨y, hy, connectedComponentIn_eq (interior_subset hxy)⟩
  have hVprops (D : Set X) (hD : D ∈ V) :
      IsOpen D ∧ IsConnected D ∧ IsCompact (closure D) ∧ frontier D ⊆ frontier U := by
    obtain ⟨x, hx, rfl⟩ := hVmem D |>.mp hD
    exact ⟨hCop x, hCconn x hx, hcomp x hx, hCfront x⟩
  let L : Set X := ⋃ D ∈ V, closure D
  have hLcompact : IsCompact L := by
    apply V.finite_toSet.isCompact_biUnion
    intro D hD
    exact (hVprops D hD).2.2.1
  have hLclosed : IsClosed L := V.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closure)
  have hDin (D : Set X) (hD : D ∈ V) : D ⊆ interior L := by
    have hsub : D ⊆ L := by
      intro z hz
      exact mem_iUnion₂.mpr ⟨D, hD, subset_closure hz⟩
    exact (hVprops D hD).1.subset_interior_iff.mpr hsub
  have hPL : P ⊆ interior L := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    have hD : C y ∈ V := Finset.mem_image.mpr ⟨y, hy, rfl⟩
    exact hDin (C y) hD (interior_subset hxy)
  have hreg : closure (interior L) = L := by
    apply Subset.antisymm
    · exact closure_minimal interior_subset hLclosed
    · intro z hz
      obtain ⟨D, hD, hzD⟩ := mem_iUnion₂.mp hz
      exact closure_mono (hDin D hD) hzD
  have hfront : frontier L ⊆ frontier U := by
    intro z hz
    by_contra hzU
    have hzL : z ∈ L := hLclosed.closure_eq ▸ hz.1
    obtain ⟨D, hD, hzD⟩ := mem_iUnion₂.mp hzL
    have hzC : z ∈ D := by
      by_contra hznot
      have hzfr : z ∈ frontier D := ⟨hzD, fun hi => hznot (interior_subset hi)⟩
      exact hzU ((hVprops D hD).2.2.2 hzfr)
    exact hz.2 (hDin D hD hzC)
  refine ⟨V, ?_, ?_, ?_⟩
  · intro D
    exact hVmem D
  · intro D hD
    exact hVprops D hD
  · dsimp only [L]
    exact ⟨hLcompact, hPL, hreg, hfront⟩

theorem eq_univ_of_isOpen_of_isCompact_connectedComponent
    {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {U : Set X} [LocallyConnectedSpace U] (hU : IsOpen U) (x : U)
    (hcompact : IsCompact (connectedComponent x)) : U = univ := by
  have hclopen : IsClopen ((Subtype.val : U → X) '' connectedComponent x) :=
    ⟨(hcompact.image continuous_subtype_val).isClosed,
      hU.isOpenMap_subtype_val _ isOpen_connectedComponent⟩
  have heq := hclopen.eq_univ ⟨x.val, x, mem_connectedComponent, rfl⟩
  apply eq_univ_of_forall
  intro y
  obtain ⟨z, _, hzy⟩ := Set.eq_univ_iff_forall.mp heq y
  exact hzy ▸ z.property


end DifferentialGeometry.Topology
