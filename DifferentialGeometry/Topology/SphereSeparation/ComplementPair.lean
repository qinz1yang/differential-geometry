import DifferentialGeometry.Topology.SphereSeparation.Defs

set_option autoImplicit false

namespace Poincare.Topology.SphereSeparation

open Set

structure ComplementPair {X : Type*} [TopologicalSpace X] (S : Set X) where
  left : Set X
  right : Set X
  isOpen_left : IsOpen left
  isOpen_right : IsOpen right
  isConnected_left : IsConnected left
  isConnected_right : IsConnected right
  disjoint : Disjoint left right
  union_eq_compl : left ∪ right = Sᶜ

namespace ComplementPair

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem left_subset_compl (p : ComplementPair S) : p.left ⊆ Sᶜ := by
  rw [← p.union_eq_compl]
  exact subset_union_left

theorem right_subset_compl (p : ComplementPair S) : p.right ⊆ Sᶜ := by
  rw [← p.union_eq_compl]
  exact subset_union_right

theorem left_disjoint_sphere (p : ComplementPair S) : Disjoint p.left S := by
  rw [Set.disjoint_left]
  exact fun _ hx hS => p.left_subset_compl hx hS

theorem right_disjoint_sphere (p : ComplementPair S) : Disjoint p.right S := by
  rw [Set.disjoint_left]
  exact fun _ hx hS => p.right_subset_compl hx hS

theorem subset_left_or_subset_right (p : ComplementPair S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ) :
    C ⊆ p.left ∨ C ⊆ p.right := by
  apply hC.subset_or_subset p.isOpen_left p.isOpen_right p.disjoint
  simpa only [p.union_eq_compl] using hCS

theorem closure_left_eq (p : ComplementPair S) (hSleft : S ⊆ closure p.left) :
    closure p.left = p.left ∪ S := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxCompl : x ∈ Sᶜ := hxS
      rw [← p.union_eq_compl] at hxCompl
      rcases hxCompl with hxLeft | hxRight
      · exact Or.inl hxLeft
      · exact False.elim (Set.disjoint_left.1 (p.disjoint.closure_left p.isOpen_right) hx hxRight)
  · exact union_subset subset_closure hSleft


theorem closure_right_eq (p : ComplementPair S) (hSright : S ⊆ closure p.right) :
    closure p.right = p.right ∪ S := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxCompl : x ∈ Sᶜ := hxS
      rw [← p.union_eq_compl] at hxCompl
      rcases hxCompl with hxLeft | hxRight
      · exact False.elim
          (Set.disjoint_left.1 (p.disjoint.closure_right p.isOpen_left) hxLeft hx)
      · exact Or.inl hxRight
  · exact union_subset subset_closure hSright

theorem frontier_left_eq (p : ComplementPair S) (hSleft : S ⊆ closure p.left) :
    frontier p.left = S := by
  rw [p.isOpen_left.frontier_eq, p.closure_left_eq hSleft]
  ext x
  constructor
  · rintro ⟨hx, hxNotLeft⟩
    rcases hx with hxLeft | hxS
    · exact False.elim (hxNotLeft hxLeft)
    · exact hxS
  · intro hxS
    exact ⟨Or.inr hxS, fun hxLeft =>
      Set.disjoint_left.1 p.left_disjoint_sphere hxLeft hxS⟩

theorem frontier_right_eq (p : ComplementPair S) (hSright : S ⊆ closure p.right) :
    frontier p.right = S := by
  rw [p.isOpen_right.frontier_eq, p.closure_right_eq hSright]
  ext x
  constructor
  · rintro ⟨hx, hxNotRight⟩
    rcases hx with hxRight | hxS
    · exact False.elim (hxNotRight hxRight)
    · exact hxS
  · intro hxS
    exact ⟨Or.inr hxS, fun hxRight =>
      Set.disjoint_left.1 p.right_disjoint_sphere hxRight hxS⟩

theorem interior_closure_left_eq (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    interior (closure p.left) = p.left := by
  apply Set.Subset.antisymm
  · intro x hxInterior
    have hxClosure : x ∈ closure p.left := interior_subset hxInterior
    rw [p.closure_left_eq hSleft] at hxClosure
    rcases hxClosure with hxLeft | hxS
    · exact hxLeft
    · have hxRightClosure : x ∈ closure p.right := hSright hxS
      obtain ⟨y, hyInterior, hyRight⟩ :=
        mem_closure_iff.1 hxRightClosure (interior (closure p.left)) isOpen_interior hxInterior
      exact False.elim
        (Set.disjoint_left.1 (p.disjoint.closure_left p.isOpen_right)
          (interior_subset hyInterior) hyRight)
  · exact (subset_interior_iff_isOpen.2 p.isOpen_left).trans
      (interior_mono subset_closure)

theorem interior_closure_right_eq (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    interior (closure p.right) = p.right := by
  apply Set.Subset.antisymm
  · intro x hxInterior
    have hxClosure : x ∈ closure p.right := interior_subset hxInterior
    rw [p.closure_right_eq hSright] at hxClosure
    rcases hxClosure with hxRight | hxS
    · exact hxRight
    · have hxLeftClosure : x ∈ closure p.left := hSleft hxS
      obtain ⟨y, hyInterior, hyLeft⟩ :=
        mem_closure_iff.1 hxLeftClosure (interior (closure p.right)) isOpen_interior hxInterior
      exact False.elim
        (Set.disjoint_left.1 (p.disjoint.closure_right p.isOpen_left)
          hyLeft (interior_subset hyInterior))
  · exact (subset_interior_iff_isOpen.2 p.isOpen_right).trans
      (interior_mono subset_closure)

def toSphereSides (p : ComplementPair S)
    (hCompact : IsCompact (closure p.left))
    (hNoncompact : ¬ IsCompact (closure p.right))
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    SphereSides S where
  compactSide := p.left
  endSide := p.right
  isOpen_compactSide := p.isOpen_left
  isOpen_endSide := p.isOpen_right
  isConnected_compactSide := p.isConnected_left
  isConnected_endSide := p.isConnected_right
  disjoint := p.disjoint
  union_eq_compl := p.union_eq_compl
  isCompact_closure_compactSide := hCompact
  not_isCompact_closure_endSide := hNoncompact
  frontier_compactSide := p.frontier_left_eq hSleft
  frontier_endSide := p.frontier_right_eq hSright
  closure_compactSide := p.closure_left_eq hSleft
  closure_endSide := p.closure_right_eq hSright
  interior_closure_compactSide := p.interior_closure_left_eq hSleft hSright


def swap (p : ComplementPair S) : ComplementPair S where
  left := p.right
  right := p.left
  isOpen_left := p.isOpen_right
  isOpen_right := p.isOpen_left
  isConnected_left := p.isConnected_right
  isConnected_right := p.isConnected_left
  disjoint := p.disjoint.symm
  union_eq_compl := by rw [union_comm, p.union_eq_compl]

end ComplementPair

end Poincare.Topology.SphereSeparation
