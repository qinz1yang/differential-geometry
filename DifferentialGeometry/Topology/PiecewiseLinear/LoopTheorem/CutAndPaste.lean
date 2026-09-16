import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import Mathlib.Tactic.Group

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace SingularTwoCell

universe u

theorem exists_two_cells_of_isCrosscut
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) {p q : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCrosscut (frontier D.domain) A p q) :
    ∃ D₁ D₂ : SingularTwoCell M,
      D₁.domain ∪ D₂.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧
      frontier D₁.domain = (D₁.domain ∩ frontier D.domain) ∪ A ∧
      frontier D₂.domain = (D₂.domain ∩ frontier D.domain) ∪ A ∧
      A ⊆ frontier D₁.domain ∧
      A ⊆ frontier D₂.domain ∧
      IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
      IsPLBall 1 (D₂.domain ∩ frontier D.domain) ∧
      Set.range D₁.boundary =
        D '' (D₁.domain ∩ frontier D.domain) ∪ D '' A ∧
      Set.range D₂.boundary =
        D '' (D₂.domain ∩ frontier D.domain) ∪ D '' A ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 C → C ⊆ D.domain →
        Disjoint (interior C) A → C ⊆ D₁.domain ∨ C ⊆ D₂.domain := by
  obtain ⟨U, V, hU, hV, hunion, hinter, hfrontU, hfrontV, hAU, hAV,
    htraceU, htraceV, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut D.isPLBall_domain hA hcut
  have hUD : U ⊆ D.domain := hunion ▸ subset_union_left
  have hVD : V ⊆ D.domain := hunion ▸ subset_union_right
  have htraceUSub : U ∩ frontier D.domain ⊆ frontier U := by
    intro x hx
    apply (mem_frontier_iff_notMem_interior hx.1).mpr
    intro hxint
    exact (mem_frontier_iff_notMem_interior (hUD hx.1)).mp hx.2
      (interior_mono hUD hxint)
  have htraceVSub : V ∩ frontier D.domain ⊆ frontier V := by
    intro x hx
    apply (mem_frontier_iff_notMem_interior hx.1).mpr
    intro hxint
    exact (mem_frontier_iff_notMem_interior (hVD hx.1)).mp hx.2
      (interior_mono hVD hxint)
  have hfrontUSub : frontier U ⊆ (U ∩ frontier D.domain) ∪ A := by
    intro x hx
    rcases hfrontU hx with hxD | hxA
    · exact Or.inl ⟨hU.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
    · exact Or.inr hxA
  have hfrontVSub : frontier V ⊆ (V ∩ frontier D.domain) ∪ A := by
    intro x hx
    rcases hfrontV hx with hxD | hxA
    · exact Or.inl ⟨hV.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
    · exact Or.inr hxA
  have hfrontUEq : frontier U = (U ∩ frontier D.domain) ∪ A :=
    Subset.antisymm hfrontUSub (union_subset htraceUSub hAU)
  have hfrontVEq : frontier V = (V ∩ frontier D.domain) ∪ A :=
    Subset.antisymm hfrontVSub (union_subset htraceVSub hAV)
  let D₁ := D.restrict hU hUD
  let D₂ := D.restrict hV hVD
  refine ⟨D₁, D₂, hunion, hinter, hfrontUEq, hfrontVEq, hAU, hAV,
    htraceU, htraceV, ?_, ?_, rfl, rfl, hside⟩
  · change Set.range (D.restrict hU hUD).boundary =
      D '' (U ∩ frontier D.domain) ∪ D '' A
    rw [D.range_boundary_restrict hU hUD, hfrontUEq, image_union]
  · change Set.range (D.restrict hV hVD).boundary =
      D '' (V ∩ frontier D.domain) ∪ D '' A
    rw [D.range_boundary_restrict hV hVD, hfrontVEq, image_union]

end SingularTwoCell

universe u

open Classical in
theorem loopRepresentativeAlong_mem_iff_loopClassMeets
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (L : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (q : Path x (L 0)) :
    loopRepresentativeAlong q (⟨L, rfl⟩ : basedCircleLoop (L 0)) ∈ N ↔
      loopClassMeets L x N := by
  let l := loopRepresentativeAlong q (⟨L, rfl⟩ : basedCircleLoop (L 0))
  have hclass : FreeLoop.conjugacyClass L x = ConjClasses.mk l :=
    FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q
      (⟨L, rfl⟩ : basedCircleLoop (L 0))
  have hl : l ∈ (FreeLoop.conjugacyClass L x).carrier := by
    rw [hclass]
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl
  constructor
  · intro hlN
    exact ⟨l, hl, hlN⟩
  · intro hmeet
    exact ((conjugacyClassMeets_iff_carrier_subset
      (FreeLoop.conjugacyClass L x) N).mp hmeet) hl

open Classical in
theorem not_loopClassMeets_iff_loopRepresentativeAlong_not_mem
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (L : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (q : Path x (L 0)) :
    ¬loopClassMeets L x N ↔
      loopRepresentativeAlong q (⟨L, rfl⟩ : basedCircleLoop (L 0)) ∉ N :=
  (not_congr (loopRepresentativeAlong_mem_iff_loopClassMeets L x N q)).symm

theorem not_mem_or_not_mem_of_eq_mul_conj_mul_conj
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x y : G}
    (hl : l = a * (x * b * x⁻¹) * (y * a⁻¹ * y⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem
    (N.mul_mem ha (‹N.Normal›.conj_mem b hb x))
    (‹N.Normal›.conj_mem a⁻¹ (N.inv_mem ha) y)

theorem not_mem_or_not_mem_of_eq_mul_conj_inv_mul
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x : G}
    (hl : l = a * (x * (b⁻¹ * a) * x⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem ha
    (‹N.Normal›.conj_mem (b⁻¹ * a) (N.mul_mem (N.inv_mem hb) ha) x)

open Classical in
theorem not_loopClassMeets_or_not_loopClassMeets_of_eq_mul_conj_mul_conj
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (L L₁ L₂ : freeLoop X)
    (q : Path x (L 0)) (q₁ : Path x (L₁ 0)) (q₂ : Path x (L₂ 0))
    (a b : FundamentalGroup X x)
    (hword :
      loopRepresentativeAlong q (⟨L, rfl⟩ : basedCircleLoop (L 0)) =
        loopRepresentativeAlong q₁ (⟨L₁, rfl⟩ : basedCircleLoop (L₁ 0)) *
          (a * loopRepresentativeAlong q₂
            (⟨L₂, rfl⟩ : basedCircleLoop (L₂ 0)) * a⁻¹) *
          (b * (loopRepresentativeAlong q₁
            (⟨L₁, rfl⟩ : basedCircleLoop (L₁ 0)))⁻¹ * b⁻¹))
    (hL : ¬loopClassMeets L x N) :
    ¬loopClassMeets L₁ x N ∨ ¬loopClassMeets L₂ x N := by
  have hrep : loopRepresentativeAlong q
      (⟨L, rfl⟩ : basedCircleLoop (L 0)) ∉ N :=
    (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem L x N q).mp hL
  have hsplit := not_mem_or_not_mem_of_eq_mul_conj_mul_conj N hword hrep
  exact hsplit.imp
    (fun h => (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem
      L₁ x N q₁).mpr h)
    (fun h => (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem
      L₂ x N q₂).mpr h)

theorem four_path_mul_conj_inv_mul_factorization
    {G : Type*} [Group G] (s t u p : G) :
    s * t * u * p =
      (s * u) * ((u⁻¹ * t * u) * ((s * t⁻¹ * u * p⁻¹)⁻¹ * (s * u)) *
        (u⁻¹ * t * u)⁻¹) := by
  group

theorem not_mem_or_not_mem_of_four_path_factorization
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {s t u p : G} (hN : s * t * u * p ∉ N) :
    s * u ∉ N ∨ s * t⁻¹ * u * p⁻¹ ∉ N := by
  apply not_mem_or_not_mem_of_eq_mul_conj_inv_mul N
    (four_path_mul_conj_inv_mul_factorization s t u p) hN

open Classical in
theorem not_loopClassMeets_or_not_loopClassMeets_of_four_path_factorization
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (L L₁ L₂ : freeLoop X)
    (q : Path x (L 0)) (q₁ : Path x (L₁ 0)) (q₂ : Path x (L₂ 0))
    (s t u p : FundamentalGroup X x)
    (hword :
      loopRepresentativeAlong q (⟨L, rfl⟩ : basedCircleLoop (L 0)) =
        s * t * u * p)
    (hword₁ :
      loopRepresentativeAlong q₁ (⟨L₁, rfl⟩ : basedCircleLoop (L₁ 0)) = s * u)
    (hword₂ :
      loopRepresentativeAlong q₂ (⟨L₂, rfl⟩ : basedCircleLoop (L₂ 0)) =
        s * t⁻¹ * u * p⁻¹)
    (hL : ¬loopClassMeets L x N) :
    ¬loopClassMeets L₁ x N ∨ ¬loopClassMeets L₂ x N := by
  have hrep : loopRepresentativeAlong q
      (⟨L, rfl⟩ : basedCircleLoop (L 0)) ∉ N :=
    (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem L x N q).mp hL
  have hproduct : s * t * u * p ∉ N := by
    rw [← hword]
    exact hrep
  have hsplit := not_mem_or_not_mem_of_four_path_factorization N hproduct
  exact hsplit.imp
    (fun h => (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem
      L₁ x N q₁).mpr (by rw [hword₁]; exact h))
    (fun h => (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem
      L₂ x N q₂).mpr (by rw [hword₂]; exact h))

end DifferentialGeometry.Topology.PiecewiseLinear
