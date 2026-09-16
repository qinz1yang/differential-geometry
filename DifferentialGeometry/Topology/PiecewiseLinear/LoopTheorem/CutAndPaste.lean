import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut
import Mathlib.Tactic.Group

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace SingularTwoCell

universe u

private theorem connected_subset_left_or_right_of_closed_union
    {X : Type*} [TopologicalSpace X] {S U V I : Set X}
    (hS : IsConnected S) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : S ⊆ U ∪ V) (hinter : U ∩ V = I) (hdisjoint : Disjoint S I) :
    S ⊆ U ∨ S ⊆ V := by
  by_contra hside
  rw [not_or] at hside
  obtain ⟨x, hxS, hxU⟩ := Set.not_subset.mp hside.1
  obtain ⟨y, hyS, hyV⟩ := Set.not_subset.mp hside.2
  have hxV : x ∈ V := (hcover hxS).resolve_left hxU
  have hyU : y ∈ U := (hcover hyS).resolve_right hyV
  have hmeet := (isPreconnected_closed_iff.mp hS.isPreconnected)
    U V hU hV hcover ⟨y, hyS, hyU⟩ ⟨x, hxS, hxV⟩
  obtain ⟨z, hzS, hzU, hzV⟩ := hmeet
  exact Set.disjoint_left.mp hdisjoint hzS (hinter ▸ ⟨hzU, hzV⟩)

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

theorem exists_two_cells_with_second_crosscut
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hC : IsPLBall 1 C) (hdisjoint : Disjoint A C)
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hcutA : Schoenflies.IsCrosscut (frontier D.domain) A p q)
    (hcutC : Schoenflies.IsCrosscut (frontier D.domain) C r s) :
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
      ((C ⊆ D₁.domain ∧
          Schoenflies.IsCrosscut (frontier D₁.domain) C r s) ∨
        (C ⊆ D₂.domain ∧
          Schoenflies.IsCrosscut (frontier D₂.domain) C r s)) := by
  obtain ⟨D₁, D₂, hunion, hinter, hfront₁, hfront₂, hA₁, hA₂,
    htrace₁, htrace₂, hrange₁, hrange₂, hfun₁, hfun₂, -⟩ :=
    D.exists_two_cells_of_isCrosscut hA hcutA
  have hCD : C ⊆ D.domain := by
    intro x hx
    by_cases hxend : x ∈ ({r, s} : Set (EuclideanSpace ℝ (Fin 2)))
    · rcases hxend with rfl | rfl
      · exact D.frontier_subset_domain hcutC.left_mem
      · exact D.frontier_subset_domain hcutC.right_mem
    · exact interior_subset ((D.isPLBall_domain.interior_eq_inside_frontier.symm ▸
        hcutC.sdiff_subset ⟨hx, hxend⟩))
  have hCside : C ⊆ D₁.domain ∨ C ⊆ D₂.domain := by
    apply connected_subset_left_or_right_of_closed_union hC.isConnected
      D₁.isPLBall_domain.isPolyhedron.isClosed
      D₂.isPLBall_domain.isPolyhedron.isClosed
      (fun z hz => by rw [hunion]; exact hCD hz) hinter hdisjoint.symm
  refine ⟨D₁, D₂, hunion, hinter, hfront₁, hfront₂, hA₁, hA₂,
    htrace₁, htrace₂, hrange₁, hrange₂, hfun₁, hfun₂, ?_⟩
  rcases hCside with hC₁ | hC₂
  · exact Or.inl ⟨hC₁, isCrosscut_of_subset_side D.isPLBall_domain
      D₁.isPLBall_domain hcutC hC₁ hfront₁ hdisjoint.symm⟩
  · exact Or.inr ⟨hC₂, isCrosscut_of_subset_side D.isPLBall_domain
      D₂.isPLBall_domain hcutC hC₂ hfront₂ hdisjoint.symm⟩

private theorem exists_three_cells_of_nested_splits
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D O S Q R : SingularTwoCell M)
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hunionOS : O.domain ∪ S.domain = D.domain)
    (hinterOS : O.domain ∩ S.domain = A)
    (hunionQR : Q.domain ∪ R.domain = S.domain)
    (hinterQR : Q.domain ∩ R.domain = C)
    (hAO : A ⊆ O.domain) (hAQ : A ⊆ Q.domain)
    (hdisjoint : Disjoint A C)
    (hfunO : O.toFun = D.toFun) (hfunS : S.toFun = D.toFun)
    (hfunQ : Q.toFun = S.toFun) (hfunR : R.toFun = S.toFun) :
    ∃ D₁ D₂ D₃ : SingularTwoCell M,
      D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧
      D₂.domain ∩ D₃.domain = C ∧
      Disjoint D₁.domain D₃.domain ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun := by
  have hQS : Q.domain ⊆ S.domain := by
    intro x hx
    rw [← hunionQR]
    exact Or.inl hx
  have hRS : R.domain ⊆ S.domain := by
    intro x hx
    rw [← hunionQR]
    exact Or.inr hx
  refine ⟨O, Q, R, ?_, ?_, hinterQR, ?_, hfunO,
    hfunQ.trans hfunS, hfunR.trans hfunS⟩
  · rw [union_assoc, hunionQR, hunionOS]
  · apply Subset.antisymm
    · rintro x ⟨hxO, hxQ⟩
      exact hinterOS ▸ ⟨hxO, hQS hxQ⟩
    · intro x hxA
      exact ⟨hAO hxA, hAQ hxA⟩
  · rw [Set.disjoint_left]
    intro x hxO hxR
    have hxA : x ∈ A := hinterOS ▸ ⟨hxO, hRS hxR⟩
    have hxC : x ∈ C := hinterQR ▸ ⟨hAQ hxA, hxR⟩
    exact Set.disjoint_left.mp hdisjoint hxA hxC

theorem exists_three_cells_of_two_disjoint_crosscuts
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hC : IsPLBall 1 C) (hdisjoint : Disjoint A C)
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hcutA : Schoenflies.IsCrosscut (frontier D.domain) A p q)
    (hcutC : Schoenflies.IsCrosscut (frontier D.domain) C r s) :
    ∃ D₁ D₂ D₃ : SingularTwoCell M,
      D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧
      D₂.domain ∩ D₃.domain = C ∧
      Disjoint D₁.domain D₃.domain ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun := by
  obtain ⟨S₁, S₂, hunion, hinter, -, -, hA₁, hA₂, -, -, -, -,
    hfun₁, hfun₂, hCside⟩ :=
    D.exists_two_cells_with_second_crosscut hA hC hdisjoint hcutA hcutC
  have hA₁dom : A ⊆ S₁.domain := hA₁.trans S₁.frontier_subset_domain
  have hA₂dom : A ⊆ S₂.domain := hA₂.trans S₂.frontier_subset_domain
  rcases hCside with ⟨hCS₁, hcutCS₁⟩ | ⟨hCS₂, hcutCS₂⟩
  · obtain ⟨Q, R, hunionQR, hinterQR, -, -, -, -, -, -, -, -,
      hfunQ, hfunR, -⟩ := S₁.exists_two_cells_of_isCrosscut hC hcutCS₁
    have hAside : A ⊆ Q.domain ∨ A ⊆ R.domain := by
      apply connected_subset_left_or_right_of_closed_union hA.isConnected
        Q.isPLBall_domain.isPolyhedron.isClosed R.isPLBall_domain.isPolyhedron.isClosed
        (fun x hx => by rw [hunionQR]; exact hA₁dom hx) hinterQR hdisjoint
    have houter : S₂.domain ∩ S₁.domain = A := by
      rw [inter_comm]
      exact hinter
    rcases hAside with hAQ | hAR
    · exact exists_three_cells_of_nested_splits D S₂ S₁ Q R
        (by rw [union_comm]; exact hunion) houter hunionQR hinterQR hA₂dom hAQ
          hdisjoint hfun₂ hfun₁ hfunQ hfunR
    · exact exists_three_cells_of_nested_splits D S₂ S₁ R Q
        (by rw [union_comm]; exact hunion) houter
          (by rw [union_comm]; exact hunionQR)
          (by rw [inter_comm]; exact hinterQR) hA₂dom hAR hdisjoint
          hfun₂ hfun₁ hfunR hfunQ
  · obtain ⟨Q, R, hunionQR, hinterQR, -, -, -, -, -, -, -, -,
      hfunQ, hfunR, -⟩ := S₂.exists_two_cells_of_isCrosscut hC hcutCS₂
    have hAside : A ⊆ Q.domain ∨ A ⊆ R.domain := by
      apply connected_subset_left_or_right_of_closed_union hA.isConnected
        Q.isPLBall_domain.isPolyhedron.isClosed R.isPLBall_domain.isPolyhedron.isClosed
        (fun x hx => by rw [hunionQR]; exact hA₂dom hx) hinterQR hdisjoint
    rcases hAside with hAQ | hAR
    · exact exists_three_cells_of_nested_splits D S₁ S₂ Q R
        hunion hinter hunionQR hinterQR hA₁dom hAQ hdisjoint
          hfun₁ hfun₂ hfunQ hfunR
    · exact exists_three_cells_of_nested_splits D S₁ S₂ R Q
        hunion hinter (by rw [union_comm]; exact hunionQR)
          (by rw [inter_comm]; exact hinterQR) hA₁dom hAR hdisjoint
          hfun₁ hfun₂ hfunR hfunQ

end SingularTwoCell

universe u

namespace NormalSingularCellData

open Classical in
theorem exists_three_cells_of_boundaryBranch
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c)
    (hboundaryCrossing : ∀ y ∈ doublePointSet D D.domain ∩ BdM,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        ∃ N : Set (EuclideanSpace ℝ (Fin 3)),
          HasPLBoundaryDoubleCrossingAt (e ∘ D)
            (D.domain ∩ D ⁻¹' e.source) N (e y)) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      ∃ D₁ D₂ D₃ : SingularTwoCell M,
        D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
        D₁.domain ∩ D₂.domain = A ∧
        D₂.domain ∩ D₃.domain = C ∧
        Disjoint D₁.domain D₃.domain ∧
        D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, ⟨p, q, hcutA⟩,
    r, s, hcutC⟩ :=
    hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch hc hboundaryCrossing
  obtain ⟨D₁, D₂, D₃, hunion, hinter₁, hinter₂, hdisjoint₁₃,
    hfun₁, hfun₂, hfun₃⟩ :=
    D.exists_three_cells_of_two_disjoint_crosscuts hA hC hdisjoint hcutA hcutC
  exact ⟨A, C, hA, hC, hdisjoint, hcover, D₁, D₂, D₃, hunion,
    hinter₁, hinter₂, hdisjoint₁₃, hfun₁, hfun₂, hfun₃⟩

end NormalSingularCellData

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
