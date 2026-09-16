import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing
import DifferentialGeometry.External.Schoenflies.BoundaryContinuity2
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

private theorem isCutPair_frontier_side_of_isCrosscut
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D U : SingularTwoCell M) {A : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCrosscut (frontier D.domain) A p q)
    (hfront : frontier U.domain = (U.domain ∩ frontier D.domain) ∪ A)
    (hAfront : A ⊆ frontier U.domain) :
    Schoenflies.IsCutPair (frontier U.domain) p q A
      (U.domain ∩ frontier D.domain) := by
  obtain ⟨R, hpair, -, -⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere U.isPLSphere_frontier
      hcut.arc hAfront
  have hp : p ∈ U.domain ∩ frontier D.domain :=
    ⟨U.frontier_subset_domain (hAfront hcut.arc.left_mem), hcut.left_mem⟩
  have hq : q ∈ U.domain ∩ frontier D.domain :=
    ⟨U.frontier_subset_domain (hAfront hcut.arc.right_mem), hcut.right_mem⟩
  have hR : R = U.domain ∩ frontier D.domain := by
    apply Subset.antisymm
    · intro x hxR
      have hxfront := hpair.snd_subset hxR
      rw [hfront] at hxfront
      rcases hxfront with hx | hxA
      · exact hx
      · have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hpair.inter_eq.subset ⟨hxA, hxR⟩
        rcases hxpair with rfl | rfl
        · exact hp
        · exact hq
    · intro x hx
      have hxfront : x ∈ frontier U.domain :=
        hfront.symm.subset (Or.inl hx)
      have hxunion : x ∈ A ∪ R := hpair.union_eq.symm.subset hxfront
      rcases hxunion with hxA | hxR
      · have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hcut.inter_eq.subset ⟨hxA, hx.2⟩
        rcases hxpair with rfl | rfl
        · exact hpair.snd.left_mem
        · exact hpair.snd.right_mem
      · exact hxR
  rw [hR] at hpair
  exact hpair

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
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hcutA : Schoenflies.IsCrosscut (frontier D.domain) A p q)
    (hcutC : Schoenflies.IsCrosscut (frontier D.domain) C r s)
    (hunionOS : O.domain ∪ S.domain = D.domain)
    (hinterOS : O.domain ∩ S.domain = A)
    (hunionQR : Q.domain ∪ R.domain = S.domain)
    (hinterQR : Q.domain ∩ R.domain = C)
    (hfrontO : frontier O.domain = (O.domain ∩ frontier D.domain) ∪ A)
    (hfrontS : frontier S.domain = (S.domain ∩ frontier D.domain) ∪ A)
    (hfrontR : frontier R.domain = (R.domain ∩ frontier S.domain) ∪ C)
    (htraceO : IsPLBall 1 (O.domain ∩ frontier D.domain))
    (htraceR : IsPLBall 1 (R.domain ∩ frontier S.domain))
    (hAO : A ⊆ O.domain) (hAQ : A ⊆ Q.domain)
    (hAfrontO : A ⊆ frontier O.domain) (hAfrontS : A ⊆ frontier S.domain)
    (hCfrontQ : C ⊆ frontier Q.domain) (hCfrontR : C ⊆ frontier R.domain)
    (hdisjoint : Disjoint A C)
    (hfunO : O.toFun = D.toFun) (hfunS : S.toFun = D.toFun)
    (hfunQ : Q.toFun = S.toFun) (hfunR : R.toFun = S.toFun) :
    ∃ D₁ D₂ D₃ : SingularTwoCell M,
      D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧
      D₂.domain ∩ D₃.domain = C ∧
      A ⊆ frontier D₁.domain ∧ A ⊆ frontier D₂.domain ∧
      C ⊆ frontier D₂.domain ∧ C ⊆ frontier D₃.domain ∧
      Disjoint D₁.domain D₃.domain ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun ∧
      IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
      IsPLBall 1 (D₃.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₁.domain) p q A
        (D₁.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₃.domain) r s C
        (D₃.domain ∩ frontier D.domain) := by
  have hQS : Q.domain ⊆ S.domain := by
    intro x hx
    rw [← hunionQR]
    exact Or.inl hx
  have hRS : R.domain ⊆ S.domain := by
    intro x hx
    rw [← hunionQR]
    exact Or.inr hx
  have hSD : S.domain ⊆ D.domain := by
    intro x hx
    rw [← hunionOS]
    exact Or.inr hx
  have hAfrontQ : A ⊆ frontier Q.domain := by
    intro x hxA
    apply (mem_frontier_iff_notMem_interior (hAQ hxA)).mpr
    intro hxQ
    exact (mem_frontier_iff_notMem_interior
      (S.frontier_subset_domain (hAfrontS hxA))).mp (hAfrontS hxA) (interior_mono hQS hxQ)
  have hcover : O.domain ∪ Q.domain ∪ R.domain = D.domain := by
    rw [union_assoc, hunionQR, hunionOS]
  have hinterOQ : O.domain ∩ Q.domain = A := by
    apply Subset.antisymm
    · rintro x ⟨hxO, hxQ⟩
      exact hinterOS ▸ ⟨hxO, hQS hxQ⟩
    · intro x hxA
      exact ⟨hAO hxA, hAQ hxA⟩
  have houter : Disjoint O.domain R.domain := by
    rw [Set.disjoint_left]
    intro x hxO hxR
    have hxA : x ∈ A := hinterOS ▸ ⟨hxO, hRS hxR⟩
    have hxC : x ∈ C := hinterQR ▸ ⟨hAQ hxA, hxR⟩
    exact Set.disjoint_left.mp hdisjoint hxA hxC
  have htraceEq : R.domain ∩ frontier S.domain =
      R.domain ∩ frontier D.domain := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxfrontS⟩
      rw [hfrontS] at hxfrontS
      rcases hxfrontS with hx | hxA
      · exact ⟨hxR, hx.2⟩
      · exact (Set.disjoint_left.mp houter (hAO hxA) hxR).elim
    · rintro x ⟨hxR, hxfrontD⟩
      have hxS : x ∈ S.domain := hRS hxR
      refine ⟨hxR, (mem_frontier_iff_notMem_interior hxS).mpr ?_⟩
      intro hxintS
      exact (mem_frontier_iff_notMem_interior (hSD hxS)).mp hxfrontD
        (interior_mono hSD hxintS)
  have hfrontR' : frontier R.domain = (R.domain ∩ frontier D.domain) ∪ C := by
    rw [hfrontR, htraceEq]
  have htraceR' : IsPLBall 1 (R.domain ∩ frontier D.domain) := by
    rw [← htraceEq]
    exact htraceR
  have hcutO := isCutPair_frontier_side_of_isCrosscut D O hcutA hfrontO hAfrontO
  have hcutR := isCutPair_frontier_side_of_isCrosscut D R hcutC hfrontR' hCfrontR
  exact ⟨O, Q, R, hcover, hinterOQ, hinterQR, hAfrontO, hAfrontQ,
    hCfrontQ, hCfrontR, houter, hfunO, hfunQ.trans hfunS, hfunR.trans hfunS,
    htraceO, htraceR', hcutO, hcutR⟩

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
      A ⊆ frontier D₁.domain ∧ A ⊆ frontier D₂.domain ∧
      C ⊆ frontier D₂.domain ∧ C ⊆ frontier D₃.domain ∧
      Disjoint D₁.domain D₃.domain ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun ∧
      IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
      IsPLBall 1 (D₃.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₁.domain) p q A
        (D₁.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₃.domain) r s C
        (D₃.domain ∩ frontier D.domain) := by
  obtain ⟨S₁, S₂, hunion, hinter, hfront₁, hfront₂, hA₁, hA₂,
    htrace₁, htrace₂, -, -,
    hfun₁, hfun₂, hCside⟩ :=
    D.exists_two_cells_with_second_crosscut hA hC hdisjoint hcutA hcutC
  have hA₁dom : A ⊆ S₁.domain := hA₁.trans S₁.frontier_subset_domain
  have hA₂dom : A ⊆ S₂.domain := hA₂.trans S₂.frontier_subset_domain
  rcases hCside with ⟨hCS₁, hcutCS₁⟩ | ⟨hCS₂, hcutCS₂⟩
  · obtain ⟨Q, R, hunionQR, hinterQR, hfrontQ, hfrontR, hCQ, hCR,
      htraceQ, htraceR, -, -,
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
        hcutA hcutC (by rw [union_comm]; exact hunion) houter hunionQR hinterQR
          hfront₂ hfront₁ hfrontR htrace₂ htraceR hA₂dom hAQ
          hA₂ hA₁ hCQ hCR hdisjoint hfun₂ hfun₁ hfunQ hfunR
    · exact exists_three_cells_of_nested_splits D S₂ S₁ R Q
        hcutA hcutC (by rw [union_comm]; exact hunion) houter
          (by rw [union_comm]; exact hunionQR)
          (by rw [inter_comm]; exact hinterQR) hfront₂ hfront₁ hfrontQ
          htrace₂ htraceQ hA₂dom hAR
          hA₂ hA₁ hCR hCQ hdisjoint hfun₂ hfun₁ hfunR hfunQ
  · obtain ⟨Q, R, hunionQR, hinterQR, hfrontQ, hfrontR, hCQ, hCR,
      htraceQ, htraceR, -, -,
      hfunQ, hfunR, -⟩ := S₂.exists_two_cells_of_isCrosscut hC hcutCS₂
    have hAside : A ⊆ Q.domain ∨ A ⊆ R.domain := by
      apply connected_subset_left_or_right_of_closed_union hA.isConnected
        Q.isPLBall_domain.isPolyhedron.isClosed R.isPLBall_domain.isPolyhedron.isClosed
        (fun x hx => by rw [hunionQR]; exact hA₂dom hx) hinterQR hdisjoint
    rcases hAside with hAQ | hAR
    · exact exists_three_cells_of_nested_splits D S₁ S₂ Q R
        hcutA hcutC hunion hinter hunionQR hinterQR hfront₁ hfront₂ hfrontR
          htrace₁ htraceR hA₁dom hAQ
          hA₁ hA₂ hCQ hCR hdisjoint hfun₁ hfun₂ hfunQ hfunR
    · exact exists_three_cells_of_nested_splits D S₁ S₂ R Q
        hcutA hcutC hunion hinter (by rw [union_comm]; exact hunionQR)
          (by rw [inter_comm]; exact hinterQR) hfront₁ hfront₂ hfrontQ
          htrace₁ htraceQ hA₁dom hAR
          hA₁ hA₂ hCR hCQ hdisjoint hfun₁ hfun₂ hfunR hfunQ

end SingularTwoCell

universe u

namespace NormalSingularCellData

open Classical in
theorem exists_three_cells_of_boundaryBranch
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      ∃ p q r s : EuclideanSpace ℝ (Fin 2),
      ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
        IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A ∧
        ∃ D₁ D₂ D₃ : SingularTwoCell M,
        D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
        D₁.domain ∩ D₂.domain = A ∧
        D₂.domain ∩ D₃.domain = C ∧
        A ⊆ frontier D₁.domain ∧ A ⊆ frontier D₂.domain ∧
        C ⊆ frontier D₂.domain ∧ C ⊆ frontier D₃.domain ∧
        Disjoint D₁.domain D₃.domain ∧
        D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun ∧
        IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
        IsPLBall 1 (D₃.domain ∩ frontier D.domain) ∧
        Schoenflies.IsCutPair (frontier D₁.domain) p q A
          (D₁.domain ∩ frontier D.domain) ∧
        Schoenflies.IsCutPair (frontier D₃.domain) r s C
          (D₃.domain ∩ frontier D.domain) := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, -, -, ⟨g, hg, hcompat⟩,
    ⟨p, q, hcutA⟩, r, s, hcutC⟩ :=
    hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate
      hc
  obtain ⟨D₁, D₂, D₃, hunion, hinter₁, hinter₂,
    hA₁, hA₂, hC₂, hC₃, hdisjoint₁₃,
    hfun₁, hfun₂, hfun₃, htrace₁, htrace₃, hcut₁, hcut₃⟩ :=
    D.exists_three_cells_of_two_disjoint_crosscuts hA hC hdisjoint hcutA hcutC
  exact ⟨A, C, hA, hC, hdisjoint, hcover, p, q, r, s, g, hg, hcompat,
    D₁, D₂, D₃, hunion,
    hinter₁, hinter₂, hA₁, hA₂, hC₂, hC₃,
    hdisjoint₁₃, hfun₁, hfun₂, hfun₃,
    htrace₁, htrace₃, hcut₁, hcut₃⟩

open Classical in
theorem exists_boundary_surgery_cell_of_boundaryBranch
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C U V : Set (EuclideanSpace ℝ (Fin 2)),
    ∃ p q r s : EuclideanSpace ℝ (Fin 2),
    ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    ∃ G : SingularTwoCell M,
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      IsPLBall 1 U ∧ IsPLBall 1 V ∧ Disjoint U V ∧
      IsPLHomeomorphOn g A C ∧
      ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
      G '' G.domain ⊆ D '' D.domain ∧
      Set.range G.boundary = D '' (U ∪ V) ∧
      Set.range G.boundary ⊆ B ∧ G '' G.domain ∩ BdM ⊆ B := by
  obtain ⟨A, C, hA, hC, hAC, hcover, p, q, r, s, g, hg, hcompat,
    D₁, D₂, D₃, hdomains, -, -, hA₁, -, -, hC₃, hdisjoint₁₃,
    hfun₁, -, hfun₃, htrace₁, htrace₃, hcut₁, hcut₃⟩ :=
    hD.exists_three_cells_of_boundaryBranch hc
  have hcompat₁₃ : EqOn D₁ (D₃ ∘ g) A := by
    intro x hx
    change D₁.toFun x = D₃.toFun (g x)
    rw [hfun₁, hfun₃]
    exact hcompat hx
  obtain ⟨G, P, Q, f₁, f₃, hP, hQ, -, hGdomain, -, -, -, hf₁, hf₃, -,
    hf₁seam, hf₃seam, hG₁, hG₃, a, b, R, T, hcutP, hcutQ, -, -, hfrontG,
    hf₁a, hf₁b, hf₃a, hf₃b⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA hcut₁.fst hA₁ hg hC₃
      hcompat₁₃
  have horientation :=
    IsPLHomeomorphOn.maps_arc_endpoints hA hC hcut₁.fst hcut₃.fst hg
  have hf₁front : IsPLHomeomorphOn f₁ (frontier P) (frontier D₁.domain) := by
    rw [← hf₁.image_frontier (by simp) hP.isPolyhedron.isClosed
      D₁.isPLBall_domain.isPolyhedron.isClosed]
    exact hf₁.restrict hP.isPLSphere_frontier.isPolyhedron
      hP.isPolyhedron.isClosed.frontier_subset
  have hf₃front : IsPLHomeomorphOn f₃ (frontier Q) (frontier D₃.domain) := by
    rw [← hf₃.image_frontier (by simp) hQ.isPolyhedron.isClosed
      D₃.isPLBall_domain.isPolyhedron.isClosed]
    exact hf₃.restrict hQ.isPLSphere_frontier.isPolyhedron
      hQ.isPolyhedron.isClosed.frontier_subset
  have hcutR := hcutP.image hf₁front.isPiecewiseAffineOn.continuousOn
    hf₁front.bijOn.injOn
  rw [hf₁front.image_eq, hf₁seam, hf₁a, hf₁b] at hcutR
  have hRimage : f₁ '' R = D₁.domain ∩ frontier D.domain := by
    rcases DifferentialGeometry.Topology.PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair
      hcut₁ hcutR.snd hcutR.snd_subset with hbad | hgood
    · exact (hcutR.ne hbad.symm).elim
    · exact hgood
  have hcutT := hcutQ.image hf₃front.isPiecewiseAffineOn.continuousOn
    hf₃front.bijOn.injOn
  rw [hf₃front.image_eq, hf₃seam] at hcutT
  have hcut₃' : Schoenflies.IsCutPair (frontier D₃.domain) (f₃ a) (f₃ b) C
      (D₃.domain ∩ frontier D.domain) := by
    rcases horientation with horientation | horientation
    · simpa only [hf₃a, hf₃b, horientation.1, horientation.2] using hcut₃
    · have hrev : Schoenflies.IsCutPair (frontier D₃.domain) s r C
          (D₃.domain ∩ frontier D.domain) :=
        ⟨hcut₃.fst.reverse, hcut₃.snd.reverse, hcut₃.union_eq, by
          rw [hcut₃.inter_eq, pair_comm]⟩
      simpa only [hf₃a, hf₃b, horientation.1, horientation.2] using hrev
  have hTimage : f₃ '' T = D₃.domain ∩ frontier D.domain := by
    rcases DifferentialGeometry.Topology.PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair
      hcut₃' hcutT.snd hcutT.snd_subset with hbad | hgood
    · exact (hcutT.ne hbad.symm).elim
    · exact hgood
  have hRsubP : R ⊆ P :=
    hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hTsubQ : T ⊆ Q :=
    hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hGR : G '' R = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      G '' R = (D₁ ∘ f₁) '' R := Set.image_congr (hG₁.mono hRsubP)
      _ = D₁ '' (f₁ '' R) := image_comp D₁ f₁ R
      _ = D₁ '' (D₁.domain ∩ frontier D.domain) := congrArg (D₁ '' ·) hRimage
      _ = D '' (D₁.domain ∩ frontier D.domain) := by rw [hfun₁]
  have hGT : G '' T = D '' (D₃.domain ∩ frontier D.domain) := by
    calc
      G '' T = (D₃ ∘ f₃) '' T := Set.image_congr (hG₃.mono hTsubQ)
      _ = D₃ '' (f₃ '' T) := image_comp D₃ f₃ T
      _ = D₃ '' (D₃.domain ∩ frontier D.domain) := congrArg (D₃ '' ·) hTimage
      _ = D '' (D₃.domain ∩ frontier D.domain) := by rw [hfun₃]
  have hboundaryRange : Set.range G.boundary = G '' frontier G.domain := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hGimage : G '' G.domain ⊆ D '' D.domain := by
    rintro y ⟨x, hx, rfl⟩
    rw [hGdomain] at hx
    rcases hx with hxP | hxQ
    · refine ⟨f₁ x, ?_, ?_⟩
      · have hxD₁ := hf₁.bijOn.mapsTo hxP
        rw [← hdomains]
        exact Or.inl (Or.inl hxD₁)
      · rw [← hfun₁]
        exact (hG₁ hxP).symm
    · refine ⟨f₃ x, ?_, ?_⟩
      · have hxD₃ := hf₃.bijOn.mapsTo hxQ
        rw [← hdomains]
        exact Or.inr hxD₃
      · rw [← hfun₃]
        exact (hG₃ hxQ).symm
  have hrange : Set.range G.boundary =
      D '' ((D₁.domain ∩ frontier D.domain) ∪
        (D₃.domain ∩ frontier D.domain)) := by
    calc
      Set.range G.boundary = G '' frontier G.domain := hboundaryRange
      _ = G '' (R ∪ T) := congrArg (G '' ·) hfrontG
      _ = G '' R ∪ G '' T := image_union G R T
      _ = D '' (D₁.domain ∩ frontier D.domain) ∪
          D '' (D₃.domain ∩ frontier D.domain) := congrArg₂ (· ∪ ·) hGR hGT
      _ = D '' ((D₁.domain ∩ frontier D.domain) ∪
          (D₃.domain ∩ frontier D.domain)) := (image_union D _ _).symm
  have hrangeB : Set.range G.boundary ⊆ B := by
    rw [hrange]
    rintro y ⟨x, hx, rfl⟩
    apply hD.boundary_image_subset
    exact ⟨⟨x, hx.elim And.right And.right⟩, rfl⟩
  have hinterB : G '' G.domain ∩ BdM ⊆ B := by
    intro y hy
    have hyD : y ∈ D '' D.domain := hGimage hy.1
    apply hD.boundary_image_subset
    rw [← hD.image_inter_boundary]
    exact ⟨hyD, hy.2⟩
  exact ⟨A, C, D₁.domain ∩ frontier D.domain,
    D₃.domain ∩ frontier D.domain, p, q, r, s, g, G,
    hA, hC, hAC, hcover, htrace₁, htrace₃,
    hdisjoint₁₃.mono inter_subset_left inter_subset_left, hg, horientation,
    hGimage, hrange, hrangeB, hinterB⟩

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
