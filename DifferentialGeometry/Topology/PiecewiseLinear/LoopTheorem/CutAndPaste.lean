import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin
import DifferentialGeometry.External.Schoenflies.BoundaryContinuity2
import Mathlib.Tactic.Group

open Set Topology

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

namespace NormalSingularSetTriangulation

open Classical in
theorem restrict_space_eq_inter_preimage_doublePointSet
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hclopen : IsClopen
      (((↑) : doublePointSet D D.domain → M) ⁻¹' doublePointSet G G.domain)) :
    (restrict T.complex
      (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space =
        T.complex.space ∩
          T.piece.piece.map ⁻¹' doublePointSet G G.domain := by
  let Q := T.piece.piece.map ⁻¹' doublePointSet G G.domain
  let L := restrict T.complex Q
  apply Subset.antisymm
  · intro x hx
    exact ⟨space_mono_of_faces_subset (restrict_faces_subset T.complex Q) hx,
      restrict_space_subset T.complex Q hx⟩
  · intro x hx
    rw [T.space_eq_iUnion_branchComplex] at hx
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hx.1
    have hcarrier : T.piece.piece.map x ∈ T.branchCarrier c := ⟨x, hxc, rfl⟩
    let y : doublePointSet D D.domain :=
      ⟨T.piece.piece.map x, T.branchCarrier_subset_doublePointSet c hcarrier⟩
    have hybranch : y ∈ T.branchSet c := hcarrier
    have hyG : y ∈
        ((↑) : doublePointSet D D.domain → M) ⁻¹' doublePointSet G G.domain := hx.2
    have hbranch : T.branchSet c ⊆
        ((↑) : doublePointSet D D.domain → M) ⁻¹' doublePointSet G G.domain :=
      (T.branchSet_isConnected c).isPreconnected.subset_isClopen hclopen
        ⟨y, hybranch, hyG⟩
    obtain ⟨s, hs, hxs⟩ := (T.branchComplex c).mem_space_iff.mp hxc
    apply L.convexHull_subset_space
    · refine ⟨T.branchComplex_faces_subset c hs, ?_⟩
      intro z hzs
      have hzcarrier : T.piece.piece.map z ∈ T.branchCarrier c :=
        ⟨z, (T.branchComplex c).convexHull_subset_space hs hzs, rfl⟩
      let w : doublePointSet D D.domain :=
        ⟨T.piece.piece.map z, T.branchCarrier_subset_doublePointSet c hzcarrier⟩
      have hwbranch : w ∈ T.branchSet c := hzcarrier
      exact hbranch hwbranch
    · exact hxs

theorem restrict_space_mem_nhdsWithin_doublePointSet
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hspace : (restrict T.complex
      (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space =
        T.complex.space ∩
          T.piece.piece.map ⁻¹' doublePointSet G G.domain)
    (hopen : ∀ y ∈ doublePointSet G G.domain,
      doublePointSet G G.domain ∈ 𝓝[doublePointSet D D.domain] y) :
    ∀ x ∈ (restrict T.complex
      (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space,
      (restrict T.complex
        (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space ∈
          𝓝[T.complex.space] x := by
  let Q := T.piece.piece.map ⁻¹' doublePointSet G G.domain
  let L := restrict T.complex Q
  intro x hx
  have hxold : x ∈ T.complex.space := (hspace.subset hx).1
  have hxG : T.piece.piece.map x ∈ doublePointSet G G.domain :=
    (hspace.subset hx).2
  have hmap : MapsTo T.piece.piece.map T.complex.space
      (doublePointSet D D.domain) := by
    intro z hz
    rw [← T.map_space]
    exact ⟨z, hz, rfl⟩
  have hpre : Q ∈ 𝓝[T.complex.space] x :=
    (T.piece.piece.continuousOn.mono
      (space_mono_of_faces_subset T.faces_subset) x hxold).tendsto_nhdsWithin hmap
        (hopen (T.piece.piece.map x) hxG)
  rw [hspace]
  exact Filter.inter_mem self_mem_nhdsWithin hpre

open Classical in
theorem isCombinatorialManifoldWithBoundary_restrict_of_space_mem_nhdsWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) (Q : Set E)
    (hnhds : ∀ x ∈ (restrict K Q).space,
      (restrict K Q).space ∈ 𝓝[K.space] x) :
    IsCombinatorialManifoldWithBoundary 1 (restrict K Q) := by
  intro x hx
  have hxL : x ∈ (restrict K Q).space := (restrict K Q).subset_space hx (by simp)
  have hlink := geometricLink_eq_of_space_mem_nhdsWithin
    (restrict_faces_subset K Q) (hnhds x hxL)
  rw [hlink]
  exact hK x (restrict_faces_subset K Q hx)

theorem map_restrict_space_eq_doublePointSet
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hsub : doublePointSet G G.domain ⊆ doublePointSet D D.domain)
    (hspace : (restrict T.complex
      (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space =
        T.complex.space ∩
          T.piece.piece.map ⁻¹' doublePointSet G G.domain) :
    T.piece.piece.map '' (restrict T.complex
      (T.piece.piece.map ⁻¹' doublePointSet G G.domain)).space =
        doublePointSet G G.domain := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (hspace.subset hx).2
  · intro y hy
    have hyold : y ∈ doublePointSet D D.domain := hsub hy
    rw [← T.map_space] at hyold
    obtain ⟨x, hx, rfl⟩ := hyold
    exact ⟨x, hspace.symm.subset ⟨hx, hy⟩, rfl⟩

open Classical in
theorem mem_boundaryComplex_one_space_iff_of_space_mem_nhdsWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (hL : IsCombinatorialManifoldWithBoundary 1 L) (hLK : L.space ⊆ K.space)
    {p : E} (hp : p ∈ L.space) (hnhds : L.space ∈ 𝓝[K.space] p) :
    p ∈ (boundaryComplex 1 L).space ↔ p ∈ (boundaryComplex 1 K).space := by
  exact mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 0)
    K L hK hL hLK hp hnhds

open Classical in
theorem map_boundaryComplex_eq_inter_of_space_mem_nhdsWithin
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (f : E → M) {oldS S BdM : Set M}
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (hL : IsCombinatorialManifoldWithBoundary 1 L) (hLK : L.space ⊆ K.space)
    (hnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[K.space] x)
    (hmapSpace : f '' L.space = S) (hSsub : S ⊆ oldS)
    (hmapBoundary : f '' (boundaryComplex 1 K).space = oldS ∩ BdM)
    (hinj : Set.InjOn f K.space) :
    f '' (boundaryComplex 1 L).space = S ∩ BdM := by
  have hboundary {x : E} (hx : x ∈ L.space) :
      x ∈ (boundaryComplex 1 L).space ↔ x ∈ (boundaryComplex 1 K).space :=
    mem_boundaryComplex_one_space_iff_of_space_mem_nhdsWithin
      hK hL hLK hx (hnhds x hx)
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxL : x ∈ L.space :=
      space_mono_of_faces_subset (boundaryComplex_faces_subset 1 L) hx
    have hxoldBoundary : x ∈ (boundaryComplex 1 K).space := (hboundary hxL).mp hx
    refine ⟨hmapSpace.subset ⟨x, hxL, rfl⟩, ?_⟩
    have himage : f x ∈ f '' (boundaryComplex 1 K).space :=
      ⟨x, hxoldBoundary, rfl⟩
    rw [hmapBoundary] at himage
    exact himage.2
  · intro y hy
    have hyimage : y ∈ f '' L.space := by
      rw [hmapSpace]
      exact hy.1
    obtain ⟨x, hxL, hxy⟩ := hyimage
    have hyoldBoundary : y ∈ f '' (boundaryComplex 1 K).space := by
      rw [hmapBoundary]
      exact ⟨hSsub hy.1, hy.2⟩
    obtain ⟨z, hzoldBoundary, hzy⟩ := hyoldBoundary
    have hzK : z ∈ K.space :=
      space_mono_of_faces_subset (boundaryComplex_faces_subset 1 K) hzoldBoundary
    have hzx : z = x := hinj hzK (hLK hxL) (hzy.trans hxy.symm)
    subst z
    exact ⟨x, (hboundary hxL).mpr hzoldBoundary, hxy⟩

open Classical in
private noncomputable def boundaryComplexOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) : Geometry.SimplicialComplex ℝ E :=
  boundaryComplex 1 K

open Classical in
private structure BoundaryComplexImage
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → M) (K : Geometry.SimplicialComplex ℝ E) (S BdM : Set M) : Prop where
  image_eq : f '' (boundaryComplexOne K).space = S ∩ BdM

open Classical in
private theorem boundaryComplexImage_of_space_mem_nhdsWithin
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (f : E → M) {oldS S BdM : Set M}
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (hL : IsCombinatorialManifoldWithBoundary 1 L) (hLK : L.space ⊆ K.space)
    (hnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[K.space] x)
    (hmapSpace : f '' L.space = S) (hSsub : S ⊆ oldS)
    (hmapBoundary : BoundaryComplexImage f K oldS BdM)
    (hinj : Set.InjOn f K.space) : BoundaryComplexImage f L S BdM :=
  ⟨map_boundaryComplex_eq_inter_of_space_mem_nhdsWithin f hK hL hLK hnhds
    hmapSpace hSsub hmapBoundary.image_eq hinj⟩

open Classical in
private noncomputable def singularBoundaryComplexModel
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM) :=
  boundaryComplex 1 T.complex

open Classical in
private theorem singularBoundaryComplexModel_image
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM) :
    T.piece.piece.map '' T.singularBoundaryComplexModel.space =
      doublePointSet D D.domain ∩ BdM :=
  T.map_boundary

private theorem singularBoundaryComplexModel_eq_boundaryComplexOne
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM) :
    T.singularBoundaryComplexModel = boundaryComplexOne T.complex := by
  unfold singularBoundaryComplexModel boundaryComplexOne
  exact congrArg
    (fun d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim)) =>
      @boundaryComplex (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _ d 1 T.complex)
    (Subsingleton.elim _ _)

open Classical in
private theorem boundaryComplexImage
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM) :
    BoundaryComplexImage T.piece.piece.map T.complex
      (doublePointSet D D.domain) BdM := by
  refine ⟨?_⟩
  rw [← T.singularBoundaryComplexModel_eq_boundaryComplexOne]
  exact T.singularBoundaryComplexModel_image

theorem isClopen_preimage_doublePointSet
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D G : SingularTwoCell M}
    (hcompact : IsCompact (doublePointSet G G.domain))
    (hopen : ∀ y ∈ doublePointSet G G.domain,
      doublePointSet G G.domain ∈ 𝓝[doublePointSet D D.domain] y) :
    IsClopen (((↑) : doublePointSet D D.domain → M) ⁻¹'
      doublePointSet G G.domain) := by
  have hopen' : IsOpen (((↑) : doublePointSet D D.domain → M) ⁻¹'
      doublePointSet G G.domain) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact preimage_coe_mem_nhds_subtype.mpr (hopen y hy)
  have hclosed : IsClosed (((↑) : doublePointSet D D.domain → M) ⁻¹'
      doublePointSet G G.domain) :=
    hcompact.isClosed.preimage continuous_subtype_val
  exact ⟨hclosed, hopen'⟩

open Classical in
private theorem boundaryComplexImage_subcomplex
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hsub : doublePointSet G G.domain ⊆ doublePointSet D D.domain)
    (L : Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin T.piece.ambientDim)))
    (hfinite : L.faces.Finite) (hfaces : L.faces ⊆ T.complex.faces)
    (hLnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[T.complex.space] x)
    (hLmanifold : IsCombinatorialManifoldWithBoundary 1 L)
    (hmapSpace : T.piece.piece.map '' L.space = doublePointSet G G.domain) :
    BoundaryComplexImage T.piece.piece.map L (doublePointSet G G.domain) BdM := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite L.faces := hfinite.to_subtype
  have hLsubset : L.space ⊆ T.complex.space :=
    space_mono_of_faces_subset hfaces
  have hmapBoundaryOld := T.boundaryComplexImage
  have hinj : Set.InjOn T.piece.piece.map T.complex.space := by
    intro x hx y hy hxy
    exact T.piece.piece.bijOn.injOn
      (space_mono_of_faces_subset T.faces_subset hx)
      (space_mono_of_faces_subset T.faces_subset hy) hxy
  exact boundaryComplexImage_of_space_mem_nhdsWithin
    (E := EuclideanSpace ℝ (Fin T.piece.ambientDim)) (M := M)
    (K := T.complex) (L := L) (oldS := doublePointSet D D.domain)
    (S := doublePointSet G G.domain) (BdM := BdM) T.piece.piece.map
    T.isManifoldWithBoundary hLmanifold hLsubset hLnhds hmapSpace hsub
    hmapBoundaryOld hinj

open Classical in
theorem exists_subcomplex_normalSingularSetTriangulation
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hsub : doublePointSet G G.domain ⊆ doublePointSet D D.domain)
    (L : Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin T.piece.ambientDim)))
    (hfinite : L.faces.Finite) (hfaces : L.faces ⊆ T.complex.faces)
    (hLnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[T.complex.space] x)
    (hLmanifold : IsCombinatorialManifoldWithBoundary 1 L)
    (hmapSpace : T.piece.piece.map '' L.space = doublePointSet G G.domain) :
    Nonempty (NormalSingularSetTriangulation G BdM) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite L.faces := hfinite.to_subtype
  have hmapBoundary := T.boundaryComplexImage_subcomplex hsub L hfinite hfaces
    hLnhds hLmanifold hmapSpace
  exact ⟨{
    carrier := T.carrier
    piece := T.piece
    complex := L
    finite_faces := hfinite
    faces_subset := hfaces.trans T.faces_subset
    isManifoldWithBoundary := hLmanifold
    map_space := hmapSpace
    map_boundary := by
      have hmodel : boundaryComplexOne L = boundaryComplex 1 L := by
        unfold boundaryComplexOne
        exact congrArg
          (fun d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim)) =>
            @boundaryComplex (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _ d 1 L)
          (Subsingleton.elim _ _)
      rw [← hmodel]
      exact hmapBoundary.image_eq }⟩

open Classical in
theorem restrict_to_clopen_doublePointSet
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D G : SingularTwoCell M} {BdM : Set M}
    (T : NormalSingularSetTriangulation D BdM)
    (hsub : doublePointSet G G.domain ⊆ doublePointSet D D.domain)
    (hcompact : IsCompact (doublePointSet G G.domain))
    (hopen : ∀ y ∈ doublePointSet G G.domain,
      doublePointSet G G.domain ∈ 𝓝[doublePointSet D D.domain] y) :
    Nonempty (NormalSingularSetTriangulation G BdM) := by
  let Q := T.piece.piece.map ⁻¹' doublePointSet G G.domain
  let L := restrict T.complex Q
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite L.faces := (restrict_faces_finite T.complex Q).to_subtype
  have hSclopen : IsClopen (((↑) : doublePointSet D D.domain → M) ⁻¹'
      doublePointSet G G.domain) := isClopen_preimage_doublePointSet hcompact hopen
  have hLspace : L.space = T.complex.space ∩ Q :=
    T.restrict_space_eq_inter_preimage_doublePointSet hSclopen
  have hLnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[T.complex.space] x :=
    T.restrict_space_mem_nhdsWithin_doublePointSet hLspace hopen
  have hLmanifold : IsCombinatorialManifoldWithBoundary 1 L :=
    isCombinatorialManifoldWithBoundary_restrict_of_space_mem_nhdsWithin
      T.isManifoldWithBoundary Q hLnhds
  have hmapSpace : T.piece.piece.map '' L.space = doublePointSet G G.domain :=
    T.map_restrict_space_eq_doublePointSet hsub hLspace
  exact T.exists_subcomplex_normalSingularSetTriangulation hsub L
    (restrict_faces_finite T.complex Q) (restrict_faces_subset T.complex Q)
    hLnhds hLmanifold hmapSpace

end NormalSingularSetTriangulation

open Classical in
theorem doublePointSet_mem_nhdsWithin_of_pullback
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {P O : Set X} {Q : Set Z} {S : Set Y} {f : X → Y} {g : Z → Y} {r : Z → X}
    (hP : IsCompact P) (hf : ContinuousOn f P)
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2)
    (hrP : MapsTo r Q P) (hrf : ∀ x ∈ Q, f (r x) = g x) (hrinj : InjOn r Q)
    (hrO : MapsTo r Q O)
    (hOnhds : ∀ x ∈ O, f x ∉ S → O ∈ 𝓝[P] x)
    (hlift : ∀ x ∈ O, f x ∉ S → ∃ z ∈ Q, r z = x)
    (hS : IsClosed S) (hdisjoint : Disjoint (doublePointSet g Q) S) :
    ∀ y ∈ doublePointSet g Q, doublePointSet g Q ∈ 𝓝[doublePointSet f P] y := by
  intro y hy
  have hyS : y ∉ S := fun hyS => Set.disjoint_left.mp hdisjoint hy hyS
  obtain ⟨a, ha, b, hb, hab, hga, hgb⟩ := hy
  have hrab : r a ≠ r b := fun h => hab (hrinj ha hb h)
  have hfa : f (r a) = y := (hrf a ha).trans hga
  have hfb : f (r b) = y := (hrf b hb).trans hgb
  have hfiber : P ∩ f ⁻¹' {y} = {r a, r b} :=
    fiber_eq_pair_of_encard_le_two f P (hrP ha) (hrP hb) hrab hfa hfb (hcard y)
  have hcover : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ O := by
    have h := eventually_preimage_subset_union_of_fiber_eq_pair f hP hf hfiber
      (hOnhds (r a) (hrO ha) (hfa ▸ hyS))
      (hOnhds (r b) (hrO hb) (hfb ▸ hyS))
    simpa only [union_self] using h
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨Sᶜ ∩ {z | P ∩ f ⁻¹' {z} ⊆ O},
    Filter.inter_mem (hS.isOpen_compl.mem_nhds hyS) hcover, ?_⟩
  rintro z ⟨hz, u, huP, v, hvP, huv, hfu, hfv⟩
  have huO : u ∈ O := hz.2 ⟨huP, hfu⟩
  have hvO : v ∈ O := hz.2 ⟨hvP, hfv⟩
  have hfuS : f u ∉ S := fun hmem => hz.1 (hfu ▸ hmem)
  have hfvS : f v ∉ S := fun hmem => hz.1 (hfv ▸ hmem)
  obtain ⟨u', hu'Q, hru⟩ := hlift u huO hfuS
  obtain ⟨v', hv'Q, hrv⟩ := hlift v hvO hfvS
  have hu'v' : u' ≠ v' := by
    intro huv'
    apply huv
    calc
      u = r u' := hru.symm
      _ = r v' := congrArg r huv'
      _ = v := hrv
  refine ⟨u', hu'Q, v', hv'Q, hu'v', ?_, ?_⟩
  · exact (hrf u' hu'Q).symm.trans ((congrArg f hru).trans hfu)
  · exact (hrf v' hv'Q).symm.trans ((congrArg f hrv).trans hfv)

namespace NormalSingularCellData

open Classical in
theorem fiber_subset_frontier_of_mem_image_inter_boundary
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) {y : M}
    (hy : y ∈ D '' D.domain ∩ BdM) :
    D.domain ∩ D ⁻¹' {y} ⊆ frontier D.domain := by
  intro x hx
  by_cases hdouble : y ∈ doublePointSet D D.domain
  · obtain ⟨e, -, hye, N, hcrossing⟩ :=
      hD.exists_boundary_crossing_chart ⟨hdouble, hy.2⟩
    exact hD.fiber_subset_frontier_of_boundary_crossing hye hcrossing hx
  · have hyrange : y ∈ Set.range D.boundary := hD.image_inter_boundary.subset hy
    obtain ⟨z, hz⟩ := hyrange
    have hzdomain : (z : EuclideanSpace ℝ (Fin 2)) ∈ D.domain :=
      D.frontier_subset_domain z.property
    have hxz : x = z := by
      by_contra hxz
      exact hdouble ⟨x, hx.1, z, hzdomain, hxz, hx.2, hz⟩
    exact hxz ▸ z.property

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
      IsPLHomeomorphOn (hD.branchCoordinate c) A
        (hD.singularSet.branchComplex c).space ∧
      IsPLHomeomorphOn (hD.branchCoordinate c) C
        (hD.singularSet.branchComplex c).space ∧
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
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, hAcoordinate, hCcoordinate, ⟨g, hg, hcompat⟩,
    ⟨p, q, hcutA⟩, r, s, hcutC⟩ :=
    hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate
      hc
  obtain ⟨D₁, D₂, D₃, hunion, hinter₁, hinter₂,
    hA₁, hA₂, hC₂, hC₃, hdisjoint₁₃,
    hfun₁, hfun₂, hfun₃, htrace₁, htrace₃, hcut₁, hcut₃⟩ :=
    D.exists_three_cells_of_two_disjoint_crosscuts hA hC hdisjoint hcutA hcutC
  exact ⟨A, C, hA, hC, hdisjoint, hcover, hAcoordinate, hCcoordinate,
    p, q, r, s, g, hg, hcompat,
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
      G '' G.domain ∩ BdM = Set.range G.boundary ∧
      Set.range G.boundary ⊆ B ∧ G '' G.domain ∩ BdM ⊆ B ∧
      (∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, Set.InjOn G W) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
      doublePointSet G G.domain ⊆ doublePointSet D D.domain ∧
      Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c) ∧
      Nonempty (NormalSingularSetTriangulation G BdM) := by
  obtain ⟨A, C, hA, hC, hAC, hcover, hAcoordinate, -, p, q, r, s, g, hg, hcompat,
    D₁, D₂, D₃, hdomains, hinter₁₂, hinter₂₃, hA₁, -, -, hC₃, hdisjoint₁₃,
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
  have hD₁sub : D₁.domain ⊆ D.domain := by
    intro x hx
    rw [← hdomains]
    exact Or.inl (Or.inl hx)
  have hD₃sub : D₃.domain ⊆ D.domain := by
    intro x hx
    rw [← hdomains]
    exact Or.inr hx
  let pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => if x ∈ P then f₁ x else f₃ x
  have hpullback_mem : MapsTo pullback G.domain D.domain := by
    intro x hx
    rw [hGdomain] at hx
    by_cases hxP : x ∈ P
    · change (if x ∈ P then f₁ x else f₃ x) ∈ D.domain
      rw [if_pos hxP]
      exact hD₁sub (hf₁.bijOn.mapsTo hxP)
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      change (if x ∈ P then f₁ x else f₃ x) ∈ D.domain
      rw [if_neg hxP]
      exact hD₃sub (hf₃.bijOn.mapsTo hxQ)
  have hpullback_apply : ∀ x ∈ G.domain, D (pullback x) = G x := by
    intro x hx
    rw [hGdomain] at hx
    by_cases hxP : x ∈ P
    · change D (if x ∈ P then f₁ x else f₃ x) = G x
      rw [if_pos hxP]
      exact (congrFun hfun₁ (f₁ x)).symm.trans (hG₁ hxP).symm
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      change D (if x ∈ P then f₁ x else f₃ x) = G x
      rw [if_neg hxP]
      exact (congrFun hfun₃ (f₃ x)).symm.trans (hG₃ hxQ).symm
  have hpullback_inj : InjOn pullback G.domain := by
    intro x hx y hy hxy
    rw [hGdomain] at hx hy
    by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
    · apply hf₁.bijOn.injOn hxP hyP
      simpa only [pullback, if_pos hxP, if_pos hyP] using hxy
    · have hyQ : y ∈ Q := hy.resolve_left hyP
      exfalso
      have hmaps : f₁ x = f₃ y := by
        simpa only [pullback, if_pos hxP, if_neg hyP] using hxy
      exact Set.disjoint_left.mp hdisjoint₁₃
        (hf₁.bijOn.mapsTo hxP) (hmaps ▸ hf₃.bijOn.mapsTo hyQ)
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      exfalso
      have hmaps : f₁ y = f₃ x := by
        simpa only [pullback, if_neg hxP, if_pos hyP] using hxy.symm
      exact Set.disjoint_left.mp hdisjoint₁₃
        (hf₁.bijOn.mapsTo hyP) (hmaps ▸ hf₃.bijOn.mapsTo hxQ)
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      have hyQ : y ∈ Q := hy.resolve_left hyP
      apply hf₃.bijOn.injOn hxQ hyQ
      simpa only [pullback, if_neg hxP, if_neg hyP] using hxy
  have hfiber : ∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2 := by
    intro y
    have hmaps : pullback '' (G.domain ∩ G ⁻¹' {y}) ⊆
        D.domain ∩ D ⁻¹' {y} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨hpullback_mem hx.1, ?_⟩
      change D (pullback x) = y
      exact (hpullback_apply x hx.1).trans hx.2
    calc
      (G.domain ∩ G ⁻¹' {y}).encard =
          (pullback '' (G.domain ∩ G ⁻¹' {y})).encard :=
        (hpullback_inj.mono inter_subset_left).encard_image.symm
      _ ≤ (D.domain ∩ D ⁻¹' {y}).encard := encard_le_encard hmaps
      _ ≤ 2 := hD.fiber_le_two y
  have hdouble : doublePointSet G G.domain ⊆ doublePointSet D D.domain := by
    rintro y ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    refine ⟨pullback x, hpullback_mem hx, pullback z, hpullback_mem hz, ?_, ?_, ?_⟩
    · intro h
      exact hxz (hpullback_inj hx hz h)
    · exact (hpullback_apply x hx).trans hxy
    · exact (hpullback_apply z hz).trans hzy
  have hAsub : A ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_left
  have hDinjA : InjOn D A := by
    intro x hx z hz hxz
    apply hAcoordinate.bijOn.injOn hx hz
    apply (hD.singularSet.branchPieceIn c).bijOn.injOn
      (hAcoordinate.bijOn.mapsTo hx) (hAcoordinate.bijOn.mapsTo hz)
    calc
      (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) = D x :=
        hD.branchPieceIn_map_branchCoordinate c (hAsub hx)
      _ = D z := hxz
      _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c z) :=
        (hD.branchPieceIn_map_branchCoordinate c (hAsub hz)).symm
  have hpullback_branch : ∀ {x}, x ∈ G.domain → pullback x ∈ A ∪ C →
      x ∈ P ∩ Q ∧ f₁ x ∈ A := by
    intro x hx hxbranch
    rw [hGdomain] at hx
    by_cases hxP : x ∈ P
    · have hxbranch' : f₁ x ∈ A ∪ C := by
        simpa only [pullback, if_pos hxP] using hxbranch
      rcases hxbranch' with hxA | hxC
      · have hximage : f₁ x ∈ f₁ '' (P ∩ Q) := hf₁seam.symm.subset hxA
        obtain ⟨w, hw, hwx⟩ := hximage
        have hxeq : x = w := hf₁.bijOn.injOn hxP hw.1 hwx.symm
        exact ⟨hxeq ▸ hw, hxA⟩
      · exact (Set.disjoint_left.mp hdisjoint₁₃
          (hf₁.bijOn.mapsTo hxP) (D₃.frontier_subset_domain (hC₃ hxC))).elim
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      have hxbranch' : f₃ x ∈ A ∪ C := by
        simpa only [pullback, if_neg hxP] using hxbranch
      rcases hxbranch' with hxA | hxC
      · exact (Set.disjoint_left.mp hdisjoint₁₃
          (D₁.frontier_subset_domain (hA₁ hxA)) (hf₃.bijOn.mapsTo hxQ)).elim
      · have hximage : f₃ x ∈ f₃ '' (P ∩ Q) := hf₃seam.symm.subset hxC
        obtain ⟨w, hw, hwx⟩ := hximage
        have hxeq : x = w := hf₃.bijOn.injOn hxQ hw.2 hwx.symm
        exact (hxP (hxeq ▸ hw.1)).elim
  have hremove : Disjoint (doublePointSet G G.domain)
      (hD.singularSet.branchCarrier c) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, z, hz, hxz, hxy, hzy⟩ hybranch
    have hxpre : pullback x ∈ hD.branchPreimage c := by
      refine ⟨hpullback_mem hx, ?_⟩
      change D (pullback x) ∈ hD.singularSet.branchCarrier c
      rw [hpullback_apply x hx, hxy]
      exact hybranch
    have hzpre : pullback z ∈ hD.branchPreimage c := by
      refine ⟨hpullback_mem hz, ?_⟩
      change D (pullback z) ∈ hD.singularSet.branchCarrier c
      rw [hpullback_apply z hz, hzy]
      exact hybranch
    rw [hcover] at hxpre hzpre
    obtain ⟨hxseam, hxA⟩ := hpullback_branch hx hxpre
    obtain ⟨hzseam, hzA⟩ := hpullback_branch hz hzpre
    apply hxz
    apply hf₁.bijOn.injOn hxseam.1 hzseam.1
    apply hDinjA hxA hzA
    calc
      D (f₁ x) = G x := (congrFun hfun₁ (f₁ x)).symm.trans (hG₁ hxseam.1).symm
      _ = y := hxy
      _ = G z := hzy.symm
      _ = D (f₁ z) := (hG₁ hzseam.1).trans (congrFun hfun₁ (f₁ z))
  let outer := D₁.domain ∪ D₃.domain
  have hpullback_outer : MapsTo pullback G.domain outer := by
    intro x hx
    have hxunion : x ∈ P ∪ Q := hGdomain.subset hx
    by_cases hxP : x ∈ P
    · exact Or.inl (by
        simpa only [pullback, if_pos hxP] using hf₁.bijOn.mapsTo hxP)
    · have hxQ : x ∈ Q := hxunion.resolve_left hxP
      exact Or.inr (by
        simpa only [pullback, if_neg hxP] using hf₃.bijOn.mapsTo hxQ)
  have houter_nhds : ∀ x ∈ outer, D x ∉ hD.singularSet.branchCarrier c →
      outer ∈ 𝓝[D.domain] x := by
    intro x hxouter hximage
    have hxD₂ : x ∉ D₂.domain := by
      intro hxD₂
      rcases hxouter with hxD₁ | hxD₃
      · have hxA : x ∈ A := hinter₁₂.subset ⟨hxD₁, hxD₂⟩
        have hxpre : x ∈ hD.branchPreimage c := by
          rw [hcover]
          exact Or.inl hxA
        exact hximage hxpre.2
      · have hxC : x ∈ C := hinter₂₃.subset ⟨hxD₂, hxD₃⟩
        have hxpre : x ∈ hD.branchPreimage c := by
          rw [hcover]
          exact Or.inr hxC
        exact hximage hxpre.2
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨D₂.domainᶜ,
      D₂.isPLBall_domain.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxD₂, ?_⟩
    intro z hz
    have hzdomain : z ∈ D.domain := hz.2
    rw [← hdomains] at hzdomain
    rcases hzdomain with (hzD₁ | hzD₂) | hzD₃
    · exact Or.inl hzD₁
    · exact (hz.1 hzD₂).elim
    · exact Or.inr hzD₃
  have hlift_outer : ∀ x ∈ outer, D x ∉ hD.singularSet.branchCarrier c →
      ∃ z ∈ G.domain, pullback z = x := by
    intro x hxouter hximage
    rcases hxouter with hxD₁ | hxD₃
    · obtain ⟨z, hzP, hzx⟩ := hf₁.bijOn.surjOn hxD₁
      have hzG : z ∈ G.domain := hGdomain.symm.subset (Or.inl hzP)
      refine ⟨z, hzG, ?_⟩
      change (if z ∈ P then f₁ z else f₃ z) = x
      rw [if_pos hzP, hzx]
    · obtain ⟨z, hzQ, hzx⟩ := hf₃.bijOn.surjOn hxD₃
      have hzP : z ∉ P := by
        intro hzP
        have hxC : x ∈ C := by
          rw [← hf₃seam]
          exact ⟨z, ⟨hzP, hzQ⟩, hzx⟩
        have hxpre : x ∈ hD.branchPreimage c := by
          rw [hcover]
          exact Or.inr hxC
        exact hximage hxpre.2
      have hzG : z ∈ G.domain := hGdomain.symm.subset (Or.inr hzQ)
      refine ⟨z, hzG, ?_⟩
      change (if z ∈ P then f₁ z else f₃ z) = x
      rw [if_neg hzP, hzx]
  have hopenDouble : ∀ y ∈ doublePointSet G G.domain,
      doublePointSet G G.domain ∈ 𝓝[doublePointSet D D.domain] y :=
    doublePointSet_mem_nhdsWithin_of_pullback
      (P := D.domain) (O := outer) (Q := G.domain)
      (S := hD.singularSet.branchCarrier c) (f := D) (g := G) (r := pullback)
      D.isPLBall_domain.isPolyhedron.isCompact D.continuousOn hD.fiber_le_two
      hpullback_mem hpullback_apply hpullback_inj hpullback_outer houter_nhds
      hlift_outer (hD.singularSet.branchCarrier_isCompact c).isClosed hremove
  let _ : Finite hD.singularSet.complex.faces :=
    hD.singularSet.finite_faces.to_subtype
  let _ : Finite hD.singularSet.complex.vertices :=
    (SimplicialComplex.finite_vertices hD.singularSet.complex).to_subtype
  let _ : Finite hD.singularSet.Branch := inferInstance
  let otherBranches : Set M :=
    ⋃ d : {d : hD.singularSet.Branch // d ≠ c},
      hD.singularSet.branchCarrier d.1
  have hotherCompact : IsCompact otherBranches :=
    isCompact_iUnion fun d => hD.singularSet.branchCarrier_isCompact d.1
  have hselectedOther : Disjoint (hD.singularSet.branchCarrier c) otherBranches := by
    apply Set.disjoint_left.mpr
    intro y hyc hyo
    obtain ⟨d, hyd⟩ := mem_iUnion.mp hyo
    exact Set.disjoint_left.mp
      (hD.singularSet.pairwise_disjoint_branchCarrier d.2.symm) hyc hyd
  have hselected_of_double_not_other {y : M}
      (hy : y ∈ doublePointSet D D.domain) (hyo : y ∉ otherBranches) :
      y ∈ hD.singularSet.branchCarrier c := by
    have hyunion : y ∈ ⋃ d : hD.singularSet.Branch,
        hD.singularSet.branchCarrier d := by
      rw [hD.singularSet.iUnion_branchCarrier]
      exact hy
    obtain ⟨d, hyd⟩ := mem_iUnion.mp hyunion
    by_cases hdc : d = c
    · simpa only [hdc] using hyd
    · exact (hyo (mem_iUnion.mpr ⟨⟨d, hdc⟩, hyd⟩)).elim
  have hcross_inj : ∀ {u v}, u ∈ P → v ∈ Q →
      G u ∉ otherBranches → G u = G v → u = v := by
    intro u v huP hvQ huother huv
    have hfu : f₁ u ∈ D₁.domain := hf₁.bijOn.mapsTo huP
    have hfv : f₃ v ∈ D₃.domain := hf₃.bijOn.mapsTo hvQ
    have hDuv : D (f₁ u) = D (f₃ v) := by
      calc
        D (f₁ u) = D₁ (f₁ u) := congrFun hfun₁ (f₁ u) |>.symm
        _ = G u := (hG₁ huP).symm
        _ = G v := huv
        _ = D₃ (f₃ v) := hG₃ hvQ
        _ = D (f₃ v) := congrFun hfun₃ (f₃ v)
    have hfuv : f₁ u ≠ f₃ v := by
      intro h
      exact Set.disjoint_left.mp hdisjoint₁₃ hfu (h ▸ hfv)
    have hyold : G u ∈ doublePointSet D D.domain := by
      refine ⟨f₁ u, hD₁sub hfu, f₃ v, hD₃sub hfv, hfuv, ?_, ?_⟩
      · exact (congrFun hfun₁ (f₁ u)).symm.trans (hG₁ huP).symm
      · exact ((congrFun hfun₃ (f₃ v)).symm.trans (hG₃ hvQ).symm).trans huv.symm
    have hyselected := hselected_of_double_not_other hyold huother
    have huDomain : u ∈ G.domain := hGdomain.symm.subset (Or.inl huP)
    have hvDomain : v ∈ G.domain := hGdomain.symm.subset (Or.inr hvQ)
    have hupre : pullback u ∈ hD.branchPreimage c := by
      refine ⟨hpullback_mem huDomain, ?_⟩
      change D (pullback u) ∈ hD.singularSet.branchCarrier c
      rw [hpullback_apply u huDomain]
      exact hyselected
    have hvpre : pullback v ∈ hD.branchPreimage c := by
      refine ⟨hpullback_mem hvDomain, ?_⟩
      change D (pullback v) ∈ hD.singularSet.branchCarrier c
      rw [hpullback_apply v hvDomain, ← huv]
      exact hyselected
    rw [hcover] at hupre hvpre
    obtain ⟨huseam, huA⟩ := hpullback_branch huDomain hupre
    obtain ⟨hvseam, hvA⟩ := hpullback_branch hvDomain hvpre
    apply hf₁.bijOn.injOn huseam.1 hvseam.1
    apply hDinjA huA hvA
    calc
      D (f₁ u) = G u := (congrFun hfun₁ (f₁ u)).symm.trans (hG₁ huP).symm
      _ = G v := huv
      _ = D (f₁ v) := (hG₁ hvseam.1).trans (congrFun hfun₁ (f₁ v))
  have hlocallyInjective :
      ∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, Set.InjOn G W := by
    intro x hx
    have hxunion : x ∈ P ∪ Q := hGdomain.subset hx
    by_cases hxP : x ∈ P
    · by_cases hxQ : x ∈ Q
      · have hfxA : f₁ x ∈ A := by
          rw [← hf₁seam]
          exact ⟨x, ⟨hxP, hxQ⟩, rfl⟩
        have hGselected : G x ∈ hD.singularSet.branchCarrier c := by
          have hpre := hAsub hfxA
          rw [hG₁ hxP, hfun₁]
          exact hpre.2
        have hGother : G x ∉ otherBranches :=
          Set.disjoint_left.mp hselectedOther hGselected
        obtain ⟨U₁, hU₁, hinj₁⟩ := hD.locallyInjective (f₁ x)
          (hD₁sub (hf₁.bijOn.mapsTo hxP))
        obtain ⟨U₃, hU₃, hinj₃⟩ := hD.locallyInjective (f₃ x)
          (hD₃sub (hf₃.bijOn.mapsTo hxQ))
        let W₁ := P ∩ f₁ ⁻¹' U₁ ∩ G ⁻¹' otherBranchesᶜ
        let W₃ := Q ∩ f₃ ⁻¹' U₃ ∩ G ⁻¹' otherBranchesᶜ
        have hf₁U₁ : f₁ ⁻¹' U₁ ∈ 𝓝[P] x :=
          (hf₁.2.1.continuousOn x hxP).tendsto_nhdsWithin
            (fun z hz => hD₁sub (hf₁.bijOn.mapsTo hz)) hU₁
        have hf₃U₃ : f₃ ⁻¹' U₃ ∈ 𝓝[Q] x :=
          (hf₃.2.1.continuousOn x hxQ).tendsto_nhdsWithin
            (fun z hz => hD₃sub (hf₃.bijOn.mapsTo hz)) hU₃
        have hGcompl : G ⁻¹' otherBranchesᶜ ∈ 𝓝[G.domain] x :=
          (G.continuousOn x hx).preimage_mem_nhdsWithin
            (hotherCompact.isClosed.isOpen_compl.mem_nhds hGother)
        have hGcomplP : G ⁻¹' otherBranchesᶜ ∈ 𝓝[P] x :=
          nhdsWithin_mono x (fun z hz => hGdomain.symm.subset (Or.inl hz)) hGcompl
        have hGcomplQ : G ⁻¹' otherBranchesᶜ ∈ 𝓝[Q] x :=
          nhdsWithin_mono x (fun z hz => hGdomain.symm.subset (Or.inr hz)) hGcompl
        have hW₁ : W₁ ∈ 𝓝[P] x := by
          exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hf₁U₁) hGcomplP
        have hW₃ : W₃ ∈ 𝓝[Q] x := by
          exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hf₃U₃) hGcomplQ
        refine ⟨W₁ ∪ W₃, ?_, ?_⟩
        · rw [hGdomain, nhdsWithin_union]
          exact ⟨Filter.mem_of_superset hW₁ subset_union_left,
            Filter.mem_of_superset hW₃ subset_union_right⟩
        · intro u hu v hv huv
          rcases hu with hu | hu <;> rcases hv with hv | hv
          · apply hf₁.bijOn.injOn hu.1.1 hv.1.1
            apply hinj₁ hu.1.2 hv.1.2
            calc
              D (f₁ u) = G u := (congrFun hfun₁ (f₁ u)).symm.trans (hG₁ hu.1.1).symm
              _ = G v := huv
              _ = D (f₁ v) := (hG₁ hv.1.1).trans (congrFun hfun₁ (f₁ v))
          · exact hcross_inj hu.1.1 hv.1.1 hu.2 huv
          · exact (hcross_inj hv.1.1 hu.1.1 hv.2 huv.symm).symm
          · apply hf₃.bijOn.injOn hu.1.1 hv.1.1
            apply hinj₃ hu.1.2 hv.1.2
            calc
              D (f₃ u) = G u := (congrFun hfun₃ (f₃ u)).symm.trans (hG₃ hu.1.1).symm
              _ = G v := huv
              _ = D (f₃ v) := (hG₃ hv.1.1).trans (congrFun hfun₃ (f₃ v))
      · obtain ⟨U, hU, hinj⟩ := hD.locallyInjective (f₁ x)
          (hD₁sub (hf₁.bijOn.mapsTo hxP))
        let W := P ∩ f₁ ⁻¹' U ∩ Qᶜ
        have hfU : f₁ ⁻¹' U ∈ 𝓝[P] x :=
          (hf₁.2.1.continuousOn x hxP).tendsto_nhdsWithin
            (fun z hz => hD₁sub (hf₁.bijOn.mapsTo hz)) hU
        have hWₚ : W ∈ 𝓝[P] x := by
          exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hfU)
            (mem_nhdsWithin_of_mem_nhds
              (hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ))
        have hemptyQ : (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[Q] x := by
          apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          exact ⟨Qᶜ, hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ, by simp⟩
        refine ⟨W, ?_, ?_⟩
        · rw [hGdomain, nhdsWithin_union]
          exact ⟨hWₚ, Filter.mem_of_superset hemptyQ (empty_subset W)⟩
        · intro u hu v hv huv
          apply hf₁.bijOn.injOn hu.1.1 hv.1.1
          apply hinj hu.1.2 hv.1.2
          calc
            D (f₁ u) = G u := (congrFun hfun₁ (f₁ u)).symm.trans (hG₁ hu.1.1).symm
            _ = G v := huv
            _ = D (f₁ v) := (hG₁ hv.1.1).trans (congrFun hfun₁ (f₁ v))
    · have hxQ : x ∈ Q := hxunion.resolve_left hxP
      obtain ⟨U, hU, hinj⟩ := hD.locallyInjective (f₃ x)
        (hD₃sub (hf₃.bijOn.mapsTo hxQ))
      let W := Q ∩ f₃ ⁻¹' U ∩ Pᶜ
      have hfU : f₃ ⁻¹' U ∈ 𝓝[Q] x :=
        (hf₃.2.1.continuousOn x hxQ).tendsto_nhdsWithin
          (fun z hz => hD₃sub (hf₃.bijOn.mapsTo hz)) hU
      have hWQ : W ∈ 𝓝[Q] x := by
        exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hfU)
          (mem_nhdsWithin_of_mem_nhds
            (hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP))
      have hemptyP : (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[P] x := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        exact ⟨Pᶜ, hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP, by simp⟩
      refine ⟨W, ?_, ?_⟩
      · rw [hGdomain, nhdsWithin_union]
        exact ⟨Filter.mem_of_superset hemptyP (empty_subset W), hWQ⟩
      · intro u hu v hv huv
        apply hf₃.bijOn.injOn hu.1.1 hv.1.1
        apply hinj hu.1.2 hv.1.2
        calc
          D (f₃ u) = G u := (congrFun hfun₃ (f₃ u)).symm.trans (hG₃ hu.1.1).symm
          _ = G v := huv
          _ = D (f₃ v) := (hG₃ hv.1.1).trans (congrFun hfun₃ (f₃ v))
  have hGlocal : IsLocallyInjective (G.domain.domRestrict G) := by
    rw [isLocallyInjective_iff_nhds]
    intro x
    obtain ⟨W, hW, hinj⟩ := hlocallyInjective x x.2
    let V : Set G.domain := ((↑) : G.domain → EuclideanSpace ℝ (Fin 2)) ⁻¹' W
    refine ⟨V, preimage_coe_mem_nhds_subtype.mpr hW, ?_⟩
    intro a ha b hb hab
    apply Subtype.ext
    exact hinj ha hb hab
  have hdoubleCompact : IsCompact (doublePointSet G G.domain) :=
    isCompact_doublePointSet_of_isLocallyInjective
      G.isPLBall_domain.isPolyhedron.isCompact G.continuousOn hGlocal
  have hGsingular : Nonempty (NormalSingularSetTriangulation G BdM) :=
    hD.singularSet.restrict_to_clopen_doublePointSet hdouble hdoubleCompact hopenDouble
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
  have himageBoundary : G '' G.domain ∩ BdM = Set.range G.boundary := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, hxy⟩, hyBdM⟩
      have hpullbackDomain : pullback x ∈ D.domain := hpullback_mem hx
      have hpullbackImage : D (pullback x) = y := (hpullback_apply x hx).trans hxy
      have hpullbackFrontier : pullback x ∈ frontier D.domain :=
        hD.fiber_subset_frontier_of_mem_image_inter_boundary
          ⟨⟨pullback x, hpullbackDomain, hpullbackImage⟩, hyBdM⟩
          ⟨hpullbackDomain, hpullbackImage⟩
      rw [hrange]
      refine ⟨pullback x, ?_, hpullbackImage⟩
      rcases hpullback_outer hx with hpullbackD₁ | hpullbackD₃
      · exact Or.inl ⟨hpullbackD₁, hpullbackFrontier⟩
      · exact Or.inr ⟨hpullbackD₃, hpullbackFrontier⟩
    · intro y hy
      have hyOld := hy
      rw [hrange] at hyOld
      obtain ⟨x, hx, hxy⟩ := hyOld
      have hxfrontier : x ∈ frontier D.domain := hx.elim And.right And.right
      have hyOldRange : y ∈ Set.range D.boundary := ⟨⟨x, hxfrontier⟩, hxy⟩
      have hyOldBoundary : y ∈ D '' D.domain ∩ BdM := by
        rw [hD.image_inter_boundary]
        exact hyOldRange
      refine ⟨?_, hyOldBoundary.2⟩
      obtain ⟨z, hzy⟩ := hy
      exact ⟨z, G.frontier_subset_domain z.property, hzy⟩
  have hrangeB : Set.range G.boundary ⊆ B := by
    rw [hrange]
    rintro y ⟨x, hx, rfl⟩
    apply hD.boundary_image_subset
    exact ⟨⟨x, hx.elim And.right And.right⟩, rfl⟩
  have hinterB : G '' G.domain ∩ BdM ⊆ B := by
    rw [himageBoundary]
    exact hrangeB
  exact ⟨A, C, D₁.domain ∩ frontier D.domain,
    D₃.domain ∩ frontier D.domain, p, q, r, s, g, G,
    hA, hC, hAC, hcover, htrace₁, htrace₃,
    hdisjoint₁₃.mono inter_subset_left inter_subset_left, hg, horientation,
    hGimage, hrange, himageBoundary, hrangeB, hinterB, hlocallyInjective, hfiber,
    hdouble, hremove, hGsingular⟩

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
