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

open Classical in
private theorem isPLHomeomorphOn_inter_isOpen
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    {O : Set E} (hO : IsOpen O) :
    IsPLHomeomorphOn f (P ∩ O)
      (Q ∩ Function.invFunOn f P ⁻¹' O) := by
  let j := Function.invFunOn f P
  let P' := P ∩ O
  let Q' := Q ∩ j ⁻¹' O
  have hbij : BijOn f P' Q' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨hxP, hxO⟩
      exact ⟨hf.bijOn.mapsTo hxP, by
        change Function.invFunOn f P (f x) ∈ O
        rw [hf.bijOn.invOn_invFunOn.1 hxP]
        exact hxO⟩
    · exact hf.bijOn.injOn.mono inter_subset_left
    · rintro y ⟨hyQ, hyO⟩
      refine ⟨j y, ⟨hf.bijOn.surjOn.mapsTo_invFunOn hyQ, hyO⟩, ?_⟩
      exact hf.bijOn.invOn_invFunOn.2 hyQ
  refine ⟨hbij, hf.isPiecewiseAffineOn.inter_of_isOpen hO, ?_⟩
  have hj : IsPiecewiseAffineOn j Q' := by
    intro y hy
    have hcont : ContinuousWithinAt j Q y :=
      hf.isPiecewiseAffineOn_invFunOn.continuousOn y hy.1
    have hpre : j ⁻¹' O ∈ 𝓝[Q] y :=
      hcont.preimage_mem_nhdsWithin (hO.mem_nhds hy.2)
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    have hlocal := (hf.isPiecewiseAffineOn_invFunOn y hy.1).inter_of_mem_nhds hV
    have heq : Q ∩ V = Q' ∩ V := by
      apply Subset.antisymm
      · intro z hz
        exact ⟨⟨hz.1, hVsub ⟨hz.2, hz.1⟩⟩, hz.2⟩
      · exact fun z hz => ⟨hz.1.1, hz.2⟩
    rw [heq] at hlocal
    exact hlocal.of_inter_of_mem_nhds hV
  refine hj.congr fun y hy => ?_
  have hyP' : Function.invFunOn f P' y ∈ P' :=
    hbij.surjOn.mapsTo_invFunOn hy
  have hyf : f (Function.invFunOn f P' y) = y :=
    hbij.invOn_invFunOn.2 hy
  have hjP : j y ∈ P := hf.bijOn.surjOn.mapsTo_invFunOn hy.1
  have hjf : f (j y) = y := hf.bijOn.invOn_invFunOn.2 hy.1
  exact hf.bijOn.injOn hyP'.1 hjP (hyf.trans hjf.symm)

open Classical in
private theorem isPLHomeomorphOn_trans_inter
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E → F} {g : F → G} {P : Set E} {Q A : Set F} {B : Set G}
    (hf : IsPLHomeomorphOn f P Q) (hg : IsPLHomeomorphOn g A B) :
    IsPLHomeomorphOn (g ∘ f) (P ∩ f ⁻¹' A)
      (B ∩ Function.invFunOn g A ⁻¹' Q) := by
  let R := P ∩ f ⁻¹' A
  let S := B ∩ Function.invFunOn g A ⁻¹' Q
  let jf := Function.invFunOn f P
  let jg := Function.invFunOn g A
  have hbij : BijOn (g ∘ f) R S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨hxP, hxfA⟩
      exact ⟨hg.bijOn.mapsTo hxfA, by
        change Function.invFunOn g A (g (f x)) ∈ Q
        rw [hg.bijOn.invOn_invFunOn.1 hxfA]
        exact hf.bijOn.mapsTo hxP⟩
    · intro x hx y hy hxy
      apply hf.bijOn.injOn hx.1 hy.1
      apply hg.bijOn.injOn hx.2 hy.2
      exact hxy
    · rintro z ⟨hzB, hzQ⟩
      let y := jg z
      have hyA : y ∈ A := hg.bijOn.surjOn.mapsTo_invFunOn hzB
      have hgy : g y = z := hg.bijOn.invOn_invFunOn.2 hzB
      have hyQ : y ∈ Q := hzQ
      let x := jf y
      have hxP : x ∈ P := hf.bijOn.surjOn.mapsTo_invFunOn hyQ
      have hfx : f x = y := hf.bijOn.invOn_invFunOn.2 hyQ
      refine ⟨x, ⟨hxP, ?_⟩, ?_⟩
      · change f x ∈ A
        rw [hfx]
        exact hyA
      change g (f x) = z
      rw [hfx, hgy]
  refine ⟨hbij, hg.isPiecewiseAffineOn.comp hf.isPiecewiseAffineOn, ?_⟩
  have hinv : IsPiecewiseAffineOn (jf ∘ jg) S := by
    change IsPiecewiseAffineOn (jf ∘ jg) (B ∩ jg ⁻¹' Q)
    exact hf.isPiecewiseAffineOn_invFunOn.comp hg.isPiecewiseAffineOn_invFunOn
  refine hinv.congr fun z hz => ?_
  have hzR : Function.invFunOn (g ∘ f) R z ∈ R :=
    hbij.surjOn.mapsTo_invFunOn hz
  have hzcomp : (g ∘ f) (Function.invFunOn (g ∘ f) R z) = z :=
    hbij.invOn_invFunOn.2 hz
  have hjgA : jg z ∈ A := hg.bijOn.surjOn.mapsTo_invFunOn hz.1
  have hgjg : g (jg z) = z := hg.bijOn.invOn_invFunOn.2 hz.1
  have hjfP : jf (jg z) ∈ P := hf.bijOn.surjOn.mapsTo_invFunOn hz.2
  have hfjf : f (jf (jg z)) = jg z := hf.bijOn.invOn_invFunOn.2 hz.2
  apply hbij.injOn hzR ⟨hjfP, by
    change f (jf (jg z)) ∈ A
    rw [hfjf]
    exact hjgA⟩
  calc
    (g ∘ f) (Function.invFunOn (g ∘ f) R z) = z := hzcomp
    _ = (g ∘ f) (jf (jg z)) := by
      change z = g (f (jf (jg z)))
      rw [hfjf, hgjg]

private theorem eventually_mem_iff_of_subset_of_mem_nhdsWithin
    {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hBA : B ⊆ A) (hB : B ∈ 𝓝[A] x) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B := by
  obtain ⟨U, hU, hUA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hB
  filter_upwards [hU] with y hy
  exact ⟨fun hyA => hUA ⟨hy, hyA⟩, fun hyB => hBA hyB⟩

open Classical in
private theorem exists_crossing_patches_of_source_changes
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f g : E → F} {pullback ru rv : E → E}
    {P Q₀ Q A B Su Sv Tu Tv : Set E} {u v : E} {y : F}
    (hQQ₀ : Q ⊆ Q₀)
    (hgu : g u = y) (hgv : g v = y)
    (hru : IsPLHomeomorphOn ru Su Tu) (hrv : IsPLHomeomorphOn rv Sv Tv)
    (huSu : u ∈ Su) (hvSv : v ∈ Sv)
    (hSuNhds : Su ∈ 𝓝[Q₀] u) (hSvNhds : Sv ∈ 𝓝[Q₀] v)
    (hSuP_Q : Su ∩ ru ⁻¹' P ⊆ Q) (hSvP_Q : Sv ∩ rv ⁻¹' P ⊆ Q)
    (hruPull : EqOn ru pullback Su) (hrvPull : EqOn rv pullback Sv)
    (hguEq : EqOn g (f ∘ ru) Su) (hgvEq : EqOn g (f ∘ rv) Sv)
    (hPTu : P ∈ 𝓝[Tu] (ru u)) (hPTv : P ∈ 𝓝[Tv] (rv v))
    (hTuNhds : Tu ∈ 𝓝[P] (ru u)) (hTvNhds : Tv ∈ 𝓝[P] (rv v))
    (hruA : ru u ∈ A) (hrvB : rv v ∈ B)
    (hAnhds : A ∈ 𝓝[P] (ru u)) (hBnhds : B ∈ 𝓝[P] (rv v))
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B)
    (hfA : IsPLHomeomorphOn f A (f '' A))
    (hfB : IsPLHomeomorphOn f B (f '' B))
    (hcoverOfNhds : ∀ A' B' : Set E,
      A' ∈ 𝓝[Q₀] u → B' ∈ 𝓝[Q₀] v →
        ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B') :
    ∃ A' B' : Set E,
      u ∈ A' ∧ v ∈ B' ∧ g u = y ∧ g v = y ∧
      A' ⊆ Q ∧ B' ⊆ Q ∧ Disjoint A' B' ∧
      A' ∈ 𝓝[Q] u ∧ B' ∈ 𝓝[Q] v ∧
      IsPLHomeomorphOn g A' (g '' A') ∧
      IsPLHomeomorphOn g B' (g '' B') ∧
      (∀ᶠ z in 𝓝 y, z ∈ f '' A ↔ z ∈ g '' A') ∧
      (∀ᶠ z in 𝓝 y, z ∈ f '' B ↔ z ∈ g '' B') ∧
      ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B' := by
  let A' := Su ∩ ru ⁻¹' A
  let B' := Sv ∩ rv ⁻¹' B
  have huA' : u ∈ A' := ⟨huSu, hruA⟩
  have hvB' : v ∈ B' := ⟨hvSv, hrvB⟩
  have hA'Q : A' ⊆ Q := fun _ hw => hSuP_Q ⟨hw.1, hAP hw.2⟩
  have hB'Q : B' ⊆ Q := fun _ hw => hSvP_Q ⟨hw.1, hBP hw.2⟩
  have hA'B' : Disjoint A' B' := by
    apply Set.disjoint_left.mpr
    intro w hwA hwB
    have heq : ru w = rv w := (hruPull hwA.1).trans (hrvPull hwB.1).symm
    exact Set.disjoint_left.mp hAB hwA.2 (heq ▸ hwB.2)
  have hA'Su : A' ∈ 𝓝[Su] u := by
    apply Filter.inter_mem self_mem_nhdsWithin
    apply (hru.isPiecewiseAffineOn.continuousOn u huSu).preimage_mem_nhdsWithin'
    rw [hru.image_eq]
    exact mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hAnhds hPTu
  have hB'Sv : B' ∈ 𝓝[Sv] v := by
    apply Filter.inter_mem self_mem_nhdsWithin
    apply (hrv.isPiecewiseAffineOn.continuousOn v hvSv).preimage_mem_nhdsWithin'
    rw [hrv.image_eq]
    exact mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hBnhds hPTv
  have hA'nhds₀ : A' ∈ 𝓝[Q₀] u :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hA'Su hSuNhds
  have hB'nhds₀ : B' ∈ 𝓝[Q₀] v :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hB'Sv hSvNhds
  have hA'nhds : A' ∈ 𝓝[Q] u := nhdsWithin_mono u hQQ₀ hA'nhds₀
  have hB'nhds : B' ∈ 𝓝[Q] v := nhdsWithin_mono v hQQ₀ hB'nhds₀
  let TA := f '' A ∩ Function.invFunOn f A ⁻¹' Tu
  let TB := f '' B ∩ Function.invFunOn f B ⁻¹' Tv
  have hplAraw : IsPLHomeomorphOn (f ∘ ru) A' TA :=
    isPLHomeomorphOn_trans_inter hru hfA
  have hplBraw : IsPLHomeomorphOn (f ∘ rv) B' TB :=
    isPLHomeomorphOn_trans_inter hrv hfB
  have hplA : IsPLHomeomorphOn g A' TA :=
    hplAraw.congr (hguEq.mono inter_subset_left)
  have hplB : IsPLHomeomorphOn g B' TB :=
    hplBraw.congr (hgvEq.mono inter_subset_left)
  have hf_ru : f (ru u) = y := (hguEq huSu).symm.trans hgu
  have hf_rv : f (rv v) = y := (hgvEq hvSv).symm.trans hgv
  have hyA : y ∈ f '' A := ⟨ru u, hruA, hf_ru⟩
  have hyB : y ∈ f '' B := ⟨rv v, hrvB, hf_rv⟩
  have hjA : Function.invFunOn f A y = ru u := by
    rw [← hf_ru]
    exact hfA.bijOn.invOn_invFunOn.1 hruA
  have hjB : Function.invFunOn f B y = rv v := by
    rw [← hf_rv]
    exact hfB.bijOn.invOn_invFunOn.1 hrvB
  have hTAnhds : TA ∈ 𝓝[f '' A] y := by
    apply Filter.inter_mem self_mem_nhdsWithin
    apply (hfA.isPiecewiseAffineOn_invFunOn.continuousOn y hyA).preimage_mem_nhdsWithin'
    rw [hfA.symm.image_eq, hjA]
    exact nhdsWithin_mono (ru u) hAP hTuNhds
  have hTBnhds : TB ∈ 𝓝[f '' B] y := by
    apply Filter.inter_mem self_mem_nhdsWithin
    apply (hfB.isPiecewiseAffineOn_invFunOn.continuousOn y hyB).preimage_mem_nhdsWithin'
    rw [hfB.symm.image_eq, hjB]
    exact nhdsWithin_mono (rv v) hBP hTvNhds
  have hAgerm : ∀ᶠ z in 𝓝 y, z ∈ f '' A ↔ z ∈ g '' A' := by
    rw [hplA.image_eq]
    exact eventually_mem_iff_of_subset_of_mem_nhdsWithin inter_subset_left hTAnhds
  have hBgerm : ∀ᶠ z in 𝓝 y, z ∈ f '' B ↔ z ∈ g '' B' := by
    rw [hplB.image_eq]
    exact eventually_mem_iff_of_subset_of_mem_nhdsWithin inter_subset_left hTBnhds
  have hcover : ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B' :=
    hcoverOfNhds A' B' hA'nhds₀ hB'nhds₀
  exact ⟨A', B', huA', hvB', hgu, hgv, hA'Q, hB'Q, hA'B',
    hA'nhds, hB'nhds, hplA.image_eq.symm ▸ hplA,
    hplB.image_eq.symm ▸ hplB, hAgerm, hBgerm, hcover⟩

open Classical in
private theorem transport_doubleCrossing_of_source_changes
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f g : E → F} {pullback ru rv : E → E}
    {P Q₀ Q Su Sv Tu Tv : Set E} {u v : E} {y : F}
    (hQQ₀ : Q ⊆ Q₀)
    (hpullbackInj : InjOn pullback Q₀)
    (huQ₀ : u ∈ Q₀) (hvQ₀ : v ∈ Q₀) (huv : u ≠ v)
    (hgu : g u = y) (hgv : g v = y)
    (hru : IsPLHomeomorphOn ru Su Tu) (hrv : IsPLHomeomorphOn rv Sv Tv)
    (huSu : u ∈ Su) (hvSv : v ∈ Sv)
    (hSuNhds : Su ∈ 𝓝[Q₀] u) (hSvNhds : Sv ∈ 𝓝[Q₀] v)
    (hSuP_Q : Su ∩ ru ⁻¹' P ⊆ Q) (hSvP_Q : Sv ∩ rv ⁻¹' P ⊆ Q)
    (hruPull : EqOn ru pullback Su) (hrvPull : EqOn rv pullback Sv)
    (hguEq : EqOn g (f ∘ ru) Su) (hgvEq : EqOn g (f ∘ rv) Sv)
    (hruP : ru u ∈ P) (hrvP : rv v ∈ P)
    (hPTu : P ∈ 𝓝[Tu] (ru u)) (hPTv : P ∈ 𝓝[Tv] (rv v))
    (hTuNhds : Tu ∈ 𝓝[P] (ru u)) (hTvNhds : Tv ∈ 𝓝[P] (rv v))
    (hcoverOfNhds : ∀ A' B' : Set E,
      A' ∈ 𝓝[Q₀] u → B' ∈ 𝓝[Q₀] v →
        ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B')
    (hcross : HasPLDoubleCrossingAt f P y) :
    HasPLDoubleCrossingAt g Q y := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hAB,
    hAnhds, hBnhds, hfA, hfB, htarget, hcoverOld⟩ := hcross
  have hf_ru : f (ru u) = y := (hguEq huSu).symm.trans hgu
  have hf_rv : f (rv v) = y := (hgvEq hvSv).symm.trans hgv
  have hruAB : ru u ∈ A ∪ B := hcoverOld.self_of_nhds
    ⟨hruP, hf_ru⟩
  have hrvAB : rv v ∈ A ∪ B := hcoverOld.self_of_nhds
    ⟨hrvP, hf_rv⟩
  rcases hruAB with hruA | hruB <;> rcases hrvAB with hrvA | hrvB
  · have hrr : ru u = rv v := hfA.bijOn.injOn hruA hrvA (hf_ru.trans hf_rv.symm)
    have hpull : pullback u = pullback v :=
      (hruPull huSu).symm.trans (hrr.trans (hrvPull hvSv))
    exact (huv (hpullbackInj huQ₀ hvQ₀ hpull)).elim
  · have haru : a = ru u := hfA.bijOn.injOn haA hruA (hfa.trans hf_ru.symm)
    have hbrv : b = rv v := hfB.bijOn.injOn hbB hrvB (hfb.trans hf_rv.symm)
    have hAnhds' : A ∈ 𝓝[P] (ru u) := by rwa [← haru]
    have hBnhds' : B ∈ 𝓝[P] (rv v) := by rwa [← hbrv]
    obtain ⟨A', B', huA', hvB', hgu', hgv', hA'Q, hB'Q, hA'B',
      hA'nhds, hB'nhds, hgA, hgB, hAgerm, hBgerm, hcover⟩ :=
      exists_crossing_patches_of_source_changes
        (f := f) (g := g) (pullback := pullback)
        (ru := ru) (rv := rv) (P := P) (Q₀ := Q₀) (Q := Q) (A := A) (B := B)
        (Su := Su) (Sv := Sv) (Tu := Tu) (Tv := Tv)
        hQQ₀ hgu hgv hru hrv huSu hvSv hSuNhds hSvNhds hSuP_Q hSvP_Q
        hruPull hrvPull hguEq hgvEq hPTu hPTv hTuNhds hTvNhds
        hruA hrvB hAnhds' hBnhds' hAP hBP hAB hfA hfB hcoverOfNhds
    exact ⟨u, v, A', B', huA', hvB', hgu', hgv', hA'Q, hB'Q,
      hA'B', hA'nhds, hB'nhds, hgA, hgB, htarget.congr hAgerm hBgerm, hcover⟩
  · have harv : a = rv v := hfA.bijOn.injOn haA hrvA (hfa.trans hf_rv.symm)
    have hbru : b = ru u := hfB.bijOn.injOn hbB hruB (hfb.trans hf_ru.symm)
    have hAnhds' : A ∈ 𝓝[P] (rv v) := by rwa [← harv]
    have hBnhds' : B ∈ 𝓝[P] (ru u) := by rwa [← hbru]
    have hcoverSwap : ∀ A' B' : Set E,
        A' ∈ 𝓝[Q₀] v → B' ∈ 𝓝[Q₀] u →
          ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B' := by
      intro A' B' hA' hB'
      filter_upwards [hcoverOfNhds B' A' hB' hA'] with z hz
      intro w hw
      rcases hz hw with hwB | hwA
      · exact Or.inr hwB
      · exact Or.inl hwA
    obtain ⟨A', B', hvA', huB', hgv', hgu', hA'Q, hB'Q, hA'B',
      hA'nhds, hB'nhds, hgA, hgB, hAgerm, hBgerm, hcover⟩ :=
      exists_crossing_patches_of_source_changes
        (f := f) (g := g) (pullback := pullback)
        (ru := rv) (rv := ru) (P := P) (Q₀ := Q₀) (Q := Q) (A := A) (B := B)
        (Su := Sv) (Sv := Su) (Tu := Tv) (Tv := Tu)
        hQQ₀ hgv hgu hrv hru hvSv huSu hSvNhds hSuNhds hSvP_Q hSuP_Q
        hrvPull hruPull hgvEq hguEq hPTv hPTu hTvNhds hTuNhds
        hrvA hruB hAnhds' hBnhds' hAP hBP hAB hfA hfB hcoverSwap
    exact ⟨v, u, A', B', hvA', huB', hgv', hgu', hA'Q, hB'Q,
      hA'B', hA'nhds, hB'nhds, hgA, hgB, htarget.congr hAgerm hBgerm, hcover⟩
  · have hrr : ru u = rv v := hfB.bijOn.injOn hruB hrvB (hf_ru.trans hf_rv.symm)
    have hpull : pullback u = pullback v :=
      (hruPull huSu).symm.trans (hrr.trans (hrvPull hvSv))
    exact (huv (hpullbackInj huQ₀ hvQ₀ hpull)).elim

open Classical in
private theorem transport_boundaryDoubleCrossing_of_source_changes
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f g : E → F} {pullback ru rv : E → E}
    {P Q₀ Q Su Sv Tu Tv : Set E} {M : Set F} {u v : E} {y : F}
    (hQQ₀ : Q ⊆ Q₀)
    (hpullbackInj : InjOn pullback Q₀)
    (huQ₀ : u ∈ Q₀) (hvQ₀ : v ∈ Q₀) (huv : u ≠ v)
    (hgu : g u = y) (hgv : g v = y)
    (hru : IsPLHomeomorphOn ru Su Tu) (hrv : IsPLHomeomorphOn rv Sv Tv)
    (huSu : u ∈ Su) (hvSv : v ∈ Sv)
    (hSuNhds : Su ∈ 𝓝[Q₀] u) (hSvNhds : Sv ∈ 𝓝[Q₀] v)
    (hSuP_Q : Su ∩ ru ⁻¹' P ⊆ Q) (hSvP_Q : Sv ∩ rv ⁻¹' P ⊆ Q)
    (hruPull : EqOn ru pullback Su) (hrvPull : EqOn rv pullback Sv)
    (hguEq : EqOn g (f ∘ ru) Su) (hgvEq : EqOn g (f ∘ rv) Sv)
    (hruP : ru u ∈ P) (hrvP : rv v ∈ P)
    (hPTu : P ∈ 𝓝[Tu] (ru u)) (hPTv : P ∈ 𝓝[Tv] (rv v))
    (hTuNhds : Tu ∈ 𝓝[P] (ru u)) (hTvNhds : Tv ∈ 𝓝[P] (rv v))
    (hcoverOfNhds : ∀ A' B' : Set E,
      A' ∈ 𝓝[Q₀] u → B' ∈ 𝓝[Q₀] v →
        ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B')
    (hcross : HasPLBoundaryDoubleCrossingAt f P M y) :
    HasPLBoundaryDoubleCrossingAt g Q M y := by
  obtain ⟨a, b, A, B, haA, hbB, hfa, hfb, hAP, hBP, hAB,
    hAnhds, hBnhds, hfA, hfB, htarget, hcoverOld⟩ := hcross
  have hf_ru : f (ru u) = y := (hguEq huSu).symm.trans hgu
  have hf_rv : f (rv v) = y := (hgvEq hvSv).symm.trans hgv
  have hruAB : ru u ∈ A ∪ B := hcoverOld.self_of_nhds
    ⟨hruP, hf_ru⟩
  have hrvAB : rv v ∈ A ∪ B := hcoverOld.self_of_nhds
    ⟨hrvP, hf_rv⟩
  rcases hruAB with hruA | hruB <;> rcases hrvAB with hrvA | hrvB
  · have hrr : ru u = rv v := hfA.bijOn.injOn hruA hrvA (hf_ru.trans hf_rv.symm)
    have hpull : pullback u = pullback v :=
      (hruPull huSu).symm.trans (hrr.trans (hrvPull hvSv))
    exact (huv (hpullbackInj huQ₀ hvQ₀ hpull)).elim
  · have haru : a = ru u := hfA.bijOn.injOn haA hruA (hfa.trans hf_ru.symm)
    have hbrv : b = rv v := hfB.bijOn.injOn hbB hrvB (hfb.trans hf_rv.symm)
    have hAnhds' : A ∈ 𝓝[P] (ru u) := by rwa [← haru]
    have hBnhds' : B ∈ 𝓝[P] (rv v) := by rwa [← hbrv]
    obtain ⟨A', B', huA', hvB', hgu', hgv', hA'Q, hB'Q, hA'B',
      hA'nhds, hB'nhds, hgA, hgB, hAgerm, hBgerm, hcover⟩ :=
      exists_crossing_patches_of_source_changes
        (f := f) (g := g) (pullback := pullback)
        (ru := ru) (rv := rv) (P := P) (Q₀ := Q₀) (Q := Q) (A := A) (B := B)
        (Su := Su) (Sv := Sv) (Tu := Tu) (Tv := Tv)
        hQQ₀ hgu hgv hru hrv huSu hvSv hSuNhds hSvNhds hSuP_Q hSvP_Q
        hruPull hrvPull hguEq hgvEq hPTu hPTv hTuNhds hTvNhds
        hruA hrvB hAnhds' hBnhds' hAP hBP hAB hfA hfB hcoverOfNhds
    exact ⟨u, v, A', B', huA', hvB', hgu', hgv', hA'Q, hB'Q,
      hA'B', hA'nhds, hB'nhds, hgA, hgB,
      htarget.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hAgerm hBgerm, hcover⟩
  · have harv : a = rv v := hfA.bijOn.injOn haA hrvA (hfa.trans hf_rv.symm)
    have hbru : b = ru u := hfB.bijOn.injOn hbB hruB (hfb.trans hf_ru.symm)
    have hAnhds' : A ∈ 𝓝[P] (rv v) := by rwa [← harv]
    have hBnhds' : B ∈ 𝓝[P] (ru u) := by rwa [← hbru]
    have hcoverSwap : ∀ A' B' : Set E,
        A' ∈ 𝓝[Q₀] v → B' ∈ 𝓝[Q₀] u →
          ∀ᶠ z in 𝓝 y, Q ∩ g ⁻¹' {z} ⊆ A' ∪ B' := by
      intro A' B' hA' hB'
      filter_upwards [hcoverOfNhds B' A' hB' hA'] with z hz
      intro w hw
      rcases hz hw with hwB | hwA
      · exact Or.inr hwB
      · exact Or.inl hwA
    obtain ⟨A', B', hvA', huB', hgv', hgu', hA'Q, hB'Q, hA'B',
      hA'nhds, hB'nhds, hgA, hgB, hAgerm, hBgerm, hcover⟩ :=
      exists_crossing_patches_of_source_changes
        (f := f) (g := g) (pullback := pullback)
        (ru := rv) (rv := ru) (P := P) (Q₀ := Q₀) (Q := Q) (A := A) (B := B)
        (Su := Sv) (Sv := Su) (Tu := Tv) (Tv := Tu)
        hQQ₀ hgv hgu hrv hru hvSv huSu hSvNhds hSuNhds hSvP_Q hSuP_Q
        hrvPull hruPull hgvEq hguEq hPTv hPTu hTvNhds hTuNhds
        hrvA hruB hAnhds' hBnhds' hAP hBP hAB hfA hfB hcoverSwap
    exact ⟨v, u, A', B', hvA', huB', hgv', hgu', hA'Q, hB'Q,
      hA'B', hA'nhds, hB'nhds, hgA, hgB,
      htarget.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hAgerm hBgerm, hcover⟩
  · have hrr : ru u = rv v := hfB.bijOn.injOn hruB hrvB (hf_ru.trans hf_rv.symm)
    have hpull : pullback u = pullback v :=
      (hruPull huSu).symm.trans (hrr.trans (hrvPull hvSv))
    exact (huv (hpullbackInj huQ₀ hvQ₀ hpull)).elim

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
theorem exists_cross_boundary_surgery_cell_of_boundaryBranch
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C U₁ U₂ U₃ P Q P' Q' A' R T : Set (EuclideanSpace ℝ (Fin 2)),
    ∃ p q r s a b : EuclideanSpace ℝ (Fin 2),
    ∃ g f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    ∃ H G : SingularTwoCell M,
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A ∧
      p ∈ A ∧ q ∈ A ∧ r ∈ C ∧ s ∈ C ∧
      ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
      U₁ ∪ U₂ ∪ U₃ = D.domain ∧ U₁ ∩ U₂ = A ∧ U₂ ∩ U₃ = C ∧
      Disjoint U₁ U₃ ∧
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P U₁ ∧ IsPLHomeomorphOn f₂ Q U₂ ∧
      f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = C ∧
      EqOn H (D ∘ f₁) P ∧ EqOn H (D ∘ f₂) Q ∧
      A' = Function.invFunOn f₂ Q '' A ∧ IsPLBall 1 A' ∧
      A' ⊆ frontier H.domain ∧ IsPLHomeomorphOn (g ∘ f₂) A' C ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧ IsPLHomeomorphOn f₃ Q' U₃ ∧
      h '' (P' ∩ Q') = A' ∧ f₃ '' (P' ∩ Q') = C ∧
      EqOn G (H ∘ h) P' ∧ EqOn G (D ∘ f₃) Q' ∧
      Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
      Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      h a = Function.invFunOn f₂ Q p ∧ h b = Function.invFunOn f₂ Q q ∧
      f₃ a = g p ∧ f₃ b = g q ∧
      G '' G.domain ⊆ D '' D.domain ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x)
          (e : loopCircle ≃ₜ frontier G.domain),
        Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
          ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨A, C, hA, hC, hAC, hcover, -, -, p, q, r, s, g, hg, hcompat,
    D₁, D₂, D₃, hdomains, hinter₁₂, hinter₂₃, hA₁, hA₂, hC₂, hC₃,
    hdisjoint₁₃, hfun₁, hfun₂, hfun₃, -, -, hcut₁, hcut₃⟩ :=
    hD.exists_three_cells_of_boundaryBranch hc
  have hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A := by
    intro x hx
    change D₁.toFun x = D₂.toFun (g x)
    rw [hfun₁, hfun₂]
    exact hcompat hx
  have hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A := by
    intro x hx
    change D₂.toFun x = D₃.toFun (g x)
    rw [hfun₂, hfun₃]
    exact hcompat hx
  obtain ⟨H, G, P, Q, P', Q', f₁, f₂, h, f₃, A', hP, hQ, hHdomain,
    hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, hA', hA'front, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    a, b, R, T, hcutP', hcutQ', hR, hT, hfrontG, hha, hhb, hf₃a, hf₃b,
    x, y, σ, ω, e, hσrange, hωrange, hboundaryParam⟩ :=
    D₁.exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs D₂ D₃ hA hAC
      hcut₁.fst hA₁ hA₂ hC₂ hC₃ hg hcompat₁₂ hcompat₂₃
  have horientation :=
    IsPLHomeomorphOn.maps_arc_endpoints hA hC hcut₁.fst hcut₃.fst hg
  have hH₁' : EqOn H (D ∘ f₁) P := by
    intro z hz
    simpa only [Function.comp_apply, hfun₁] using hH₁ hz
  have hH₂' : EqOn H (D ∘ f₂) Q := by
    intro z hz
    simpa only [Function.comp_apply, hfun₂] using hH₂ hz
  have hG₃' : EqOn G (D ∘ f₃) Q' := by
    intro z hz
    simpa only [Function.comp_apply, hfun₃] using hG₃ hz
  have hU₁D : D₁.domain ⊆ D.domain := by
    intro z hz
    rw [← hdomains]
    exact Or.inl (Or.inl hz)
  have hU₂D : D₂.domain ⊆ D.domain := by
    intro z hz
    rw [← hdomains]
    exact Or.inl (Or.inr hz)
  have hU₃D : D₃.domain ⊆ D.domain := by
    intro z hz
    rw [← hdomains]
    exact Or.inr hz
  have hHimage : H '' H.domain ⊆ D '' D.domain := by
    rintro z ⟨w, hw, rfl⟩
    rw [hHdomain] at hw
    rcases hw with hwP | hwQ
    · exact ⟨f₁ w, hU₁D (hf₁.bijOn.mapsTo hwP), (hH₁' hwP).symm⟩
    · exact ⟨f₂ w, hU₂D (hf₂.bijOn.mapsTo hwQ), (hH₂' hwQ).symm⟩
  have hGimage : G '' G.domain ⊆ D '' D.domain := by
    rintro z ⟨w, hw, rfl⟩
    rw [hGdomain] at hw
    rcases hw with hwP | hwQ
    · obtain ⟨u, hu, hGu⟩ := hHimage ⟨h w, hh.bijOn.mapsTo hwP, rfl⟩
      exact ⟨u, hu, hGu.trans (hGH hwP).symm⟩
    · exact ⟨f₃ w, hU₃D (hf₃.bijOn.mapsTo hwQ), (hG₃' hwQ).symm⟩
  exact ⟨A, C, D₁.domain, D₂.domain, D₃.domain, P, Q, P', Q', A', R, T,
    p, q, r, s, a, b, g, f₁, f₂, h, f₃, H, G, hA, hC, hAC, hcover, hg,
    hcompat, hcut₁.fst.left_mem, hcut₁.fst.right_mem, hcut₃.fst.left_mem,
    hcut₃.fst.right_mem, horientation, hdomains, hinter₁₂, hinter₂₃,
    hdisjoint₁₃, hP, hQ, hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁', hH₂',
    hA'def, hA', hA'front, hk, hP', hQ', hGdomain, hh, hf₃, hhseam,
    hf₃seam, hGH, hG₃', hcutP', hcutQ', hR, hT, hfrontG, hha, hhb,
    hf₃a, hf₃b, hGimage, x, y, σ, ω, e, hσrange, hωrange, hboundaryParam⟩

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
    ∃ pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      IsPLBall 1 U ∧ IsPLBall 1 V ∧ Disjoint U V ∧
      IsPLHomeomorphOn g A C ∧
      p ∈ A ∧ q ∈ A ∧ r ∈ C ∧ s ∈ C ∧
      EqOn D (D ∘ g) A ∧
      ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
      MapsTo pullback G.domain D.domain ∧
      InjOn pullback G.domain ∧
      EqOn (D ∘ pullback) G G.domain ∧
      Disjoint (pullback '' G.domain) C ∧
      G '' G.domain ⊆ D '' D.domain ∧
      Set.range G.boundary = D '' (U ∪ V) ∧
      G '' G.domain ∩ BdM = Set.range G.boundary ∧
      Set.range G.boundary ⊆ B ∧ G '' G.domain ∩ BdM ⊆ B ∧
      (∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, Set.InjOn G W) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
       doublePointSet G G.domain ⊆ doublePointSet D D.domain ∧
       Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c) ∧
       Nonempty (NormalSingularSetTriangulation G BdM) ∧
       Nonempty (NormalSingularCellData G BdM B) ∧
       ∃ (x y : M) (σ : Path x y) (ω : Path y x)
          (e : loopCircle ≃ₜ frontier G.domain),
         Set.range σ = D '' U ∧ Set.range ω = D '' V ∧
           ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
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
  have hRT : R ∩ T = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      have hxP : x ∈ P :=
        hP.isPolyhedron.isClosed.frontier_subset (hcutP.snd_subset hxR)
      have hxQ : x ∈ Q :=
        hQ.isPolyhedron.isClosed.frontier_subset (hcutQ.snd_subset hxT)
      exact hcutP.inter_eq.subset ⟨⟨hxP, hxQ⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP.snd.left_mem, hcutQ.snd.left_mem⟩
      · exact ⟨hcutP.snd.right_mem, hcutQ.snd.right_mem⟩
  obtain ⟨a', b', ρ, κ, e, hρrange, hκrange, he⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union hcutP.snd hcutQ.snd hRT hfrontG
  let σ : Path (G.boundary a') (G.boundary b') := ρ.map G.boundary.continuous
  let ω : Path (G.boundary b') (G.boundary a') := κ.map G.boundary.continuous
  have hσrange : Set.range σ = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      Set.range σ = G '' R := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          refine ⟨ρ t, ?_, rfl⟩
          rw [← hρrange]
          exact ⟨t, rfl⟩
        · rintro ⟨w, hwR, rfl⟩
          rw [← hρrange] at hwR
          obtain ⟨t, htw⟩ := hwR
          refine ⟨t, ?_⟩
          change G (ρ t) = G w
          exact congrArg G htw
      _ = D '' (D₁.domain ∩ frontier D.domain) := hGR
  have hωrange : Set.range ω = D '' (D₃.domain ∩ frontier D.domain) := by
    calc
      Set.range ω = G '' T := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          refine ⟨κ t, ?_, rfl⟩
          rw [← hκrange]
          exact ⟨t, rfl⟩
        · rintro ⟨w, hwT, rfl⟩
          rw [← hκrange] at hwT
          obtain ⟨t, htw⟩ := hwT
          refine ⟨t, ?_⟩
          change G (κ t) = G w
          exact congrArg G htw
      _ = D '' (D₃.domain ∩ frontier D.domain) := hGT
  have hboundaryParam : ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
    intro θ
    rw [he θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map G.boundary.continuous) t = (σ.trans ω) t
    rw [Path.map_trans]
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
  have hpullback_disjoint_C : Disjoint (pullback '' G.domain) C := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxC
    obtain ⟨hxseam, hfxA⟩ := hpullback_branch hx (Or.inr hxC)
    have hpullback_eq : pullback x = f₁ x := by
      change (if x ∈ P then f₁ x else f₃ x) = f₁ x
      rw [if_pos hxseam.1]
    rw [hpullback_eq] at hxC
    exact Set.disjoint_left.mp hAC hfxA hxC
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
  have hside : ∀ x ∈ G.domain,
      G x ∉ hD.singularSet.branchCarrier c →
        ∃ S T : Set (EuclideanSpace ℝ (Fin 2)),
        ∃ r : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
          x ∈ S ∧ S ∈ 𝓝[G.domain] x ∧ T ∈ 𝓝[D.domain] (r x) ∧
          IsPLHomeomorphOn r S T ∧ EqOn r pullback S ∧
          EqOn G (D ∘ r) S ∧ S ⊆ G.domain ∧ T ⊆ D.domain := by
    intro x hx hximage
    have hxunion : x ∈ P ∪ Q := hGdomain.subset hx
    by_cases hxP : x ∈ P
    · have hxQ : x ∉ Q := by
        intro hxQ
        have hfxA : f₁ x ∈ A := by
          rw [← hf₁seam]
          exact ⟨x, ⟨hxP, hxQ⟩, rfl⟩
        apply hximage
        rw [hG₁ hxP, hfun₁]
        exact (hAsub hfxA).2
      let S := P ∩ Qᶜ
      let T := D₁.domain ∩ Function.invFunOn f₁ P ⁻¹' Qᶜ
      have hxS : x ∈ S := ⟨hxP, hxQ⟩
      have hpl : IsPLHomeomorphOn f₁ S T :=
        isPLHomeomorphOn_inter_isOpen hf₁ hQ.isPolyhedron.isClosed.isOpen_compl
      have hSnhds : S ∈ 𝓝[G.domain] x := by
        have hbase : G.domain ∩ Qᶜ ∈ 𝓝[G.domain] x :=
          Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds
              (hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ))
        apply Filter.mem_of_superset hbase
        rintro z ⟨hzG, hzQ⟩
        exact ⟨(hGdomain.subset hzG).resolve_right hzQ, hzQ⟩
      have hfxD₁ : f₁ x ∈ D₁.domain := hf₁.bijOn.mapsTo hxP
      have hfxNotD₂ : f₁ x ∉ D₂.domain := by
        intro hfxD₂
        have hfxA : f₁ x ∈ A := hinter₁₂.subset ⟨hfxD₁, hfxD₂⟩
        obtain ⟨z, hz, hzx⟩ := hf₁seam.symm.subset hfxA
        have hzx' : z = x := hf₁.bijOn.injOn hz.1 hxP hzx
        exact hxQ (hzx' ▸ hz.2)
      have hfxNotD₃ : f₁ x ∉ D₃.domain := by
        intro hfxD₃
        exact Set.disjoint_left.mp hdisjoint₁₃ hfxD₁ hfxD₃
      have hD₁nhds : D₁.domain ∈ 𝓝[D.domain] (f₁ x) := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        refine ⟨(D₂.domain ∪ D₃.domain)ᶜ,
          (D₂.isPLBall_domain.isPolyhedron.isClosed.union
            D₃.isPLBall_domain.isPolyhedron.isClosed).isOpen_compl.mem_nhds ?_, ?_⟩
        · rintro (hfxD₂ | hfxD₃)
          · exact hfxNotD₂ hfxD₂
          · exact hfxNotD₃ hfxD₃
        · intro z hz
          have hzD : z ∈ D.domain := hz.2
          rw [← hdomains] at hzD
          rcases hzD with (hzD₁ | hzD₂) | hzD₃
          · exact hzD₁
          · exact (hz.1 (Or.inl hzD₂)).elim
          · exact (hz.1 (Or.inr hzD₃)).elim
      have hinv : Function.invFunOn f₁ P (f₁ x) = x :=
        hf₁.bijOn.invOn_invFunOn.1 hxP
      have hpre : Function.invFunOn f₁ P ⁻¹' Qᶜ ∈ 𝓝[D₁.domain] (f₁ x) := by
        apply (hf₁.isPiecewiseAffineOn_invFunOn.continuousOn (f₁ x) hfxD₁).preimage_mem_nhdsWithin'
        rw [hf₁.symm.image_eq, hinv]
        exact mem_nhdsWithin_of_mem_nhds
          (hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ)
      have hTD₁ : T ∈ 𝓝[D₁.domain] (f₁ x) :=
        Filter.inter_mem self_mem_nhdsWithin hpre
      have hTnhds : T ∈ 𝓝[D.domain] (f₁ x) :=
        mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hTD₁ hD₁nhds
      have hpull : EqOn f₁ pullback S := by
        intro z hz
        change f₁ z = if z ∈ P then f₁ z else f₃ z
        rw [if_pos hz.1]
      have hmap : EqOn G (D ∘ f₁) S := by
        intro z hz
        exact (hG₁ hz.1).trans (congrFun hfun₁ (f₁ z))
      exact ⟨S, T, f₁, hxS, hSnhds, hTnhds, hpl, hpull, hmap,
        fun _ hz => hGdomain.symm.subset (Or.inl hz.1),
        fun _ hz => hD₁sub hz.1⟩
    · have hxQ : x ∈ Q := hxunion.resolve_left hxP
      let S := Q ∩ Pᶜ
      let T := D₃.domain ∩ Function.invFunOn f₃ Q ⁻¹' Pᶜ
      have hxS : x ∈ S := ⟨hxQ, hxP⟩
      have hpl : IsPLHomeomorphOn f₃ S T :=
        isPLHomeomorphOn_inter_isOpen hf₃ hP.isPolyhedron.isClosed.isOpen_compl
      have hSnhds : S ∈ 𝓝[G.domain] x := by
        have hbase : G.domain ∩ Pᶜ ∈ 𝓝[G.domain] x :=
          Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds
              (hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP))
        apply Filter.mem_of_superset hbase
        rintro z ⟨hzG, hzP⟩
        exact ⟨(hGdomain.subset hzG).resolve_left hzP, hzP⟩
      have hfxD₃ : f₃ x ∈ D₃.domain := hf₃.bijOn.mapsTo hxQ
      have hfxNotD₂ : f₃ x ∉ D₂.domain := by
        intro hfxD₂
        have hfxC : f₃ x ∈ C := hinter₂₃.subset ⟨hfxD₂, hfxD₃⟩
        obtain ⟨z, hz, hzx⟩ := hf₃seam.symm.subset hfxC
        have hzx' : z = x := hf₃.bijOn.injOn hz.2 hxQ hzx
        exact hxP (hzx' ▸ hz.1)
      have hfxNotD₁ : f₃ x ∉ D₁.domain := by
        intro hfxD₁
        exact Set.disjoint_left.mp hdisjoint₁₃ hfxD₁ hfxD₃
      have hD₃nhds : D₃.domain ∈ 𝓝[D.domain] (f₃ x) := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        refine ⟨(D₁.domain ∪ D₂.domain)ᶜ,
          (D₁.isPLBall_domain.isPolyhedron.isClosed.union
            D₂.isPLBall_domain.isPolyhedron.isClosed).isOpen_compl.mem_nhds ?_, ?_⟩
        · rintro (hfxD₁ | hfxD₂)
          · exact hfxNotD₁ hfxD₁
          · exact hfxNotD₂ hfxD₂
        · intro z hz
          have hzD : z ∈ D.domain := hz.2
          rw [← hdomains] at hzD
          rcases hzD with (hzD₁ | hzD₂) | hzD₃
          · exact (hz.1 (Or.inl hzD₁)).elim
          · exact (hz.1 (Or.inr hzD₂)).elim
          · exact hzD₃
      have hinv : Function.invFunOn f₃ Q (f₃ x) = x :=
        hf₃.bijOn.invOn_invFunOn.1 hxQ
      have hpre : Function.invFunOn f₃ Q ⁻¹' Pᶜ ∈ 𝓝[D₃.domain] (f₃ x) := by
        apply (hf₃.isPiecewiseAffineOn_invFunOn.continuousOn (f₃ x) hfxD₃).preimage_mem_nhdsWithin'
        rw [hf₃.symm.image_eq, hinv]
        exact mem_nhdsWithin_of_mem_nhds
          (hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP)
      have hTD₃ : T ∈ 𝓝[D₃.domain] (f₃ x) :=
        Filter.inter_mem self_mem_nhdsWithin hpre
      have hTnhds : T ∈ 𝓝[D.domain] (f₃ x) :=
        mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hTD₃ hD₃nhds
      have hpull : EqOn f₃ pullback S := by
        intro z hz
        change f₃ z = if z ∈ P then f₁ z else f₃ z
        rw [if_neg hz.2]
      have hmap : EqOn G (D ∘ f₃) S := by
        intro z hz
        exact (hG₃ hz.1).trans (congrFun hfun₃ (f₃ z))
      exact ⟨S, T, f₃, hxS, hSnhds, hTnhds, hpl, hpull, hmap,
        fun _ hz => hGdomain.symm.subset (Or.inr hz.1),
        fun _ hz => hD₃sub hz.1⟩
  have hGcrossing : ∀ y ∈ doublePointSet G G.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y) := by
    intro y hy
    have hyOld : y ∈ doublePointSet D D.domain := hdouble hy
    have hyNotBranch : y ∉ hD.singularSet.branchCarrier c :=
      Set.disjoint_left.mp hremove hy
    obtain ⟨u, hu, v, hv, huv, huy, hvy⟩ := hy
    have huNotBranch : G u ∉ hD.singularSet.branchCarrier c := by
      simpa only [huy] using hyNotBranch
    have hvNotBranch : G v ∉ hD.singularSet.branchCarrier c := by
      simpa only [hvy] using hyNotBranch
    obtain ⟨Su, Tu, ru, huSu, hSuNhds, hTuNhds, hru, hruPull,
      hGu, hSuG, hTuD⟩ := hside u hu huNotBranch
    obtain ⟨Sv, Tv, rv, hvSv, hSvNhds, hTvNhds, hrv, hrvPull,
      hGv, hSvG, hTvD⟩ := hside v hv hvNotBranch
    obtain ⟨e, he, hye, hcross⟩ := hD.crossing y hyOld
    let PD := D.domain ∩ D ⁻¹' e.source
    let PG := G.domain ∩ G ⁻¹' e.source
    have hruPD : ru u ∈ PD := by
      refine ⟨hTuD (hru.bijOn.mapsTo huSu), ?_⟩
      change D (ru u) ∈ e.source
      have hEq := hGu huSu
      change G u = D (ru u) at hEq
      rw [← hEq, huy]
      exact hye
    have hrvPD : rv v ∈ PD := by
      refine ⟨hTvD (hrv.bijOn.mapsTo hvSv), ?_⟩
      change D (rv v) ∈ e.source
      have hEq := hGv hvSv
      change G v = D (rv v) at hEq
      rw [← hEq, hvy]
      exact hye
    have hPDnhdsTu : PD ∈ 𝓝[Tu] (ru u) := by
      apply nhdsWithin_mono (ru u) hTuD
      apply Filter.inter_mem self_mem_nhdsWithin
      exact (D.continuousOn (ru u) hruPD.1).preimage_mem_nhdsWithin
        (e.open_source.mem_nhds hruPD.2)
    have hPDnhdsTv : PD ∈ 𝓝[Tv] (rv v) := by
      apply nhdsWithin_mono (rv v) hTvD
      apply Filter.inter_mem self_mem_nhdsWithin
      exact (D.continuousOn (rv v) hrvPD.1).preimage_mem_nhdsWithin
        (e.open_source.mem_nhds hrvPD.2)
    have hTuNhdsPD : Tu ∈ 𝓝[PD] (ru u) :=
      nhdsWithin_mono (ru u) inter_subset_left hTuNhds
    have hTvNhdsPD : Tv ∈ 𝓝[PD] (rv v) :=
      nhdsWithin_mono (rv v) inter_subset_left hTvNhds
    have hSuPD_PG : Su ∩ ru ⁻¹' PD ⊆ PG := by
      rintro w ⟨hwSu, hwPD⟩
      refine ⟨hSuG hwSu, ?_⟩
      change G w ∈ e.source
      rw [hGu hwSu]
      exact hwPD.2
    have hSvPD_PG : Sv ∩ rv ⁻¹' PD ⊆ PG := by
      rintro w ⟨hwSv, hwPD⟩
      refine ⟨hSvG hwSv, ?_⟩
      change G w ∈ e.source
      rw [hGv hwSv]
      exact hwPD.2
    have hcoordU : EqOn (e ∘ G) ((e ∘ D) ∘ ru) Su := by
      intro w hw
      exact congrArg e (hGu hw)
    have hcoordV : EqOn (e ∘ G) ((e ∘ D) ∘ rv) Sv := by
      intro w hw
      exact congrArg e (hGv hw)
    have hgu : (e ∘ G) u = e y := congrArg e huy
    have hgv : (e ∘ G) v = e y := congrArg e hvy
    have hfiberPair : G.domain ∩ G ⁻¹' {y} = {u, v} :=
      fiber_eq_pair_of_encard_le_two G G.domain hu hv huv huy hvy (hfiber y)
    have htend : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
      simpa only [ContinuousAt, e.left_inv hye] using
        e.symm.continuousAt (e.map_source hye)
    have hcoverOfNhds : ∀ A' B' : Set (EuclideanSpace ℝ (Fin 2)),
        A' ∈ 𝓝[G.domain] u → B' ∈ 𝓝[G.domain] v →
          ∀ᶠ z in 𝓝 (e y), PG ∩ (e ∘ G) ⁻¹' {z} ⊆ A' ∪ B' := by
      intro A' B' hA' hB'
      have hcover : ∀ᶠ z in 𝓝 y, G.domain ∩ G ⁻¹' {z} ⊆ A' ∪ B' :=
        eventually_preimage_subset_union_of_fiber_eq_pair G
          G.isPLBall_domain.isPolyhedron.isCompact G.continuousOn hfiberPair hA' hB'
      filter_upwards [htend.eventually hcover,
        e.open_target.mem_nhds (e.map_source hye)] with z hz hzTarget
      intro w hw
      apply hz
      refine ⟨hw.1.1, ?_⟩
      change G w = e.symm z
      have heq : e (G w) = z := hw.2
      exact e.injOn hw.1.2 (e.map_target hzTarget)
        (heq.trans (e.right_inv hzTarget).symm)
    refine ⟨e, he, hye, ?_⟩
    rcases hcross with ⟨hyBoundary, N, hcross⟩ | ⟨hyInterior, hcross⟩
    · refine Or.inl ⟨hyBoundary, N, ?_⟩
      exact transport_boundaryDoubleCrossing_of_source_changes
        (f := e ∘ D) (g := e ∘ G) (pullback := pullback)
        (ru := ru) (rv := rv) (P := PD) (Q₀ := G.domain) (Q := PG)
        (Su := Su) (Sv := Sv) (Tu := Tu) (Tv := Tv)
        inter_subset_left hpullback_inj hu hv huv hgu hgv hru hrv huSu hvSv
        hSuNhds hSvNhds hSuPD_PG hSvPD_PG hruPull hrvPull hcoordU hcoordV
        hruPD hrvPD hPDnhdsTu hPDnhdsTv hTuNhdsPD hTvNhdsPD hcoverOfNhds hcross
    · refine Or.inr ⟨hyInterior, ?_⟩
      exact transport_doubleCrossing_of_source_changes
        (f := e ∘ D) (g := e ∘ G) (pullback := pullback)
        (ru := ru) (rv := rv) (P := PD) (Q₀ := G.domain) (Q := PG)
        (Su := Su) (Sv := Sv) (Tu := Tu) (Tv := Tv)
        inter_subset_left hpullback_inj hu hv huv hgu hgv hru hrv huSu hvSv
        hSuNhds hSvNhds hSuPD_PG hSvPD_PG hruPull hrvPull hcoordU hcoordV
        hruPD hrvPD hPDnhdsTu hPDnhdsTv hTuNhdsPD hTvNhdsPD hcoverOfNhds hcross
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
  have hGnormal : Nonempty (NormalSingularCellData G BdM B) :=
    ⟨{
      locallyInjective := hlocallyInjective
      fiber_le_two := hfiber
      boundary_image_subset := hrangeB
      image_inter_boundary := himageBoundary
      singularSet := Classical.choice hGsingular
      crossing := hGcrossing }⟩
  exact ⟨A, C, D₁.domain ∩ frontier D.domain,
    D₃.domain ∩ frontier D.domain, p, q, r, s, g, G, pullback,
    hA, hC, hAC, hcover, htrace₁, htrace₃,
    hdisjoint₁₃.mono inter_subset_left inter_subset_left, hg,
    hcut₁.fst.left_mem, hcut₁.fst.right_mem,
    hcut₃.fst.left_mem, hcut₃.fst.right_mem, hcompat, horientation,
    hpullback_mem, hpullback_inj, hpullback_apply, hpullback_disjoint_C,
     hGimage, hrange, himageBoundary, hrangeB, hinterB, hlocallyInjective, hfiber,
     hdouble, hremove, hGsingular, hGnormal,
     G.boundary a', G.boundary b', σ, ω, e, hσrange, hωrange, hboundaryParam⟩

end NormalSingularCellData

open Classical in
theorem simplicialComplexity_lt_of_surgery_pullback
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces]
    (D G : SingularTwoCell M)
    (pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hLdomain : L.vertices ⊆ G.domain)
    (hvertices : MapsTo pullback L.vertices K.vertices)
    (hinj : InjOn pullback G.domain)
    (hfactor : EqOn (D ∘ pullback) G G.domain)
    (hdisjoint : Disjoint (pullback '' G.domain) C)
    {v w : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ K.vertices) (hw : w ∈ K.vertices)
    (hvw : v ≠ w) (hDvw : D v = D w) (hwC : w ∈ C) :
    simplicialComplexity L G < simplicialComplexity K D := by
  apply simplicialComplexity_lt_of_vertex_injection_of_missing_collision
    K L D G pullback hvertices (hinj.mono hLdomain)
  · intro x hx
    exact hfactor (hLdomain hx)
  · refine ⟨v, hv, w, hw, hvw, hDvw, ?_⟩
    rintro ⟨x, hx, hxeq⟩
    exact Set.disjoint_left.mp hdisjoint
      ⟨x, hLdomain hx, rfl⟩ (hxeq ▸ hwC)

open Classical in
theorem simplicialComplexity_lt_of_surgery_pullback_of_seam
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces]
    (D G : SingularTwoCell M)
    (pullback g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hLdomain : L.vertices ⊆ G.domain)
    (hvertices : MapsTo pullback L.vertices K.vertices)
    (hinj : InjOn pullback G.domain)
    (hfactor : EqOn (D ∘ pullback) G G.domain)
    (hdisjoint : Disjoint (pullback '' G.domain) C)
    (hAC : Disjoint A C) (hpA : p ∈ A) (hrC : r ∈ C) (hsC : s ∈ C)
    (hcompat : EqOn D (D ∘ g) A)
    (horientation : (g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r))
    (hp : p ∈ K.vertices) (hr : r ∈ K.vertices) (hs : s ∈ K.vertices) :
    simplicialComplexity L G < simplicialComplexity K D := by
  rcases horientation with horientation | horientation
  · apply simplicialComplexity_lt_of_surgery_pullback K L D G pullback
      hLdomain hvertices hinj hfactor hdisjoint hp hr
    · intro hpr
      exact Set.disjoint_left.mp hAC hpA (by simpa only [hpr] using hrC)
    · exact (hcompat hpA).trans (congrArg D horientation.1)
    · exact hrC
  · apply simplicialComplexity_lt_of_surgery_pullback K L D G pullback
      hLdomain hvertices hinj hfactor hdisjoint hp hs
    · intro hps
      exact Set.disjoint_left.mp hAC hpA (by simpa only [hps] using hsC)
    · exact (hcompat hpA).trans (congrArg D horientation.1)
    · exact hsC

open Classical in
theorem exists_isSubdivision_mapsTo_vertices
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (f : F → E) (hf : MapsTo f L.vertices K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E,
      IsSubdivision K' K ∧ K'.faces.Finite ∧ MapsTo f L.vertices K'.vertices := by
  let _ : Finite L.vertices := (SimplicialComplex.finite_vertices L).to_subtype
  let Q : L.vertices → Set E := fun v => {f v}
  have hsingleton : ∀ x : E, IsPolyhedron ({x} : Set E) := by
    intro x
    have h := isPolyhedron_convexHull_of_affineIndependent ({x} : Finset E)
      (affineIndependent_of_subsingleton ℝ _)
    rwa [Finset.coe_singleton, convexHull_singleton] at h
  obtain ⟨K', hK', hfinite, hcover⟩ := exists_isSubdivision_subcomplexes K Q
    (fun v => hsingleton (f v))
    (fun v => singleton_subset_iff.mpr (hf v.property))
  refine ⟨K', hK', hfinite, ?_⟩
  intro v hv
  have hmem : f v ∈ Q ⟨v, hv⟩ := rfl
  obtain ⟨s, ⟨hs, hsQ⟩, -⟩ := mem_iUnion₂.mp ((hcover ⟨v, hv⟩).subset hmem)
  have hpoint : ∀ w ∈ s, w = f v := fun w hw =>
    Set.mem_singleton_iff.mp (hsQ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)))
  obtain ⟨w, hw⟩ := K'.nonempty_of_mem_faces hs
  have hseq : s = {f v} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hpoint w hw ▸ hw, hpoint⟩
  change ({f v} : Finset E) ∈ K'.faces
  rw [← hseq]
  exact hs

open Classical in
theorem exists_simplicialComplexity_lt_of_surgery_pullback_of_seam
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D G : SingularTwoCell M)
    (pullback g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hpD : p ∈ D.domain) (hrD : r ∈ D.domain) (hsD : s ∈ D.domain)
    (hpullback : MapsTo pullback G.domain D.domain)
    (hinj : InjOn pullback G.domain)
    (hfactor : EqOn (D ∘ pullback) G G.domain)
    (hdisjoint : Disjoint (pullback '' G.domain) C)
    (hAC : Disjoint A C) (hpA : p ∈ A) (hrC : r ∈ C) (hsC : s ∈ C)
    (hcompat : EqOn D (D ∘ g) A)
    (horientation : (g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) :
    ∃ (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (hKfinite : K.faces.Finite) (hLfinite : L.faces.Finite),
      let _ : Finite K.faces := hKfinite.to_subtype
      let _ : Finite L.faces := hLfinite.to_subtype
      K.space = D.domain ∧ L.space = G.domain ∧
        MapsTo pullback L.vertices K.vertices ∧
          p ∈ K.vertices ∧ r ∈ K.vertices ∧ s ∈ K.vertices ∧
            simplicialComplexity L G < simplicialComplexity K D := by
  obtain ⟨L, hLfinite, hLspace⟩ := G.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfinite.to_subtype
  have hLdomain : L.vertices ⊆ G.domain := by
    rw [← hLspace]
    exact L.vertices_subset_space
  obtain ⟨K₀, hK₀finite, hK₀space⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite K₀.faces := hK₀finite.to_subtype
  have hpullback₀ : MapsTo pullback L.vertices K₀.space := by
    intro v hv
    rw [hK₀space]
    exact hpullback (hLdomain hv)
  obtain ⟨K₁, hK₁, hK₁finite, hpullback₁⟩ :=
    exists_isSubdivision_mapsTo_vertices K₀ L pullback hpullback₀
  let _ : Finite K₁.faces := hK₁finite.to_subtype
  have hpK₁ : p ∈ K₁.space := by
    rw [hK₁.space_eq, hK₀space]
    exact hpD
  obtain ⟨K₂, hK₂, hK₂finite, hpK₂⟩ := exists_isSubdivision_singleton_mem K₁ hpK₁
  let _ : Finite K₂.faces := hK₂finite.to_subtype
  have hrK₂ : r ∈ K₂.space := by
    rw [hK₂.space_eq, hK₁.space_eq, hK₀space]
    exact hrD
  obtain ⟨K₃, hK₃, hK₃finite, hrK₃⟩ := exists_isSubdivision_singleton_mem K₂ hrK₂
  let _ : Finite K₃.faces := hK₃finite.to_subtype
  have hsK₃ : s ∈ K₃.space := by
    rw [hK₃.space_eq, hK₂.space_eq, hK₁.space_eq, hK₀space]
    exact hsD
  obtain ⟨K, hK, hKfinite, hsK⟩ := exists_isSubdivision_singleton_mem K₃ hsK₃
  let _ : Finite K.faces := hKfinite.to_subtype
  have hpullbackK : MapsTo pullback L.vertices K.vertices := fun v hv =>
    hK.singleton_mem (hK₃.singleton_mem (hK₂.singleton_mem (hpullback₁ hv)))
  have hpK : p ∈ K.vertices := hK.singleton_mem (hK₃.singleton_mem hpK₂)
  have hrK : r ∈ K.vertices := hK.singleton_mem hrK₃
  have hKspace : K.space = D.domain :=
    hK.space_eq.trans (hK₃.space_eq.trans
      (hK₂.space_eq.trans (hK₁.space_eq.trans hK₀space)))
  refine ⟨K, L, hKfinite, hLfinite, hKspace, hLspace, hpullbackK, hpK, hrK, hsK, ?_⟩
  exact simplicialComplexity_lt_of_surgery_pullback_of_seam K L D G pullback g
    hLdomain hpullbackK hinj hfactor hdisjoint hAC hpA hrC hsC hcompat horientation
    hpK hrK hsK

namespace NormalSingularCellData

open Classical in
theorem exists_boundary_surgery_cell_with_simplicialComplexity_lt
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ (U V : Set (EuclideanSpace ℝ (Fin 2))) (G : SingularTwoCell M)
        (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (hKfinite : K.faces.Finite) (hLfinite : L.faces.Finite),
      let _ : Finite K.faces := hKfinite.to_subtype
      let _ : Finite L.faces := hLfinite.to_subtype
      IsPLBall 1 U ∧ IsPLBall 1 V ∧ Disjoint U V ∧
        G '' G.domain ⊆ D '' D.domain ∧
          Set.range G.boundary = D '' (U ∪ V) ∧
            G '' G.domain ∩ BdM = Set.range G.boundary ∧
              Set.range G.boundary ⊆ B ∧
                Nonempty (NormalSingularCellData G BdM B) ∧
                  K.space = D.domain ∧ L.space = G.domain ∧
                    simplicialComplexity L G < simplicialComplexity K D := by
  obtain ⟨A, C, U, V, p, q, r, s, g, G, pullback,
    hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
    hcompat, horientation, hpullback, hinj, hfactor, hdisjoint,
    hGimage, hboundary, himageBoundary, hboundaryB, hinterB, hlocal, hfiber,
    hdouble, hremove, htriangulated, hnormal, -⟩ :=
    hD.exists_boundary_surgery_cell_of_boundaryBranch hc
  have hpD : p ∈ D.domain := by
    have : p ∈ hD.branchPreimage c := by
      rw [hcover]
      exact Or.inl hpA
    exact this.1
  have hrD : r ∈ D.domain := by
    have : r ∈ hD.branchPreimage c := by
      rw [hcover]
      exact Or.inr hrC
    exact this.1
  have hsD : s ∈ D.domain := by
    have : s ∈ hD.branchPreimage c := by
      rw [hcover]
      exact Or.inr hsC
    exact this.1
  obtain ⟨K, L, hKfinite, hLfinite, hKspace, hLspace, -, -, -, -, hlt⟩ :=
    exists_simplicialComplexity_lt_of_surgery_pullback_of_seam D G pullback g
      hpD hrD hsD hpullback hinj hfactor hdisjoint hAC hpA hrC hsC hcompat horientation
  exact ⟨U, V, G, K, L, hKfinite, hLfinite, hU, hV, hUV, hGimage, hboundary,
    himageBoundary, hboundaryB, hnormal, hKspace, hLspace, hlt⟩

end NormalSingularCellData

open Classical in
theorem loopRepresentativeAlong_mem_iff_loopClassMeets_basedCircle
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x y : X} (q : Path x y) (γ : basedCircleLoop y)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    loopRepresentativeAlong q γ ∈ N ↔ loopClassMeets γ.val x N := by
  let l := loopRepresentativeAlong q γ
  have hclass : FreeLoop.conjugacyClass γ.val x = ConjClasses.mk l :=
    FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q γ
  have hl : l ∈ (FreeLoop.conjugacyClass γ.val x).carrier := by
    rw [hclass]
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl
  constructor
  · intro hlN
    exact ⟨l, hl, hlN⟩
  · intro hmeet
    exact ((conjugacyClassMeets_iff_carrier_subset
      (FreeLoop.conjugacyClass γ.val x) N).mp hmeet) hl

open Classical in
theorem not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x y : X} (q : Path x y) (γ : basedCircleLoop y)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    ¬loopClassMeets γ.val x N ↔ loopRepresentativeAlong q γ ∉ N :=
  (not_congr (loopRepresentativeAlong_mem_iff_loopClassMeets_basedCircle q γ N)).symm

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

theorem not_mem_or_not_mem_of_four_path_reverse_order
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {a b c d : G} (hN : d * c * b * a ∉ N) :
    c⁻¹ * a ∉ N ∨ b * c * d * a ∉ N := by
  by_contra h
  rw [not_or] at h
  have h₁ : c⁻¹ * a ∈ N := not_not.mp h.1
  have h₂ : b * c * d * a ∈ N := not_not.mp h.2
  apply hN
  rw [show d * c * b * a =
      ((d * a) * (c⁻¹ * a)⁻¹ * (d * a)⁻¹) *
        ((b * c)⁻¹ * (b * c * d * a) * (b * c)) * (c⁻¹ * a) by group]
  exact N.mul_mem
    (N.mul_mem
      (‹N.Normal›.conj_mem (c⁻¹ * a)⁻¹ (N.inv_mem h₁) (d * a))
      (by
        have hconj := ‹N.Normal›.conj_mem (b * c * d * a) h₂ (b * c)⁻¹
        simpa only [inv_inv] using hconj)) h₁

theorem not_mem_or_not_mem_of_four_path_preserving_order
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {a b c d : G} (hN : d * c * b * a ∉ N) :
    c * a ∉ N ∨ d⁻¹ * c * b⁻¹ * a ∉ N := by
  by_contra h
  rw [not_or] at h
  have h₁ : c * a ∈ N := not_not.mp h.1
  have h₂ : d⁻¹ * c * b⁻¹ * a ∈ N := not_not.mp h.2
  apply hN
  rw [show d * c * b * a =
      (c * b * c⁻¹)⁻¹ *
        ((c * a) * (d⁻¹ * c * b⁻¹ * a)⁻¹) *
        (c * b * c⁻¹) * (c * a) by group]
  exact N.mul_mem
    (by
      have hconj := ‹N.Normal›.conj_mem
        ((c * a) * (d⁻¹ * c * b⁻¹ * a)⁻¹)
        (N.mul_mem h₁ (N.inv_mem h₂)) (c * b * c⁻¹)⁻¹
      simpa only [inv_inv] using hconj) h₁

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

section

open CategoryTheory

private def reconnectionPathArrow
    {X : Type u} [TopologicalSpace X] {x y : X}
    (p : Path x y) : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
  Path.Homotopic.Quotient.mk p

private def reconnectionPathClass
    {X : Type u} [TopologicalSpace X] {x : X}
    (p : Path x x) : FundamentalGroup X x :=
  reconnectionPathArrow p

private theorem pathClass_reverse_reconnection_original
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ υ : Path a b) (τ φ : Path b a) :
    reconnectionPathClass (σ.trans (τ.trans (υ.trans φ))) =
      reconnectionPathClass (c.trans φ) *
        reconnectionPathClass (υ.trans c.symm) *
        reconnectionPathClass (c.trans τ) *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (reconnectionPathArrow σ ≫ (reconnectionPathArrow τ ≫
      (reconnectionPathArrow υ ≫ reconnectionPathArrow φ))) =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      ((reconnectionPathArrow c ≫ reconnectionPathArrow τ) ≫
      ((reconnectionPathArrow υ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      (reconnectionPathArrow c ≫ reconnectionPathArrow φ)))
  simp

private theorem pathClass_reverse_reconnection_first
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ υ : Path a b) :
    reconnectionPathClass (σ.trans υ.symm) =
      (reconnectionPathClass (υ.trans c.symm))⁻¹ *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow υ) =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      CategoryTheory.Groupoid.inv
        (reconnectionPathArrow υ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c))
  simp

private theorem pathClass_reverse_reconnection_second
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ υ : Path a b) (τ φ : Path b a) :
    reconnectionPathClass (σ.trans (φ.trans (υ.trans τ))) =
      reconnectionPathClass (c.trans τ) *
        reconnectionPathClass (υ.trans c.symm) *
        reconnectionPathClass (c.trans φ) *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (reconnectionPathArrow σ ≫ (reconnectionPathArrow φ ≫
      (reconnectionPathArrow υ ≫ reconnectionPathArrow τ))) =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      ((reconnectionPathArrow c ≫ reconnectionPathArrow φ) ≫
      ((reconnectionPathArrow υ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      (reconnectionPathArrow c ≫ reconnectionPathArrow τ)))
  simp

private theorem pathClass_preserving_reconnection_original
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a) :
    reconnectionPathClass (σ.trans (τ.trans (υ.trans φ))) =
      reconnectionPathClass φ * reconnectionPathClass (c.trans υ) *
        reconnectionPathClass (c.trans (τ.trans c.symm)) *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (reconnectionPathArrow σ ≫ (reconnectionPathArrow τ ≫
      (reconnectionPathArrow υ ≫ reconnectionPathArrow φ))) =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      ((reconnectionPathArrow c ≫
        (reconnectionPathArrow τ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c))) ≫
      ((reconnectionPathArrow c ≫ reconnectionPathArrow υ) ≫ reconnectionPathArrow φ))
  simp

private theorem pathClass_preserving_reconnection_first
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ : Path a b) (υ : Path b a) :
    reconnectionPathClass (σ.trans υ) =
      reconnectionPathClass (c.trans υ) *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change reconnectionPathArrow σ ≫ reconnectionPathArrow υ =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      (reconnectionPathArrow c ≫ reconnectionPathArrow υ)
  simp

private theorem pathClass_preserving_reconnection_second
    {X : Type u} [TopologicalSpace X] {a b : X}
    (c σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a) :
    reconnectionPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm))) =
      (reconnectionPathClass φ)⁻¹ * reconnectionPathClass (c.trans υ) *
        (reconnectionPathClass (c.trans (τ.trans c.symm)))⁻¹ *
        reconnectionPathClass (σ.trans c.symm) := by
  unfold reconnectionPathClass reconnectionPathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change (reconnectionPathArrow σ ≫
      (CategoryTheory.Groupoid.inv (reconnectionPathArrow τ) ≫
      (reconnectionPathArrow υ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow φ)))) =
    (reconnectionPathArrow σ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c)) ≫
      (CategoryTheory.Groupoid.inv
        (reconnectionPathArrow c ≫
          (reconnectionPathArrow τ ≫ CategoryTheory.Groupoid.inv (reconnectionPathArrow c))) ≫
      ((reconnectionPathArrow c ≫ reconnectionPathArrow υ) ≫
        CategoryTheory.Groupoid.inv (reconnectionPathArrow φ)))
  simp

open Classical in
private theorem loopRepresentativeAlong_reverse_reconnection_original
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ υ : Path a b) (τ φ : Path b a) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans (τ.trans (υ.trans φ))),
          pathToCircle_zero _⟩ : basedCircleLoop a) =
      F (reconnectionPathClass (c.trans φ)) *
        F (reconnectionPathClass (υ.trans c.symm)) *
        F (reconnectionPathClass (c.trans τ)) *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans (τ.trans (υ.trans φ)))) = _
  rw [pathClass_reverse_reconnection_original c σ υ τ φ]
  simp only [map_mul]

open Classical in
private theorem loopRepresentativeAlong_reverse_reconnection_first
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ υ : Path a b) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans υ.symm), pathToCircle_zero _⟩ : basedCircleLoop a) =
      (F (reconnectionPathClass (υ.trans c.symm)))⁻¹ *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans υ.symm)) = _
  rw [pathClass_reverse_reconnection_first c σ υ]
  simp only [map_mul]
  rw [(DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).map_inv]

open Classical in
private theorem loopRepresentativeAlong_reverse_reconnection_second
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ υ : Path a b) (τ φ : Path b a) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans (φ.trans (υ.trans τ))),
          pathToCircle_zero _⟩ : basedCircleLoop a) =
      F (reconnectionPathClass (c.trans τ)) *
        F (reconnectionPathClass (υ.trans c.symm)) *
        F (reconnectionPathClass (c.trans φ)) *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans (φ.trans (υ.trans τ)))) = _
  rw [pathClass_reverse_reconnection_second c σ υ τ φ]
  simp only [map_mul]

open Classical in
private theorem loopRepresentativeAlong_preserving_reconnection_original
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans (τ.trans (υ.trans φ))),
          pathToCircle_zero _⟩ : basedCircleLoop a) =
      F (reconnectionPathClass φ) * F (reconnectionPathClass (c.trans υ)) *
        F (reconnectionPathClass (c.trans (τ.trans c.symm))) *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans (τ.trans (υ.trans φ)))) = _
  rw [pathClass_preserving_reconnection_original c σ τ υ φ]
  simp only [map_mul]

open Classical in
private theorem loopRepresentativeAlong_preserving_reconnection_first
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ : Path a b) (υ : Path b a) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans υ), pathToCircle_zero _⟩ : basedCircleLoop a) =
      F (reconnectionPathClass (c.trans υ)) *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans υ)) = _
  rw [pathClass_preserving_reconnection_first c σ υ]
  simp only [map_mul]

open Classical in
private theorem loopRepresentativeAlong_preserving_reconnection_second
    {X : Type u} [TopologicalSpace X] {x a b : X}
    (q : Path x a) (c σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a) :
    let F := DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    loopRepresentativeAlong q
        (⟨pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))),
          pathToCircle_zero _⟩ : basedCircleLoop a) =
      (F (reconnectionPathClass φ))⁻¹ * F (reconnectionPathClass (c.trans υ)) *
        (F (reconnectionPathClass (c.trans (τ.trans c.symm))))⁻¹ *
        F (reconnectionPathClass (σ.trans c.symm)) := by
  dsimp only
  rw [loopRepresentativeAlong_pathToCircle]
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (reconnectionPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm)))) = _
  rw [pathClass_preserving_reconnection_second c σ τ υ φ]
  simp only [map_mul]
  rw [(DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).map_inv,
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).map_inv]

open Classical in
private theorem not_loopClassMeets_based_of_reverse_words
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x a : X} (q : Path x a) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (γ γ₁ γ₂ : basedCircleLoop a) (A B C D : FundamentalGroup X x)
    (hword : loopRepresentativeAlong q γ = D * C * B * A)
    (hword₁ : loopRepresentativeAlong q γ₁ = C⁻¹ * A)
    (hword₂ : loopRepresentativeAlong q γ₂ = B * C * D * A)
    (hL : ¬loopClassMeets γ.val x N) :
    ¬loopClassMeets γ₁.val x N ∨ ¬loopClassMeets γ₂.val x N := by
  have hrep : loopRepresentativeAlong q γ ∉ N :=
    (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ N).mp hL
  have hsplit : C⁻¹ * A ∉ N ∨ B * C * D * A ∉ N :=
    not_mem_or_not_mem_of_four_path_reverse_order N (by rw [← hword]; exact hrep)
  exact hsplit.imp
    (fun h =>
      (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ₁ N).mpr
        (by rw [hword₁]; exact h))
    (fun h =>
      (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ₂ N).mpr
        (by rw [hword₂]; exact h))

open Classical in
private theorem not_loopClassMeets_based_of_preserving_words
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x a : X} (q : Path x a) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (γ γ₁ γ₂ : basedCircleLoop a) (A B C D : FundamentalGroup X x)
    (hword : loopRepresentativeAlong q γ = D * C * B * A)
    (hword₁ : loopRepresentativeAlong q γ₁ = C * A)
    (hword₂ : loopRepresentativeAlong q γ₂ = D⁻¹ * C * B⁻¹ * A)
    (hL : ¬loopClassMeets γ.val x N) :
    ¬loopClassMeets γ₁.val x N ∨ ¬loopClassMeets γ₂.val x N := by
  have hrep : loopRepresentativeAlong q γ ∉ N :=
    (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ N).mp hL
  have hsplit : C * A ∉ N ∨ D⁻¹ * C * B⁻¹ * A ∉ N :=
    not_mem_or_not_mem_of_four_path_preserving_order N (by rw [← hword]; exact hrep)
  exact hsplit.imp
    (fun h =>
      (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ₁ N).mpr
        (by rw [hword₁]; exact h))
    (fun h =>
      (not_loopClassMeets_iff_loopRepresentativeAlong_not_mem_basedCircle q γ₂ N).mpr
        (by rw [hword₂]; exact h))

open Classical in
theorem not_loopClassMeets_or_not_loopClassMeets_of_endpoint_reversing_reconnection
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x a b : X} (q : Path x a) (c σ υ : Path a b) (τ φ : Path b a)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (hL : ¬loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N) :
    ¬loopClassMeets (pathToCircle (σ.trans υ.symm)) x N ∨
      ¬loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) x N := by
  exact not_loopClassMeets_based_of_reverse_words q N
    (⟨pathToCircle (σ.trans (τ.trans (υ.trans φ))), pathToCircle_zero _⟩)
    (⟨pathToCircle (σ.trans υ.symm), pathToCircle_zero _⟩)
    (⟨pathToCircle (σ.trans (φ.trans (υ.trans τ))), pathToCircle_zero _⟩)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (σ.trans c.symm)))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (c.trans τ)))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (υ.trans c.symm)))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (c.trans φ)))
    (loopRepresentativeAlong_reverse_reconnection_original q c σ υ τ φ)
    (loopRepresentativeAlong_reverse_reconnection_first q c σ υ)
    (loopRepresentativeAlong_reverse_reconnection_second q c σ υ τ φ) hL

open Classical in
theorem not_loopClassMeets_or_not_loopClassMeets_of_endpoint_preserving_reconnection
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x a b : X} (q : Path x a) (c σ : Path a b)
    (τ : Path b b) (υ : Path b a) (φ : Path a a)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (hL : ¬loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N) :
    ¬loopClassMeets (pathToCircle (σ.trans υ)) x N ∨
      ¬loopClassMeets
        (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) x N := by
  exact not_loopClassMeets_based_of_preserving_words q N
    (⟨pathToCircle (σ.trans (τ.trans (υ.trans φ))), pathToCircle_zero _⟩)
    (⟨pathToCircle (σ.trans υ), pathToCircle_zero _⟩)
    (⟨pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))), pathToCircle_zero _⟩)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (σ.trans c.symm)))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (c.trans (τ.trans c.symm))))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass (c.trans υ)))
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
      (reconnectionPathClass φ))
    (loopRepresentativeAlong_preserving_reconnection_original q c σ τ υ φ)
    (loopRepresentativeAlong_preserving_reconnection_first q c σ υ)
    (loopRepresentativeAlong_preserving_reconnection_second q c σ τ υ φ) hL

end

end DifferentialGeometry.Topology.PiecewiseLinear
