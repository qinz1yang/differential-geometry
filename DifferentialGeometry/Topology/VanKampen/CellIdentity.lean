/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Homotopy.Product
import DifferentialGeometry.Topology.VanKampen.Evaluation
import DifferentialGeometry.Topology.VanKampen.HomotopyGrid

set_option autoImplicit false

open CategoryTheory Set unitInterval
open scoped unitInterval

universe u v

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def convexSubtypeSegment {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) (a b : S) : _root_.Path a b where
  toFun t := ⟨AffineMap.lineMap a.1 b.1 (t : ℝ), hS.lineMap_mem a.2 b.2 t.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  source' := by
    apply Subtype.ext
    simp
  target' := by
    apply Subtype.ext
    simp

noncomputable def convexSubtypePathHomotopy {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) {a b : S} (p q : _root_.Path a b) :
    p.Homotopy q where
  toFun z := ⟨AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ),
    hS.lineMap_mem (p z.2).2 (q z.2).2 z.1.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp
  map_one_left t := by
    apply Subtype.ext
    simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      apply Subtype.ext
      simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Subtype.ext
      simp

def gridCellSet {n : ℕ} (i j : Fin n) : Set (ℝ × ℝ) :=
  Icc (standardTime n i.castSucc : ℝ) (standardTime n i.succ : ℝ) ×ˢ
    Icc (standardTime n j.castSucc : ℝ) (standardTime n j.succ : ℝ)

abbrev GridCell {n : ℕ} (i j : Fin n) := ↥(gridCellSet i j)

theorem convex_gridCellSet {n : ℕ} (i j : Fin n) : Convex ℝ (gridCellSet i j) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

noncomputable def gridCell00 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

noncomputable def gridCell10 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

noncomputable def gridCell01 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

noncomputable def gridCell11 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

def gridCellInclusion {n : ℕ} (i j : Fin n) : C(GridCell i j, I × I) where
  toFun z :=
    (⟨z.1.1, (standardTime n i.castSucc).2.1.trans z.2.1.1,
        z.2.1.2.trans (standardTime n i.succ).2.2⟩,
      ⟨z.1.2, (standardTime n j.castSucc).2.1.trans z.2.2.1,
        z.2.2.2.trans (standardTime n j.succ).2.2⟩)
  continuous_toFun := by fun_prop

def gridCellMap {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (i j : Fin n) : C(GridCell i j, X) :=
  H.comp (gridCellInclusion i j)

noncomputable def cellBottom {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell10 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellRight {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell10 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellLeft {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell01 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellTop {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell01 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def gridBottom {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellBottom hn i j).map (gridCellMap H i j).continuous

noncomputable def gridRight {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellRight hn i j).map (gridCellMap H i j).continuous

noncomputable def gridLeft {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellLeft hn i j).map (gridCellMap H i j).continuous

noncomputable def gridTop {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellTop hn i j).map (gridCellMap H i j).continuous

noncomputable def gridCellParameterHomotopy {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ((cellBottom hn i j).trans (cellRight hn i j)).Homotopy
      ((cellLeft hn i j).trans (cellTop hn i j)) :=
  convexSubtypePathHomotopy (convex_gridCellSet i j)
    ((cellBottom hn i j).trans (cellRight hn i j))
    ((cellLeft hn i j).trans (cellTop hn i j))

noncomputable def gridCellBoundaryHomotopy {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (gridBottom H hn i j).trans (gridRight H hn i j) |>.Homotopy
      ((gridLeft H hn i j).trans (gridTop H hn i j)) where
  toFun z := gridCellMap H i j (gridCellParameterHomotopy hn i j z)
  continuous_toFun := (gridCellMap H i j).continuous.comp
    (gridCellParameterHomotopy hn i j).continuous
  map_zero_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (0, t)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_zero_left t)
  map_one_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (1, t)) =
      ((cellLeft hn i j).map (gridCellMap H i j).continuous).trans
        ((cellTop hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_one_left t)
  prop' t s hs := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (t, s)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) s
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).prop' t s hs)

theorem gridCellMap_mem_of_image_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : GridCell i j) : gridCellMap H i j z ∈ A := by
  apply hcell
  refine ⟨gridCellInclusion i j z, ?_, rfl⟩
  constructor
  · constructor
    · exact_mod_cast z.2.1.1
    · exact_mod_cast z.2.1.2
  · constructor
    · exact_mod_cast z.2.2.1
    · exact_mod_cast z.2.2.2

def pathHomotopyIn {X : Type u} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : _root_.Path x y} (hp : range p ⊆ A) (hq : range q ⊆ A)
    (K : p.Homotopy q) (hK : ∀ z, K z ∈ A) :
    (pathIn A p hp).Homotopy (pathIn A q hq) where
  toFun z := ⟨K z, hK z⟩
  continuous_toFun := K.continuous.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact K.map_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact K.map_one_left t
  prop' t s hs := by
    apply Subtype.ext
    exact K.prop' t s hs

theorem LocalFunctorData.leftPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = univ) {x y : X} {p q : _root_.Path x y}
    (hp : range p ⊆ U) (hq : range q ⊆ U) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ U) :
    F.leftPathMap hcover p hp = F.leftPathMap hcover q hq := by
  unfold LocalFunctorData.leftPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.left.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

theorem LocalFunctorData.rightPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = univ) {x y : X} {p q : _root_.Path x y}
    (hp : range p ⊆ V) (hq : range q ⊆ V) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ V) :
    F.rightPathMap hcover p hp = F.rightPathMap hcover q hq := by
  unfold LocalFunctorData.rightPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.right.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

theorem range_gridBottom_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridBottom H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellBottom hn i j) t)

theorem range_gridRight_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridRight H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellRight hn i j) t)

theorem range_gridLeft_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridLeft H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellLeft hn i j) t)

theorem range_gridTop_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridTop H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellTop hn i j) t)

theorem gridCellBoundaryHomotopy_mem {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : I × I) : gridCellBoundaryHomotopy H hn i j z ∈ A := by
  exact gridCellMap_mem_of_image_subset H i j hcell
    (gridCellParameterHomotopy hn i j z)

theorem LocalFunctorData.cell_boundary_of_side
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) (side : CoverSide)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rw [← F.rawEvaluation_trans hU hV hcover (gridBottom H hn i j) (gridRight H hn i j),
    ← F.rawEvaluation_trans hU hV hcover (gridLeft H hn i j) (gridTop H hn i j)]
  have hbr : range ((gridBottom H hn i j).trans (gridRight H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact union_subset (range_gridBottom_subset H hn i j hcell)
      (range_gridRight_subset H hn i j hcell)
  have hlt : range ((gridLeft H hn i j).trans (gridTop H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact union_subset (range_gridLeft_subset H hn i j hcell)
      (range_gridTop_subset H hn i j hcell)
  have hK : ∀ z, gridCellBoundaryHomotopy H hn i j z ∈ side.set U V :=
    gridCellBoundaryHomotopy_mem H hn i j hcell
  cases side
  · rw [F.rawEvaluation_eq_leftPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_leftPathMap hU hV hcover _ hlt]
    exact F.leftPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK
  · rw [F.rawEvaluation_eq_rightPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_rightPathMap hU hV hcover _ hlt]
    exact F.rightPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK

theorem LocalFunctorData.cell_boundary
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid H U V n)
    (i j : Fin n) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rcases hgrid i j with hcell | hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .left hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .right hcell

end DifferentialGeometry.Topology.VanKampen
