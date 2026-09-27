/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.CellIdentity
import DifferentialGeometry.Topology.VanKampen.GroupoidTelescope

set_option autoImplicit false

open CategoryTheory Set unitInterval
open scoped unitInterval

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) : C(I × I, X) where
  toFun z := K (z.2, z.1)
  continuous_toFun := K.continuous.comp (by fun_prop)

noncomputable def homotopyVerticalEdge {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (k : Fin (n + 1)) (j : Fin n) :
    _root_.Path (K.eval (standardTime n j.castSucc) (standardTime n k))
      (K.eval (standardTime n j.succ) (standardTime n k)) where
  toFun t := K (Set.Icc.convexComb (standardTime n j.castSucc)
    (standardTime n j.succ) t, standardTime n k)
  continuous_toFun := K.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

theorem gridBottom_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridBottom (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.castSucc)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.2 : ℝ) = standardTime n j.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell10]
    ring
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

theorem gridTop_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridTop (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.succ)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.2 : ℝ) = standardTime n j.succ
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell01, gridCell11]
    ring
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

theorem gridLeft_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridLeft (homotopySquare K) hn i j = homotopyVerticalEdge K i.castSucc j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.1 : ℝ) = standardTime n i.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell01]
    ring

theorem gridRight_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridRight (homotopySquare K) hn i j = homotopyVerticalEdge K i.succ j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.1 : ℝ) = standardTime n i.succ
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell10, gridCell11]
    ring

theorem LocalFunctorData.rawEvaluation_heq_of_pointwise
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y x' y' : X} (p : _root_.Path x y) (q : _root_.Path x' y')
    (h : ∀ t, p t = q t) :
    F.rawEvaluation hU hV hcover p ≍ F.rawEvaluation hU hV hcover q := by
  have hx : x = x' := p.source.symm.trans ((h 0).trans q.source)
  have hy : y = y' := p.target.symm.trans ((h 1).trans q.target)
  subst x'
  subst y'
  have hpq : p = q := by
    apply _root_.Path.ext
    funext t
    exact h t
  subst q
  exact HEq.rfl

theorem LocalFunctorData.rawEvaluation_eq_sidePathMap
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover p = F.sidePathMap hcover p side hp := by
  cases side
  · exact F.rawEvaluation_eq_leftPathMap hU hV hcover p hp
  · exact F.rawEvaluation_eq_rightPathMap hU hV hcover p hp

noncomputable def LocalFunctorData.rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) : ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun k ↦ F.gluedObj hcover (K.eval (standardTime n r) (standardTime n k)))
    (fun i ↦ F.rawEvaluation hU hV hcover
      (standardSubpath (K.eval (standardTime n r)) i))

theorem LocalFunctorData.rawRowChain_map_succ
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) (i : ℕ) (hi : i < n) :
    (F.rawRowChain hU hV hcover K n r).map' i (i + 1) =
      F.rawEvaluation hU hV hcover
        (standardSubpath (K.eval (standardTime n r)) ⟨i, hi⟩) := by
  apply ComposableArrows.mkOfObjOfMapSucc_map_succ

theorem homotopyRow_isCovered_bottom {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.castSucc)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell

theorem homotopyRow_isCovered_top {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.succ)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell

set_option backward.isDefEq.respectTransparency false in
theorem LocalFunctorData.rawRowChain_eq_assignedChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawRowChain hU hV hcover K n r =
      F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp) := by
  unfold LocalFunctorData.rawRowChain LocalFunctorData.assignedChain
  congr 1
  funext i
  exact F.rawEvaluation_eq_sidePathMap hU hV hcover _ _ _

theorem LocalFunctorData.rawRowChain_hom_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    (F.rawRowChain hU hV hcover K n r).hom ≍
      F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) := by
  rw [F.rawRowChain_eq_assignedChain hU hV hcover K r hp]
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  exact (LocalFunctorData.normalizeHom_heq _ _ _).symm

noncomputable def LocalFunctorData.rawRowTransformation
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawRowChain hU hV hcover K n j.castSucc ⟶
      F.rawRowChain hU hV hcover K n j.succ :=
  ComposableArrows.homMk
    (fun k ↦ F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j))
    (by
      intro i hi
      rw [F.rawRowChain_map_succ hU hV hcover K n j.castSucc i hi,
        F.rawRowChain_map_succ hU hV hcover K n j.succ i hi]
      let k : Fin n := ⟨i, hi⟩
      change F.rawEvaluation hU hV hcover
          (standardSubpath (K.eval (standardTime n j.castSucc)) k) ≫
            F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.succ j) =
        F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.castSucc j) ≫
          F.rawEvaluation hU hV hcover
            (standardSubpath (K.eval (standardTime n j.succ)) k)
      rw [← gridBottom_homotopySquare K hn k j,
        ← gridRight_homotopySquare K hn k j,
        ← gridLeft_homotopySquare K hn k j,
        ← gridTop_homotopySquare K hn k j]
      exact F.cell_boundary hU hV hcover (homotopySquare K) hn hgrid k j)

theorem LocalFunctorData.rawRowTransformation_app
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) (k : Fin (n + 1)) :
    (F.rawRowTransformation hU hV hcover K hn hgrid j).app k =
      F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j) :=
  rfl

theorem homotopyVerticalEdge_zero_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ}
    (j : Fin n) (t : I) : homotopyVerticalEdge K (0 : Fin (n + 1)) j t = x := by
  simp [homotopyVerticalEdge]

theorem homotopyVerticalEdge_last_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (j : Fin n) (t : I) : homotopyVerticalEdge K (Fin.last n) j t = y := by
  simp [homotopyVerticalEdge, standardTime_last hn]

theorem LocalFunctorData.rawRowTransformation_app_zero_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) 0 ≍
      𝟙 (F.gluedObj hcover x) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (0 : Fin (n + 1)) j) ≍ 𝟙 (F.gluedObj hcover x)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (0 : Fin (n + 1)) j) (_root_.Path.refl x)
      (homotopyVerticalEdge_zero_apply K j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover x))

theorem LocalFunctorData.rawRowTransformation_app_last_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) n ≍
      𝟙 (F.gluedObj hcover y) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (Fin.last n) j) ≍ 𝟙 (F.gluedObj hcover y)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (Fin.last n) j) (_root_.Path.refl y)
      (homotopyVerticalEdge_last_apply K hn j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover y))

theorem LocalFunctorData.normalizeHom_inv
    {G : Type v} [Groupoid G] {a a' b b' : G}
    (ha : a = a') (hb : b = b') (f : a' ⟶ b') :
    LocalFunctorData.normalizeHom hb ha (inv f) =
      inv (LocalFunctorData.normalizeHom ha hb f) := by
  subst a'
  subst b'
  simp [LocalFunctorData.normalizeHom]

theorem LocalFunctorData.gluedObj_eq_rawRowChain_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) :
    F.gluedObj hcover x = (F.rawRowChain hU hV hcover K n r).left := by
  change F.gluedObj hcover x =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n 0))
  apply congrArg (F.gluedObj hcover)
  simp

theorem LocalFunctorData.gluedObj_eq_rawRowChain_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1)) :
    F.gluedObj hcover y = (F.rawRowChain hU hV hcover K n r).right := by
  change F.gluedObj hcover y =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n (Fin.last n)))
  apply congrArg (F.gluedObj hcover)
  simp [standardTime_last hn]

theorem LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) =
      LocalFunctorData.normalizeHom
        (F.gluedObj_eq_rawRowChain_left hU hV hcover K n r)
        (F.gluedObj_eq_rawRowChain_right hU hV hcover K hn r)
        (F.rawRowChain hU hV hcover K n r).hom := by
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  apply LocalFunctorData.normalizeHom_eq_of_heq
  have hhom :
      (F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp)).hom ≍
        (F.rawRowChain hU hV hcover K n r).hom := by
    apply Functor.hcongr_hom
    exact (F.rawRowChain_eq_assignedChain hU hV hcover K r hp).symm
  exact hhom

theorem LocalFunctorData.rawEvaluation_eval_succ_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) =
      F.rawEvaluation hU hV hcover (K.eval (standardTime n j.castSucc)) := by
  let R := F.rawRowChain hU hV hcover K n j.castSucc
  let S := F.rawRowChain hU hV hcover K n j.succ
  let α : R ⟶ S := F.rawRowTransformation hU hV hcover K hn hgrid j
  have htel : S.hom =
      inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) :=
    groupoid_telescope α
  have hα0 : ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≍
      𝟙 (F.gluedObj hcover x) := by
    exact F.rawRowTransformation_app_zero_heq hU hV hcover K hn hgrid j
  have hαn : ComposableArrows.app' α n (hi := le_rfl) ≍
      𝟙 (F.gluedObj hcover y) := by
    exact F.rawRowTransformation_app_last_heq hU hV hcover K hn hgrid j
  let rx : F.gluedObj hcover x = R.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.castSucc
  let sx : F.gluedObj hcover x = S.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.succ
  let ry : F.gluedObj hcover y = R.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.castSucc
  let sy : F.gluedObj hcover y = S.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.succ
  have hα0Norm : LocalFunctorData.normalizeHom rx sx
      (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) = 𝟙 (F.gluedObj hcover x) := by
    calc
      LocalFunctorData.normalizeHom rx sx
          (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover x)) :=
        LocalFunctorData.normalizeHom_eq_of_heq rx rfl sx rfl _ _ hα0
      _ = 𝟙 (F.gluedObj hcover x) := LocalFunctorData.normalizeHom_id rfl
  have hαnNorm : LocalFunctorData.normalizeHom ry sy
      (ComposableArrows.app' α n (hi := le_rfl)) = 𝟙 (F.gluedObj hcover y) := by
    calc
      LocalFunctorData.normalizeHom ry sy
          (ComposableArrows.app' α n (hi := le_rfl)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover y)) :=
        LocalFunctorData.normalizeHom_eq_of_heq ry rfl sy rfl _ _ hαn
      _ = 𝟙 (F.gluedObj hcover y) := LocalFunctorData.normalizeHom_id rfl
  have hnorm : LocalFunctorData.normalizeHom sx sy S.hom =
      LocalFunctorData.normalizeHom rx ry R.hom := by
    rw [htel]
    rw [LocalFunctorData.normalizeHom_comp sx rx sy
      (inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)))
      (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_comp rx ry sy R.hom
      (ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_inv rx sx,
      hα0Norm, hαnNorm]
    simp
  rw [F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.succ
      (homotopyRow_isCovered_top K hn hgrid j),
    F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.castSucc
      (homotopyRow_isCovered_bottom K hn hgrid j)]
  exact hnorm

theorem LocalFunctorData.rawEvaluation_eq_of_homotopyGrid
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  have hrows : ∀ (k : ℕ) (hk : k ≤ n),
      F.rawEvaluation hU hV hcover
          (K.eval (standardTime n ⟨k, Nat.lt_succ_of_le hk⟩)) =
        F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        let j : Fin n := ⟨k, hklt⟩
        calc
          F.rawEvaluation hU hV hcover
              (K.eval (standardTime n ⟨k + 1, Nat.lt_succ_of_le hk⟩)) =
              F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) := by
                rfl
          _ = F.rawEvaluation hU hV hcover
              (K.eval (standardTime n j.castSucc)) :=
                F.rawEvaluation_eval_succ_eq hU hV hcover K hn hgrid j
          _ = F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) :=
                ih (Nat.le_of_succ_le hk)
  have hlast := hrows n le_rfl
  have hfin : (⟨n, Nat.lt_succ_of_le (le_refl n)⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    rfl
  rw [hfin, standardTime_last hn] at hlast
  simpa using hlast.symm

theorem LocalFunctorData.rawEvaluation_eq_of_homotopy
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  obtain ⟨n, hn, hgrid⟩ := exists_coveredGrid (homotopySquare K) hU hV hcover
  exact F.rawEvaluation_eq_of_homotopyGrid hU hV hcover K hn hgrid

theorem LocalFunctorData.rawEvaluation_eq_of_homotopic
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (hpq : p.Homotopic q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  rcases hpq with ⟨K⟩
  exact F.rawEvaluation_eq_of_homotopy hU hV hcover K

end DifferentialGeometry.Topology.VanKampen
