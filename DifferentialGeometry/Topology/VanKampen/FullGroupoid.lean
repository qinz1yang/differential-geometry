/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import DifferentialGeometry.Topology.VanKampen.HomotopyInvariance

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def subsetToAmbient {X : Type u} [TopologicalSpace X] (A : Set X) : C(A, X) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

theorem fundamentalGroupoid_coverSquare_commutes
    {X : Type u} [TopologicalSpace X] (U V : Set X) :
    FundamentalGroupoid.map (interToLeft U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient U) =
      FundamentalGroupoid.map (interToRight U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient V) := by
  apply CategoryTheory.Functor.hext
  · intro z
    apply FundamentalGroupoid.ext
    rfl
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        apply Path.Homotopic.hpath_hext
        intro t
        rfl

theorem range_path_map_subsetToAmbient {X : Type u} [TopologicalSpace X]
    {A : Set X} {a b : A} (p : _root_.Path a b) :
    range (p.map (subsetToAmbient A).continuous) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact (p t).2

theorem pathIn_map_subsetToAmbient {X : Type u} [TopologicalSpace X]
    {A : Set X} {a b : A} (p : _root_.Path a b)
    (hp : range (p.map (subsetToAmbient A).continuous) ⊆ A) :
    pathIn A (p.map (subsetToAmbient A).continuous) hp = p := by
  apply _root_.Path.ext
  rfl

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def descendedEvaluation (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} :
    Path.Homotopic.Quotient x y → (F.gluedObj hcover x ⟶ F.gluedObj hcover y) :=
  Quotient.lift (F.rawEvaluation hU hV hcover)
    (fun _ _ hpq ↦ F.rawEvaluation_eq_of_homotopic hU hV hcover hpq)

@[simp]
theorem descendedEvaluation_mk (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y) :
    F.descendedEvaluation hU hV hcover (Path.Homotopic.Quotient.mk p) =
      F.rawEvaluation hU hV hcover p :=
  rfl

noncomputable def extension (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) : FundamentalGroupoid X ⥤ G where
  obj x := F.gluedObj hcover x.as
  map γ := F.descendedEvaluation hU hV hcover γ
  map_id x := by
    change F.rawEvaluation hU hV hcover (_root_.Path.refl x.as) =
      𝟙 (F.gluedObj hcover x.as)
    exact F.rawEvaluation_refl hU hV hcover x.as
  map_comp := by
    rintro a b c γ δ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction δ using Path.Homotopic.Quotient.ind with
      | mk q =>
        exact F.rawEvaluation_trans hU hV hcover p q

theorem extension_comp_left (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙ F.extension hU hV hcover = F.left := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.gluedObj_eq_left hcover z.as.2
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        let hp := range_path_map_subsetToAmbient p
        change F.rawEvaluation hU hV hcover
            (p.map (subsetToAmbient U).continuous) ≍
          F.left.map (Path.Homotopic.Quotient.mk p)
        rw [F.rawEvaluation_eq_leftPathMap hU hV hcover _ hp]
        unfold leftPathMap
        exact (normalizeHom_heq _ _ _).trans (heq_of_eq (congrArg F.left.map
          (congrArg Path.Homotopic.Quotient.mk (pathIn_map_subsetToAmbient p hp))))

theorem extension_comp_right (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient V) ⋙ F.extension hU hV hcover = F.right := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.gluedObj_eq_right hcover z.as.2
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        let hp := range_path_map_subsetToAmbient p
        change F.rawEvaluation hU hV hcover
            (p.map (subsetToAmbient V).continuous) ≍
          F.right.map (Path.Homotopic.Quotient.mk p)
        rw [F.rawEvaluation_eq_rightPathMap hU hV hcover _ hp]
        unfold rightPathMap
        exact (normalizeHom_heq _ _ _).trans (heq_of_eq (congrArg F.right.map
          (congrArg Path.Homotopic.Quotient.mk (pathIn_map_subsetToAmbient p hp))))

theorem alternate_obj_eq (_hU : IsOpen U) (_hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    (z : FundamentalGroupoid X) : L.obj z = F.gluedObj hcover z.as := by
  classical
  by_cases hzU : z.as ∈ U
  · let zu : FundamentalGroupoid U := ⟨⟨z.as, hzU⟩⟩
    have h := CategoryTheory.Functor.congr_obj hleft zu
    have hzu : (FundamentalGroupoid.map (subsetToAmbient U)).obj zu = z := by
      apply FundamentalGroupoid.ext
      rfl
    calc
      L.obj z = L.obj ((FundamentalGroupoid.map (subsetToAmbient U)).obj zu) :=
        congrArg L.obj hzu.symm
      _ = F.left.obj zu := h
      _ = F.gluedObj hcover z.as := by
        symm
        exact F.gluedObj_eq_left hcover hzU
  · have hzV : z.as ∈ V := by
      have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
      exact hz.resolve_left hzU
    let zv : FundamentalGroupoid V := ⟨⟨z.as, hzV⟩⟩
    have h := CategoryTheory.Functor.congr_obj hright zv
    have hzv : (FundamentalGroupoid.map (subsetToAmbient V)).obj zv = z := by
      apply FundamentalGroupoid.ext
      rfl
    calc
      L.obj z = L.obj ((FundamentalGroupoid.map (subsetToAmbient V)).obj zv) :=
        congrArg L.obj hzv.symm
      _ = F.right.obj zv := h
      _ = F.gluedObj hcover z.as := by
        symm
        exact F.gluedObj_eq_right hcover hzV

theorem alternate_map_mk_heq_sidePathMap (_hU : IsOpen U) (_hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) :
    L.map (Path.Homotopic.Quotient.mk p) ≍ F.sidePathMap hcover p side hp := by
  cases side with
  | left =>
      let hpU : range p ⊆ U := by simpa [CoverSide.set] using hp
      let pU := pathIn U p hpU
      have hmap := CategoryTheory.Functor.hcongr_hom hleft
        (Path.Homotopic.Quotient.mk pU)
      change L.map ((Path.Homotopic.Quotient.mk pU).map (subsetToAmbient U)) ≍
        F.left.map (Path.Homotopic.Quotient.mk pU) at hmap
      have hq : (Path.Homotopic.Quotient.mk pU).map (subsetToAmbient U) =
          Path.Homotopic.Quotient.mk p := by
        apply congrArg Path.Homotopic.Quotient.mk
        apply _root_.Path.ext
        rfl
      rw [hq] at hmap
      change L.map (Path.Homotopic.Quotient.mk p) ≍ F.leftPathMap hcover p hpU
      unfold leftPathMap
      exact hmap.trans (normalizeHom_heq _ _ _).symm
  | right =>
      let hpV : range p ⊆ V := by simpa [CoverSide.set] using hp
      let pV := pathIn V p hpV
      have hmap := CategoryTheory.Functor.hcongr_hom hright
        (Path.Homotopic.Quotient.mk pV)
      change L.map ((Path.Homotopic.Quotient.mk pV).map (subsetToAmbient V)) ≍
        F.right.map (Path.Homotopic.Quotient.mk pV) at hmap
      have hq : (Path.Homotopic.Quotient.mk pV).map (subsetToAmbient V) =
          Path.Homotopic.Quotient.mk p := by
        apply congrArg Path.Homotopic.Quotient.mk
        apply _root_.Path.ext
        rfl
      rw [hq] at hmap
      change L.map (Path.Homotopic.Quotient.mk p) ≍ F.rightPathMap hcover p hpV
      unfold rightPathMap
      exact hmap.trans (normalizeHom_heq _ _ _).symm

theorem mappedStandardPathChain_hom_heq (L : FundamentalGroupoid X ⥤ G)
    {x y : X} (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) :
    ((L.mapComposableArrows n).obj (standardPathChain p n)).hom ≍
      L.map (Path.Homotopic.Quotient.mk p) := by
  have h0 : (standardPathChain p n).left = FundamentalGroupoid.mk x := by
    apply FundamentalGroupoid.ext
    change p (standardTime n 0) = x
    rw [standardTime_zero, p.source]
  have h1 : (standardPathChain p n).right = FundamentalGroupoid.mk y := by
    apply FundamentalGroupoid.ext
    change p (standardTime n (Fin.last n)) = y
    rw [standardTime_last hn, p.target]
  have hraw : (standardPathChain p n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk p ≫ eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq p hn)
  change L.map (standardPathChain p n).hom ≍
    L.map (Path.Homotopic.Quotient.mk p)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg L.obj h0) (congrArg L.obj h1)).mp
  rw [hraw, L.map_comp, L.map_comp]
  simp only [CategoryTheory.eqToHom_map]

noncomputable def alternateNormalizedChain (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) (n : ℕ) : ComposableArrows G n :=
  normalizedChainOf
    (fun i ↦ F.gluedObj hcover (p (standardTime n i)))
    ((L.mapComposableArrows n).obj (standardPathChain p n))
    (fun i ↦ (F.alternate_obj_eq hU hV hcover L hleft hright
      ⟨p (standardTime n i)⟩).symm)

set_option backward.isDefEq.respectTransparency false in
theorem alternateNormalizedChain_eq_assignedChain
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) {n : ℕ} (sigma : CoverAssignment p U V n) :
    F.alternateNormalizedChain hU hV hcover L hleft hright p n =
      F.assignedChain hcover p sigma := by
  unfold alternateNormalizedChain normalizedChainOf assignedChain
  congr 1
  funext i
  change normalizeHom
      ((F.alternate_obj_eq hU hV hcover L hleft hright
        ⟨p (standardTime n i.castSucc)⟩).symm)
      ((F.alternate_obj_eq hU hV hcover L hleft hright
        ⟨p (standardTime n i.succ)⟩).symm)
      (L.map (Path.Homotopic.Quotient.mk (standardSubpath p i))) =
        F.sidePathMap hcover (standardSubpath p i) (sigma.side i) (sigma.range_subset i)
  calc
    normalizeHom
        ((F.alternate_obj_eq hU hV hcover L hleft hright
          ⟨p (standardTime n i.castSucc)⟩).symm)
        ((F.alternate_obj_eq hU hV hcover L hleft hright
          ⟨p (standardTime n i.succ)⟩).symm)
        (L.map (Path.Homotopic.Quotient.mk (standardSubpath p i))) =
      normalizeHom rfl rfl
        (F.sidePathMap hcover (standardSubpath p i) (sigma.side i)
          (sigma.range_subset i)) := by
        apply normalizeHom_eq_of_heq
        exact F.alternate_map_mk_heq_sidePathMap hU hV hcover L hleft hright
          (standardSubpath p i) (sigma.side i) (sigma.range_subset i)
    _ = F.sidePathMap hcover (standardSubpath p i) (sigma.side i)
        (sigma.range_subset i) := by simp [normalizeHom]

set_option backward.isDefEq.respectTransparency false in
theorem alternate_map_mk_heq_rawEvaluation
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) :
    L.map (Path.Homotopic.Quotient.mk p) ≍ F.rawEvaluation hU hV hcover p := by
  obtain ⟨n, hn, hp⟩ := Path.exists_isCovered p hU hV hcover
  let sigma := CoverAssignment.ofIsCovered hp
  let mappedChain := (L.mapComposableArrows n).obj (standardPathChain p n)
  let normalizedChain := F.alternateNormalizedChain hU hV hcover L hleft hright p n
  have hmapped : mappedChain.hom ≍ L.map (Path.Homotopic.Quotient.mk p) := by
    exact mappedStandardPathChain_hom_heq L p hn
  have hnormalized : normalizedChain.hom ≍ mappedChain.hom := by
    unfold normalizedChain alternateNormalizedChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have hassigned : normalizedChain.hom ≍ (F.assignedChain hcover p sigma).hom := by
    apply Functor.hcongr_hom
    exact F.alternateNormalizedChain_eq_assignedChain hU hV hcover L hleft hright p sigma
  have hcovered : (F.assignedChain hcover p sigma).hom ≍
      F.coveredEvaluation hcover p hn hp := by
    unfold sigma coveredEvaluation assignedEvaluation
    exact (normalizeHom_heq _ _ _).symm
  have hraw : F.coveredEvaluation hcover p hn hp ≍
      F.rawEvaluation hU hV hcover p := by
    exact heq_of_eq (F.rawEvaluation_eq_covered hU hV hcover p hn hp).symm
  exact hmapped.symm.trans
    (hnormalized.symm.trans (hassigned.trans (hcovered.trans hraw)))

theorem extension_unique (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right) :
    L = F.extension hU hV hcover := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.alternate_obj_eq hU hV hcover L hleft hright z
  · intro a b gamma
    induction gamma using Path.Homotopic.Quotient.ind with
    | mk p =>
        exact F.alternate_map_mk_heq_rawEvaluation hU hV hcover L hleft hright p

end LocalFunctorData

def fullGroupoidSquareIsPushoutStatement
    {X : Type u} [TopologicalSpace X] (U V : Set X) : Prop :=
  @IsPushout Grpd.{u, u} _
    (Grpd.of (FundamentalGroupoid (↑(U ∩ V))))
    (Grpd.of (FundamentalGroupoid U))
    (Grpd.of (FundamentalGroupoid V))
    (Grpd.of (FundamentalGroupoid X))
    (FundamentalGroupoid.map (interToLeft U V))
    (FundamentalGroupoid.map (interToRight U V))
    (FundamentalGroupoid.map (subsetToAmbient U))
    (FundamentalGroupoid.map (subsetToAmbient V))

theorem seifertVanKampen {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    fullGroupoidSquareIsPushoutStatement U V := by
  unfold fullGroupoidSquareIsPushoutStatement
  refine { w := by exact fundamentalGroupoid_coverSquare_commutes U V, isColimit' := ?_ }
  constructor
  apply PushoutCocone.isColimitAux'
  intro s
  let F : LocalFunctorData U V s.pt := {
    left := s.inl
    right := s.inr
    compatibility := s.condition }
  refine ⟨F.extension hU hV hcover, ?_, ?_, ?_⟩
  · exact F.extension_comp_left hU hV hcover
  · exact F.extension_comp_right hU hV hcover
  · intro L hleft hright
    exact F.extension_unique hU hV hcover L hleft hright

end DifferentialGeometry.Topology.VanKampen
