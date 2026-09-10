import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

namespace Poincare.SSet

variable {X : _root_.SSet.{u}} (s : X.N)


def costar : X.Subcomplex where
  obj m := {x | ¬s.subcomplex ≤ Subfunctor.ofSection x}
  map {m l} f x hx h := hx (h.trans (by
    rw [Subfunctor.ofSection_le_iff]
    exact ⟨f, rfl⟩))


@[simp]
theorem mem_costar_iff {m : SimplexCategoryᵒᵖ} (x : X.obj m) :
    x ∈ (costar s).obj m ↔ ¬s.subcomplex ≤ Subfunctor.ofSection x := Iff.rfl


theorem notMem_costar : s.simplex ∉ (costar s).obj _ := by
  exact fun h ↦ h le_rfl


def nondegenerateCellMap : (Δ[s.dim] : _root_.SSet.{u}) ⟶ X :=
  _root_.SSet.yonedaEquiv.symm s.simplex


theorem costar_preimage_cellMap :
    (costar s).preimage (nondegenerateCellMap s) = _root_.SSet.boundary s.dim := by
  ext ⟨⟨m⟩⟩ x
  obtain ⟨f, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective x
  change (¬s.subcomplex ≤ _root_.SSet.Subcomplex.ofSimplex
    (X.map f.op s.simplex)) ↔ ¬Function.Surjective f.toOrderHom
  rw [← SimplexCategory.epi_iff_surjective]
  apply not_congr
  constructor
  · intro h
    rw [_root_.SSet.Subcomplex.ofSimplex_le_iff,
      _root_.SSet.Subcomplex.mem_ofSimplex_obj_iff] at h
    obtain ⟨g, hg⟩ := h
    have hcomp : X.map (g ≫ f).op s.simplex = s.simplex := by
      simpa only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] using hg
    have : Mono (g ≫ f) := X.mono_of_nonDegenerate ⟨_, s.nonDegenerate⟩ _ _ hcomp
    have heq := SimplexCategory.eq_id_of_mono (g ≫ f)
    have : Epi (g ≫ f) := by rw [heq]; infer_instance
    exact epi_of_epi g f
  · intro hf
    rw [_root_.SSet.Subcomplex.ofSimplex_map_of_epi]

theorem nondegenerate_mem_costar_iff (t : X.N) :
    t.simplex ∈ (costar s).obj _ ↔ ¬s ≤ t := Iff.rfl


theorem costar_sup_cell_eq_top (hs : IsMax s) :
    costar s ⊔ s.subcomplex = ⊤ := by
  apply top_unique
  rw [← _root_.SSet.N.iSup_subcomplex_eq_top X]
  apply iSup_le
  intro t
  by_cases h : s ≤ t
  · have ht : t = s := le_antisymm (hs h) h
    rw [ht]
    exact le_sup_right
  · exact (show t.subcomplex ≤ costar s from
      (Subfunctor.ofSection_le_iff _ _).mpr h).trans le_sup_left


theorem nondegenerateCellMap_injOn_compl_boundary (m : ℕ) :
    Set.InjOn ((nondegenerateCellMap s).app (op ⦋m⦌))
      ((_root_.SSet.boundary s.dim).obj (op ⦋m⦌))ᶜ := by
  intro x hx y hy h
  obtain ⟨f, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective x
  obtain ⟨g, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective y
  have : Epi f := by
    simpa [_root_.SSet.boundary, SimplexCategory.epi_iff_surjective] using! hx
  have h' : X.map f.op s.simplex = X.map g.op s.simplex := h
  have heq := X.unique_nonDegenerate_map _ f ⟨_, s.nonDegenerate⟩ rfl
    g ⟨_, s.nonDegenerate⟩ h'
  rw [heq]

def costarAttachingMap : (_root_.SSet.boundary s.dim : _root_.SSet.{u}) ⟶ costar s :=
  _root_.SSet.Subcomplex.lift ((_root_.SSet.boundary s.dim).ι ≫ nondegenerateCellMap s) (by
    rw [_root_.SSet.Subcomplex.range_comp, _root_.SSet.Subcomplex.image_le_iff,
      costar_preimage_cellMap]
    simp)


@[reassoc (attr := simp)]
theorem costarAttachingMap_inclusion :
    costarAttachingMap s ≫ (costar s).ι =
      (_root_.SSet.boundary s.dim).ι ≫ nondegenerateCellMap s := rfl


theorem costar_cell_isPullback :
    IsPullback (costarAttachingMap s) (_root_.SSet.boundary s.dim).ι
      (costar s).ι (nondegenerateCellMap s) where
  w := costarAttachingMap_inclusion s
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨m⟩⟩ ↦ by
    apply (isLimitMapConePullbackConeEquiv _ _).2
    apply IsPullback.isLimit
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro x y h
      exact Subtype.ext h.2
    · intro x y h
      change x.val = (nondegenerateCellMap s).app _ y at h
      have hy : y ∈ (_root_.SSet.boundary s.dim).obj (op ⦋m⦌) := by
        rw [← costar_preimage_cellMap s]
        change (nondegenerateCellMap s).app _ y ∈ (costar s).obj _
        rw [← h]
        exact x.prop
      exact ⟨⟨y, hy⟩, Subtype.ext h.symm, rfl⟩)⟩

theorem costar_cell_isPushout (hs : IsMax s) :
    IsPushout (_root_.SSet.boundary s.dim).ι (costarAttachingMap s)
      (nondegenerateCellMap s) (costar s).ι := by
  apply IsPushout.flip
  refine { w := costarAttachingMap_inclusion s, isColimit' := ⟨?_⟩ }
  apply evaluationJointlyReflectsColimits _
  intro ⟨⟨m⟩⟩
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).2
  apply IsPushout.isColimit
  apply Types.isPushout_of_isPullback_of_mono'
  · exact (costar_cell_isPullback s).map ((evaluation _ _).obj _)
  · have hsup := congrArg (fun A : X.Subcomplex ↦ A.obj (op ⦋m⦌))
      (costar_sup_cell_eq_top s hs)
    have hr : _root_.SSet.Subcomplex.range (nondegenerateCellMap s) = s.subcomplex :=
      by simpa [nondegenerateCellMap] using
        _root_.SSet.Subcomplex.range_eq_ofSimplex (nondegenerateCellMap s)
    have hr' := congrArg (fun A : X.Subcomplex ↦ A.obj (op ⦋m⦌)) hr
    change Set.range (fun x : (costar s).obj (op ⦋m⦌) ↦ x.val) ∪
      Set.range ((nondegenerateCellMap s).app (op ⦋m⦌)) = Set.univ
    rw [Subtype.range_coe_subtype]
    change Set.range ((nondegenerateCellMap s).app (op ⦋m⦌)) = _ at hr'
    rw [hr']
    exact hsup
  · intro x y hx hy h
    apply nondegenerateCellMap_injOn_compl_boundary s m
    · exact fun hx' ↦ hx ⟨⟨x, hx'⟩, rfl⟩
    · exact fun hy' ↦ hy ⟨⟨y, hy'⟩, rfl⟩
    · exact h

def costarNondegenerateEquiv :
    (costar s : _root_.SSet).N ≃ {t : X.N // ¬s ≤ t} where
  toFun t := ⟨_root_.SSet.N.mk t.simplex.val
    (((costar s).mem_nonDegenerate_iff t.simplex).mp t.nonDegenerate), t.simplex.prop⟩
  invFun t := _root_.SSet.N.mk ⟨t.val.simplex, t.prop⟩
    (((costar s).mem_nonDegenerate_iff ⟨t.val.simplex, t.prop⟩).mpr t.val.nonDegenerate)
  left_inv t := by cases t; rfl
  right_inv t := by rcases t with ⟨t, ht⟩; cases t; rfl

theorem card_costar_nondegenerate_lt [X.Finite] :
    Nat.card (costar s : _root_.SSet).N < Nat.card X.N := by
  classical
  let := Fintype.ofFinite X.N
  let := Fintype.ofFinite (costar s : _root_.SSet).N
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective
    (fun t ↦ (costarNondegenerateEquiv s t).val)
    (Subtype.val_injective.comp (costarNondegenerateEquiv s).injective)
  intro h
  obtain ⟨t, ht⟩ := h s
  exact (costarNondegenerateEquiv s t).prop (le_of_eq ht.symm)

end Poincare.SSet
