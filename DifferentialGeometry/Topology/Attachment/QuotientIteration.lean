import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false
noncomputable section

open Set Function Topology

namespace DifferentialGeometry.Topology

variable {P : Type*} [TopologicalSpace P]

def quotientQuotientMap {r s : Setoid P} (h : r ≤ s) :
    Quotient (Setoid.ker (Quot.mapRight h)) → Quotient s :=
  Quotient.lift (fun w => Quot.mapRight h w) (fun _ _ hw => hw)

theorem continuous_quotientQuotientMap {r s : Setoid P} (h : r ≤ s) :
    Continuous (quotientQuotientMap h) :=
  Continuous.quotient_lift (continuous_quot_map (fun _ _ hab => h hab) continuous_id)
    (fun _ _ hw => hw)

def quotientQuotientMapInv {r s : Setoid P} (h : r ≤ s) :
    Quotient s → Quotient (Setoid.ker (Quot.mapRight h)) :=
  Quotient.lift (fun a => Quotient.mk'' (Quotient.mk'' a))
    (fun _ _ hab => Quotient.sound (Quotient.sound hab))

theorem continuous_quotientQuotientMapInv {r s : Setoid P} (h : r ≤ s) :
    Continuous (quotientQuotientMapInv h) :=
  Continuous.quotient_lift
    (continuous_quotient_mk'.comp (continuous_quotient_mk' :
      Continuous (Quotient.mk'' : P → Quotient r)))
    (fun _ _ hab => Quotient.sound (Quotient.sound hab))

omit [TopologicalSpace P] in
theorem quotientQuotientMap_leftInverse {r s : Setoid P} (h : r ≤ s) :
    Function.LeftInverse (quotientQuotientMapInv h) (quotientQuotientMap h) := by
  intro z
  induction z using Quotient.inductionOn with
  | _ w => induction w using Quotient.inductionOn with | _ a => rfl

omit [TopologicalSpace P] in
theorem quotientQuotientMap_rightInverse {r s : Setoid P} (h : r ≤ s) :
    Function.RightInverse (quotientQuotientMapInv h) (quotientQuotientMap h) := by
  intro z
  induction z using Quotient.inductionOn with
  | _ a => rfl

def quotientQuotientHomeomorph {r s : Setoid P} (h : r ≤ s) :
    Quotient (Setoid.ker (Quot.mapRight h)) ≃ₜ Quotient s where
  toFun := quotientQuotientMap h
  invFun := quotientQuotientMapInv h
  left_inv := quotientQuotientMap_leftInverse h
  right_inv := quotientQuotientMap_rightInverse h
  continuous_toFun := continuous_quotientQuotientMap h
  continuous_invFun := continuous_quotientQuotientMapInv h

def quotientQuotientHomeomorph_comap {r : Setoid P} (u : Setoid (Quotient r)) :
    Quotient u ≃ₜ Quotient (Setoid.comap (Quotient.mk'' : P → Quotient r) u) := by
  have hle : r ≤ Setoid.comap (Quotient.mk'' : P → Quotient r) u := fun x y hxy => by
    have hxy' : (Quotient.mk'' x : Quotient r) = Quotient.mk'' y := Quotient.sound hxy
    change u (Quotient.mk'' x) (Quotient.mk'' y)
    exact hxy' ▸ u.refl _
  have hmap : ∀ a : P, Quot.mapRight hle (Quotient.mk'' a) =
      (Quotient.mk'' a : Quotient (Setoid.comap (Quotient.mk'' : P → Quotient r) u)) :=
    fun _ => rfl
  have hker : ∀ x y, u x y ↔ Setoid.ker (Quot.mapRight hle) x y := by
    intro x y
    change u x y ↔ Quot.mapRight hle x = Quot.mapRight hle y
    constructor
    · intro hxy
      induction x using Quotient.inductionOn with
      | _ a =>
        induction y using Quotient.inductionOn with
        | _ b =>
          have hab : Setoid.comap (Quotient.mk'' : P → Quotient r) u a b := hxy
          exact Quotient.sound hab
    · intro hxy
      induction x using Quotient.inductionOn with
      | _ a =>
        induction y using Quotient.inductionOn with
        | _ b =>
          rw [hmap a, hmap b] at hxy
          exact Quotient.exact
            (s := Setoid.comap (Quotient.mk'' : P → Quotient r) u) hxy
  let e : Quotient u ≃ₜ Quotient (Setoid.ker (Quot.mapRight hle)) :=
    Homeomorph.Quotient.congrRight hker
  exact e.trans (quotientQuotientHomeomorph hle)

theorem ker_mapRight_homeomorph_congr {P' : Type*} [TopologicalSpace P']
    {r s : Setoid P} {r' s' : Setoid P'} (h : r ≤ s) (h' : r' ≤ s')
    (e : P ≃ₜ P') (hr : ∀ x y, r x y ↔ r' (e x) (e y))
    (hs : ∀ x y, s x y ↔ s' (e x) (e y)) :
    ∀ x y, Setoid.ker (Quot.mapRight h) x y ↔
      Setoid.ker (Quot.mapRight h') ((Homeomorph.Quotient.congr e hr) x)
        ((Homeomorph.Quotient.congr e hr) y) := by
  have key : ∀ z : Quotient r, Quot.mapRight h' ((Homeomorph.Quotient.congr e hr) z) =
      (Homeomorph.Quotient.congr e hs) (Quot.mapRight h z) := by
    intro z
    induction z using Quotient.inductionOn with
    | _ a => rfl
  intro x y
  change Quot.mapRight h x = Quot.mapRight h y ↔
    Quot.mapRight h' ((Homeomorph.Quotient.congr e hr) x) =
      Quot.mapRight h' ((Homeomorph.Quotient.congr e hr) y)
  rw [key x, key y]
  exact ⟨fun hxy => congrArg (Homeomorph.Quotient.congr e hs) hxy,
    fun hxy => (Homeomorph.Quotient.congr e hs).injective hxy⟩

@[simp]
theorem quotientQuotientHomeomorph_mk {r s : Setoid P} (h : r ≤ s) (x : Quotient r) :
    quotientQuotientHomeomorph h (Quotient.mk'' x) = Quot.mapRight h x := rfl

@[simp]
theorem quotientQuotientHomeomorph_mk_mk {r s : Setoid P} (h : r ≤ s) (a : P) :
    quotientQuotientHomeomorph h (Quotient.mk'' (Quotient.mk'' a)) = Quotient.mk'' a := rfl

@[simp]
theorem quotientQuotientHomeomorph_symm_mk {r s : Setoid P} (h : r ≤ s) (a : P) :
    (quotientQuotientHomeomorph h).symm (Quotient.mk'' a)
      = Quotient.mk'' (Quotient.mk'' a) := rfl

@[simp]
theorem quotientQuotientHomeomorph_comap_mk_mk {r : Setoid P} (u : Setoid (Quotient r))
    (a : P) :
    quotientQuotientHomeomorph_comap u (Quotient.mk'' (Quotient.mk'' a))
      = Quotient.mk'' a := rfl

@[simp]
theorem quotientQuotientHomeomorph_comap_symm_mk {r : Setoid P} (u : Setoid (Quotient r))
    (a : P) :
    (quotientQuotientHomeomorph_comap u).symm (Quotient.mk'' a)
      = Quotient.mk'' (Quotient.mk'' a) := rfl

@[simp]
theorem quotientQuotientHomeomorph_refl_mk (r : Setoid P) (x : Quotient r) :
    quotientQuotientHomeomorph (le_refl r) (Quotient.mk'' x) = x := by
  induction x using Quotient.inductionOn with
  | _ a => rfl

@[simp]
theorem quotientQuotientHomeomorph_refl_symm (r : Setoid P) (x : Quotient r) :
    (quotientQuotientHomeomorph (le_refl r)).symm x = Quotient.mk'' x := by
  induction x using Quotient.inductionOn with
  | _ a => rfl

theorem quotientQuotientHomeomorph_naturality
    {P' : Type*} [TopologicalSpace P'] {r s : Setoid P} {r' s' : Setoid P'}
    (h : r ≤ s) (h' : r' ≤ s') (e : P ≃ₜ P')
    (hr : ∀ x y, r x y ↔ r' (e x) (e y)) (hs : ∀ x y, s x y ↔ s' (e x) (e y)) :
    (quotientQuotientHomeomorph h).trans (Homeomorph.Quotient.congr e hs) =
      (Homeomorph.Quotient.congr (Homeomorph.Quotient.congr e hr)
        (ker_mapRight_homeomorph_congr h h' e hr hs)
        : Quotient (Setoid.ker (Quot.mapRight h)) ≃ₜ
          Quotient (Setoid.ker (Quot.mapRight h'))).trans
        (quotientQuotientHomeomorph h') := by
  ext z
  induction z using Quotient.inductionOn with
  | _ x => induction x using Quotient.inductionOn with | _ a =>
      simp only [Homeomorph.trans_apply]
      rfl

end DifferentialGeometry.Topology
