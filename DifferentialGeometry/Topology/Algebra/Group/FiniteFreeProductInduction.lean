/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct

set_option autoImplicit false

universe u

namespace DifferentialGeometry.Algebra.Group


abbrev finFreeProductFamily (G : ℕ → Type u) (n : ℕ) : Fin n → Type u :=
  fun i => G i.val


def finFreeProductToCoprod (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    Monoid.CoprodI (finFreeProductFamily G (Nat.succ n)) →*
      Monoid.Coprod (Monoid.CoprodI (finFreeProductFamily G n)) (G n) :=
  Monoid.CoprodI.lift (Fin.lastCases Monoid.Coprod.inr fun i =>
    Monoid.Coprod.inl.comp
      (Monoid.CoprodI.of (M := finFreeProductFamily G n) (i := i)))


def coprodToFinFreeProduct (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    Monoid.Coprod (Monoid.CoprodI (finFreeProductFamily G n)) (G n) →*
      Monoid.CoprodI (finFreeProductFamily G (Nat.succ n)) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      Monoid.CoprodI.of (M := finFreeProductFamily G (Nat.succ n))
        (i := Fin.castSucc i))
    (Monoid.CoprodI.of (M := finFreeProductFamily G (Nat.succ n))
      (i := Fin.last n))


theorem finFreeProductMaps_forward_inverse
    (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    (finFreeProductToCoprod G n).comp (coprodToFinFreeProduct G n) =
      MonoidHom.id
        (Monoid.Coprod (Monoid.CoprodI (finFreeProductFamily G n)) (G n)) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [finFreeProductToCoprod, coprodToFinFreeProduct]
  · ext g
    simp [finFreeProductToCoprod, coprodToFinFreeProduct]


theorem finFreeProductMaps_inverse_forward
    (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    (coprodToFinFreeProduct G n).comp (finFreeProductToCoprod G n) =
      MonoidHom.id (Monoid.CoprodI (finFreeProductFamily G (Nat.succ n))) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · ext g
    simp [finFreeProductToCoprod, coprodToFinFreeProduct]
  · ext g
    simp [finFreeProductToCoprod, coprodToFinFreeProduct]

def finFreeProductEquivCoprod
    (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    Monoid.CoprodI (finFreeProductFamily G (Nat.succ n)) ≃*
      Monoid.Coprod (Monoid.CoprodI (finFreeProductFamily G n)) (G n) :=
  MonoidHom.toMulEquiv
    (finFreeProductToCoprod G n)
    (coprodToFinFreeProduct G n)
    (finFreeProductMaps_inverse_forward G n)
    (finFreeProductMaps_forward_inverse G n)


theorem finFreeProductEquivCoprod_comp_castSucc
    (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) (i : Fin n) :
    (finFreeProductEquivCoprod G n).toMonoidHom.comp
        (Monoid.CoprodI.of (M := finFreeProductFamily G (Nat.succ n))
          (i := Fin.castSucc i)) =
      Monoid.Coprod.inl.comp
        (Monoid.CoprodI.of (M := finFreeProductFamily G n) (i := i)) := by
  ext g
  simp [finFreeProductEquivCoprod, finFreeProductToCoprod]


theorem finFreeProductEquivCoprod_comp_last
    (G : ℕ → Type u) [∀ n, Group (G n)] (n : ℕ) :
    (finFreeProductEquivCoprod G n).toMonoidHom.comp
        (Monoid.CoprodI.of (M := finFreeProductFamily G (Nat.succ n))
          (i := Fin.last n)) =
      Monoid.Coprod.inr := by
  ext g
  simp [finFreeProductEquivCoprod, finFreeProductToCoprod]

noncomputable def finiteFreeProductEquiv
    (G P : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (P n)]
    (base : P 0 ≃* PUnit)
    (step : ∀ n, P (Nat.succ n) ≃* Monoid.Coprod (P n) (G n)) :
    ∀ n, P n ≃* Monoid.CoprodI (finFreeProductFamily G n)
  | 0 => by
      letI : Subsingleton (Monoid.CoprodI (finFreeProductFamily G 0)) :=
        (coprodI_subsingleton_iff (finFreeProductFamily G 0)).mpr fun i => i.elim0
      letI : Unique (Monoid.CoprodI (finFreeProductFamily G 0)) :=
        { default := 1
          uniq := fun x => Subsingleton.elim x 1 }
      exact base.trans (MulEquiv.ofUnique :
        Monoid.CoprodI (finFreeProductFamily G 0) ≃* PUnit).symm
  | Nat.succ n =>
      (step n).trans
        (((finiteFreeProductEquiv G P base step n).coprodCongr
          (MulEquiv.refl (G n))).trans
            (finFreeProductEquivCoprod G n).symm)

noncomputable def finiteFactorToStage
    (G P : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (P n)]
    (step : ∀ n, P (Nat.succ n) ≃* Monoid.Coprod (P n) (G n)) :
    ∀ (n : ℕ), (i : Fin n) → finFreeProductFamily G n i →* P n
  | 0 => fun i => i.elim0
  | Nat.succ n => Fin.lastCases
      ((step n).symm.toMonoidHom.comp Monoid.Coprod.inr)
      (fun i =>
        (step n).symm.toMonoidHom.comp
          (Monoid.Coprod.inl.comp (finiteFactorToStage G P step n i)))

theorem finiteFreeProductEquiv_comp_factorToStage
    (G P : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (P n)]
    (base : P 0 ≃* PUnit)
    (step : ∀ n, P (Nat.succ n) ≃* Monoid.Coprod (P n) (G n)) :
    ∀ (n : ℕ) (i : Fin n),
      (finiteFreeProductEquiv G P base step n).toMonoidHom.comp
          (finiteFactorToStage G P step n i) =
        (Monoid.CoprodI.of : finFreeProductFamily G n i →*
          Monoid.CoprodI (finFreeProductFamily G n)) := by
  intro n
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · ext g
        simp only [finiteFreeProductEquiv, finiteFactorToStage, Fin.lastCases_last,
          MonoidHom.comp_apply]
        change
          (((finiteFreeProductEquiv G P base step n).coprodCongr
              (MulEquiv.refl (G n))).trans
            (finFreeProductEquivCoprod G n).symm)
              ((step n) ((step n).symm (Monoid.Coprod.inr g))) = _
        rw [MulEquiv.apply_symm_apply]
        rfl
      · ext g
        simp only [finiteFreeProductEquiv, finiteFactorToStage, Fin.lastCases_castSucc,
          MonoidHom.comp_apply]
        change
          (((finiteFreeProductEquiv G P base step n).coprodCongr
              (MulEquiv.refl (G n))).trans
            (finFreeProductEquivCoprod G n).symm)
              ((step n) ((step n).symm
                (Monoid.Coprod.inl ((finiteFactorToStage G P step n j) g)))) = _
        rw [MulEquiv.apply_symm_apply]
        change
          (finFreeProductEquivCoprod G n).symm
              (Monoid.Coprod.inl
                ((finiteFreeProductEquiv G P base step n)
                  ((finiteFactorToStage G P step n j) g))) = _
        have hj := DFunLike.congr_fun (ih j) g
        change
          (finiteFreeProductEquiv G P base step n)
              ((finiteFactorToStage G P step n j) g) =
            Monoid.CoprodI.of (M := finFreeProductFamily G n) (i := j) g at hj
        rw [hj]
        rfl

end DifferentialGeometry.Algebra.Group
