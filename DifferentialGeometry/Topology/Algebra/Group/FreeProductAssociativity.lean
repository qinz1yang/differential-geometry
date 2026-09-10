/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.GroupTheory.Coprod.Basic
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct

set_option autoImplicit false

universe u v

namespace Poincare.Algebra.Group


abbrev optionFreeProductFactor {ι : Type u} (G : ι → Type v) (H : Type v) :
    Option ι → Type v
  | none => H
  | some i => G i

instance optionFreeProductFactorGroup {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H]
    (i : Option ι) : Group (optionFreeProductFactor G H i) := by
  cases i <;> simp only [optionFreeProductFactor] <;> infer_instance


def coprodIOptionToCoprod {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.CoprodI (optionFreeProductFactor G H) →*
      Monoid.Coprod (Monoid.CoprodI G) H :=
  Monoid.CoprodI.lift fun
    | none => Monoid.Coprod.inr
    | some i => Monoid.Coprod.inl.comp
        (Monoid.CoprodI.of (M := G) (i := i))


def coprodToCoprodIOption {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.Coprod (Monoid.CoprodI G) H →*
      Monoid.CoprodI (optionFreeProductFactor G H) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := some i))
    (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := none))

theorem coprodOptionMaps_forward_inverse {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodIOptionToCoprod G H).comp (coprodToCoprodIOption G H) =
      MonoidHom.id (Monoid.Coprod (Monoid.CoprodI G) H) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [coprodIOptionToCoprod, coprodToCoprodIOption]
  · rfl

theorem coprodOptionMaps_inverse_forward {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodToCoprodIOption G H).comp (coprodIOptionToCoprod G H) =
      MonoidHom.id (Monoid.CoprodI (optionFreeProductFactor G H)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i with
  | none => rfl
  | some i =>
      ext g
      simp [coprodIOptionToCoprod, coprodToCoprodIOption]

def coprodIOptionEquivCoprod {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    Monoid.CoprodI (optionFreeProductFactor G H) ≃*
      Monoid.Coprod (Monoid.CoprodI G) H :=
  MonoidHom.toMulEquiv
    (coprodIOptionToCoprod G H)
    (coprodToCoprodIOption G H)
    (coprodOptionMaps_inverse_forward G H)
    (coprodOptionMaps_forward_inverse G H)

theorem coprodIOptionEquivCoprod_comp_none {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H] :
    (coprodIOptionEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := none)) =
      Monoid.Coprod.inr := by
  rfl

theorem coprodIOptionEquivCoprod_comp_some {ι : Type u}
    (G : ι → Type v) (H : Type v) [∀ i, Group (G i)] [Group H]
    (i : ι) :
    (coprodIOptionEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := optionFreeProductFactor G H) (i := some i)) =
      Monoid.Coprod.inl.comp (Monoid.CoprodI.of (M := G) (i := i)) := by
  rfl

end Poincare.Algebra.Group
