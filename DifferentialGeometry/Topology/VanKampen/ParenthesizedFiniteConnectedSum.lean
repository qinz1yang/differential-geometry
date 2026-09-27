/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSum

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Algebra.Group



instance sumElimGroup {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] (i : Sum ι κ) :
    Group (Sum.elim G H i) := by
  cases i <;> simp only [Sum.elim] <;> infer_instance


def sumFreeProductToCoprod {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] :
    Monoid.CoprodI (Sum.elim G H) →*
      Monoid.Coprod (Monoid.CoprodI G) (Monoid.CoprodI H) :=
  Monoid.CoprodI.lift fun
    | Sum.inl i => Monoid.Coprod.inl.comp
        (Monoid.CoprodI.of (M := G) (i := i))
    | Sum.inr j => Monoid.Coprod.inr.comp
        (Monoid.CoprodI.of (M := H) (i := j))


def coprodToSumFreeProduct {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] :
    Monoid.Coprod (Monoid.CoprodI G) (Monoid.CoprodI H) →*
      Monoid.CoprodI (Sum.elim G H) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inl i))
    (Monoid.CoprodI.lift fun j =>
      Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inr j))

theorem sumFreeProductMaps_forward_inverse {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] :
    (sumFreeProductToCoprod G H).comp (coprodToSumFreeProduct G H) =
      MonoidHom.id (Monoid.Coprod (Monoid.CoprodI G) (Monoid.CoprodI H)) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    rfl
  · apply Monoid.CoprodI.ext_hom
    intro j
    ext h
    rfl

theorem sumFreeProductMaps_inverse_forward {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] :
    (coprodToSumFreeProduct G H).comp (sumFreeProductToCoprod G H) =
      MonoidHom.id (Monoid.CoprodI (Sum.elim G H)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i with
  | inl i =>
      ext g
      rfl
  | inr j =>
      ext h
      rfl


def sumFreeProductEquivCoprod {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] :
    Monoid.CoprodI (Sum.elim G H) ≃*
      Monoid.Coprod (Monoid.CoprodI G) (Monoid.CoprodI H) :=
  MonoidHom.toMulEquiv
    (sumFreeProductToCoprod G H)
    (coprodToSumFreeProduct G H)
    (sumFreeProductMaps_inverse_forward G H)
    (sumFreeProductMaps_forward_inverse G H)

theorem sumFreeProductEquivCoprod_comp_inl {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] (i : ι) :
    (sumFreeProductEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inl i)) =
      Monoid.Coprod.inl.comp (Monoid.CoprodI.of (M := G) (i := i)) := by
  rfl

theorem sumFreeProductEquivCoprod_comp_inr {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] (j : κ) :
    (sumFreeProductEquivCoprod G H).toMonoidHom.comp
        (Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inr j)) =
      Monoid.Coprod.inr.comp (Monoid.CoprodI.of (M := H) (i := j)) := by
  rfl

theorem sumFreeProductEquivCoprod_symm_comp_inl {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] (i : ι) :
    (sumFreeProductEquivCoprod G H).symm.toMonoidHom.comp
        (Monoid.Coprod.inl.comp (Monoid.CoprodI.of (M := G) (i := i))) =
      (Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inl i)) := by
  rfl

theorem sumFreeProductEquivCoprod_symm_comp_inr {ι κ : Type*}
    (G : ι → Type u) (H : κ → Type u)
    [∀ i, Group (G i)] [∀ j, Group (H j)] (j : κ) :
    (sumFreeProductEquivCoprod G H).symm.toMonoidHom.comp
        (Monoid.Coprod.inr.comp (Monoid.CoprodI.of (M := H) (i := j))) =
      (Monoid.CoprodI.of (M := Sum.elim G H) (i := Sum.inr j)) := by
  rfl



inductive ParenthesizedConnectedSumConstruction :
    (r : ℕ) → (ι : Type) → BasedConnectedClosedSmoothThreeManifold → Type (u + 1)
  | empty (result : BasedConnectedClosedSmoothThreeManifold)
      (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
      (sphereRealization_basepoint :
        sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
      ParenthesizedConnectedSumConstruction 0 Empty result
  | singleton (factor : BasedConnectedClosedSmoothThreeManifold) :
      ParenthesizedConnectedSumConstruction 1 PUnit factor
  | combine {r s : ℕ}
      {ι κ : Type}
      {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
      (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
      (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
      (result : BasedConnectedClosedSmoothThreeManifold)
      (step : ConnectedSumStep leftResult rightResult result) :
      ParenthesizedConnectedSumConstruction (r + s) (Sum ι κ) result


@[reducible]
def ParenthesizedConnectedSumConstruction.factorManifold
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) :
    ι → BasedConnectedClosedSmoothThreeManifold :=
  match c with
  | .empty _ _ _ => fun i => i.elim
  | .singleton factor => fun _ => factor
  | .combine left _ right _ _ _ => Sum.elim left.factorManifold right.factorManifold


abbrev ParenthesizedConnectedSumConstruction.factorFundamentalGroup
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : ι) :=
  FundamentalGroup (c.factorManifold i) (c.factorManifold i).basepoint

noncomputable instance ParenthesizedConnectedSumConstruction.factorFundamentalGroupGroup
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : ι) :
    Group (c.factorFundamentalGroup i) := by
  infer_instance


noncomputable def ParenthesizedConnectedSumConstruction.factorIndexEquivFin :
    {r : ℕ} → {ι : Type} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : ParenthesizedConnectedSumConstruction r ι result) → ι ≃ Fin r
  | _, _, _, .empty _ _ _ => Equiv.equivOfIsEmpty Empty (Fin 0)
  | _, _, _, .singleton _ => (Equiv.equivPUnit (Fin 1)).symm
  | _, _, _, .combine left _ right _ _ _ =>
      (left.factorIndexEquivFin.sumCongr right.factorIndexEquivFin).trans finSumFinEquiv


abbrev ParenthesizedConnectedSumConstruction.orderedFactorManifold
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : Fin r) :=
  c.factorManifold (c.factorIndexEquivFin.symm i)


abbrev ParenthesizedConnectedSumConstruction.orderedFactorFundamentalGroup
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : Fin r) :=
  FundamentalGroup (c.orderedFactorManifold i) (c.orderedFactorManifold i).basepoint

noncomputable instance ParenthesizedConnectedSumConstruction.orderedFactorFundamentalGroupGroup
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : Fin r) :
    Group (c.orderedFactorFundamentalGroup i) := by
  infer_instance

@[simp]
theorem ParenthesizedConnectedSumConstruction.factorManifold_combine_inl
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (i : ι) :
    (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
      result step).factorManifold (Sum.inl i) = left.factorManifold i := by
  simp [ParenthesizedConnectedSumConstruction.factorManifold]

@[simp]
theorem ParenthesizedConnectedSumConstruction.factorManifold_combine_inr
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (j : κ) :
    (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
      result step).factorManifold (Sum.inr j) = right.factorManifold j := by
  simp [ParenthesizedConnectedSumConstruction.factorManifold]


noncomputable def combineLeftFactorEquiv
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (i : ι) :
    (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
      result step).factorFundamentalGroup (Sum.inl i) ≃*
      left.factorFundamentalGroup i :=
  basedFundamentalGroupEquivOfEq
    (ParenthesizedConnectedSumConstruction.factorManifold_combine_inl
      left left_nonempty right right_nonempty result step i)


noncomputable def combineRightFactorEquiv
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (j : κ) :
    (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
      result step).factorFundamentalGroup (Sum.inr j) ≃*
      right.factorFundamentalGroup j :=
  basedFundamentalGroupEquivOfEq
    (ParenthesizedConnectedSumConstruction.factorManifold_combine_inr
      left left_nonempty right right_nonempty result step j)

noncomputable def combineFactorEquiv
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) :
    ∀ i,
      (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
        result step).factorFundamentalGroup i ≃*
      Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup i
  | Sum.inl i => combineLeftFactorEquiv
      left left_nonempty right right_nonempty result step i
  | Sum.inr j => combineRightFactorEquiv
      left left_nonempty right right_nonempty result step j

noncomputable def combineFactorFreeProductEquivCoprod
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) :
    Monoid.CoprodI
        (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
          result step).factorFundamentalGroup ≃*
      Monoid.Coprod (Monoid.CoprodI left.factorFundamentalGroup)
        (Monoid.CoprodI right.factorFundamentalGroup) :=
  (coprodIMulEquiv
    (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
      result step).factorFundamentalGroup
    (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
    (combineFactorEquiv left left_nonempty right right_nonempty result step)).trans
      (sumFreeProductEquivCoprod left.factorFundamentalGroup right.factorFundamentalGroup)


theorem combineFactorFreeProductEquivCoprod_comp_inl
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (i : ι) :
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
      result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (ParenthesizedConnectedSumConstruction.combine left left_nonempty right
            right_nonempty result step).factorFundamentalGroup)
          (i := Sum.inl i)) =
      Monoid.Coprod.inl.comp
        ((Monoid.CoprodI.of (M := left.factorFundamentalGroup) (i := i)).comp
          (combineLeftFactorEquiv left left_nonempty right right_nonempty result step
            i).toMonoidHom) := by
  ext g
  change
    (sumFreeProductEquivCoprod left.factorFundamentalGroup right.factorFundamentalGroup)
      ((coprodIMulEquiv
        (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
          result step).factorFundamentalGroup
        (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
        (combineFactorEquiv left left_nonempty right right_nonempty result step))
          (Monoid.CoprodI.of g)) = _
  have hmap := DFunLike.congr_fun
    (coprodIMulEquiv_comp_of
      (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
        result step).factorFundamentalGroup
      (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
      (combineFactorEquiv left left_nonempty right right_nonempty result step) (Sum.inl i)) g
  change
    (coprodIMulEquiv
      (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
        result step).factorFundamentalGroup
      (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
      (combineFactorEquiv left left_nonempty right right_nonempty result step))
        (Monoid.CoprodI.of g) =
      Monoid.CoprodI.of
        (M := Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
        (i := Sum.inl i)
        (combineLeftFactorEquiv left left_nonempty right right_nonempty result step i g)
    at hmap
  rw [hmap]
  rfl


theorem combineFactorFreeProductEquivCoprod_comp_inr
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (j : κ) :
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
      result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (ParenthesizedConnectedSumConstruction.combine left left_nonempty right
            right_nonempty result step).factorFundamentalGroup)
          (i := Sum.inr j)) =
      Monoid.Coprod.inr.comp
        ((Monoid.CoprodI.of (M := right.factorFundamentalGroup) (i := j)).comp
          (combineRightFactorEquiv left left_nonempty right right_nonempty result step
            j).toMonoidHom) := by
  ext g
  change
    (sumFreeProductEquivCoprod left.factorFundamentalGroup right.factorFundamentalGroup)
      ((coprodIMulEquiv
        (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
          result step).factorFundamentalGroup
        (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
        (combineFactorEquiv left left_nonempty right right_nonempty result step))
          (Monoid.CoprodI.of g)) = _
  have hmap := DFunLike.congr_fun
    (coprodIMulEquiv_comp_of
      (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
        result step).factorFundamentalGroup
      (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
      (combineFactorEquiv left left_nonempty right right_nonempty result step) (Sum.inr j)) g
  change
    (coprodIMulEquiv
      (ParenthesizedConnectedSumConstruction.combine left left_nonempty right right_nonempty
        result step).factorFundamentalGroup
      (Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
      (combineFactorEquiv left left_nonempty right right_nonempty result step))
        (Monoid.CoprodI.of g) =
      Monoid.CoprodI.of
        (M := Sum.elim left.factorFundamentalGroup right.factorFundamentalGroup)
        (i := Sum.inr j)
        (combineRightFactorEquiv left left_nonempty right right_nonempty result step j g)
    at hmap
  rw [hmap]
  rfl


theorem combineFactorFreeProductEquivCoprod_symm_comp_inl
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (i : ι) :
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
      result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inl.comp
          ((Monoid.CoprodI.of (M := left.factorFundamentalGroup) (i := i)).comp
            (combineLeftFactorEquiv left left_nonempty right right_nonempty result step
              i).toMonoidHom)) =
      (Monoid.CoprodI.of
        (M := (ParenthesizedConnectedSumConstruction.combine left left_nonempty right
          right_nonempty result step).factorFundamentalGroup)
        (i := Sum.inl i)) := by
  ext g
  apply (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
    result step).injective
  change
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty result step)
      ((combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
        result step).symm
          (Monoid.Coprod.inl
            (Monoid.CoprodI.of
              (combineLeftFactorEquiv left left_nonempty right right_nonempty result step
                i g)))) =
      (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty result step)
        (Monoid.CoprodI.of g)
  rw [(combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
    result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (combineFactorFreeProductEquivCoprod_comp_inl
      left left_nonempty right right_nonempty result step i) g).symm


theorem combineFactorFreeProductEquivCoprod_symm_comp_inr
    {r s : ℕ} {ι κ : Type}
    {leftResult rightResult : BasedConnectedClosedSmoothThreeManifold}
    (left : ParenthesizedConnectedSumConstruction r ι leftResult) (left_nonempty : 0 < r)
    (right : ParenthesizedConnectedSumConstruction s κ rightResult) (right_nonempty : 0 < s)
    (result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep leftResult rightResult result) (j : κ) :
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
      result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inr.comp
          ((Monoid.CoprodI.of (M := right.factorFundamentalGroup) (i := j)).comp
            (combineRightFactorEquiv left left_nonempty right right_nonempty result step
              j).toMonoidHom)) =
      (Monoid.CoprodI.of
        (M := (ParenthesizedConnectedSumConstruction.combine left left_nonempty right
          right_nonempty result step).factorFundamentalGroup)
        (i := Sum.inr j)) := by
  ext g
  apply (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
    result step).injective
  change
    (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty result step)
      ((combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
        result step).symm
          (Monoid.Coprod.inr
            (Monoid.CoprodI.of
              (combineRightFactorEquiv left left_nonempty right right_nonempty result step
                j g)))) =
      (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty result step)
        (Monoid.CoprodI.of g)
  rw [(combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
    result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (combineFactorFreeProductEquivCoprod_comp_inr
      left left_nonempty right right_nonempty result step j) g).symm



noncomputable def emptyParenthesizedConnectedSumFundamentalGroupEquiv
    (result : BasedConnectedClosedSmoothThreeManifold)
    (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
    (sphereRealization_basepoint :
      sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
    FundamentalGroup result result.basepoint ≃*
      Monoid.CoprodI
        (ParenthesizedConnectedSumConstruction.empty result sphereRealization
          sphereRealization_basepoint).factorFundamentalGroup := by
  let sphereEquiv : FundamentalGroup result result.basepoint ≃*
      FundamentalGroup DifferentialGeometry.Topology.SphereThree DifferentialGeometry.Topology.sphereThreeNorth :=
    DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      sphereRealization.toHomotopyEquiv result.basepoint
        DifferentialGeometry.Topology.sphereThreeNorth sphereRealization_basepoint
  let target := Monoid.CoprodI
    (ParenthesizedConnectedSumConstruction.empty result sphereRealization
      sphereRealization_basepoint).factorFundamentalGroup
  letI : Subsingleton target :=
    (coprodI_subsingleton_iff _).mpr fun i => i.elim
  letI : Unique target :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  letI : Unique (FundamentalGroup DifferentialGeometry.Topology.SphereThree
      DifferentialGeometry.Topology.sphereThreeNorth) :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  exact sphereEquiv.trans MulEquiv.ofUnique

noncomputable def fundamentalGroupEquiv_parenthesizedConnectedSumLeaves :
    {r : ℕ} → {ι : Type} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : ParenthesizedConnectedSumConstruction r ι result) →
      FundamentalGroup result result.basepoint ≃*
        Monoid.CoprodI c.factorFundamentalGroup
  | _, _, _, .empty result sphereRealization sphereRealization_basepoint =>
      emptyParenthesizedConnectedSumFundamentalGroupEquiv
        result sphereRealization sphereRealization_basepoint
  | _, _, _, .singleton factor =>
      (coprodISingletonEquiv (FundamentalGroup factor factor.basepoint)).symm
  | _, _, _, .combine left left_nonempty right right_nonempty result step =>
      step.fundamentalGroupEquiv.trans <|
        ((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves left).coprodCongr
          (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves right)).trans <|
            (combineFactorFreeProductEquivCoprod left left_nonempty
              right right_nonempty result step).symm

noncomputable def ParenthesizedConnectedSumConstruction.factorToResult :
    {r : ℕ} → {ι : Type} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : ParenthesizedConnectedSumConstruction r ι result) →
      (i : ι) → c.factorFundamentalGroup i →*
        FundamentalGroup result result.basepoint
  | _, _, _, .empty _ _ _, i => i.elim
  | _, _, _, .singleton _, _ => MonoidHom.id _
  | _, _, _, .combine left left_nonempty right right_nonempty result step, Sum.inl i =>
      step.leftFactorHom.comp <| (left.factorToResult i).comp <|
        (combineLeftFactorEquiv left left_nonempty right right_nonempty result step
          i).toMonoidHom
  | _, _, _, .combine left left_nonempty right right_nonempty result step, Sum.inr j =>
      step.rightFactorHom.comp <| (right.factorToResult j).comp <|
        (combineRightFactorEquiv left left_nonempty right right_nonempty result step
          j).toMonoidHom


theorem fundamentalGroupEquiv_parenthesizedConnectedSumLeaves_comp_factorToResult :
    {r : ℕ} → {ι : Type} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : ParenthesizedConnectedSumConstruction r ι result) → (i : ι) →
      (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves c).toMonoidHom.comp
          (c.factorToResult i) =
        (Monoid.CoprodI.of : c.factorFundamentalGroup i →*
          Monoid.CoprodI c.factorFundamentalGroup) := by
  intro r ι result c
  induction c with
  | empty result sphereRealization sphereRealization_basepoint =>
      intro i
      exact i.elim
  | singleton factor =>
      intro i
      rcases i with ⟨⟩
      ext g
      rfl
  | @combine r s ι κ leftResult rightResult left left_nonempty right right_nonempty result step
      ihLeft ihRight =>
      intro i
      cases i with
      | inl i =>
          ext g
          simp only [fundamentalGroupEquiv_parenthesizedConnectedSumLeaves,
            ParenthesizedConnectedSumConstruction.factorToResult,
            MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          let gLeft := combineLeftFactorEquiv left left_nonempty right right_nonempty result step
            i g
          have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_leftFactorHom
            (left.factorToResult i gLeft)
          change step.fundamentalGroupEquiv
              (step.leftFactorHom (left.factorToResult i gLeft)) =
            Monoid.Coprod.inl (left.factorToResult i gLeft) at hstep
          change
            (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
              result step).symm
                (((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves left).coprodCongr
                  (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves right))
                    (step.fundamentalGroupEquiv
                      (step.leftFactorHom (left.factorToResult i gLeft)))) =
              Monoid.CoprodI.of g
          rw [hstep]
          change
            (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
              result step).symm
                (Monoid.Coprod.inl
                  ((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves left)
                    (left.factorToResult i gLeft))) =
              Monoid.CoprodI.of g
          have hih := DFunLike.congr_fun (ihLeft i) gLeft
          change
            (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves left)
                (left.factorToResult i gLeft) = Monoid.CoprodI.of gLeft at hih
          rw [hih]
          exact DFunLike.congr_fun
            (combineFactorFreeProductEquivCoprod_symm_comp_inl
              left left_nonempty right right_nonempty result step i) g
      | inr j =>
          ext g
          simp only [fundamentalGroupEquiv_parenthesizedConnectedSumLeaves,
            ParenthesizedConnectedSumConstruction.factorToResult,
            MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          let gRight := combineRightFactorEquiv left left_nonempty right right_nonempty result step
            j g
          have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_rightFactorHom
            (right.factorToResult j gRight)
          change step.fundamentalGroupEquiv
              (step.rightFactorHom (right.factorToResult j gRight)) =
            Monoid.Coprod.inr (right.factorToResult j gRight) at hstep
          change
            (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
              result step).symm
                (((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves left).coprodCongr
                  (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves right))
                    (step.fundamentalGroupEquiv
                      (step.rightFactorHom (right.factorToResult j gRight)))) =
              Monoid.CoprodI.of g
          rw [hstep]
          change
            (combineFactorFreeProductEquivCoprod left left_nonempty right right_nonempty
              result step).symm
                (Monoid.Coprod.inr
                  ((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves right)
                    (right.factorToResult j gRight))) =
              Monoid.CoprodI.of g
          have hih := DFunLike.congr_fun (ihRight j) gRight
          change
            (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves right)
                (right.factorToResult j gRight) = Monoid.CoprodI.of gRight at hih
          rw [hih]
          exact DFunLike.congr_fun
            (combineFactorFreeProductEquivCoprod_symm_comp_inr
              left left_nonempty right right_nonempty result step j) g

noncomputable def ParenthesizedConnectedSumConstruction.orderedToLeavesFreeProductEquiv
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) :
    Monoid.CoprodI c.orderedFactorFundamentalGroup ≃*
      Monoid.CoprodI c.factorFundamentalGroup :=
  coprodIReindexEquiv c.orderedFactorFundamentalGroup c.factorFundamentalGroup
    c.factorIndexEquivFin.symm fun _ => MulEquiv.refl _


noncomputable def ParenthesizedConnectedSumConstruction.leavesToOrderedFreeProductEquiv
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) :
    Monoid.CoprodI c.factorFundamentalGroup ≃*
      Monoid.CoprodI c.orderedFactorFundamentalGroup :=
  c.orderedToLeavesFreeProductEquiv.symm

noncomputable def fundamentalGroupEquiv_parenthesizedFiniteConnectedSum
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) :
    FundamentalGroup result result.basepoint ≃*
      Monoid.CoprodI c.orderedFactorFundamentalGroup :=
  (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves c).trans
    c.leavesToOrderedFreeProductEquiv


noncomputable def ParenthesizedConnectedSumConstruction.orderedFactorToResult
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : Fin r) :
    c.orderedFactorFundamentalGroup i →* FundamentalGroup result result.basepoint :=
  c.factorToResult (c.factorIndexEquivFin.symm i)

theorem fundamentalGroupEquiv_parenthesizedFiniteConnectedSum_comp_orderedFactorToResult
    {r : ℕ} {ι : Type} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : ParenthesizedConnectedSumConstruction r ι result) (i : Fin r) :
    (fundamentalGroupEquiv_parenthesizedFiniteConnectedSum c).toMonoidHom.comp
        (c.orderedFactorToResult i) =
      (Monoid.CoprodI.of : c.orderedFactorFundamentalGroup i →*
        Monoid.CoprodI c.orderedFactorFundamentalGroup) := by
  ext g
  change c.leavesToOrderedFreeProductEquiv
      ((fundamentalGroupEquiv_parenthesizedConnectedSumLeaves c)
        (c.factorToResult (c.factorIndexEquivFin.symm i) g)) =
    Monoid.CoprodI.of
      (M := c.orderedFactorFundamentalGroup) (i := i) g
  have hleaf := DFunLike.congr_fun
    (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves_comp_factorToResult
      c (c.factorIndexEquivFin.symm i)) g
  change
    (fundamentalGroupEquiv_parenthesizedConnectedSumLeaves c)
        (c.factorToResult (c.factorIndexEquivFin.symm i) g) =
      Monoid.CoprodI.of
        (M := c.factorFundamentalGroup) (i := c.factorIndexEquivFin.symm i) g at hleaf
  rw [hleaf]
  change c.leavesToOrderedFreeProductEquiv
      (Monoid.CoprodI.of
        (M := c.factorFundamentalGroup) (i := c.factorIndexEquivFin.symm i) g) =
    Monoid.CoprodI.of (M := c.orderedFactorFundamentalGroup) (i := i) g
  apply c.orderedToLeavesFreeProductEquiv.injective
  change c.orderedToLeavesFreeProductEquiv
      (c.orderedToLeavesFreeProductEquiv.symm
        (Monoid.CoprodI.of
          (M := c.factorFundamentalGroup) (i := c.factorIndexEquivFin.symm i) g)) =
    c.orderedToLeavesFreeProductEquiv
      (Monoid.CoprodI.of (M := c.orderedFactorFundamentalGroup) (i := i) g)
  rw [c.orderedToLeavesFreeProductEquiv.apply_symm_apply]
  have hreindex := DFunLike.congr_fun
    (coprodIReindexEquiv_comp_of c.orderedFactorFundamentalGroup
      c.factorFundamentalGroup c.factorIndexEquivFin.symm
      (fun _ => MulEquiv.refl _) i) g
  exact hreindex.symm

end DifferentialGeometry.Topology.ThreeManifold
