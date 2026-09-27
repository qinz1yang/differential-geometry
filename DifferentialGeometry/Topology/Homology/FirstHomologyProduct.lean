/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Product
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying

open scoped ContinuousMap

namespace DifferentialGeometry.Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem integralFirstHomology_prod_decomposition
    [PathConnectedSpace X] [PathConnectedSpace Y] (x : X) (y : Y)
    (a : integralSingularHomology 1 (X × Y)) :
    integralSingularHomologyMap 1
        (⟨fun p : X => (p, y), continuous_id.prodMk continuous_const⟩ : C(X, X × Y))
        (integralSingularHomologyMap 1 ContinuousMap.fst a) +
      integralSingularHomologyMap 1
        (⟨fun q : Y => (x, q), continuous_const.prodMk continuous_id⟩ : C(Y, X × Y))
        (integralSingularHomologyMap 1 ContinuousMap.snd a) = a := by
  let iX : C(X, X × Y) := ⟨fun p => (p, y), continuous_id.prodMk continuous_const⟩
  let iY : C(Y, X × Y) := ⟨fun q => (x, q), continuous_const.prodMk continuous_id⟩
  have hX (p : FundamentalGroup X x) :
      FundamentalGroup.map iX x p = Path.Homotopic.prod p (1 : FundamentalGroup Y y) := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  have hY (q : FundamentalGroup Y y) :
      FundamentalGroup.map iY y q = Path.Homotopic.prod (1 : FundamentalGroup X x) q := by
    induction q using Path.Homotopic.Quotient.ind with
    | mk q => rfl
  have hdecomp (p : FundamentalGroup (X × Y) (x, y)) :
      FundamentalGroup.map iX x (FundamentalGroup.map ContinuousMap.fst (x, y) p) *
        FundamentalGroup.map iY y (FundamentalGroup.map ContinuousMap.snd (x, y) p) = p := by
    change FundamentalGroup.map iX x (Path.Homotopic.projLeft p) *
      FundamentalGroup.map iY y (Path.Homotopic.projRight p) = p
    rw [hX, hY]
    apply (fundamentalGroupProdEquiv x y).injective
    rw [map_mul]
    simp only [fundamentalGroupProdEquiv_apply, Path.Homotopic.projLeft_prod,
      Path.Homotopic.projRight_prod, Prod.mk_mul_mk]
    exact Prod.ext (@mul_one (FundamentalGroup X x) inferInstance (Path.Homotopic.projLeft p))
      (@one_mul (FundamentalGroup Y y) inferInstance (Path.Homotopic.projRight p))
  obtain ⟨p, hp⟩ := hurewiczOne_surjective (x, y) (Multiplicative.ofAdd a)
  have ha : (hurewiczOne (x, y) p).toAdd = a := congrArg Multiplicative.toAdd hp
  rw [← ha]
  change integralSingularHomologyMap 1 iX
      (integralSingularHomologyMap 1 ContinuousMap.fst (hurewiczOne (x, y) p).toAdd) +
    integralSingularHomologyMap 1 iY
      (integralSingularHomologyMap 1 ContinuousMap.snd (hurewiczOne (x, y) p).toAdd) = _
  rw [← hurewiczOne_map, ← hurewiczOne_map, ← hurewiczOne_map, ← hurewiczOne_map]
  change (hurewiczOne (x, y)
      (FundamentalGroup.map iX x (FundamentalGroup.map ContinuousMap.fst (x, y) p)) *
    hurewiczOne (x, y)
      (FundamentalGroup.map iY y (FundamentalGroup.map ContinuousMap.snd (x, y) p))).toAdd = _
  rw [← map_mul, hdecomp]

noncomputable def integralSingularHomologyOneProdEquiv
    [PathConnectedSpace X] [PathConnectedSpace Y] :
    integralSingularHomology 1 (X × Y) ≃ₗ[ℤ]
      integralSingularHomology 1 X × integralSingularHomology 1 Y := by
  classical
  let x : X := Classical.arbitrary X
  let y : Y := Classical.arbitrary Y
  let iX : C(X, X × Y) := ⟨fun p => (p, y), continuous_id.prodMk continuous_const⟩
  let iY : C(Y, X × Y) := ⟨fun q => (x, q), continuous_const.prodMk continuous_id⟩
  let e : integralSingularHomology 1 (X × Y) ≃+
      integralSingularHomology 1 X × integralSingularHomology 1 Y :=
    { toFun := fun a => (integralSingularHomologyMap 1 ContinuousMap.fst a,
        integralSingularHomologyMap 1 ContinuousMap.snd a)
      invFun := fun a => integralSingularHomologyMap 1 iX a.1 +
        integralSingularHomologyMap 1 iY a.2
      left_inv := integralFirstHomology_prod_decomposition x y
      right_inv := ?_
      map_add' := fun a b => Prod.ext (map_add _ a b) (map_add _ a b) }
  · exact e.toIntLinearEquiv
  · intro a
    apply Prod.ext
    · change integralSingularHomologyMap 1 ContinuousMap.fst
        (integralSingularHomologyMap 1 iX a.1 + integralSingularHomologyMap 1 iY a.2) = a.1
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp]
      change integralSingularHomologyMap 1 (ContinuousMap.id X) a.1 +
        integralSingularHomologyMap 1 (ContinuousMap.const Y x) a.2 = a.1
      rw [integralSingularHomologyMap_id, integralSingularHomologyMap_const 1 one_ne_zero,
        LinearMap.id_apply, LinearMap.zero_apply, add_zero]
    · change integralSingularHomologyMap 1 ContinuousMap.snd
        (integralSingularHomologyMap 1 iX a.1 + integralSingularHomologyMap 1 iY a.2) = a.2
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp]
      change integralSingularHomologyMap 1 (ContinuousMap.const X y) a.1 +
        integralSingularHomologyMap 1 (ContinuousMap.id Y) a.2 = a.2
      rw [integralSingularHomologyMap_const 1 one_ne_zero, integralSingularHomologyMap_id,
        LinearMap.zero_apply, LinearMap.id_apply, zero_add]

theorem integralSingularHomologyOneProdEquiv_apply
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (a : integralSingularHomology 1 (X × Y)) :
    integralSingularHomologyOneProdEquiv a =
      (integralSingularHomologyMap 1 ContinuousMap.fst a,
        integralSingularHomologyMap 1 ContinuousMap.snd a) := rfl

end DifferentialGeometry.Topology
