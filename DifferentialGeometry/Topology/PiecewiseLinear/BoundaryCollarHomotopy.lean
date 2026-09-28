/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import Mathlib.Topology.Homotopy.Equiv

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {e : B → X} (c : TwoSidedCollar e)

private noncomputable def domainDeformationValue (K : Set X)
    (q : unitInterval × c.domainNeighborhood K) : X := by
  classical
  exact if hx : q.2.val ∈ c.range then
    let p := c.homeomorphRange.symm ⟨q.2.val, hx⟩
    c.toFun (p.1, (1 - q.1.val) * p.2 + q.1.val * min p.2 0)
  else q.2.val

private theorem domainDeformationValue_eq_of_mem {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (q : unitInterval × c.domainNeighborhood K) (hq : q.2.val ∈ K) :
    c.domainDeformationValue K q = q.2.val := by
  classical
  unfold domainDeformationValue
  split_ifs with hx
  · let p := c.homeomorphRange.symm ⟨q.2.val, hx⟩
    have hp : c.toFun p = q.2.val :=
      congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨q.2.val, hx⟩)
    have ht : p.2 ≤ 0 := (hside p).mp (hp.symm ▸ hq)
    change c.toFun (p.1, (1 - q.1.val) * p.2 + q.1.val * min p.2 0) = q.2.val
    rw [min_eq_left ht, show (1 - q.1.val) * p.2 + q.1.val * p.2 = p.2 by ring]
    exact hp
  · rfl

private theorem continuous_domainDeformationValue {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    Continuous (c.domainDeformationValue K) := by
  let A : Set (unitInterval × c.domainNeighborhood K) :=
    (fun q => q.2.val) ⁻¹' interior K
  let C : Set (unitInterval × c.domainNeighborhood K) :=
    (fun q => q.2.val) ⁻¹' c.range
  have hv : Continuous (fun q : unitInterval × c.domainNeighborhood K => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hA : IsOpen A := isOpen_interior.preimage hv
  have hC : IsOpen C := c.isOpen_range.preimage hv
  have hcover : A ∪ C = univ := eq_univ_of_forall fun q => q.2.property
  rw [← continuousOn_univ, ← hcover, continuousOn_union_iff_of_isOpen hA hC]
  constructor
  · exact hv.continuousOn.congr
      (fun q hq => c.domainDeformationValue_eq_of_mem hside q (interior_subset hq))
  · rw [continuousOn_iff_continuous_domRestrict]
    let j : C → c.range := fun q => ⟨q.val.2.val, q.property⟩
    have hj : Continuous j := (hv.comp continuous_subtype_val).subtype_mk _
    have hp := c.homeomorphRange.symm.continuous.comp hj
    have ht : Continuous (fun q : C => q.val.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have hg : Continuous (fun q : C => c.toFun
        ((c.homeomorphRange.symm (j q)).1,
          (1 - q.val.1.val) * (c.homeomorphRange.symm (j q)).2 +
            q.val.1.val * min (c.homeomorphRange.symm (j q)).2 0)) :=
      c.isOpenEmbedding_toFun.continuous.comp ((continuous_fst.comp hp).prodMk
        (((continuous_const.sub ht).mul (continuous_snd.comp hp)).add
          (ht.mul ((continuous_snd.comp hp).min continuous_const))))
    exact hg.congr fun q => by
      classical
      change _ = c.domainDeformationValue K q.val
      unfold domainDeformationValue
      rw [dite_eq_left (show q.val.2.val ∈ c.range from q.property)]

private theorem domainDeformationValue_mem (K : Set X)
    (q : unitInterval × c.domainNeighborhood K) :
    c.domainDeformationValue K q ∈ c.domainNeighborhood K := by
  classical
  unfold domainDeformationValue
  split_ifs with hx
  · exact Or.inr ⟨_, rfl⟩
  · exact q.2.property

noncomputable def domainHomotopyEquiv {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    K ≃ₕ c.domainNeighborhood K where
  toFun := c.domainInclusion hK hfront
  invFun := c.domainRetraction hside
  left_inv := by
    have heq : (c.domainRetraction hside).comp (c.domainInclusion hK hfront) =
        ContinuousMap.id K := by
      apply ContinuousMap.ext
      exact c.domainRetraction_leftInverse hK hfront hside
    rw [heq]
  right_inv := by
    apply ContinuousMap.Homotopic.symm
    refine ⟨{
      toFun := fun q => ⟨c.domainDeformationValue K q, c.domainDeformationValue_mem K q⟩
      continuous_toFun := (c.continuous_domainDeformationValue hside).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      classical
      unfold domainDeformationValue
      split_ifs with hx
      · change c.toFun ((c.homeomorphRange.symm ⟨x.val, hx⟩).1,
          (1 - (0 : ℝ)) * (c.homeomorphRange.symm ⟨x.val, hx⟩).2 +
            0 * min (c.homeomorphRange.symm ⟨x.val, hx⟩).2 0) = x.val
        simp only [sub_zero, one_mul, zero_mul, add_zero]
        exact congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨x.val, hx⟩)
      · rfl
    · intro x
      apply Subtype.ext
      classical
      change c.domainDeformationValue K (1, x) = _
      unfold domainDeformationValue
      split_ifs with hx
      · change c.toFun (_, (1 - (1 : ℝ)) * _ + 1 * min _ 0) =
          (if hy : x.val ∈ c.range then
            c.toFun ((c.homeomorphRange.symm ⟨x.val, hy⟩).1,
              min (c.homeomorphRange.symm ⟨x.val, hy⟩).2 0) else x.val)
        rw [dite_eq_left hx]
        simp
      · change x.val = (if hy : x.val ∈ c.range then _ else x.val)
        rw [dite_eq_right hx]

theorem domainHomotopyEquiv_apply {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) (x : K) :
    (c.domainHomotopyEquiv hK hfront hside x : X) = x.val := rfl

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
