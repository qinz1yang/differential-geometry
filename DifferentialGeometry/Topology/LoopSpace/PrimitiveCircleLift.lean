/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.CircleLoopGenerator
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Set AddSubgroup

namespace DifferentialGeometry.Topology

theorem exists_real_lift_with_integer_shift (ρ : C(loopCircle, loopCircle)) :
    ∃ (F : C(ℝ, ℝ)) (n : ℤ),
      (∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle)) ∧
        ∀ t : ℝ, F (t + 1) = F t + (n : ℝ) := by
  have hcov := circleQuotientCovering.isCoveringMap
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (ρ 0)
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ρ.comp ⟨fun t : ℝ => (t : loopCircle), AddCircle.continuous_mk' (1 : ℝ)⟩)
    0 c hc
  have hF (t : ℝ) : (F t : loopCircle) = ρ (t : loopCircle) := congrFun hFlift t
  have hz : ((F 1 - F 0 : ℝ) : loopCircle) = 0 := by
    rw [AddCircle.coe_sub, hF, hF, AddCircle.coe_period, AddCircle.coe_zero, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  have hn' : F 1 = F 0 + (n : ℝ) := by
    have := hn
    simp only [zsmul_eq_mul, mul_one] at this
    linarith
  have hshift : (fun t : ℝ => F (t + 1)) = fun t => F t + (n : ℝ) := by
    refine hcov.eq_of_comp_eq
      (F.continuous.comp (continuous_id.add continuous_const))
      (F.continuous.add continuous_const) ?_ 0 ?_
    · funext t
      change (F (t + 1) : loopCircle) = ((F t + (n : ℝ) : ℝ) : loopCircle)
      rw [hF, AddCircle.coe_add_period, AddCircle.coe_add, hF]
      have hz' : ((n : ℝ) : loopCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
        exact ⟨n, by simp⟩
      rw [hz', add_zero]
    · simpa only [zero_add] using hn'
  exact ⟨F, n, hF, congrFun hshift⟩

theorem integer_shift_eq_one_or_neg_one_of_surjective_fundamentalGroup
    (ρ : C(loopCircle, loopCircle)) (F : C(ℝ, ℝ)) (n : ℤ)
    (hlift : ∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle))
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (honto : Function.Surjective (FundamentalGroup.map ρ 0)) : n = 1 ∨ n = -1 := by
  let a : ((↑) : ℝ → loopCircle) ⁻¹' {ρ 0} := ⟨F 0, hlift 0⟩
  let b : ((↑) : ℝ → loopCircle) ⁻¹' {ρ 0} :=
    ⟨F 1, by
      change (F 1 : loopCircle) = ρ 0
      simpa only [AddCircle.coe_period] using hlift 1⟩
  let s := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)
  let φ := circleQuotientCovering.fundamentalGroupToMulOpposite a
  let zn : zmultiples (1 : ℝ) := ⟨(n : ℝ), intCast_mem_zmultiples_one (R := ℝ) n⟩
  have hmon : circleQuotientCovering.isCoveringMap.monodromy
      (FundamentalGroup.map ρ 0 s) a = b := by
    apply circleQuotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (unitRealPath.map F.continuous))
    change Path.Homotopic.Quotient.mk _ =
      (Path.Homotopic.Quotient.mk (circleGeneratorPath.map ρ.continuous)).cast _ _
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk
      ((circleGeneratorPath.map ρ.continuous).cast a.property b.property)
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact hlift (t : ℝ)
  have himage : φ (FundamentalGroup.map ρ 0 s) =
      MulOpposite.op (Multiplicative.ofAdd zn) := by
    apply circleQuotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    rw [hmon]
    change (n : ℝ) + F 0 = F 1
    have h := hshift 0
    simpa only [zero_add, add_comm] using h.symm
  have hφonto := circleQuotientCovering.fundamentalGroupToMulOpposite_surjective a
  obtain ⟨v, hv⟩ := hφonto
    (MulOpposite.op (Multiplicative.ofAdd (⟨1, mem_zmultiples (1 : ℝ)⟩ : zmultiples (1 : ℝ))))
  obtain ⟨u, hu⟩ := honto v
  obtain ⟨k, hk⟩ := exists_zpow_fundamentalGroup_loopCircle u
  have hp : (MulOpposite.op (Multiplicative.ofAdd zn)) ^ k =
      MulOpposite.op (Multiplicative.ofAdd (⟨1, mem_zmultiples (1 : ℝ)⟩ : zmultiples (1 : ℝ))) := by
    rw [← himage, ← map_zpow, ← map_zpow, ← hk, hu, hv]
  have hr := congrArg
    (fun z : (Multiplicative (zmultiples (1 : ℝ)))ᵐᵒᵖ =>
      ((Multiplicative.toAdd z.unop : zmultiples (1 : ℝ)) : ℝ)) hp
  have hkn : k * n = 1 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [MulOpposite.unop_zpow, MulOpposite.unop_op, toAdd_zpow,
      toAdd_ofAdd, AddSubgroup.coe_zsmul, zn, zsmul_eq_mul, Int.cast_mul, Int.cast_one] using hr
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hkn with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem exists_primitive_real_lift (ρ : C(loopCircle, loopCircle))
    (honto : Function.Surjective (FundamentalGroup.map ρ 0)) :
    ∃ F : C(ℝ, ℝ), (∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle)) ∧
      ((∀ t : ℝ, F (t + 1) = F t + 1) ∨ (∀ t : ℝ, F (t + 1) = F t - 1)) := by
  obtain ⟨F, n, hlift, hshift⟩ := exists_real_lift_with_integer_shift ρ
  refine ⟨F, hlift, ?_⟩
  rcases integer_shift_eq_one_or_neg_one_of_surjective_fundamentalGroup
    ρ F n hlift hshift honto with hn | hn
  · exact Or.inl (fun t => by simpa [hn] using hshift t)
  · exact Or.inr (fun t => by simpa [hn, sub_eq_add_neg] using hshift t)

end DifferentialGeometry.Topology
