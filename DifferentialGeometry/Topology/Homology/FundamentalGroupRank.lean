/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FieldHurewiczOne
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

open scoped IsMulCommutative

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X] [PathConnectedSpace X]
variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] [Module.IsTorsionFree ℤ A]

theorem fieldSingularHomology_one_finrank_le_of_fundamentalGroup_injective
    (x : X) (f : FundamentalGroup X x →* Multiplicative A) (hf : Function.Injective f) :
    Module.finrank k ((fieldSingularChains (k := k) (X := X)).homology 1) ≤
      Module.finrank ℤ A := by
  classical
  let _ : IsMulCommutative (FundamentalGroup X x) := isMulCommutative_iff.mpr fun a b => by
    apply hf
    rw [map_mul, map_mul, mul_comm]
  let F := f.toAdditiveLeft.toIntLinearMap
  have hF : Function.Injective F := by
    intro a b h
    exact Additive.toMul.injective (hf (congrArg Multiplicative.ofAdd h))
  let _ : Module.Finite ℤ (Additive (FundamentalGroup X x)) := Module.Finite.of_injective F hF
  let _ : Module.IsTorsionFree ℤ (Additive (FundamentalGroup X x)) :=
    hF.moduleIsTorsionFree F F.map_smul
  let b := Module.Free.chooseBasis ℤ (Additive (FundamentalGroup X x))
  let h := (fieldHurewiczOne (k := k) x).toAdditiveLeft
  let S := Submodule.span k (Set.range (fun i => h (b i)))
  have hmem (a : Additive (FundamentalGroup X x)) : h a ∈ S := by
    have ha : a ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add a c _ _ ha hc => simpa only [map_add] using S.add_mem ha hc
    | smul r a _ ha =>
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul k]
      exact S.smul_mem (r : k) ha
  have hspan : S = ⊤ := by
    apply top_unique
    rw [← fieldHurewiczOne_span_range (k := k) x]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hmem (Additive.ofMul a)
  have hrank := finrank_le_of_span_eq_top hspan
  rw [← Module.finrank_eq_card_basis b] at hrank
  exact hrank.trans (LinearMap.finrank_le_finrank_of_injective hF)

end DifferentialGeometry.Topology
