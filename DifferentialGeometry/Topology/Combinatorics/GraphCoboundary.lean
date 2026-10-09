/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Field.ZMod

namespace DifferentialGeometry.Topology.Combinatorics

noncomputable def edgeBoundary {V E : Type*} (ends : E → V × V) (e : E) :
    V → ZMod 2 := by
  classical
  exact Pi.single (ends e).1 1 + Pi.single (ends e).2 1

private noncomputable def incidence {V E : Type*} (ends : E → V × V) :
    (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (edgeBoundary ends)

private noncomputable def signFunctional {E : Type*} (sign : E → ZMod 2) :
    Module.Dual (ZMod 2) (E →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) sign

private theorem exists_vertex_signs_of_linear_cycle_zero {V E : Type*}
    (ends : E → V × V) (sign : E → ZMod 2)
    (hcycle : ∀ z : E →₀ ZMod 2, incidence ends z = 0 → signFunctional sign z = 0) :
    ∃ sigma : V → ZMod 2,
      ∀ e, sign e = sigma (ends e).1 + sigma (ends e).2 := by
  classical
  have hmem : signFunctional sign ∈ (LinearMap.ker (incidence ends)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact hcycle z (LinearMap.mem_ker.mp hz)
  have hmem' : signFunctional sign ∈ LinearMap.range (incidence ends).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker (incidence ends)]
    exact hmem
  obtain ⟨lambda, hlambda⟩ := hmem'
  refine ⟨fun v => lambda (Pi.single v 1), ?_⟩
  intro e
  have he := congrArg (fun f : Module.Dual (ZMod 2) (E →₀ ZMod 2) =>
    f (Finsupp.single e 1)) hlambda.symm
  simp only [signFunctional, incidence, LinearMap.dualMap_apply,
    Finsupp.linearCombination_single, one_smul,
    edgeBoundary, map_add] at he
  exact he

theorem exists_vertex_signs_of_cycle_zero {V E : Type*}
    (ends : E → V × V) (sign : E → ZMod 2)
    (hcycle : ∀ F : Finset E,
      (∀ v : V, ∑ e ∈ F, (edgeBoundary ends e) v = 0) →
      ∑ e ∈ F, sign e = 0) :
    ∃ sigma : V → ZMod 2,
      ∀ e, sign e = sigma (ends e).1 + sigma (ends e).2 := by
  classical
  apply exists_vertex_signs_of_linear_cycle_zero ends sign
  intro z hz
  let F : Finset E := z.support
  have hzone (e : E) (he : e ∈ F) : z e = 1 := by
    have hne : z e ≠ 0 := Finsupp.mem_support_iff.mp he
    have h01 : z e = 0 ∨ z e = 1 :=
      (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (z e)
    exact h01.resolve_left hne
  have hB (v : V) :
      (incidence ends z) v = ∑ e ∈ F, (edgeBoundary ends e) v := by
    simp only [incidence, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [hzone e he, one_mul]
  have hL : signFunctional sign z = ∑ e ∈ F, sign e := by
    simp only [signFunctional, Finsupp.linearCombination_apply, Finsupp.sum,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [hzone e he, one_mul]
  rw [hL]
  apply hcycle F
  intro v
  rw [← hB]
  exact congrFun hz v

end DifferentialGeometry.Topology.Combinatorics
