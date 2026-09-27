/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S1" => Metric.sphere (0 : E2) 1

theorem surjective_of_fundamentalGroup_map_surjective_to_circle
    {X : Type*} [TopologicalSpace X] (f : C(X, S1)) (x : X)
    (h : Function.Surjective (FundamentalGroup.map f x)) : Function.Surjective f := by
  classical
  intro p
  by_contra hp
  let P : Set S1 := {p}ᶜ
  have hP (z : X) : f z ∈ P := fun hz => hp ⟨z, hz⟩
  let f' : C(X, P) := ⟨fun z => ⟨f z, hP z⟩, f.continuous.subtype_mk _⟩
  let j : C(P, S1) := ⟨Subtype.val, continuous_subtype_val⟩
  have hfac : j.comp f' = f := rfl
  let s : P ≃ₜ ↥(ℝ ∙ (p : E2))ᗮ :=
    (stereographic (norm_eq_of_mem_sphere p)).toHomeomorphSourceTarget.trans
      (Homeomorph.Set.univ _)
  let : ContractibleSpace P := s.contractibleSpace
  have hnull (g : FundamentalGroup X x) : FundamentalGroup.map f x g = 1 := by
    rw [← hfac]
    change Path.Homotopic.Quotient.map g _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map j (f' x) (FundamentalGroup.map f' x g) = 1
    rw [Subsingleton.elim (FundamentalGroup.map f' x g) 1, map_one]
  let a : Circle ≃ₜ S1 :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]
  let e : FundamentalGroup S1 (f x) ≃* Multiplicative ℤ :=
    (fundamentalGroupMulEquivOfHomotopyEquiv a.symm.toHomotopyEquiv
      (f x) (a.symm (f x)) rfl).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        (a.symm (f x)) (1 : Circle)).trans fundamentalGroupCircleEquivInt)
  obtain ⟨g, hg⟩ := h (e.symm (Multiplicative.ofAdd (1 : ℤ)))
  have he := congrArg (fun z => Multiplicative.toAdd (e z)) (hg.symm.trans (hnull g))
  simp only [MulEquiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one] at he
  exact one_ne_zero he

end DifferentialGeometry.Topology.PiecewiseLinear
