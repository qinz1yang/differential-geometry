/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_eqOn_of_affine_cover {ι : Type*} (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F)
    (hcompat : ∀ i j, EqOn (A i) (A j) (C i ∩ C j)) :
    ∃ f : E → F, ∀ i, EqOn f (A i) (C i) := by
  classical
  refine ⟨fun x => if h : ∃ i, x ∈ C i then A h.choose x else 0, fun i x hx => ?_⟩
  have h : ∃ j, x ∈ C j := ⟨i, hx⟩
  simp only [dite_eq_left h]
  exact hcompat h.choose i ⟨h.choose_spec, hx⟩

theorem exists_isPiecewiseAffineOn_of_affine_cover {ι : Type*} [Finite ι] (C : ι → Set E)
    (hC : ∀ i, IsHPolytope (C i)) (A : ι → E →ᵃ[ℝ] F)
    (hcompat : ∀ i j, EqOn (A i) (A j) (C i ∩ C j)) :
    ∃ f : E → F, IsPiecewiseAffineOn f (⋃ i, C i) ∧ ∀ i, EqOn f (A i) (C i) := by
  obtain ⟨f, hf⟩ := exists_eqOn_of_affine_cover C A hcompat
  exact ⟨f, isPiecewiseAffineOn_of_forall_isHPolytope C hC (fun i => ⟨A i, hf i⟩), hf⟩

theorem mapsTo_of_affine_cover {ι : Type*} {C : ι → Set E} {A : ι → E →ᵃ[ℝ] F} {f : E → F}
    (hf : ∀ i, EqOn f (A i) (C i)) {S : Set F} (hS : ∀ i, MapsTo (A i) (C i) S) :
    MapsTo f (⋃ i, C i) S := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [hf i hi]
  exact hS i hi

theorem eqOn_of_affineMap_eq_of_mem_segment {A B : E →ᵃ[ℝ] F} {p q : E}
    (hp : A p = B p) (hq : A q = B q) : EqOn A B (segment ℝ p q) := by
  rintro x ⟨a, b, ha, hb, hab, rfl⟩
  have key : ∀ C : E →ᵃ[ℝ] F, C (a • p + b • q) = C p + b • (C q - C p) := by
    intro C
    have ha' : a = 1 - b := by linarith
    have h1 : a • p + b • q - p = b • (q - p) := by
      rw [ha']
      module
    have h2 : C.linear (a • p + b • q - p) = C (a • p + b • q) - C p := by
      simpa using C.linearMap_vsub (a • p + b • q) p
    have h3 : C.linear (q - p) = C q - C p := by simpa using C.linearMap_vsub q p
    rw [h1, LinearMap.map_smul, h3] at h2
    rw [← h2.symm]
    abel
  rw [key A, key B, hp, hq]

end DifferentialGeometry.Topology.PiecewiseLinear
