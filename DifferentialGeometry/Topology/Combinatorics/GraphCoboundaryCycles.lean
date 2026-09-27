/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Combinatorics.GraphCoboundary

namespace DifferentialGeometry.Topology.Combinatorics

theorem sum_coboundary_eq_zero_of_cycle {V E : Type*} (ends : E → V × V)
    (σ : V → ZMod 2) (F : Finset E)
    (hcycle : ∀ v : V, ∑ e ∈ F, edgeBoundary ends e v = 0) :
    ∑ e ∈ F, (σ (ends e).1 + σ (ends e).2) = 0 := by
  classical
  let T := F.image (fun e => (ends e).1) ∪ F.image (fun e => (ends e).2)
  have hlocal (e : E) (he : e ∈ F) :
      ∑ v ∈ T, σ v * edgeBoundary ends e v = σ (ends e).1 + σ (ends e).2 := by
    have h₁ : (ends e).1 ∈ T := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have h₂ : (ends e).2 ∈ T := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    simp [edgeBoundary, Pi.single_apply, mul_add, Finset.sum_add_distrib, h₁, h₂]
  calc
    _ = ∑ e ∈ F, ∑ v ∈ T, σ v * edgeBoundary ends e v :=
      Finset.sum_congr rfl fun e he => (hlocal e he).symm
    _ = ∑ v ∈ T, ∑ e ∈ F, σ v * edgeBoundary ends e v := Finset.sum_comm
    _ = ∑ v ∈ T, σ v * 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, hcycle v]
    _ = 0 := by simp

theorem cycle_zero_iff_exists_vertex_signs {V E : Type*}
    (ends : E → V × V) (sign : E → ZMod 2) :
    (∀ F : Finset E, (∀ v : V, ∑ e ∈ F, edgeBoundary ends e v = 0) →
      ∑ e ∈ F, sign e = 0) ↔
      ∃ σ : V → ZMod 2, ∀ e, sign e = σ (ends e).1 + σ (ends e).2 := by
  constructor
  · exact exists_vertex_signs_of_cycle_zero ends sign
  · rintro ⟨σ, hσ⟩ F hF
    simpa only [hσ] using sum_coboundary_eq_zero_of_cycle ends σ F hF

end DifferentialGeometry.Topology.Combinatorics
