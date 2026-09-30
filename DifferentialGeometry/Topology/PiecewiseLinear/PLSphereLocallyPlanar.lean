/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.Simplex.NormedBall
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_isOpen_inter_homeomorph_of_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 2 S) {x : E}
    (hx : x ∈ S) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ Nonempty (↥(W ∩ S) ≃ₜ U) := by
  obtain ⟨f, hf⟩ := hS
  have hβ : ∀ z : stdSimplexBoundary 3, (⟨z.1, z.2.1⟩ : Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1))) ∈
      DifferentialGeometry.Simplex.boundary (Fin (3 + 1)) := fun z => z.2.2
  have hβ' : ∀ z : DifferentialGeometry.Simplex.boundary (Fin (3 + 1)),
      (z.1.1 : Fin (3 + 1) → ℝ) ∈ stdSimplexBoundary 3 := fun z => ⟨z.1.2, z.2⟩
  let β : stdSimplexBoundary 3 ≃ₜ DifferentialGeometry.Simplex.boundary (Fin (3 + 1)) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, hβ z⟩
      invFun := fun z => ⟨z.1.1, hβ' z⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.1).subtype_mk hβ
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hβ' }
  obtain ⟨Ψ⟩ : Nonempty (S ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1) :=
    ⟨(hf.homeomorph.symm.trans β).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩
  obtain ⟨ch, hch⟩ : ∃ ch : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)
      (EuclideanSpace ℝ (Fin 2)), Ψ ⟨x, hx⟩ ∈ ch.source :=
    ⟨chartAt (EuclideanSpace ℝ (Fin 2)) (Ψ ⟨x, hx⟩),
      mem_chart_source (EuclideanSpace ℝ (Fin 2)) (Ψ ⟨x, hx⟩)⟩
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp (ch.open_source.preimage Ψ.continuous)
  have hmem : ∀ s : S, (s : E) ∈ W ↔ Ψ s ∈ ch.source := fun s => by
    change s ∈ (Subtype.val : S → E) ⁻¹' W ↔ s ∈ Ψ ⁻¹' ch.source
    rw [hWV]
  refine ⟨W, hW, (hmem ⟨x, hx⟩).mpr hch, ch.target, ch.open_target, ?_⟩
  have ha1 : ∀ z : ↥(W ∩ S), Ψ ⟨z.1, z.2.2⟩ ∈ ch.source := fun z => (hmem ⟨z.1, z.2.2⟩).mp z.2.1
  have ha2 : ∀ v : {s : S // Ψ s ∈ ch.source}, (v.1 : E) ∈ W ∩ S :=
    fun v => ⟨(hmem v.1).mpr v.2, v.1.2⟩
  let a : ↥(W ∩ S) ≃ₜ {s : S // Ψ s ∈ ch.source} :=
    { toFun := fun z => ⟨⟨z.1, z.2.2⟩, ha1 z⟩
      invFun := fun v => ⟨v.1.1, ha2 v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.2).subtype_mk ha1
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk ha2 }
  exact ⟨(a.trans (Ψ.subtype (p := fun s => Ψ s ∈ ch.source) (q := fun v => v ∈ ch.source)
    fun _ => Iff.rfl)).trans ch.toHomeomorphSourceTarget⟩

end DifferentialGeometry.Topology.PiecewiseLinear
