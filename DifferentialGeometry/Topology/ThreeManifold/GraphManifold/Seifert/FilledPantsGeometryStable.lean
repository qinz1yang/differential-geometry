import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryInvariance

/-!
# Stability of the pieces of the two-cone domain under the reflections

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3).
The wall patches are stable under their reflections (`refl_one_mem_patchOne`,
`refl_two_mem_patchTwo`), the cone disc about `v₁` under `σ₁` and under the rotation `σ₁σ₂`,
the cone disc about `v₂` under the rotation `σ₂σ₀`; the walls of the triangle minus the vertices
lie in their patches (`mem_patchOne_of_wall`, `mem_patchTwo_of_wall`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace TwoConeFold

theorem wedgeSet_conj {a : ℝ} (ha : a ≤ Real.pi) {w : ℂ} (hw : w ∈ wedgeSet a) :
    conj w ∈ wedgeSet a := by
  refine ⟨by simpa using hw.1, ?_⟩
  rw [arg_conj, ite_eq_right (fun h => by
    have := hw.2; rw [h, abs_of_pos Real.pi_pos] at this; linarith), abs_neg]
  exact hw.2

namespace Fold

open ConeShape

variable {σ : ConeShape} (D : σ.FoldData) {p₁ p₂ : ℕ} (hθ₁ : σ.θ₁ * p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * p₂ = Real.pi)

theorem refl_one_mem_patchOne {z : ℂ} (hz : z ∈ patchOne D hθ₁) :
    σ.refl 1 z ∈ patchOne D hθ₁ := by
  obtain ⟨h0, hV, hx1, hx2, hw2, hw2', hre, hwedge⟩ := hz
  refine ⟨σ.refl_im_pos h0 1, D.refl_mapsTo_V 1 hV, ?_, ?_, hw2', ?_, ?_, ?_⟩
  · simp [ConeShape.refl]; linarith
  · simp [ConeShape.refl]; linarith
  · rw [σ.refl_refl h0 1]; exact hw2
  · rw [D.f_refl 1 z hV, conj_re]; exact hre
  · rw [σ.coneDisc_vertexOne_refl_one, norm_conj]
    rcases hwedge with h | h
    · exact Or.inl h
    · exact Or.inr (wedgeSet_conj (pi_div_le_one hθ₁) h)

theorem xi_refl_two {z : ℂ} (hz : 0 < z.im) :
    exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (σ.refl 2 z) =
      conj (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) := by
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [σ.coneDisc_vertexTwo_refl_two hc, map_mul, ← exp_conj, ← mul_assoc, ← exp_add]
  have : (σ.θ₂ : ℂ) * I + 2 * ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I =
      conj ((σ.θ₂ : ℂ) * I) + 2 * Real.pi * I := by
    simp only [map_mul, conj_I, conj_ofReal]
    push_cast
    ring
  rw [this, exp_add, exp_two_pi_mul_I, mul_one]

theorem rot_coneDisc_one_refl_two {z : ℂ} (hz : 0 < z.im) :
    exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne (σ.refl 2 z) =
      conj (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z) := by
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [σ.coneDisc_vertexOne_refl_two hc, map_mul, ← exp_conj, ← mul_assoc, ← exp_add]
  congr 2
  simp only [map_mul, map_neg, conj_I, conj_ofReal]
  ring

theorem refl_two_mem_patchTwo {z : ℂ} (hz : z ∈ patchTwo D hθ₁ hθ₂) :
    σ.refl 2 z ∈ patchTwo D hθ₁ hθ₂ := by
  obtain ⟨h0, hV, hx1, hx2, hy1, hy2, hre1, hre2, hw1, hw2⟩ := hz
  have h0' := σ.refl_im_pos h0 2
  refine ⟨h0', D.refl_mapsTo_V 2 hV, hy1, hy2, by rw [σ.refl_refl h0 2]; exact hx1,
    by rw [σ.refl_refl h0 2]; exact hx2, by rw [D.f_refl 2 z hV, conj_re]; exact hre1,
    by rw [D.f_refl 2 z hV, conj_re]; exact hre2, ?_, ?_⟩
  · rw [rot_coneDisc_one_refl_two h0]
    have hn : ‖coneDisc σ.vertexOne (σ.refl 2 z)‖ = ‖coneDisc σ.vertexOne z‖ := by
      have hc : z ≠ σ.centre := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      rw [σ.coneDisc_vertexOne_refl_two hc, norm_mul, norm_conj, Complex.norm_exp]
      simp
    rw [hn]
    rcases hw1 with h | h
    · exact Or.inl h
    · exact Or.inr (wedgeSet_conj (pi_div_le_one hθ₁) h)
  · rw [xi_refl_two h0]
    have hn : ‖coneDisc σ.vertexTwo (σ.refl 2 z)‖ = ‖coneDisc σ.vertexTwo z‖ := by
      have hc : z ≠ σ.centre := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      rw [σ.coneDisc_vertexTwo_refl_two hc, norm_mul, norm_conj, Complex.norm_exp]
      simp
    rw [hn]
    rcases hw2 with h | h
    · exact Or.inl h
    · exact Or.inr (wedgeSet_conj (pi_div_le_two hθ₂) h)

theorem refl_one_mem_discOne {z : ℂ} (hz : z ∈ discOne D hθ₁) : σ.refl 1 z ∈ discOne D hθ₁ :=
  ⟨σ.refl_im_pos hz.1 1, by rw [σ.coneDisc_vertexOne_refl_one, norm_conj]; exact hz.2⟩

theorem rot_mem_discOne {z : ℂ} (hz : z ∈ discOne D hθ₁) :
    σ.refl 1 (σ.refl 2 z) ∈ discOne D hθ₁ := by
  refine ⟨σ.refl_im_pos (σ.refl_im_pos hz.1 2) 1, ?_⟩
  rw [coneDisc_rot_one hz.1, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact hz.2

theorem rot_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D hθ₂) :
    σ.refl 2 (σ.refl 0 z) ∈ discTwo D hθ₂ := by
  refine ⟨σ.refl_im_pos (σ.refl_im_pos hz.1 0) 2, ?_⟩
  rw [coneDisc_rot_two hz.1, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact hz.2

include hθ₁ in
theorem mem_patchOne_of_wall {z : ℂ} (hw : z ∈ σ.foldWall 1) (hne : z ≠ σ.vertexOne) :
    z ∈ patchOne D hθ₁ := by
  have hfix : σ.refl 1 z = z := σ.refl_of_wallSide_eq_zero hw.1.1 hw.2
  have hx : z.re = σ.width := by have := hw.2; change σ.width - z.re = 0 at this; linarith
  obtain ⟨hω0, hωa⟩ := coneDisc_vertexOne_wallOne σ hw hne
  have hp₁ : (0 : ℝ) < p₁ := by exact_mod_cast Nat.pos_of_ne_zero (p₁_ne_zero hθ₁)
  refine ⟨hw.1.1, D.foldWall_subset_V 1 hw, by rw [hx]; linarith [σ.width_pos],
    by rw [hx]; linarith [σ.width_pos], wallSide_two_pos_of_wallOne σ hw hne,
    by rw [hfix]; exact wallSide_two_pos_of_wallOne σ hw hne,
    (re_f_of_mem_foldWall_one D hθ₁ hw hne).1, Or.inr ⟨hω0, ?_⟩⟩
  rw [hωa, abs_zero]; positivity

include hθ₁ hθ₂ in
theorem mem_patchTwo_of_wall {z : ℂ} (hw : z ∈ σ.foldWall 2) (hne1 : z ≠ σ.vertexOne)
    (hne2 : z ≠ σ.vertexTwo) : z ∈ patchTwo D hθ₁ hθ₂ := by
  have hm := triangle_diff_subset_mainSet D hθ₁ hθ₂ hw.1 hne1 hne2
  have hw2 : σ.wallSide 2 z = 0 := hw.2
  rcases hm with ((h | h) | h) | h
  · have := h.2 2; rw [hw2] at this; exact absurd this (lt_irrefl 0)
  · have := h.2.2.2.1; rw [hw2] at this; exact absurd this (lt_irrefl 0)
  · have := h.2.2.2.2.1; rw [hw2] at this; exact absurd this (lt_irrefl 0)
  · exact h

end Fold

end TwoConeFold

end GC.Seifert
