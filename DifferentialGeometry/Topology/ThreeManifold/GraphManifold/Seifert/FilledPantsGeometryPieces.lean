import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryOverlap

/-!
# Combinatorics of the pieces of the two-cone domain

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3,
with review 21 §4.2–§4.4). Facts about the open pieces of `Seifert/FilledPantsGeometryDomain`
used by the fold and by the same-image analysis: the closed triangle minus its cone vertices lies
in `mainSet` (`triangle_diff_subset_mainSet`); each wall patch reflects into the triangle
(`patchZero_cases`, `patchOne_cases`, `patchTwo_cases`), so `|f| < 3` on `mainSet`
(`norm_f_lt_three_of_mainSet`); the cone discs and the mirrored pieces are separated by the real
part (`discOne ⊆ {x > W/2}`, `mirror discOne ⊆ {x < -W/2}`, `discTwo ⊆ {|x| < W/2}`,
`mainSet ⊆ {x > -W/2}`), the main piece meets its mirror only in `patchZero`
(`mainSet_inter_mirror_subset`), and `discTwo` is mirror symmetric (`refl_zero_mem_discTwo`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

variable {σ : ConeShape} (D : σ.FoldData) {p₁ p₂ : ℕ} (hθ₁ : σ.θ₁ * p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * p₂ = Real.pi)

include hθ₁ hθ₂ in
theorem triangle_diff_subset_mainSet {z : ℂ} (hz : z ∈ σ.triangle) (hne1 : z ≠ σ.vertexOne)
    (hne2 : z ≠ σ.vertexTwo) : z ∈ mainSet D hθ₁ hθ₂ := by
  by_cases hint : ∀ i, 0 < σ.wallSide i z
  · exact Or.inl (Or.inl (Or.inl ⟨hz.1, hint⟩))
  push Not at hint
  obtain ⟨i, hi⟩ := hint
  have hi0 : σ.wallSide i z = 0 := le_antisymm hi (hz.2 i)
  have hwall : z ∈ σ.foldWall i := ⟨hz, hi0⟩
  have hfix : σ.refl i z = z := σ.refl_of_wallSide_eq_zero hz.1 hi0
  have hp₁ : (0 : ℝ) < p₁ := by exact_mod_cast Nat.pos_of_ne_zero (p₁_ne_zero hθ₁)
  have hp₂ : (0 : ℝ) < p₂ := by exact_mod_cast Nat.pos_of_ne_zero (p₂_ne_zero hθ₂)
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · left; left; right
    have hx : z.re = 0 := hi0
    obtain ⟨hω0, hωa⟩ := coneDisc_vertexTwo_wallZero σ hwall hne2 (θ₂_pos hθ₂)
    refine ⟨hz.1, D.foldWall_subset_V 0 hwall, by rw [hx, abs_zero]; linarith [σ.width_pos],
      wallSide_two_pos_of_wallZero σ hwall hne2, ?_,
      (re_f_of_mem_foldWall_zero D hθ₂ hwall hne2).2, Or.inr ⟨hω0, ?_⟩⟩
    · change 0 < σ.wallSide 2 (σ.refl 0 z)
      rw [hfix]
      exact wallSide_two_pos_of_wallZero σ hwall hne2
    · rw [hωa, abs_zero]; positivity
  · left; right
    have hx : z.re = σ.width := by change σ.width - z.re = 0 at hi0; linarith
    obtain ⟨hω0, hωa⟩ := coneDisc_vertexOne_wallOne σ hwall hne1
    refine ⟨hz.1, D.foldWall_subset_V 1 hwall, by rw [hx]; linarith [σ.width_pos],
      by rw [hx]; linarith [σ.width_pos], wallSide_two_pos_of_wallOne σ hwall hne1, ?_,
      (re_f_of_mem_foldWall_one D hθ₁ hwall hne1).1, Or.inr ⟨hω0, ?_⟩⟩
    · change 0 < σ.wallSide 2 (σ.refl 1 z)
      rw [hfix]
      exact wallSide_two_pos_of_wallOne σ hwall hne1
    · rw [hωa, abs_zero]; positivity
  · right
    have hx0 : 0 < z.re := by
      rcases (hz.2 0).lt_or_eq with h | h
      · exact h
      · exfalso
        have := wallSide_two_pos_of_wallZero σ ⟨hz, h.symm⟩ hne2
        change σ.wallSide 2 z = 0 at hi0
        linarith
    have hx1 : z.re < σ.width := by
      rcases (hz.2 1).lt_or_eq with h | h
      · change 0 < σ.width - z.re at h; linarith
      · exfalso
        have := wallSide_two_pos_of_wallOne σ ⟨hz, h.symm⟩ hne1
        change σ.wallSide 2 z = 0 at hi0
        linarith
    obtain ⟨t₁, ht₁, he₁⟩ := rot_coneDisc_one_of_wallTwo σ hwall hx1
    obtain ⟨t₂, ht₂, he₂⟩ := xi_of_wallTwo σ hwall hx0 (θ₂_pos hθ₂)
    have hre := re_f_of_mem_foldWall_two D hθ₁ hθ₂ hwall hne1 hne2
    refine ⟨hz.1, D.foldWall_subset_V 2 hwall, hx0, hx1, by rw [hfix]; exact hx0,
      by rw [hfix]; exact hx1, hre.1, hre.2, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [he₁]; exact_mod_cast ht₁.ne'
    · rw [he₁, arg_ofReal_of_nonneg ht₁.le, abs_zero]; positivity
    · rw [he₂]; exact_mod_cast ht₂.ne'
    · rw [he₂, arg_ofReal_of_nonneg ht₂.le, abs_zero]; positivity

theorem patchZero_cases {z : ℂ} (hz : z ∈ patchZero D hθ₂) :
    z ∈ σ.triangle ∨ σ.refl 0 z ∈ σ.triangle := by
  obtain ⟨h0, -, hx, hw2, hw2', -, -⟩ := hz
  rw [abs_lt] at hx
  rcases le_or_gt 0 z.re with h | h
  · left
    refine ⟨h0, fun i => ?_⟩
    fin_cases i
    · exact h
    · change 0 ≤ σ.width - z.re; linarith
    · exact hw2.le
  · right
    refine ⟨by simpa [ConeShape.refl] using h0, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ (σ.refl 0 z).re; simp [ConeShape.refl]; linarith
    · change 0 ≤ σ.width - (σ.refl 0 z).re; simp [ConeShape.refl]; linarith
    · exact hw2'.le

theorem patchOne_cases {z : ℂ} (hz : z ∈ patchOne D hθ₁) :
    z ∈ σ.triangle ∨ σ.refl 1 z ∈ σ.triangle := by
  obtain ⟨h0, -, hx1, hx2, hw2, hw2', -, -⟩ := hz
  rcases le_or_gt z.re σ.width with h | h
  · left
    refine ⟨h0, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ z.re; linarith [σ.width_pos]
    · change 0 ≤ σ.width - z.re; linarith
    · exact hw2.le
  · right
    refine ⟨σ.refl_im_pos h0 1, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ (σ.refl 1 z).re; simp [ConeShape.refl]; linarith
    · change 0 ≤ σ.width - (σ.refl 1 z).re; simp [ConeShape.refl]; linarith
    · exact hw2'.le

theorem patchTwo_cases {z : ℂ} (hz : z ∈ patchTwo D hθ₁ hθ₂) :
    z ∈ σ.triangle ∨ σ.refl 2 z ∈ σ.triangle := by
  obtain ⟨h0, -, hx1, hx2, hy1, hy2, -, -, -, -⟩ := hz
  rcases le_or_gt 0 (σ.wallSide 2 z) with h | h
  · left
    refine ⟨h0, fun i => ?_⟩
    fin_cases i
    · exact hx1.le
    · change 0 ≤ σ.width - z.re; linarith
    · exact h
  · right
    refine ⟨σ.refl_im_pos h0 2, fun i => ?_⟩
    fin_cases i
    · exact hy1.le
    · change 0 ≤ σ.width - (σ.refl 2 z).re; linarith
    · change 0 ≤ σ.wallSide 2 (σ.refl 2 z)
      rw [σ.wallSide_refl_two h0]
      have hn : 0 < normSq (z - σ.centre) := normSq_pos.2 (σ.centre_ne h0)
      have : 0 < -σ.wallSide 2 z / (16 * normSq (z - σ.centre)) := by
        apply div_pos (by linarith) (by positivity)
      exact this.le

theorem norm_f_refl {i : Fin 3} {z : ℂ} (hz : z ∈ D.V i) : ‖D.f (σ.refl i z)‖ = ‖D.f z‖ := by
  rw [D.f_refl i z hz, norm_conj]

include hθ₁ hθ₂ in
theorem norm_f_lt_three_of_mainSet {z : ℂ} (hz : z ∈ mainSet D hθ₁ hθ₂) : ‖D.f z‖ < 3 := by
  rcases hz with ((h | h) | h) | h
  · exact norm_f_lt_three D ⟨h.1, fun i => (h.2 i).le⟩
  · rcases patchZero_cases D hθ₂ h with h' | h'
    · exact norm_f_lt_three D h'
    · rw [← norm_f_refl D h.2.1]; exact norm_f_lt_three D h'
  · rcases patchOne_cases D hθ₁ h with h' | h'
    · exact norm_f_lt_three D h'
    · rw [← norm_f_refl D h.2.1]; exact norm_f_lt_three D h'
  · rcases patchTwo_cases D hθ₁ hθ₂ h with h' | h'
    · exact norm_f_lt_three D h'
    · rw [← norm_f_refl D h.2.1]; exact norm_f_lt_three D h'

theorem re_gt_of_mainSet {z : ℂ} (hz : z ∈ mainSet D hθ₁ hθ₂) : -(σ.width / 2) < z.re := by
  have hw := σ.width_pos
  rcases hz with ((h | h) | h) | h
  · linarith [h.2 0, show σ.wallSide 0 z = z.re from rfl]
  · have := h.2.2.1; rw [abs_lt] at this; exact this.1
  · linarith [h.2.2.1]
  · linarith [h.2.2.1]

theorem re_lt_of_mirror_discOne {z : ℂ} (hz : z ∈ mirrorSet σ (discOne D hθ₁)) :
    z.re < -(σ.width / 2) := by
  have := re_of_mem_discOne D hθ₁ hz.2
  simp [ConeShape.refl] at this
  linarith

theorem refl_zero_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D hθ₂) :
    σ.refl 0 z ∈ discTwo D hθ₂ := by
  refine ⟨by simpa [ConeShape.refl] using hz.1, ?_⟩
  rw [σ.coneDisc_vertexTwo_refl_zero, norm_conj]
  exact hz.2

theorem mirror_discTwo {z : ℂ} (hz : z ∈ discTwo D hθ₂) : z ∈ mirrorSet σ (discTwo D hθ₂) :=
  ⟨hz.1, refl_zero_mem_discTwo D hθ₂ hz⟩

theorem not_mem_discOne_of_mirrorMain {z : ℂ} (hz : z ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    z ∉ discOne D hθ₁ := by
  intro hd
  have h1 := re_of_mem_discOne D hθ₁ hd
  have h2 := re_gt_of_mainSet D hθ₁ hθ₂ hz.2
  simp [ConeShape.refl] at h2
  linarith

theorem not_mem_mirrorDiscOne_of_main {z : ℂ} (hz : z ∈ mainSet D hθ₁ hθ₂) :
    z ∉ mirrorSet σ (discOne D hθ₁) := fun hd => by
  linarith [re_gt_of_mainSet D hθ₁ hθ₂ hz, re_lt_of_mirror_discOne D hθ₁ hd]

theorem not_mem_mirrorDiscOne_of_discOne {z : ℂ} (hz : z ∈ discOne D hθ₁) :
    z ∉ mirrorSet σ (discOne D hθ₁) := fun hd => by
  linarith [re_of_mem_discOne D hθ₁ hz, re_lt_of_mirror_discOne D hθ₁ hd, σ.width_pos]

theorem not_mem_discTwo_of_discOne {z : ℂ} (hz : z ∈ discOne D hθ₁) :
    z ∉ discTwo D hθ₂ := fun hd => by
  have h1 := re_of_mem_discOne D hθ₁ hz
  have h2 := re_of_mem_discTwo D hθ₂ hd
  rw [abs_lt] at h2
  linarith

theorem not_mem_discTwo_of_mirrorDiscOne {z : ℂ} (hz : z ∈ mirrorSet σ (discOne D hθ₁)) :
    z ∉ discTwo D hθ₂ := fun hd => by
  have h1 := re_lt_of_mirror_discOne D hθ₁ hz
  have h2 := re_of_mem_discTwo D hθ₂ hd
  rw [abs_lt] at h2
  linarith

theorem mainSet_inter_mirror_subset {z : ℂ} (hz : z ∈ mainSet D hθ₁ hθ₂)
    (hz' : z ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) : z ∈ patchZero D hθ₂ := by
  have hrefl : σ.refl 0 (σ.refl 0 z) = z := σ.refl_refl hz'.1 0
  have key : ∀ w : ℂ, w ∈ mainSet D hθ₁ hθ₂ → 0 ≤ w.re ∨ w ∈ patchZero D hθ₂ := by
    intro w hw
    rcases hw with ((h | h) | h) | h
    · exact Or.inl (h.2 0).le
    · exact Or.inr h
    · exact Or.inl (by linarith [h.2.2.1, σ.width_pos])
    · exact Or.inl h.2.2.1.le
  have hstab : ∀ w : ℂ, w ∈ patchZero D hθ₂ → σ.refl 0 w ∈ patchZero D hθ₂ := by
    rintro w ⟨h0, hV, hx, hw2, hw2', hre, hwedge⟩
    have hw0 := σ.refl_refl h0 0
    refine ⟨by simpa [ConeShape.refl] using h0, D.refl_mapsTo_V 0 hV,
      by simpa [ConeShape.refl] using hx, hw2', by rw [hw0]; exact hw2, ?_, ?_⟩
    · rw [D.f_refl 0 w hV, conj_re]; exact hre
    · rw [σ.coneDisc_vertexTwo_refl_zero, norm_conj]
      rcases hwedge with h | ⟨hne, ha⟩
      · exact Or.inl h
      · refine Or.inr ⟨by simpa using hne, ?_⟩
        rw [arg_conj, ite_eq_right (fun h => by
          rw [h, abs_of_pos Real.pi_pos] at ha
          have := pi_div_le_two hθ₂
          have hp : (1 : ℝ) < 2 * p₂ := by
            have : (1 : ℝ) ≤ p₂ := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (p₂_ne_zero hθ₂)
            linarith
          have : Real.pi / (2 * p₂) < Real.pi := by
            rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos]
          linarith), abs_neg]
        exact ha
  rcases key z hz with h | h
  · rcases key _ hz'.2 with h' | h'
    · have : z.re = 0 := by simp [ConeShape.refl] at h'; linarith
      rcases hz with ((h1 | h1) | h1) | h1
      · exfalso; have := h1.2 0; change 0 < z.re at this; linarith
      · exact h1
      · exfalso; linarith [h1.2.2.1, σ.width_pos]
      · exfalso; linarith [h1.2.2.1]
    · rw [← hrefl]; exact hstab _ h'
  · exact h

end Fold

end TwoConeFold

end GC.Seifert
