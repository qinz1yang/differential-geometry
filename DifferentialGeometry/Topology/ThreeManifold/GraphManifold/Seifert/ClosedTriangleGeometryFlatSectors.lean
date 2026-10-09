import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatWalls

/-!
# Angle domains in the vertex discs of a flat closed triangle fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.4, with review 27: the angle domains of the certificate and the single-valuedness of the phase).
The main set meets each vertex disc only in the good sector of that vertex, where the apex angle
`pⱼ arg ω̂ⱼ` lies in `(-π/2, 3π/2)` and the phase formula of the vertex holds: in the disc about
`v₁`, `-θ₁/2 < arg rotOne < 3θ₁/2` (`sector_one`); about `v₂`, `-θ₂/2 < arg rotTwo < 3θ₂/2`
(`sector_two`); about `0`, `-θ₃/2 < arg z < 3θ₃/2` (`sector_three`). The open triangle gives the
sector `(0, θⱼ)` from the signs of the two walls through the vertex; the patches give the wedges
of their definitions or are excluded by their image conditions.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem arg_mem_of_sides {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2)
    (h1 : 0 < w.im) (h2 : (exp (-((θ : ℂ) * I)) * w).im < 0) :
    w ≠ 0 ∧ 0 < arg w ∧ arg w < θ := by
  have hne : w ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have ha0 : 0 < arg w := lt_of_le_of_ne (arg_nonneg_iff.mpr h1.le) (fun h => by
    have := (arg_eq_zero_iff.mp h.symm).2
    linarith)
  have haπ : arg w < Real.pi := arg_lt_pi_iff.mpr (Or.inr h1.ne')
  have heq : arg (exp ((-θ : ℝ) * I) * w) = -θ + arg w :=
    arg_exp_mul_of_mem hne (by linarith [Real.pi_pos]) (by linarith)
  have hexp : exp (((-θ : ℝ) : ℂ) * I) = exp (-((θ : ℂ) * I)) := by
    congr 1; push_cast; ring
  have hneg := arg_neg_iff.mpr (show (exp (((-θ : ℝ) : ℂ) * I) * w).im < 0 by
    rw [hexp]; exact h2)
  rw [heq] at hneg
  exact ⟨hne, ha0, by linarith⟩

theorem arg_of_rot_wedge {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2)
    (h : exp (-((θ : ℂ) * I)) * w ∈ wedgeSet (θ / 2)) :
    w ≠ 0 ∧ θ / 2 < arg w ∧ arg w < 3 * θ / 2 := by
  obtain ⟨hne, habs⟩ := h
  have hw : w ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hne; exact hne rfl
  have hw' : w = exp ((θ : ℝ) * I) * (exp (-((θ : ℂ) * I)) * w) := by
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  have ha := abs_lt.mp habs
  have heq : arg (exp ((θ : ℝ) * I) * (exp (-((θ : ℂ) * I)) * w)) =
      θ + arg (exp (-((θ : ℂ) * I)) * w) :=
    arg_exp_mul_of_mem hne (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [← hw'] at heq
  refine ⟨hw, ?_, ?_⟩ <;> linarith

theorem arg_of_wedge {w : ℂ} {a : ℝ} (h : w ∈ wedgeSet a) :
    w ≠ 0 ∧ -a < arg w ∧ arg w < a :=
  ⟨h.1, (abs_lt.mp h.2).1, (abs_lt.mp h.2).2⟩

theorem re_f_of_mem_discOne {z : ℂ} (hd : z ∈ discOne D) : 1 ≤ (D.f z).re := by
  rw [(f_of_mem_discOne D hd).2, EuclidShape.apexOne]
  have hn : ‖σ.rotOne z‖ ≤ 1 / 2 := by
    rw [norm_rotOne]; exact (le_of_lt hd).trans (radOne_le_half D)
  have hp : ‖σ.rotOne z ^ σ.p₁ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖σ.rotOne z‖ ^ σ.p₁ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.1]

theorem re_f_of_mem_discTwo {z : ℂ} (hd : z ∈ discTwo D) : (D.f z).re ≤ -1 := by
  rw [(f_of_mem_discTwo D hd).2, EuclidShape.apexTwo]
  have hn : ‖σ.rotTwo z‖ ≤ 1 / 2 := by
    rw [norm_rotTwo]; exact (le_of_lt hd).trans (radTwo_le_half D)
  have hp : ‖σ.rotTwo z ^ σ.p₂ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖σ.rotTwo z‖ ^ σ.p₂ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.2]

theorem norm_f_of_mem_discThree {z : ℂ} (hd : z ∈ discThree D) (h0 : z ≠ 0) :
    3 ≤ ‖D.f z‖ := by
  rw [(f_of_mem_discThree D hd h0).2, compactOuterGerm, norm_neg, norm_mul, Complex.norm_real,
    norm_pow, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr h0), one_pow, mul_one]
  have hn : ‖z‖ ^ σ.p₃ ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_of_lt hd).trans (by linarith [radThree_le_half D]))
  rw [Real.norm_of_nonneg (by linarith)]
  linarith

theorem sector_one {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discOne D) :
    σ.rotOne z ≠ 0 ∧ -(σ.θ₁ / 2) < arg (σ.rotOne z) ∧ arg (σ.rotOne z) < 3 * σ.θ₁ / 2 := by
  have hnd : ¬ radOne D < ‖σ.rotOne z‖ := by rw [norm_rotOne]; exact not_lt.mpr (le_of_lt hd)
  have hθ := σ.θ₁_pos
  rcases hm with ((h | h) | h) | h
  · have h1 : 0 < (σ.rotOne z).im := by rw [← σ.wallSide_one_eq_im_rotOne]; exact h 1
    have h2 : (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im < 0 := by
      have := h 2
      rw [σ.wallSide_two_eq_rotOne] at this
      linarith
    obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₁_pos σ.θ₁_le h1 h2
    exact ⟨hne, by linarith, by linarith⟩
  · exfalso
    have := re_f_of_mem_discOne D hd
    linarith [h.2.2.2.2.2.1]
  · rcases h.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩
  · rcases h.2.2.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₁_pos σ.θ₁_le h'
      exact ⟨hne, by linarith, b⟩

theorem sector_two {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discTwo D) :
    σ.rotTwo z ≠ 0 ∧ -(σ.θ₂ / 2) < arg (σ.rotTwo z) ∧ arg (σ.rotTwo z) < 3 * σ.θ₂ / 2 := by
  have hnd : ¬ radTwo D < ‖σ.rotTwo z‖ := by rw [norm_rotTwo]; exact not_lt.mpr (le_of_lt hd)
  have hθ := σ.θ₂_pos
  rcases hm with ((h | h) | h) | h
  · have h1 : 0 < (σ.rotTwo z).im := h 2
    have h2 : (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im < 0 := by
      have := h 0
      rw [σ.wallSide_zero_eq_rotTwo] at this
      linarith
    obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₂_pos σ.θ₂_le h1 h2
    exact ⟨hne, by linarith, by linarith⟩
  · rcases h.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₂_pos σ.θ₂_le h'
      exact ⟨hne, by linarith, b⟩
  · exfalso
    have := re_f_of_mem_discTwo D hd
    linarith [h.2.2.2.2.2.1]
  · rcases h.2.2.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩

theorem sector_three {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discThree D) :
    z ≠ 0 ∧ -(σ.θ₃ / 2) < arg z ∧ arg z < 3 * σ.θ₃ / 2 := by
  have hnd : ¬ radThree D < ‖z‖ := not_lt.mpr (le_of_lt hd)
  have hθ := σ.θ₃_pos
  rcases hm with ((h | h) | h) | h
  · have h1 : 0 < z.im := h 0
    have h2 : (exp (-((σ.θ₃ : ℂ) * I)) * z).im < 0 := by
      have := h 1
      rw [σ.wallSide_one_eq_rotThree] at this
      linarith
    obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₃_pos σ.θ₃_le h1 h2
    exact ⟨hne, by linarith, by linarith⟩
  · rcases h.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩
  · rcases h.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₃_pos σ.θ₃_le h'
      exact ⟨hne, by linarith, b⟩
  · exfalso
    have h0 : z ≠ 0 := by
      intro h0
      have := h.2.1
      rw [h0, EuclidShape.wallSide_zero_zero] at this
      linarith [kap_pos D]
    have h3 := norm_f_of_mem_discThree D hd h0
    have h4 := h.2.2.2.2.2.2.2.1
    rw [normSq_eq_norm_sq] at h4
    nlinarith [norm_nonneg (D.f z)]

end ClosedTriangle

end GC.Seifert
