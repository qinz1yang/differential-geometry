import DifferentialGeometry.Geometry.Collapse.MetricRank.HalfPlaneBinding
import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# A point with a two-splitting is not a strong edge point (S-FIXTURE-C1, K1, file 7)

`isEdgePoint p Δ b s` gives a `b`-approximation `F` of `X` near `p` by `ℝ ×₂ Y` and an
`s`-approximation `G` of `Y` near `q` by the interval `[0, C]`, with `q ↦ 0`; hence a map
`π(x) = (F(x).fst, G(F(x).snd)) : X → H` (closed upper half plane) with additive distortion
`≤ b + s`
on `B(p, 6)` and `π p = (0, 0)`. A `β`-splitting of rank two at `p` contradicts the pointed
half-plane obstruction (`not_splitting_ge_two_at_halfplane_boundary_of_norm_le_SMR`, review 75
section C.5).
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

universe u v

theorem abs_sub_le_of_sq_FXC1 {P Q A d e : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hP2 : P ^ 2 = A ^ 2 + d ^ 2) (hQ2 : Q ^ 2 = A ^ 2 + e ^ 2) : |P - Q| ≤ |d - e| := by
  have key : ∀ {P Q d e : ℝ}, 0 ≤ P → 0 ≤ Q → 0 ≤ d → 0 ≤ e → P ^ 2 = A ^ 2 + d ^ 2 →
      Q ^ 2 = A ^ 2 + e ^ 2 → e ≤ d → P - Q ≤ d - e ∧ Q ≤ P := by
    intro P Q d e hP hQ hd he hP2 hQ2 hed
    have hQP : Q ≤ P := by
      apply abs_le_of_sq_le_sq' _ hP |>.2
      nlinarith
    have hQe : e ≤ Q := by
      apply le_of_sq_le_sq _ hQ
      nlinarith [sq_nonneg A]
    refine ⟨?_, hQP⟩
    have : P ^ 2 ≤ (Q + (d - e)) ^ 2 := by nlinarith
    have := abs_le_of_sq_le_sq' this (by linarith)
    linarith [this.2]
  rcases le_total e d with h | h
  · obtain ⟨h1, h2⟩ := key hP hQ hd he hP2 hQ2 h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨h1, h2⟩ := key hQ hP he hd hQ2 hP2 h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith


/-- **A point with a rank-two splitting at tolerance `β ≤ 3/20` is not a strong edge point**
(for `b ≤ 1/6`, `s ≤ 1/7`, `b + s ≤ 1/100`). -/
theorem not_isEdgePoint_of_hasEuclideanSplitting_two_FXC1 {X : Type u} [MetricSpace X] {p : X}
    {β Δ b s : ℝ} (hβ : β ≤ 3 / 20) (h2 : HasEuclideanSplitting.{u, v} p 2 β) (hb : b ≤ 1 / 6)
    (hs : s ≤ 1 / 7) (hbs : b + s ≤ 1 / 100) : ¬ isEdgePoint.{u, v} p Δ b s := by
  rintro ⟨Y, mY, q, C, hC, -, ⟨F⟩, ⟨G⟩⟩
  obtain ⟨Y', mY', q', ⟨f⟩⟩ := h2
  have hb0 := F.error_pos
  have hs0 := G.error_pos
  have hb6 : 6 ≤ b⁻¹ := (le_inv_comm₀ (by norm_num) hb0).mpr (by simpa using hb)
  have hs7 : 7 ≤ s⁻¹ := (le_inv_comm₀ (by norm_num) hs0).mpr (by simpa using hs)
  let π : X → EuclideanSpace ℝ (Fin 2) := fun x =>
    !₂[(F.toFun x).fst, ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ)]
  have hπ : ∀ x ∈ ball p 6, ∀ y ∈ ball p 6, |(dist x y - ‖π x - π y‖)| ≤ b + s := by
    intro x hx y hy
    have hxb : x ∈ ball p b⁻¹ := ball_subset_ball hb6 hx
    have hyb : y ∈ ball p b⁻¹ := ball_subset_ball hb6 hy
    have hFd := F.distortion x hxb y hyb
    have hsq := WithLp.prod_dist_sq_eq_add_sq (F.toFun x) (F.toFun y)
    have hy1 : (F.toFun x).snd ∈ ball q s⁻¹ := by
      have h1 := WithLp.dist_snd_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
      have h2 := F.radial_error x hxb
      have h3 : dist x p < 6 := hx
      rw [mem_ball]
      simp only [WithLp.toLp_snd] at h1
      rw [abs_le] at h2
      linarith [h2.2]
    have hy2 : (F.toFun y).snd ∈ ball q s⁻¹ := by
      have h1 := WithLp.dist_snd_le (F.toFun y) (WithLp.toLp 2 ((0 : ℝ), q))
      have h2 := F.radial_error y hyb
      have h3 : dist y p < 6 := hy
      rw [mem_ball]
      simp only [WithLp.toLp_snd] at h1
      rw [abs_le] at h2
      linarith [h2.2]
    have hGd := G.distortion _ hy1 _ hy2
    have hGe : dist (G.toFun (F.toFun x).snd) (G.toFun (F.toFun y).snd) =
        |((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
          ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)| := by
      rw [Subtype.dist_eq, Real.dist_eq]
    rw [hGe] at hGd
    have hnorm : ‖π x - π y‖ ^ 2 = ((F.toFun x).fst - (F.toFun y).fst) ^ 2 +
        (((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
          ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)) ^ 2 := by
      have : π x - π y = !₂[(F.toFun x).fst - (F.toFun y).fst,
          ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
            ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)] := by
        ext i
        fin_cases i <;> simp [π]
      rw [this, norm_sq_mk_SMR]
    have hd1 : dist (F.toFun x).fst (F.toFun y).fst ^ 2 =
        ((F.toFun x).fst - (F.toFun y).fst) ^ 2 := by
      rw [Real.dist_eq, sq_abs]
    generalize hg1 : ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) = g₁ at hnorm hGd
    generalize hg2 : ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ) = g₂ at hnorm hGd
    generalize hdd : dist (F.toFun x).snd (F.toFun y).snd = d at hsq hGd
    have hd0 : 0 ≤ d := hdd ▸ dist_nonneg
    have hP := abs_sub_le_of_sq_FXC1 (P := dist (F.toFun x) (F.toFun y))
      (Q := ‖π x - π y‖) (A := (F.toFun x).fst - (F.toFun y).fst) (d := d) (e := |g₁ - g₂|)
      dist_nonneg (norm_nonneg _) hd0 (abs_nonneg _) (by rw [hsq, hd1]) (by rw [hnorm, sq_abs])
    have hGd' : |(d - |g₁ - g₂|)| ≤ s := by
      rw [abs_sub_comm]
      exact hGd
    have h5 := abs_sub (dist x y) ‖π x - π y‖
    have h6 := abs_sub_le (dist x y) (dist (F.toFun x) (F.toFun y)) ‖π x - π y‖
    rw [abs_sub_comm (dist x y) (dist (F.toFun x) (F.toFun y))] at h6
    linarith
  have hH : ∀ x ∈ ball p 6, 0 ≤ π x 1 := fun x _ => (G.toFun (F.toFun x).snd).2.1
  have hp0 : ‖π p‖ ≤ 1 / 20 := by
    have hFp : F.toFun p = WithLp.toLp 2 ((0 : ℝ), q) := F.basepoint
    have hGq : G.toFun q = ⟨0, le_rfl, hC⟩ := G.basepoint
    have : π p = 0 := by
      ext i
      fin_cases i <;> simp [π, hFp, hGq]
    rw [this, norm_zero]
    norm_num
  exact not_splitting_ge_two_at_halfplane_boundary_of_norm_le_SMR hβ (by linarith) π hπ hH hp0
    (n := 2) le_rfl q' ⟨f⟩

end GC.MetricGeometry
