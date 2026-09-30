import DifferentialGeometry.Analysis.Convex.Affine
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

noncomputable def lineCoordinate (γ : ℝ → X) (x : X) : ℝ :=
  (dist x (γ 0) ^ 2 + 1 - dist x (γ 1) ^ 2) / 2

theorem concaveOn_sq_dist_sub_sq_of_isometry
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) :
    ConcaveOn ℝ univ (fun t => dist x (γ t) ^ 2 - t ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro u hu v hv a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : a = 1 - b := by linarith
  subst a
  have hd₁ : dist (γ u) (γ ((1 - b) * u + b * v)) = b * dist (γ u) (γ v) := by
    simp only [hγ.dist_eq, Real.dist_eq]
    rw [show u - ((1 - b) * u + b * v) = b * (u - v) by ring,
      abs_mul, abs_of_nonneg hb]
  have hd₂ : dist (γ ((1 - b) * u + b * v)) (γ v) = (1 - b) * dist (γ u) (γ v) := by
    simp only [hγ.dist_eq, Real.dist_eq]
    rw [show (1 - b) * u + b * v - v = (1 - b) * (u - v) by ring,
      abs_mul, abs_of_nonneg ha]
  have h := quadratic_side_comparison_of_fourPointComparison hs
    (mem_univ (γ u)) (mem_univ (γ v)) (mem_univ (γ ((1 - b) * u + b * v)))
    (mem_univ x) ⟨hb, hb1⟩ hd₁ hd₂
  rw [hγ.dist_eq, Real.dist_eq, sq_abs] at h
  simp only [smul_eq_mul]
  nlinarith

theorem sq_dist_isometry_line
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) (t : ℝ) :
    dist x (γ t) ^ 2 = t ^ 2 - 2 * t * lineCoordinate γ x + dist x (γ 0) ^ 2 := by
  have hn (u : ℝ) : 0 ≤ (dist x (γ u) ^ 2 - u ^ 2) +
      (dist x (γ (-u)) ^ 2 - (-u) ^ 2) := by
    have htri := dist_triangle (γ u) x (γ (-u))
    rw [hγ.dist_eq, Real.dist_eq, dist_comm (γ u) x] at htri
    have harg : |u - -u| = 2 * |u| := by
      rw [show u - -u = 2 * u by ring, abs_mul]
      norm_num
    rw [harg] at htri
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2 * |u|) htri
    nlinarith [sq_nonneg (dist x (γ u) - dist x (γ (-u))), sq_abs u]
  have h := (concaveOn_sq_dist_sub_sq_of_isometry hs hγ x).eq_affine_of_add_neg_nonneg hn t
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, one_pow] at h
  dsimp [lineCoordinate]
  linarith

theorem sq_dist_isometry_line_projection
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) (t : ℝ) :
    dist x (γ t) ^ 2 = (t - lineCoordinate γ x) ^ 2 +
      dist x (γ (lineCoordinate γ x)) ^ 2 := by
  have ht := sq_dist_isometry_line hs hγ x t
  have hb := sq_dist_isometry_line hs hγ x (lineCoordinate γ x)
  nlinarith

theorem existsUnique_line_distance_parameters
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) :
    ∃! bh : ℝ × ℝ, 0 ≤ bh.2 ∧
      ∀ t : ℝ, dist x (γ t) ^ 2 = (t - bh.1) ^ 2 + bh.2 ^ 2 := by
  refine ⟨(lineCoordinate γ x, dist x (γ (lineCoordinate γ x))),
    ⟨dist_nonneg, sq_dist_isometry_line_projection hs hγ x⟩, ?_⟩
  rintro ⟨b, h⟩ ⟨hh, heq⟩
  have hzero := heq 0
  have hone := heq 1
  have hb : b = lineCoordinate γ x := by dsimp [lineCoordinate]; nlinarith
  apply Prod.ext hb
  have hheight := heq b
  have hd : 0 ≤ dist x (γ (lineCoordinate γ x)) := dist_nonneg
  rw [hb] at hheight
  nlinarith

theorem dist_line_projection_le
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) (t : ℝ) :
    dist x (γ (lineCoordinate γ x)) ≤ dist x (γ t) := by
  have h := sq_dist_isometry_line_projection hs hγ x t
  nlinarith [dist_nonneg (x := x) (y := γ t),
    dist_nonneg (x := x) (y := γ (lineCoordinate γ x)), sq_nonneg (t - lineCoordinate γ x)]

theorem dist_line_projection_eq_iff
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) (t : ℝ) :
    dist x (γ t) = dist x (γ (lineCoordinate γ x)) ↔ t = lineCoordinate γ x := by
  constructor
  · intro heq
    have h := sq_dist_isometry_line_projection hs hγ x t
    rw [heq] at h
    nlinarith [sq_nonneg (t - lineCoordinate γ x)]
  · rintro rfl
    rfl

theorem existsUnique_nearest_point_on_isometry_line
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) :
    ∃! y : X, y ∈ range γ ∧ ∀ z ∈ range γ, dist x y ≤ dist x z := by
  refine ⟨γ (lineCoordinate γ x), ⟨mem_range_self _, ?_⟩, ?_⟩
  · rintro z ⟨t, rfl⟩
    exact dist_line_projection_le hs hγ x t
  · rintro y ⟨⟨t, rfl⟩, hy⟩
    have h := le_antisymm (hy _ (mem_range_self _)) (dist_line_projection_le hs hγ x t)
    exact congrArg γ ((dist_line_projection_eq_iff hs hγ x t).mp h)

theorem lineCoordinate_apply_isometry {γ : ℝ → X} (hγ : Isometry γ) (t : ℝ) :
    lineCoordinate γ (γ t) = t := by
  unfold lineCoordinate
  simp only [hγ.dist_eq, Real.dist_eq, sq_abs]
  ring

theorem lineCoordinate_affine_of_dist
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
    {a b z : X} {u : ℝ} (hu : u ∈ Icc 0 1)
    (haz : dist a z = u * dist a b) (hzb : dist z b = (1 - u) * dist a b) :
    lineCoordinate γ z = (1 - u) * lineCoordinate γ a + u * lineCoordinate γ b := by
  let δ := lineCoordinate γ z - (1 - u) * lineCoordinate γ a - u * lineCoordinate γ b
  let C := dist z (γ 0) ^ 2 - (1 - u) * dist a (γ 0) ^ 2 -
    u * dist b (γ 0) ^ 2 + u * (1 - u) * dist a b ^ 2
  have hnonneg (t : ℝ) : 0 ≤ C - 2 * t * δ := by
    have h := quadratic_side_comparison_of_fourPointComparison hs
      (mem_univ a) (mem_univ b) (mem_univ z) (mem_univ (γ t)) hu haz hzb
    rw [dist_comm (γ t) a, dist_comm (γ t) b, dist_comm (γ t) z,
      sq_dist_isometry_line hs hγ a t, sq_dist_isometry_line hs hγ b t,
      sq_dist_isometry_line hs hγ z t] at h
    dsimp [C, δ]
    nlinarith
  have hδ : δ = 0 := by
    by_contra h
    have heq : 2 * ((C + 1) / (2 * δ)) * δ = C + 1 := by field_simp
    have hh := hnonneg ((C + 1) / (2 * δ))
    rw [heq] at hh
    linarith
  dsimp [δ] at hδ
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
