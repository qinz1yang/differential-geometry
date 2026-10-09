import DifferentialGeometry.Geometry.Collapse.MetricRank.KLWitnessError
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

/-!
# Vertex configurations and their KL images (review 75, section C.3-C.5, S-X144)

Shared supplier of the binding lemmas of the rank-exactness exclusions.

* `exists_regular_triangle_SMR` (`n ≥ 2`): three vectors of `ℝⁿ` of norm `r` and mutual distance
  `√3 r` (squared forms: `‖v i‖² = r²`, `‖v i - v j‖² = 3 r²`). With `r² = 25/3` this is the
  equilateral triangle of side `5` (C.4); with `r = 5` the three vectors of norm `5` at `120°`
  (C.5).
* `exists_regular_tetrahedron_SMR` (`n ≥ 3`): the vertices `(±a, ±a, ±a)` with an even number of
  minus signs: `‖v i‖² = 3 a²`, `‖v i - v j‖² = 8 a²` (C.3: `a² = 25/8` gives side `5`).
* `exists_images_of_vertices_SMR`: for `f : KleinerLottApprox p (0, q) β` with `β ≤ 3/20` and
  an additive distortion map `π : X → W` on `B(p, 6)`, vertices of norm `≤ 5` have images
  `z i = π (x i)` with `|d(z i, z j) - ‖v i - v j‖| < 5 β + ε_m` and
  `d(z i, π p) < ‖v i‖ + 3 β + ε_m` (C.2 plus the distortion of `π`).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

section Frames

variable {n : ℕ}

theorem exists_orthonormal_two_SMR (hn : 2 ≤ n) :
    ∃ u₀ u₁ : EuclideanSpace ℝ (Fin n), ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧ inner ℝ u₀ u₁ = 0 := by
  refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, EuclideanSpace.single ⟨1, by omega⟩ 1,
    by simp, by simp, ?_⟩
  simp [EuclideanSpace.inner_single_left]

theorem exists_orthonormal_three_SMR (hn : 3 ≤ n) :
    ∃ u₀ u₁ u₂ : EuclideanSpace ℝ (Fin n), ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧ ‖u₂‖ = 1 ∧
      inner ℝ u₀ u₁ = 0 ∧ inner ℝ u₀ u₂ = 0 ∧ inner ℝ u₁ u₂ = 0 := by
  refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, EuclideanSpace.single ⟨1, by omega⟩ 1,
    EuclideanSpace.single ⟨2, by omega⟩ 1, by simp, by simp, by simp, ?_, ?_, ?_⟩ <;>
    simp [EuclideanSpace.inner_single_left]

theorem norm_sq_comb2_SMR {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u₀ u₁ : V}
    (h₀ : ‖u₀‖ = 1) (h₁ : ‖u₁‖ = 1) (h₀₁ : inner ℝ u₀ u₁ = 0) (a b : ℝ) :
    ‖a • u₀ + b • u₁‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, h₀, h₁, h₀₁, real_inner_comm u₀ u₁]
  simp only [RCLike.conj_to_real]
  ring

theorem norm_sq_comb3_SMR {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u₀ u₁ u₂ : V} (h₀ : ‖u₀‖ = 1) (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1)
    (h₀₁ : inner ℝ u₀ u₁ = 0) (h₀₂ : inner ℝ u₀ u₂ = 0) (h₁₂ : inner ℝ u₁ u₂ = 0) (a b c : ℝ) :
    ‖a • u₀ + b • u₁ + c • u₂‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, h₀, h₁, h₂, h₀₁, h₀₂, h₁₂, real_inner_comm u₀ u₁,
    real_inner_comm u₀ u₂, real_inner_comm u₁ u₂]
  simp only [RCLike.conj_to_real]
  ring

/-- Named form of `exists_regular_triangle_SMR`. -/
theorem exists_regular_triangle_named_SMR (hn : 2 ≤ n) (r : ℝ) :
    ∃ a b c : EuclideanSpace ℝ (Fin n), ‖a‖ ^ 2 = r ^ 2 ∧ ‖b‖ ^ 2 = r ^ 2 ∧ ‖c‖ ^ 2 = r ^ 2 ∧
      ‖a - b‖ ^ 2 = 3 * r ^ 2 ∧ ‖a - c‖ ^ 2 = 3 * r ^ 2 ∧ ‖b - c‖ ^ 2 = 3 * r ^ 2 := by
  obtain ⟨u₀, u₁, h₀, h₁, h₀₁⟩ := exists_orthonormal_two_SMR hn
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key := norm_sq_comb2_SMR h₀ h₁ h₀₁
  have hsub : ∀ a b a' b' : ℝ, a • u₀ + b • u₁ - (a' • u₀ + b' • u₁) =
      (a - a') • u₀ + (b - b') • u₁ := fun a b a' b' => by module
  refine ⟨r • u₀ + (0 : ℝ) • u₁, (-r / 2) • u₀ + (Real.sqrt 3 * r / 2) • u₁,
    (-r / 2) • u₀ + (-(Real.sqrt 3 * r) / 2) • u₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key]; ring
  · rw [key]; nlinarith [hs]
  · rw [key]; nlinarith [hs]
  · rw [hsub, key]; nlinarith [hs]
  · rw [hsub, key]; nlinarith [hs]
  · rw [hsub, key]; nlinarith [hs]

/-- Three vectors of norm `r` with pairwise squared distance `3 r²` (a regular triangle centred at
the origin, in a plane of `ℝⁿ`, `n ≥ 2`). -/
theorem exists_regular_triangle_SMR (hn : 2 ≤ n) (r : ℝ) :
    ∃ v : Fin 3 → EuclideanSpace ℝ (Fin n), (∀ i, ‖v i‖ ^ 2 = r ^ 2) ∧
      ∀ i j, i ≠ j → ‖v i - v j‖ ^ 2 = 3 * r ^ 2 := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := exists_regular_triangle_named_SMR hn r
  refine ⟨![a, b, c], fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using hab
    · simpa using hac
    · rw [norm_sub_rev]; simpa using hab
    · exact absurd rfl hij
    · simpa using hbc
    · rw [norm_sub_rev]; simpa using hac
    · rw [norm_sub_rev]; simpa using hbc
    · exact absurd rfl hij

/-- Named form of `exists_regular_tetrahedron_SMR`. -/
theorem exists_regular_tetrahedron_named_SMR (hn : 3 ≤ n) (t : ℝ) :
    ∃ a b c d : EuclideanSpace ℝ (Fin n), ‖a‖ ^ 2 = 3 * t ^ 2 ∧ ‖b‖ ^ 2 = 3 * t ^ 2 ∧
      ‖c‖ ^ 2 = 3 * t ^ 2 ∧ ‖d‖ ^ 2 = 3 * t ^ 2 ∧ ‖a - b‖ ^ 2 = 8 * t ^ 2 ∧
      ‖a - c‖ ^ 2 = 8 * t ^ 2 ∧ ‖a - d‖ ^ 2 = 8 * t ^ 2 ∧ ‖b - c‖ ^ 2 = 8 * t ^ 2 ∧
      ‖b - d‖ ^ 2 = 8 * t ^ 2 ∧ ‖c - d‖ ^ 2 = 8 * t ^ 2 := by
  obtain ⟨u₀, u₁, u₂, h₀, h₁, h₂, h₀₁, h₀₂, h₁₂⟩ := exists_orthonormal_three_SMR hn
  have key := norm_sq_comb3_SMR h₀ h₁ h₂ h₀₁ h₀₂ h₁₂
  have hsub : ∀ a b c a' b' c' : ℝ,
      a • u₀ + b • u₁ + c • u₂ - (a' • u₀ + b' • u₁ + c' • u₂) =
        (a - a') • u₀ + (b - b') • u₁ + (c - c') • u₂ := fun a b c a' b' c' => by module
  refine ⟨t • u₀ + t • u₁ + t • u₂, t • u₀ + (-t) • u₁ + (-t) • u₂,
    (-t) • u₀ + t • u₁ + (-t) • u₂, (-t) • u₀ + (-t) • u₁ + t • u₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (rw [key]; ring) | (rw [hsub, key]; ring)

/-- Four vectors of squared norm `3 t²` with pairwise squared distance `8 t²`: the regular
tetrahedron with vertices `(±t, ±t, ±t)` in a `3`-plane of `ℝⁿ`, `n ≥ 3`. -/
theorem exists_regular_tetrahedron_SMR (hn : 3 ≤ n) (t : ℝ) :
    ∃ v : Fin 4 → EuclideanSpace ℝ (Fin n), (∀ i, ‖v i‖ ^ 2 = 3 * t ^ 2) ∧
      ∀ i j, i ≠ j → ‖v i - v j‖ ^ 2 = 8 * t ^ 2 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_regular_tetrahedron_named_SMR hn t
  refine ⟨![a, b, c, d], fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
    · simpa using hd
  · fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | simpa using hab | simpa using hac | simpa using had | simpa using hbc
      | simpa using hbd | simpa using hcd
      | (rw [norm_sub_rev]; simpa using hab) | (rw [norm_sub_rev]; simpa using hac)
      | (rw [norm_sub_rev]; simpa using had) | (rw [norm_sub_rev]; simpa using hbc)
      | (rw [norm_sub_rev]; simpa using hbd) | (rw [norm_sub_rev]; simpa using hcd)

end Frames

section Images

variable {X : Type*} [MetricSpace X]

/-- **Images of vertices under a KL approximation and an additive distortion map.** -/
theorem exists_images_of_vertices_SMR {W Y : Type*} [MetricSpace W] [MetricSpace Y] {n : ℕ}
    {p : X} {q : Y} {β εm : ℝ} (hβ : β ≤ 3 / 20)
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β)
    (π : X → W)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |dist x y - dist (π x) (π y)| ≤ εm)
    {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin n)) (hv : ∀ i, ‖v i‖ ≤ 5) :
    ∃ z : ι → W, (∀ i j, |dist (z i) (z j) - ‖v i - v j‖| < 5 * β + εm) ∧
      (∀ i, dist (z i) (π p) < ‖v i‖ + 3 * β + εm) := by
  have hβ0 := f.error_pos
  have hinv : (3 / 20 : ℝ)⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 hβ
  norm_num at hinv
  have hdist : ∀ i j, dist (WithLp.toLp 2 (v i, q)) (WithLp.toLp 2 (v j, q)) = ‖v i - v j‖ := by
    intro i j
    exact ((WithLp.isometry_prodMk_right q).dist_eq (v i) (v j)).trans (dist_eq_norm _ _)
  have hzero : ∀ i, dist (WithLp.toLp 2 (v i, q))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) = ‖v i‖ := by
    intro i
    exact ((WithLp.isometry_prodMk_right q).dist_eq (v i) 0).trans (dist_zero_right _)
  obtain ⟨x, hx, -, hpair, hrad⟩ := f.kl_witness_error_SMR
    (fun i => (WithLp.toLp 2 (v i, q) : WithLp 2 (EuclideanSpace ℝ (Fin n) × Y))) (fun i => by
      rw [hzero]
      linarith [hv i])
  have hxb : ∀ i, x i ∈ Metric.ball p 6 := fun i => by
    have h := hrad i
    simp only [hzero] at h
    rw [Metric.mem_ball]
    linarith [hv i]
  refine ⟨fun i => π (x i), fun i j => ?_, fun i => ?_⟩
  · have h1 := hpair i j
    simp only [hdist] at h1
    have h2 := hπ (x i) (hxb i) (x j) (hxb j)
    rw [abs_lt] at h1 ⊢
    rw [abs_le] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h1 := hrad i
    simp only [hzero] at h1
    have h2 := hπ (x i) (hxb i) p (Metric.mem_ball_self (by norm_num))
    rw [abs_le] at h2
    linarith [h2.1, h2.2]

end Images

end GC.MetricGeometry
