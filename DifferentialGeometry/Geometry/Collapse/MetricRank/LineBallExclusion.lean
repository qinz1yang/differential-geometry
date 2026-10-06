import DifferentialGeometry.Geometry.Collapse.MetricRank.LineThreePoints
import DifferentialGeometry.Geometry.Collapse.MetricRank.KLVertexImages

/-!
# Line three-point exclusion at the KL level (review 75, section C.4, S-X144 group G1)

`not_splitting_ge_two_of_line_ball_SMR`: if a ball `B(p, 6)` of a metric space `X` admits an
`ε_m`-additive-distortion map `π` into `ℝ` (`ε_m ≤ 1/100`), then for `β ≤ 3/20`, every `n ≥ 2` and
every metric factor `Y` there is no Kleiner-Lott `β`-approximation from `(X, p)` to
`ℝⁿ ×₂ Y` at `(0, q)`. The equilateral triangle of side `5` in a plane of `ℝⁿ` (vertex norm
`5/√3 < 3`) gives three witnesses with `π`-images at pairwise distance in `[5 - e, 5 + e]`,
`e = 5 β + ε_m ≤ 19/25`, impossible on a line since `5 + e < 2 (5 - e)`.
The two forms needed to exclude rank two and rank three are the cases `n = 2` (at `β₂`) and
`n = 3` (at `β₃`), stated through `HasEuclideanSplitting`; no rank adapter is stated here.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

/-- **C.4: the line exclusion** (KL form). -/
theorem not_splitting_ge_two_of_line_ball_SMR {X : Type*} [MetricSpace X] {p : X} {β εm : ℝ}
    (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → ℝ)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - |π x - π y|)| ≤ εm)
    {n : ℕ} (hn : 2 ≤ n) {Y : Type*} [MetricSpace Y] (q : Y) :
    ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β) := by
  rintro ⟨f⟩
  obtain ⟨w, hw0, hwd⟩ := exists_regular_triangle_SMR hn (Real.sqrt (25 / 3))
  have hr : Real.sqrt (25 / 3) ^ 2 = 25 / 3 := Real.sq_sqrt (by norm_num)
  have hnorm : ∀ i, ‖w i‖ ≤ 5 := fun i => by
    have := hw0 i
    nlinarith [norm_nonneg (w i)]
  have hside : ∀ i j, i ≠ j → ‖w i - w j‖ = 5 := fun i j hij => by
    have := hwd i j hij
    nlinarith [norm_nonneg (w i - w j)]
  obtain ⟨z, hz, -⟩ := exists_images_of_vertices_SMR hβ f π
    (fun x hx y hy => by rw [Real.dist_eq]; exact hπ x hx y hy) w hnorm
  refine not_three_points_on_line_family_SMR (s := 5) (e := 19 / 25)
    (five_add_lt_two_mul_five_sub_SMR le_rfl) z (fun i j hij => ?_)
  have h := hz i j
  rw [hside i j hij, abs_lt] at h
  rw [← Real.dist_eq]
  constructor <;> linarith [h.1, h.2]

/-- **C.4, `HasEuclideanSplitting` form** for every `n ≥ 2`. -/
theorem not_hasEuclideanSplitting_ge_two_of_line_ball_SMR {X : Type u} [MetricSpace X] {p : X}
    {β εm : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → ℝ)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - |π x - π y|)| ≤ εm)
    {n : ℕ} (hn : 2 ≤ n) : ¬ HasEuclideanSplitting.{u, v} p n β := by
  rintro ⟨Y, mY, q, hne⟩
  exact not_splitting_ge_two_of_line_ball_SMR hβ hεm π hπ hn q hne

/-- **The rank-two form of C.4** (`n = 2`, at the tolerance `β₂`). -/
theorem not_two_of_line_ball_SMR {X : Type u} [MetricSpace X] {p : X} {β₂ εm : ℝ}
    (hβ : β₂ ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → ℝ)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - |π x - π y|)| ≤ εm) :
    ¬ HasEuclideanSplitting.{u, v} p 2 β₂ :=
  not_hasEuclideanSplitting_ge_two_of_line_ball_SMR hβ hεm π hπ le_rfl

/-- **The rank-three form of C.4** (`n = 3`, at the tolerance `β₃`). -/
theorem not_three_of_line_ball_SMR {X : Type u} [MetricSpace X] {p : X} {β₃ εm : ℝ}
    (hβ : β₃ ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → ℝ)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - |π x - π y|)| ≤ εm) :
    ¬ HasEuclideanSplitting.{u, v} p 3 β₃ :=
  not_hasEuclideanSplitting_ge_two_of_line_ball_SMR hβ hεm π hπ (by norm_num)

/-- **Consumer (explicit numbers, `ℝ`).** The real line at `0` with `π = id` and `ε_m = 0`
satisfies the hypotheses, so it has no Euclidean splitting of rank two at `3/20`. -/
theorem real_line_not_splitting_two_SMR : ¬ HasEuclideanSplitting.{0, 0} (0 : ℝ) 2 (3 / 20) :=
  not_two_of_line_ball_SMR (εm := 0) le_rfl (by norm_num) id
    (fun x _ y _ => by simp [Real.dist_eq])

/-- **Consumer (explicit numbers, `ℝ`).** Likewise no Euclidean splitting of rank three. -/
theorem real_line_not_splitting_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0} (0 : ℝ) 3 (3 / 20) :=
  not_three_of_line_ball_SMR (εm := 0) le_rfl (by norm_num) id
    (fun x _ y _ => by simp [Real.dist_eq])

end GC.MetricGeometry
