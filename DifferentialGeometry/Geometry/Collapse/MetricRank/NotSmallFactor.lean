import DifferentialGeometry.Geometry.Collapse.MetricRank.LineThreePoints
import DifferentialGeometry.Geometry.Collapse.MetricRank.KLVertexImages

/-!
# Non-slim exclusion by three far-apart points (review 75, section C.6, S-X144 group G3)

`not_small_factor_of_three_points_SMR`: if three points of `B(p, β⁻¹)` are at mutual distance
`s ± κ` with `s > 3 (D + β + κ)`, there is no bounded metric factor `Z` of diameter `< D` and no
Kleiner-Lott `β`-approximation from `(X, p)` to `ℝ ×₂ Z`. The negation is stated in the explicit
form of `EdgeFamily.covers_nonslim` (an existential over `Z`, its metric, a point, boundedness,
the diameter bound and a KL approximation into `WithLp 2 (ℝ × Z)`), without any new named
proposition. Projecting the three images to `ℝ` leaves three reals with mutual distances in
`[s - e, s + e]`, `e = D + β + κ`, which the line lemma `not_three_points_on_line_SMR` excludes.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe w

/-- **C.6: three far-apart points exclude every small factor.** -/
theorem not_small_factor_of_three_points_SMR {X : Type*} [MetricSpace X] {p : X} {β D κ s : ℝ}
    (x : Fin 3 → X) (hx : ∀ i, x i ∈ Metric.ball p β⁻¹)
    (hd : ∀ i j, i ≠ j → |dist (x i) (x j) - s| ≤ κ) (hs : 3 * (D + β + κ) < s) :
    ¬ ∃ (Z : Type w) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (Set.univ : Set Z) ∧ Metric.diam (Set.univ : Set Z) < D ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β) := by
  rintro ⟨Z, mZ, z, hb, hdiam, ⟨f⟩⟩
  have hD : 0 ≤ D := le_trans Metric.diam_nonneg hdiam.le
  have hβ := f.error_pos
  refine not_three_points_on_line_family_SMR (s := s) (e := D + β + κ) (by linarith)
    (fun i => (f.toFun (x i)).fst) (fun i j hij => ?_)
  have hdist := f.distortion (x i) (hx i) (x j) (hx j)
  have hxd := hd i j hij
  rw [abs_le] at hdist hxd
  have hsq := WithLp.prod_dist_sq_eq_add_sq (f.toFun (x i)) (f.toFun (x j))
  have hzz : dist (f.toFun (x i)).snd (f.toFun (x j)).snd < D :=
    lt_of_le_of_lt (Metric.dist_le_diam_of_mem hb (Set.mem_univ _) (Set.mem_univ _)) hdiam
  have ha := dist_nonneg (x := (f.toFun (x i)).fst) (y := (f.toFun (x j)).fst)
  have hb0 := dist_nonneg (x := (f.toFun (x i)).snd) (y := (f.toFun (x j)).snd)
  have hD0 := dist_nonneg (x := f.toFun (x i)) (y := f.toFun (x j))
  rw [Real.dist_eq] at ha hsq
  have hle : |(f.toFun (x i)).fst - (f.toFun (x j)).fst| ≤
      dist (f.toFun (x i)) (f.toFun (x j)) := by
    nlinarith
  have hge : dist (f.toFun (x i)) (f.toFun (x j)) ≤
      |(f.toFun (x i)).fst - (f.toFun (x j)).fst| +
        dist (f.toFun (x i)).snd (f.toFun (x j)).snd := by
    nlinarith [mul_nonneg ha hb0]
  constructor <;> linarith [hdist.1, hdist.2, hxd.1, hxd.2]

/-- **The edge numbers of C.6**: `D = 1000 Δ`, `s = 4 (D + 1)`, `κ ≤ 1`, `1 ≤ Δ`. -/
theorem not_small_factor_of_edge_numbers_SMR {X : Type*} [MetricSpace X] {p : X} {β Δ κ : ℝ}
    (hΔ : 1 ≤ Δ) (hκ : κ ≤ 1) (x : Fin 3 → X) (hx : ∀ i, x i ∈ Metric.ball p β⁻¹)
    (hd : ∀ i j, i ≠ j → |dist (x i) (x j) - 4 * (1000 * Δ + 1)| ≤ κ) :
    ¬ ∃ (Z : Type w) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (Set.univ : Set Z) ∧ Metric.diam (Set.univ : Set Z) < 1000 * Δ ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β) := by
  rintro ⟨Z, mZ, z, hb, hdiam, hf⟩
  have hβ1 := hf.some.error_lt_one
  exact not_small_factor_of_three_points_SMR x hx hd (by linarith) ⟨Z, mZ, z, hb, hdiam, hf⟩

/-- **Consumer (explicit numbers, `ℝ²`).** The Euclidean plane at the origin has no
`3/20`-Kleiner-Lott approximation to `ℝ ×₂ Z` with `Z` of diameter `< 1`: an equilateral triangle
of side `5` (vertex norm `5/√3 < 20/3 = (3/20)⁻¹`) has `s = 5 > 3 (1 + 3/20 + 0)`. -/
theorem euclidean_plane_no_small_factor_SMR :
    ¬ ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (Set.univ : Set Z) ∧ Metric.diam (Set.univ : Set Z) < 1 ∧
      Nonempty (KleinerLottApprox (0 : EuclideanSpace ℝ (Fin 2))
        (WithLp.toLp 2 ((0 : ℝ), z)) (3 / 20)) := by
  obtain ⟨w, hw0, hwd⟩ := exists_regular_triangle_SMR (n := 2) le_rfl (Real.sqrt (25 / 3))
  have hr : Real.sqrt (25 / 3) ^ 2 = 25 / 3 := Real.sq_sqrt (by norm_num)
  refine not_small_factor_of_three_points_SMR (D := 1) (κ := 0) (s := 5) w (fun i => ?_)
    (fun i j hij => ?_) (by norm_num)
  · have h := hw0 i
    rw [Metric.mem_ball, dist_zero_right]
    norm_num
    nlinarith [norm_nonneg (w i)]
  · have h := hwd i j hij
    rw [dist_eq_norm]
    have : ‖w i - w j‖ = 5 := by nlinarith [norm_nonneg (w i - w j)]
    rw [this]
    norm_num

end GC.MetricGeometry
