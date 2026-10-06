import DifferentialGeometry.Geometry.Collapse.MetricRank.PlanarFourPoints
import DifferentialGeometry.Geometry.Collapse.MetricRank.KLVertexImages

/-!
# Planar four-point exclusion at the KL level (review 75, section C.3, S-X144 group G5)

`not_splitting_ge_three_of_planar_ball_SMR`: if `B(p, 6)` admits an `ε_m`-additive-distortion map
`π` into `ℝ²` (`ε_m ≤ 1/100`), then for `β ≤ 3/20`, every `n ≥ 3` and every metric factor `Y` there
is no Kleiner-Lott `β`-approximation from `(X, p)` to `ℝⁿ ×₂ Y` at `(0, q)`. The regular tetrahedron
of side `5` centred at the origin of a `3`-plane of `ℝⁿ` has vertex norm `5 √6 / 4 < 4 ≤ 5`;
its four KL witnesses lie in `B(p, 6)`, their `π`-images are four points of `ℝ²` with all six
distances in `[5 - e, 5 + e]`, `e = 5 β + ε_m ≤ 19/25`, impossible by
`not_four_points_plane_five_SMR` (`(5 + e) / (5 - e) ≤ 144/106 < √2`). The rank-three form is
`n = 3` (at `β₃`). So `β₃ = 3/20` does not obstruct this route.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

/-- **C.3: the planar four-point exclusion** (KL form). -/
theorem not_splitting_ge_three_of_planar_ball_SMR {X : Type*} [MetricSpace X] {p : X}
    {β εm : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm)
    {n : ℕ} (hn : 3 ≤ n) {Y : Type*} [MetricSpace Y] (q : Y) :
    ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β) := by
  rintro ⟨f⟩
  obtain ⟨w, hw0, hwd⟩ := exists_regular_tetrahedron_SMR hn (Real.sqrt (25 / 8))
  have hr : Real.sqrt (25 / 8) ^ 2 = 25 / 8 := Real.sq_sqrt (by norm_num)
  have hnorm : ∀ i, ‖w i‖ ≤ 5 := fun i => by
    have := hw0 i
    nlinarith [norm_nonneg (w i)]
  have hside : ∀ i j, i ≠ j → ‖w i - w j‖ = 5 := fun i j hij => by
    have := hwd i j hij
    nlinarith [norm_nonneg (w i - w j)]
  obtain ⟨z, hz, -⟩ := exists_images_of_vertices_SMR hβ f π
    (fun x hx y hy => by rw [dist_eq_norm]; exact hπ x hx y hy) w hnorm
  refine not_four_points_plane_five_SMR (e := 19 / 25) le_rfl z (fun i j hij => ?_)
  have h := hz i j
  rw [hside i j hij, abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-- **C.3, `HasEuclideanSplitting` form** for every `n ≥ 3`. -/
theorem not_hasEuclideanSplitting_ge_three_of_planar_ball_SMR {X : Type u} [MetricSpace X]
    {p : X} {β εm : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100)
    (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm)
    {n : ℕ} (hn : 3 ≤ n) : ¬ HasEuclideanSplitting.{u, v} p n β := by
  rintro ⟨Y, mY, q, hne⟩
  exact not_splitting_ge_three_of_planar_ball_SMR hβ hεm π hπ hn q hne

/-- **The rank-three form of C.3** (`n = 3`, at the tolerance `β₃ = 3/20` or smaller). -/
theorem not_three_of_planar_ball_SMR {X : Type u} [MetricSpace X] {p : X} {β₃ εm : ℝ}
    (hβ : β₃ ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm) :
    ¬ HasEuclideanSplitting.{u, v} p 3 β₃ :=
  not_hasEuclideanSplitting_ge_three_of_planar_ball_SMR hβ hεm π hπ le_rfl

/-- **Consumer (explicit numbers, `ℝ²`).** The Euclidean plane at the origin (`π = id`,
`ε_m = 0`) has no Euclidean splitting of rank three at the tolerance `3/20`. -/
theorem euclidean_plane_not_splitting_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0} (0 : EuclideanSpace ℝ (Fin 2)) 3 (3 / 20) :=
  not_three_of_planar_ball_SMR (εm := 0) le_rfl (by norm_num) id
    (fun x _ y _ => by simp [dist_eq_norm])

/-- **Consumer (explicit numbers, `ℝ²`).** The same plane has no splitting of any rank `n ≥ 3`,
for example `n = 7` at `1/10`. -/
theorem euclidean_plane_not_splitting_seven_SMR :
    ¬ HasEuclideanSplitting.{0, 0} (0 : EuclideanSpace ℝ (Fin 2)) 7 (1 / 10) :=
  not_hasEuclideanSplitting_ge_three_of_planar_ball_SMR (εm := 0) (by norm_num) (by norm_num) id
    (fun x _ y _ => by simp [dist_eq_norm]) (by norm_num)

end GC.MetricGeometry
