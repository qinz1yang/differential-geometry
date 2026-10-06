import DifferentialGeometry.Geometry.Collapse.MetricRank.HalfPlaneObstruction

/-!
# The pointed half-plane obstruction at the KL level (review 75, section C.5, S-X144 group G4)

`not_splitting_ge_two_at_halfplane_boundary_SMR`: if `π : B(p, 6) → H` (the closed upper half
plane of `ℝ²`) has additive distortion `ε_m ≤ 1/100` and sends the base point to `(0, h)`,
`0 ≤ h ≤ 1/20`, then for `β ≤ 3/20`, every `n ≥ 2` and every metric factor `Y` there is no
Kleiner-Lott `β`-approximation from `(X, p)` to `ℝⁿ ×₂ Y` at `(0, q)`. The pointedness enters only
through `‖π p‖ ≤ 1/20` (`..._of_norm_le_SMR`, the strengthening).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

/-- Images of vertices as in `exists_images_of_vertices_SMR`, together with the information that
each image is the `π`-image of a point of `B(p, 6)` (needed for a constraint such as "`π` takes
values in a half plane"). -/
theorem exists_images_with_sources_SMR {X : Type*} [MetricSpace X] {W Y : Type*} [MetricSpace W]
    [MetricSpace Y] {n : ℕ} {p : X} {q : Y} {β εm : ℝ} (hβ : β ≤ 3 / 20)
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β)
    (π : X → W)
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |dist x y - dist (π x) (π y)| ≤ εm)
    {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin n)) (hv : ∀ i, ‖v i‖ ≤ 5) :
    ∃ z : ι → W, (∀ i, ∃ x ∈ Metric.ball p 6, z i = π x) ∧
      (∀ i j, |dist (z i) (z j) - ‖v i - v j‖| < 5 * β + εm) ∧
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
  refine ⟨fun i => π (x i), fun i => ⟨x i, hxb i, rfl⟩, fun i j => ?_, fun i => ?_⟩
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

/-- **C.5 (strengthened): the pointed half-plane obstruction**, with the pointedness used only
as `‖π p‖ ≤ 1/20`. -/
theorem not_splitting_ge_two_at_halfplane_boundary_of_norm_le_SMR {X : Type*} [MetricSpace X]
    {p : X} {β εm : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100)
    (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm)
    (hH : ∀ x ∈ Metric.ball p 6, 0 ≤ π x 1) (hp : ‖π p‖ ≤ 1 / 20)
    {n : ℕ} (hn : 2 ≤ n) {Y : Type*} [MetricSpace Y] (q : Y) :
    ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β) := by
  rintro ⟨f⟩
  obtain ⟨w, hw0, hwd⟩ := exists_regular_triangle_SMR hn 5
  have hnorm : ∀ i, ‖w i‖ ≤ 5 := fun i => by
    have := hw0 i
    nlinarith [norm_nonneg (w i)]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hside : ∀ i j, i ≠ j → ‖w i - w j‖ = 5 * Real.sqrt 3 := fun i j hij => by
    refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hwd i j hij]
    nlinarith
  obtain ⟨z, hsrc, hz, hzp⟩ := exists_images_with_sources_SMR hβ f π
    (fun x hx y hy => by rw [dist_eq_norm]; exact hπ x hx y hy) w hnorm
  refine not_three_in_halfplane_551_SMR z (fun i => ?_) (fun i => ?_) (fun i j hij => ?_)
  · obtain ⟨x, hx, hzx⟩ := hsrc i
    rw [hzx]
    exact hH x hx
  · have h := hzp i
    rw [dist_eq_norm] at h
    have hw := hnorm i
    calc ‖z i‖ = ‖(z i - π p) + π p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z i - π p‖ + ‖π p‖ := norm_add_le _ _
      _ ≤ 551 / 100 := by linarith
  · have h := hz i j
    rw [dist_eq_norm, hside i j hij, abs_lt] at h
    linarith [h.1, h.2]

/-- **C.5, verbatim form**: `π p = (0, h)` with `0 ≤ h ≤ 1/20` (coordinates `π p 0 = 0`,
`π p 1 = h`). -/
theorem not_splitting_ge_two_at_halfplane_boundary_SMR {X : Type*} [MetricSpace X] {p : X}
    {β εm h : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm)
    (hH : ∀ x ∈ Metric.ball p 6, 0 ≤ π x 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (hp0 : π p 0 = 0) (hp1 : π p 1 = h)
    {n : ℕ} (hn : 2 ≤ n) {Y : Type*} [MetricSpace Y] (q : Y) :
    ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), q)) β) := by
  refine not_splitting_ge_two_at_halfplane_boundary_of_norm_le_SMR hβ hεm π hπ hH ?_ hn q
  have hsq := norm_sq_fin_two_SMR (π p)
  rw [hp0, hp1] at hsq
  nlinarith [norm_nonneg (π p)]

/-- **C.5, `HasEuclideanSplitting` form** for every `n ≥ 2` (rank two and rank three alike). -/
theorem not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR {X : Type u} [MetricSpace X]
    {p : X} {β εm h : ℝ} (hβ : β ≤ 3 / 20) (hεm : εm ≤ 1 / 100)
    (π : X → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ εm)
    (hH : ∀ x ∈ Metric.ball p 6, 0 ≤ π x 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (hp0 : π p 0 = 0) (hp1 : π p 1 = h) {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasEuclideanSplitting.{u, v} p n β := by
  rintro ⟨Y, mY, q, hne⟩
  exact not_splitting_ge_two_at_halfplane_boundary_SMR hβ hεm π hπ hH hh0 hh1 hp0 hp1 hn q hne

/-- **Consumer (explicit numbers, half plane).** In the closed upper half plane
`H = {v : ℝ² | 0 ≤ v₁}` the point `(0, 1/50)` (at distance `1/50 ≤ 1/20` from the boundary) has
no Euclidean splitting of rank two at the tolerance `3/20` (`π = id`, `ε_m = 0`). -/
theorem halfplane_boundary_point_not_splitting_two_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩ :
        {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}) 2 (3 / 20) := by
  refine not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR (εm := 0) (h := 1 / 50)
    le_rfl (by norm_num) (fun x => x.1) (fun x _ y _ => ?_) (fun x _ => x.2) (by norm_num)
    (by norm_num) (by simp) (by simp) le_rfl
  rw [Subtype.dist_eq, dist_eq_norm]
  simp

/-- **Consumer (explicit numbers).** The same point has no Euclidean splitting of rank three. -/
theorem halfplane_boundary_point_not_splitting_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩ :
        {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}) 3 (3 / 20) := by
  refine not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR (εm := 0) (h := 1 / 50)
    le_rfl (by norm_num) (fun x => x.1) (fun x _ y _ => ?_) (fun x _ => x.2) (by norm_num)
    (by norm_num) (by simp) (by simp) (by norm_num)
  rw [Subtype.dist_eq, dist_eq_norm]
  simp

end GC.MetricGeometry
