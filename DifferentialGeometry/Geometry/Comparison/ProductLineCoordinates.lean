import DifferentialGeometry.Geometry.Comparison.CrossingLineCoordinates
import DifferentialGeometry.Geometry.Comparison.AlignedEuclideanCoordinates

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X B : Type*} [MetricSpace X] [MetricSpace B] {k : ℕ}

theorem euclidean_coordinate_isometry_line
    (hs : fourPointComparison 0 (Set.univ : Set X))
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    {γ : ℝ → X} (hγ : Isometry γ) {b : B}
    (hbase : e (γ 0) = WithLp.toLp 2 (0, b)) (t : ℝ) :
    (e (γ t)).fst = t • (e (γ 1)).fst := by
  ext j
  let β : ℝ → X := fun s => e.symm (WithLp.toLp 2 (PiLp.single 2 j s, b))
  have hβ : Isometry β := e.symm.isometry.comp
    ((WithLp.isometry_prodMk_right b).comp (Isometry.of_dist_eq
      (fun s t => PiLp.dist_single_same 2 (fun _ : Fin k => ℝ) j s t)))
  have hβalign (s : ℝ) : e (β s) = WithLp.toLp 2 (PiLp.single 2 j s, b) :=
    e.apply_symm_apply _
  have hβbase : β 0 = γ 0 := by
    apply e.injective
    rw [hβalign, hbase, (PiLp.single_eq_zero_iff 2 j).mpr rfl]
  have hc := lineCoordinate_crossing_isometry hs hβ hγ hβbase t
  rw [lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry e hβalign,
    lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry e hβalign] at hc
  exact hc

theorem isometry_line_product_speed
    (hs : fourPointComparison 0 (Set.univ : Set X))
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    {γ : ℝ → X} (hγ : Isometry γ) {b : B}
    (hbase : e (γ 0) = WithLp.toLp 2 (0, b)) :
    ‖(e (γ 1)).fst‖ ^ 2 + dist b (e (γ 1)).snd ^ 2 = 1 ∧
      ∀ s t : ℝ, dist (e (γ s)).snd (e (γ t)).snd =
        dist b (e (γ 1)).snd * dist s t := by
  have hspeed := WithLp.prod_dist_sq_eq_add_sq (e (γ 0)) (e (γ 1))
  rw [e.dist_eq, hγ.dist_eq, hbase] at hspeed
  norm_num only [Real.dist_eq, zero_sub, abs_neg, abs_one, one_pow, WithLp.toLp_fst,
    WithLp.toLp_snd, dist_zero_left, norm_one] at hspeed
  refine ⟨hspeed.symm, fun s t => ?_⟩
  have hd := WithLp.prod_dist_sq_eq_add_sq (e (γ s)) (e (γ t))
  rw [e.dist_eq, hγ.dist_eq,
    euclidean_coordinate_isometry_line hs e hγ hbase s,
    euclidean_coordinate_isometry_line hs e hγ hbase t] at hd
  simp only [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs] at hd
  have heq : dist (e (γ s)).snd (e (γ t)).snd ^ 2 =
      (dist b (e (γ 1)).snd * dist s t) ^ 2 := by
    rw [Real.dist_eq]
    nlinarith [congrArg (fun z : ℝ => z * |s - t| ^ 2) hspeed]
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg dist_nonneg dist_nonneg)).mp heq

theorem isometry_line_eq_euclidean_smul_of_no_factor_line
    (hs : fourPointComparison 0 (Set.univ : Set X))
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    (hnoline : ¬ ∃ η : ℝ → B, Isometry η)
    {γ : ℝ → X} (hγ : Isometry γ) {b : B}
    (hbase : e (γ 0) = WithLp.toLp 2 (0, b)) :
    ‖(e (γ 1)).fst‖ = 1 ∧
      ∀ t : ℝ, e (γ t) = WithLp.toLp 2 (t • (e (γ 1)).fst, b) := by
  obtain ⟨hspeed, hdist⟩ := isometry_line_product_speed hs e hγ hbase
  have hzero : dist b (e (γ 1)).snd = 0 := by
    by_contra hne
    have hc : 0 < dist b (e (γ 1)).snd := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    apply hnoline
    refine ⟨fun t => (e (γ (t / dist b (e (γ 1)).snd))).snd,
      Isometry.of_dist_eq (fun s t => ?_)⟩
    rw [hdist, Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hc]
    field_simp
  rw [hzero, zero_pow (by decide : 2 ≠ 0), add_zero] at hspeed
  refine ⟨(sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [one_pow] using hspeed), fun t => ?_⟩
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact euclidean_coordinate_isometry_line hs e hγ hbase t
  · have hz := hdist 0 t
    rw [hbase, hzero, zero_mul] at hz
    exact (dist_eq_zero.mp hz).symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
