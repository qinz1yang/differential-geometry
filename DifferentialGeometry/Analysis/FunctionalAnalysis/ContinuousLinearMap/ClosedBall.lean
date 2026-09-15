import Mathlib.Analysis.Normed.Operator.NNNorm

noncomputable section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 L V : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup L] [NormedSpace 𝕜 L]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

def closedBallMap (J : L →L[𝕜] V) {r R : ℝ} (hR : ‖J‖ * r ≤ R) :
    Metric.closedBall (0 : L) r → Metric.closedBall (0 : V) R := fun u =>
  ⟨J u, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : ‖(u : L)‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using u.2
    exact (J.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hu (norm_nonneg J)).trans hR)⟩

@[simp] theorem closedBallMap_coe (J : L →L[𝕜] V) {r R : ℝ} (hR : ‖J‖ * r ≤ R)
    (u : Metric.closedBall (0 : L) r) : (J.closedBallMap hR u : V) = J u := rfl

theorem lipschitzWith_closedBallMap (J : L →L[𝕜] V) {r R : ℝ} (hR : ‖J‖ * r ≤ R) :
    LipschitzWith ‖J‖₊ (J.closedBallMap hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (J (u : L)) (J (v : L)) ≤ ‖J‖ * dist (u : L) (v : L)
  exact J.dist_le_opNorm _ _

theorem exists_pos_norm_mul_le (J : L →L[𝕜] V) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ‖J‖ * r ≤ R := by
  obtain ⟨s, hs, hsJ⟩ := exists_pos_mul_lt hR ‖J‖
  refine ⟨min s R, lt_min hs hR, min_le_right _ _, ?_⟩
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg J)).trans hsJ.le

end ContinuousLinearMap

namespace LipschitzWith

variable {𝕜 L V A T : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup L] [NormedSpace 𝕜 L]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [PseudoMetricSpace A] [PseudoMetricSpace T]
  {r R : ℝ} {C : ℝ≥0}
  {N : T × Metric.closedBall (0 : V) R → A}

theorem prod_precomp_closedBall (hN : LipschitzWith C N)
    (J : L →L[𝕜] V) (hR : ‖J‖ * r ≤ R) :
    LipschitzWith (C * (1 + ‖J‖₊))
      (fun p : T × Metric.closedBall (0 : L) r => N (p.1, J.closedBallMap hR p.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hn := hN.dist_le_mul (p.1, J.closedBallMap hR p.2) (q.1, J.closedBallMap hR q.2)
  have hj := (J.lipschitzWith_closedBallMap hR).dist_le_mul p.2 q.2
  have ht : dist p.1 q.1 ≤ (1 + ‖J‖) * max (dist p.1 q.1) (dist p.2 q.2) := by
    calc
      _ ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_left _ _
      _ ≤ (1 + ‖J‖) * max (dist p.1 q.1) (dist p.2 q.2) := by
        exact le_mul_of_one_le_left (le_trans dist_nonneg (le_max_left _ _))
          (le_add_of_nonneg_right (norm_nonneg J))
  have hu : dist (J.closedBallMap hR p.2) (J.closedBallMap hR q.2) ≤
      (1 + ‖J‖) * max (dist p.1 q.1) (dist p.2 q.2) := by
    calc
      _ ≤ ‖J‖ * dist p.2 q.2 := hj
      _ ≤ ‖J‖ * max (dist p.1 q.1) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg J)
      _ ≤ (1 + ‖J‖) * max (dist p.1 q.1) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
          (le_trans dist_nonneg (le_max_left _ _))
  calc
    dist _ _ ≤ C * max (dist p.1 q.1)
        (dist (J.closedBallMap hR p.2) (J.closedBallMap hR q.2)) := by
      simpa only [Prod.dist_eq] using hn
    _ ≤ C * ((1 + ‖J‖) * max (dist p.1 q.1) (dist p.2 q.2)) :=
      mul_le_mul_of_nonneg_left (max_le ht hu) C.coe_nonneg
    _ = (C * (1 + ‖J‖₊)) * dist p q := by
      simp only [coe_nnnorm, Prod.dist_eq, mul_assoc]

end LipschitzWith

namespace LipschitzWith

variable {𝕜 L V A : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup L] [NormedSpace 𝕜 L]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup A]
  {r R : ℝ} {C : ℝ≥0}
  {N : ℝ × Metric.closedBall (0 : V) R → A}

theorem norm_sub_time_precomp_closedBall (hN : LipschitzWith C N)
    (J : L →L[𝕜] V) (hR : ‖J‖ * r ≤ R)
    (t : ℝ) (u v : Metric.closedBall (0 : L) r) :
    ‖N (t, J.closedBallMap hR u) - N (t, J.closedBallMap hR v)‖ ≤
      C * ‖J ((u : L) - (v : L))‖ := by
  have h := hN.dist_le_mul (t, J.closedBallMap hR u) (t, J.closedBallMap hR v)
  rw [Prod.dist_eq] at h
  simpa only [dist_self, max_eq_right (norm_nonneg _), Subtype.dist_eq,
    dist_eq_norm, ContinuousLinearMap.closedBallMap_coe, map_sub] using h

theorem norm_sub_origin_time_precomp_closedBall_le_max (hN : LipschitzWith C N)
    (J : L →L[𝕜] V) (hr : 0 ≤ r) (hR : ‖J‖ * r ≤ R)
    (t : ℝ) (u : Metric.closedBall (0 : L) r) :
    ‖N (t, J.closedBallMap hR u) -
      N (0, J.closedBallMap hR ⟨0, Metric.mem_closedBall_self hr⟩)‖ ≤
      C * max |t| ‖J (u : L)‖ := by
  simpa only [Prod.dist_eq, Subtype.dist_eq, ContinuousLinearMap.closedBallMap_coe,
    map_zero, dist_eq_norm, sub_zero, Real.norm_eq_abs] using
      hN.dist_le_mul (t, J.closedBallMap hR u)
        (0, J.closedBallMap hR ⟨0, Metric.mem_closedBall_self hr⟩)

theorem norm_sub_origin_time_precomp_closedBall (hN : LipschitzWith C N)
    (J : L →L[𝕜] V) (hr : 0 ≤ r) (hR : ‖J‖ * r ≤ R)
    (t : ℝ) (u : Metric.closedBall (0 : L) r) :
    ‖N (t, J.closedBallMap hR u) -
      N (0, J.closedBallMap hR ⟨0, Metric.mem_closedBall_self hr⟩)‖ ≤
      C * (|t| + ‖J‖ * ‖(u : L)‖) := by
  refine (hN.norm_sub_origin_time_precomp_closedBall_le_max J hr hR t u).trans
    (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  apply max_le
  · exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg J) (norm_nonneg (u : L)))
  · exact (J.le_opNorm (u : L)).trans (le_add_of_nonneg_left (abs_nonneg t))

theorem norm_time_precomp_closedBall_le (hN : LipschitzWith C N)
    (J : L →L[𝕜] V) (hr : 0 ≤ r) (hR : ‖J‖ * r ≤ R)
    (t : ℝ) (u : Metric.closedBall (0 : L) r) :
    ‖N (t, J.closedBallMap hR u)‖ ≤
      ‖N (0, J.closedBallMap hR ⟨0, Metric.mem_closedBall_self hr⟩)‖ +
        C * max |t| ‖J (u : L)‖ := by
  have h := hN.norm_sub_origin_time_precomp_closedBall_le_max J hr hR t u
  exact (norm_le_insert' _ _).trans (add_le_add le_rfl h)

end LipschitzWith
