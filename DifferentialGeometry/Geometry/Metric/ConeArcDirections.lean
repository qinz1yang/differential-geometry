import DifferentialGeometry.Geometry.Metric.EuclideanCone

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem dist_eq_of_dist_mk_sq_eq {r : ℝ≥0} (hr : 0 < (r : ℝ))
    {a b : Y} (hab : dist a b ≤ Real.pi) {θ : ℝ}
    (hθ : θ ∈ Icc 0 Real.pi)
    (hd : dist (mk r a) (mk r b) ^ 2 =
      2 * (r : ℝ) ^ 2 * (1 - Real.cos θ)) :
    dist a b = θ := by
  have hs := coneDistance_sq (x := ((r : ℝ), a)) (y := ((r : ℝ), b)) hr.le hr.le
  rw [min_eq_right hab] at hs
  rw [dist_mk] at hd
  have he : (2 * (r : ℝ) ^ 2) * (Real.cos (dist a b) - Real.cos θ) = 0 := by
    nlinarith only [hs, hd]
  have hc : Real.cos (dist a b) = Real.cos θ :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by positivity))
  exact Real.strictAntiOn_cos.injOn ⟨dist_nonneg, hab⟩ hθ hc

theorem exists_base_segment_of_cone_arc (hdiam : ∀ a b : Y, dist a b ≤ Real.pi)
    {r : ℝ≥0} (hr : 0 < (r : ℝ)) (a b : Y)
    (f : Icc (0 : ℝ) 1 → EuclideanCone Y)
    (hzero : f ⟨0, by norm_num⟩ = mk r a)
    (hone : f ⟨1, by norm_num⟩ = mk r b)
    (hradius : ∀ t, radius (f t) = r)
    (hd : ∀ s t, dist (f s) (f t) ^ 2 =
      2 * (r : ℝ) ^ 2 * (1 - Real.cos (dist a b * dist s t))) :
    ∃ g : Icc (0 : ℝ) 1 → Y, Continuous g ∧
      g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
      (∀ t, f t = mk r (g t)) ∧
      ∀ s t, dist (g s) (g t) = dist a b * dist s t := by
  have hex : ∀ t, ∃ u : Y, f t = mk r u := by
    intro t
    rcases eq_tip_or_eq_mk (f t) with ht | ⟨s, u, _, hu⟩
    · have h := hradius t
      rw [ht, radius_tip] at h
      exact (hr.ne' h.symm).elim
    · have hs : s = r := by
        apply NNReal.eq
        simpa only [hu, radius_mk] using hradius t
      exact ⟨u, hs ▸ hu⟩
  choose g hg using hex
  have hi : Function.Injective (mk r : Y → EuclideanCone Y) := by
    intro u v huv
    rw [mk_pos hr, mk_pos hr] at huv
    exact congrArg Prod.snd (Option.some.inj huv)
  have hdist : ∀ s t, dist (g s) (g t) = dist a b * dist s t := by
    intro s t
    apply dist_eq_of_dist_mk_sq_eq hr (hdiam _ _)
    · refine ⟨by positivity, ?_⟩
      have hst : dist s t ≤ (1 : ℝ) := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_le]
        constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
      exact (mul_le_mul_of_nonneg_left hst dist_nonneg).trans (by simpa using hdiam a b)
    · simpa only [hg s, hg t] using hd s t
  have hl : LipschitzWith ⟨dist a b, dist_nonneg⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact (hdist s t).le
  exact ⟨g, hl.continuous, hi ((hg _).symm.trans hzero),
    hi ((hg _).symm.trans hone), hg, hdist⟩

end Metric.EuclideanCone
