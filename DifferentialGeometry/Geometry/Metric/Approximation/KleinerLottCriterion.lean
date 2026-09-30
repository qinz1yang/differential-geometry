import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence

set_option autoImplicit false

open Filter

namespace GC.MetricGeometry.PointedGHConverges

theorem of_eventually_kleinerLott_approx
    {X : ℕ → Type*} {Y : Type*} [∀ n, MetricSpace (X n)] [MetricSpace Y]
    [CompleteSpace Y] {p : ∀ n, X n} {q : Y}
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) q δ)) :
    PointedGHConverges p q := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  have hR : 0 < R := hε.trans hεR
  let δ := min (ε / 4) (min (R / 4) (R + 1)⁻¹)
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδR : δ ≤ R / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδinv : δ ≤ (R + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hδone : δ < 1 := hδinv.trans_lt ((inv_lt_one₀ (by positivity)).mpr (by linarith))
  have hRinv : R < δ⁻¹ := by
    have hh := (inv_le_inv₀ (by positivity : 0 < (R + 1)⁻¹) hδ).mpr hδinv
    rw [inv_inv] at hh
    linarith
  filter_upwards [h δ hδ hδone] with n hn
  obtain ⟨f⟩ := hn
  exact ⟨(f.toClosedBall (by linarith) hRinv).enlargeError (by linarith) hεR⟩

end GC.MetricGeometry.PointedGHConverges
