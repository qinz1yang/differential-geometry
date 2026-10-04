import DifferentialGeometry.Geometry.Metric.Approximation.ConeRadialExtension

/-!
# LC25: the multiplicative form of the outward-point bound

Blueprint 207A, LC25 (`lem:collapse-cone-outward-point`, A:20953–20998): "In particular,
choosing also `15 δ < μ a` gives `d(q, q') < (1 + μ) r`." This file adds that clause to the
existing annulus theorem `KleinerLottApprox.exists_outward_point_on_annulus`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

variable {X C : Type*} [MetricSpace X] [MetricSpace C] {p q : X} {o : C} {δ : ℝ}

/-- LC25 with its multiplicative clause: under the annulus hypotheses and `15 δ < μ a`, the
outward point satisfies `d(p,q') = 2 d(p,q)`, `d(p,q) ≤ d(q,q') < d(p,q) + 15 δ` and
`d(q,q') < (1 + μ) d(p,q)`. -/
theorem KleinerLottApprox.exists_outward_point_on_annulus_lt_mul
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsegments : ∀ a b : X, ∃ c : Set.Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    {a b μ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδa : δ < a / 10) (hδb : δ < 1 / (4 * b + 20)) (hμ : 15 * δ < μ * a)
    (hq : a ≤ dist p q ∧ dist p q ≤ b) :
    ∃ q', dist p q' = 2 * dist p q ∧ dist p q ≤ dist q q' ∧
      dist q q' < dist p q + 15 * δ ∧ dist q q' < (1 + μ) * dist p q := by
  obtain ⟨q', h1, h2, h3⟩ := φ.exists_outward_point_on_annulus H hsegments ha hab hδa hδb hq
  have hμpos : 0 < μ := by
    by_contra h
    have hle : μ * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) ha.le
    linarith [φ.error_pos]
  have hμr : μ * a ≤ μ * dist p q := mul_le_mul_of_nonneg_left hq.1 hμpos.le
  exact ⟨q', h1, h2, h3, by linarith⟩

end GC.MetricGeometry
