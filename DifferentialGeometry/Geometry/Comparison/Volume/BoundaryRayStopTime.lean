import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryRayDomain

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- The exact last time up to which the original corner ray stays interior and minimizing. -/
def boundaryRayStopTime (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M) :
    ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' boundaryRayDomain g p γ)

theorem boundaryRayDomain_mem_iff_stopTime_lt
    {g : SmoothRiemannianMetric I M} {p : M} {γ : ℝ → M}
    {t : ℝ} (ht : 0 < t) :
    t ∈ boundaryRayDomain g p γ ↔
      ENNReal.ofReal t < boundaryRayStopTime g p γ := by
  constructor
  · intro htDomain
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      ((boundaryRayDomain_isOpen g p γ).mem_nhds htDomain)
    have hs : t + δ / 2 ∈ boundaryRayDomain g p γ := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, show t + δ / 2 - t = δ / 2 by ring,
        abs_of_pos (by positivity)]
      linarith
    have hlt : ENNReal.ofReal t < ENNReal.ofReal (t + δ / 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < t + δ / 2)).mpr
        (by linarith)
    exact hlt.trans_le (le_sSup ⟨t + δ / 2, hs, rfl⟩)
  · intro hlt
    obtain ⟨r, hr, htr⟩ := lt_sSup_iff.mp hlt
    obtain ⟨s, hsDomain, hsr⟩ := hr
    rw [← hsr] at htr
    have hts' : t < s :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp htr
    exact boundaryRayDomain_down g p γ ht hts'.le hsDomain

theorem boundaryRayStopTime_pos
    (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M)
    {t : ℝ} (ht : 0 < t) (hDomain : t ∈ boundaryRayDomain g p γ) :
    0 < boundaryRayStopTime g p γ := by
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ht)
    ((boundaryRayDomain_mem_iff_stopTime_lt ht).1 hDomain).le

theorem boundaryRayStopTime_not_alive
    (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M)
    {t : ℝ} (ht : 0 < t)
    (hstop : boundaryRayStopTime g p γ ≤ ENNReal.ofReal t) :
    t ∉ boundaryRayDomain g p γ := by
  intro hDomain
  have hlt := (boundaryRayDomain_mem_iff_stopTime_lt ht).1 hDomain
  exact (not_lt_of_ge hstop) hlt

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
