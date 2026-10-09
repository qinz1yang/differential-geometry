import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry.PointedGHConverges

universe u v

variable {X : ℕ → Type u} {Y : Type v}
variable [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]
variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] [MetricSpace Y]
variable {p : ∀ i, X i} {q : Y}

theorem dimH_le_two_of_vanishing_normalizedHausdorffMeasure
    (h : PointedGHConverges p q)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcompare : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, fourPointComparison 1 (ball (p i) R))
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hdim : dimH (univ : Set Y) ≤ 3)
    (hvolume : Tendsto (fun i => normalizedHausdorffMeasure 3 (ball (p i) 2)) atTop (𝓝 0)) :
    dimH (univ : Set Y) ≤ 2 := by
  by_contra hfail
  obtain ⟨v, hv, hbound⟩ := h.eventually_normalizedHausdorffMeasure_ball_lower_bound
    hcurves hcompare hcomp (lt_of_not_ge hfail) hdim
  have hsmall := hvolume.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hv))
  obtain ⟨i, hi, hj⟩ := (hbound.and hsmall).exists
  exact (not_lt_of_ge hi) hj

end GC.MetricGeometry.PointedGHConverges
