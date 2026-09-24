import DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianCurveVariation_le_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hgh : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveVariation h γ a b ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b := by
  unfold riemannianCurveVariation
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1,
        riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => edistOf_le_of_quad g h hc hgh _ _
    _ = ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        (Finset.mul_sum ..).symm
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
          ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1,
            riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} => ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1, riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

theorem le_riemannianCurveVariation_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b ≤
      riemannianCurveVariation h γ a b := by
  unfold riemannianCurveVariation
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
        riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      = ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) := Finset.mul_sum ..
    _ ≤ ∑ i ∈ Finset.range p.1,
          riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => le_edistOf_of_quad g h hc hl _ _
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
          ∑ i ∈ Finset.range q.1,
            riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} => ∑ i ∈ Finset.range q.1, riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

theorem riemannianCurveVariation_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveVariation (scaleMetric (I := I) c hc g) γ a b =
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b := by
  refine le_antisymm ?_ ?_
  · refine riemannianCurveVariation_le_of_quad g (scaleMetric (I := I) c hc g) hc ?_ γ a b
    intro x v
    simp
  · exact le_riemannianCurveVariation_of_quad g (scaleMetric (I := I) c hc g) hc
      (fun x v => by simp) γ a b


end DifferentialGeometry.Geometry
