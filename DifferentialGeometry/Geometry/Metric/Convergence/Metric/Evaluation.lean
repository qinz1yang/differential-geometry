import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section

namespace DifferentialGeometry.SmoothRiemannianMetric

open scoped Manifold ContDiff Topology
open CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

theorem tendstoUniformlyOn_inner
    {ι Q : Type*} {F : Filter ι} {S : Set Q}
    (gSeq : ι → Q → SmoothRiemannianMetric I M) (gLim : Q → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : Q → M)
    (v w : (q : Q) → TangentSpace I (x q))
    (hbound : BddAbove ((fun q =>
      Real.sqrt (gRef.inner (x q) (v q) (v q)) *
        Real.sqrt (gRef.inner (x q) (w q) (w q))) '' S))
    (hconv : TendstoUniformlyOn
      (fun i q => metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q)) (fun _ => 0) F S) :
    TendstoUniformlyOn (fun i q => (gSeq i q).inner (x q) (v q) (w q))
      (fun q => (gLim q).inner (x q) (v q) (w q)) F S := by
  obtain ⟨C, hC⟩ := hbound
  let B : ℝ := max 0 C + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_left (0 : ℝ) C]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc := Metric.tendstoUniformlyOn_iff.mp hconv (ε / B) (div_pos hε hB)
  filter_upwards [hc] with i hi
  intro q hq
  have hn : 0 ≤ metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) := Real.sqrt_nonneg _
  have hsmall : metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) < ε / B := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using hi q hq
  have hprod : Real.sqrt (gRef.inner (x q) (v q) (v q)) *
      Real.sqrt (gRef.inner (x q) (w q) (w q)) ≤ B :=
    (hC ⟨q, hq, rfl⟩).trans
      ((le_max_right 0 C).trans (le_add_of_nonneg_right zero_le_one))
  rw [Real.dist_eq, abs_sub_comm]
  calc
    |(gSeq i q).inner (x q) (v q) (w q) - (gLim q).inner (x q) (v q) (w q)| ≤
        metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) *
          (Real.sqrt (gRef.inner (x q) (v q) (v q)) *
            Real.sqrt (gRef.inner (x q) (w q) (w q))) := by
      simpa only [mul_assoc] using metricDifference_abs_le (gSeq i q) (gLim q) gRef (x q) (v q) (w q)
    _ ≤ metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q) * B :=
      mul_le_mul_of_nonneg_left hprod hn
    _ < ε := (lt_div_iff₀ hB).mp hsmall

theorem tendstoUniformlyOn_inner_of_isCompact
    {ι Q : Type*} [TopologicalSpace Q] {F : Filter ι} {S : Set Q}
    (gSeq : ι → Q → SmoothRiemannianMetric I M) (gLim : Q → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : Q → M)
    (v w : (q : Q) → TangentSpace I (x q))
    (hS : IsCompact S)
    (hv : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (v q)) S)
    (hw : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (w q)) S)
    (hconv : TendstoUniformlyOn
      (fun i q => metricDerivNorm 0 (gSeq i q) (gLim q) gRef (x q)) (fun _ => 0) F S) :
    TendstoUniformlyOn (fun i q => (gSeq i q).inner (x q) (v q) (w q))
      (fun q => (gLim q).inner (x q) (v q) (w q)) F S := by
  have hx : ContinuousOn x S := by
    intro q hq
    have h := hv q hq
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    exact h.1
  have hnorm (z : (q : Q) → TangentSpace I (x q))
      (hz : ContinuousOn (fun q => Bundle.TotalSpace.mk' E (x q) (z q)) S) :
      ContinuousOn (fun q => gRef.inner (x q) (z q) (z q)) S := by
    have h := (gRef.contMDiff.continuous.comp_continuousOn hx).clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hz hz
    intro q hq
    have hh := h q hq
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hh
    exact hh.2
  exact tendstoUniformlyOn_inner gSeq gLim gRef x v w
    (hS.bddAbove_image ((hnorm v hv).sqrt.mul (hnorm w hw).sqrt)) hconv

end DifferentialGeometry.SmoothRiemannianMetric
