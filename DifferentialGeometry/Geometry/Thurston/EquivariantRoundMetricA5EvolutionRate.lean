import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5GaugeFlow
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

/-!
# Rate transfer from the gauge-fixed limit to the normalized surface flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (vii)
and the time change of (viii)).

* `normalizedFlowMetric S t = g(t) / (2 (T* - t))` for `t < T*` (`flowExtinctionTime`).
* `normalizedFlowMetric_scalar_rate_of_gauge` (D18 (vii)): if the gauge-fixed normalized metrics
  `ψₜ* ĝ(t)` and a limit `k∞` with `R(k∞) ≡ 2` share a lower bound and `C²` bounds with respect to
  `g(0)`, and `ψₜ* ĝ(t) → k∞` in `C²` at the rate `(T* - t)^β`, then
  `|R(t, ·) · 2 (T* - t) - 2| ≤ C (T* - t)^β`: `exists_abs_metricScalarAt_sub_le` bounds the
  scalar difference by the `C²` distance, `metricScalarAt_pullback` and the scaling of the scalar
  curvature identify `R(ψₜ* ĝ(t))(x)` with `2 (T* - t) R(t, ψₜ x)`, and `ψₜ` is onto.
* `flowExtinctionTime_sub_eq_exp`: with `s = -½ log (1 - t / T*)`, `T* - t = T* e^{-2 s}`; a rate
  `e^{-β_s s}` in normalized time is the rate `(T* - t)^{β_s / 2}` in `t`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

def normalizedFlowMetric (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (t : ℝ) : SmoothRiemannianMetric I M :=
  if h : t < flowExtinctionTime S then normalizedSurfaceMetric (S.family.metric t) h
  else S.family.metric t

omit [I.Boundaryless] in
theorem metricScalarAt_normalizedFlowMetric
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {t : ℝ}
    (ht : t < flowExtinctionTime S) (x : M) :
    metricScalarAt (normalizedFlowMetric S t) x =
      S.scalar t x * (2 * (flowExtinctionTime S - t)) := by
  rw [normalizedFlowMetric]
  simp only [ht, ↓reduceDIte]
  rw [normalizedSurfaceMetric, metricScalarAt_scaleMetric]
  simp only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family_metric]
  rw [one_div, inv_inv, mul_comm]

theorem normalizedFlowMetric_scalar_rate_of_gauge [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t₀ : ℝ} (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    {lam B β : ℝ} (hlam : 0 < lam) (hβ : 0 < β) (kInf : SmoothRiemannianMetric I M)
    (hlow : ∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v)
    (hlowInf : ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
      kInf.inner x v v)
    (hbdd : ∀ t ∈ Ico t₀ T, ∀ x, ∀ q ≤ 2, metricCovDerivNorm q
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤ B)
    (hbddInf : ∀ x, ∀ q ≤ 2, metricCovDerivNorm q kInf (S.family.metric 0) x ≤ B)
    (hrate : ∀ t ∈ Ico t₀ T, ∀ q ≤ 2, ∀ x,
      metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
        (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β)
    (hround : ∀ x, metricScalarAt kInf x = 2) :
    ∃ C : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
      |S.scalar t x * (2 * (flowExtinctionTime S - t)) - 2| ≤
        C * (flowExtinctionTime S - t) ^ β := by
  have _ := hβ
  have hTT : T ≤ flowExtinctionTime S := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  obtain ⟨C, hC0, hC⟩ :=
    exists_abs_metricScalarAt_sub_le (S.family.metric 0) isCompact_univ lam B hlam
  refine ⟨C * (3 * B), fun t ht y => ?_⟩
  have htT : t < flowExtinctionTime S := ht.2.trans_le hTT
  set x := (ψ t).symm y with hx
  have hy : ψ t x = y := (ψ t).apply_symm_apply y
  have key := hC (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
    (fun z _ ξ => hlow t ht z ξ) (fun z _ ξ => hlowInf z ξ)
    (fun z _ a ha => hbdd t ht z a ha) (fun z _ a ha => hbddInf z a ha) x (mem_univ x)
  rw [metricScalarAt_pullback, hround, hy, metricScalarAt_normalizedFlowMetric S htT] at key
  have hsum : ∑ q ∈ Finset.range 3, metricDerivNorm q
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf (S.family.metric 0) x ≤
      3 * (B * (flowExtinctionTime S - t) ^ β) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    have h0 := hrate t ht 0 (by norm_num) x
    have h1 := hrate t ht 1 (by norm_num) x
    have h2 := hrate t ht 2 (by norm_num) x
    linarith
  calc |S.scalar t y * (2 * (flowExtinctionTime S - t)) - 2|
      ≤ C * ∑ q ∈ Finset.range 3, metricDerivNorm q
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
          (S.family.metric 0) x := key
    _ ≤ C * (3 * (B * (flowExtinctionTime S - t) ^ β)) :=
        mul_le_mul_of_nonneg_left hsum hC0.le
    _ = C * (3 * B) * (flowExtinctionTime S - t) ^ β := by ring

theorem flowExtinctionTime_sub_eq_exp (Tst : ℝ) (hTst : 0 < Tst) {t : ℝ} (ht : t < Tst) :
    Tst - t = Tst * Real.exp (-2 * (-(1 / 2) * Real.log (1 - t / Tst))) := by
  have hpos : 0 < 1 - t / Tst := by
    rw [sub_pos, div_lt_one hTst]
    exact ht
  rw [show -2 * (-(1 / 2) * Real.log (1 - t / Tst)) = Real.log (1 - t / Tst) by ring,
    Real.exp_log hpos]
  field_simp

end GC.Geometry
