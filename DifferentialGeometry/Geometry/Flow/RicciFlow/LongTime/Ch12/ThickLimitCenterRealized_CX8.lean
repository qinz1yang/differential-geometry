import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterTransport_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterLocal_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall

set_option autoImplicit false

/-!
# CH12-CX8: applying O7 to actual local realizations

This adapter discharges O7's metric comparison, scalar lower bound and deficit realization
from a solution with bounded curvature and injective local isometries into the actual stages.
Uniform canonical `C²` convergence is the remaining compactness input.
-/

noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

section Realized

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [SigmaCompactSpace M] in
/-- Uniform comparison on a bounded-curvature closed backward window. -/
theorem inner_comparison_of_curvature_CX8
    (L : ℝ → SmoothRiemannianMetric ThreeModel M) {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hS : IsSolutionOn (flowOn_O7 L θ hθ))
    (hcurv : ∀ s ∈ Icc (-θ) 0, ∀ x : M, curvDerivNormSq 0 (L s) x ≤ K ^ 2)
    (s : ℝ) (hs : s ∈ Icc (-θ) 0) (x : M) (v : TangentSpace ThreeModel x) :
    (L 0).inner x v v ≤ Real.exp (18 * K * θ) * (L s).inner x v v := by
  have hRm : ∀ r ∈ Icc (-θ) 0, Tensor0SBundle.normSq0S (L r) x 4
      (metricRm04At (L r) x) ≤ K ^ 2 := by
    intro r hr
    simpa only [FILL910.curvDerivNormSq_zero_eq_normSq0S_metricRm04At] using hcurv r hr x
  have h := (metric_inner_exp_bounds_of_curvature_bound (flowOn_O7 L θ hθ) hS
    (fun _ h => h) (fun _ h => h) x hRm ⟨by linarith, le_rfl⟩ hs v).2
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp
  simp only [hdim, Real.sqrt_sq hK] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (metric_inner_self_nonneg _ _ _))
  have habs : |(0 : ℝ) - s| ≤ θ := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  nlinarith

/-- All three analytic realization hypotheses of O7 follow from linked local pullbacks.
The supremum-norm convergence supplied by local flow compactness also gives its fourth
(`hconv`) hypothesis. -/
theorem eventually_defect_lt_of_realized_limit_CX8
    {P : OrientedThreeStage.{u}} {g₀ : P.Metric} {F : GC.Interface.RawSurgery P g₀}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (g : ℝ → SmoothRiemannianMetric ThreeModel M)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel M)
    {θ K : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 0 ≤ K)
    (hS : IsSolutionOn (flowOn_O7 g θ hθ.le))
    (hLS : ∀ n, IsSolutionOn (flowOn_O7 (L n) θ hθ.le))
    (hcurv : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ x : M, curvDerivNormSq 0 (L n s) x ≤ K ^ 2)
    (hconv : ∀ A : Set M, IsCompact A → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0,
        metricDerivNormSupOn A 2 (L n s) (g s) (g 0) < ε)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (httend : Tendsto t atTop atTop)
    (hreal : ∀ n, ∀ s ∈ Icc (-θ) 0, ∃ (X : OrientedThreeStage.{u}) (m : X.Metric)
      (f : M → X.Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f),
      Function.Injective f ∧
      L n s = scaleMetric (t n)⁻¹ (inv_pos.mpr (ht n)) (localPullMetric m f hf) ∧
      (∀ x : X.Carrier, -3 / (2 * (t n * (1 + s) + Hp.scalarShift)) ≤ metricScalarAt m x) ∧
      metricDeficit_O7 m Hp.scalarShift (t n * (1 + s)) =
        metricDeficit_O7 (GC.LongTime.postMetric F.observation (t n * (1 + s)))
          Hp.scalarShift (t n * (1 + s))) (q : M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, sSup (defectSet_O5 (L n 0) q) < ε := by
  have hconv' : ∀ A : Set M, IsCompact A → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0, ∀ y ∈ A, ∀ k : ℕ, k ≤ 2 →
        metricDerivNorm k (L n s) (g s) (g 0) y < ε := by
    intro A hA ε hε
    obtain ⟨N, hN⟩ := hconv A hA ε hε
    exact ⟨N, fun n hn s hs y hy k hk =>
      (derivNorm_le_sup hA hk (L n s) (g s) (g 0) hy).trans_lt (hN n hn s hs)⟩
  have hlow : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y,
      -3 * t n / (2 * (t n * (1 + s) + Hp.scalarShift)) ≤ metricScalarAt (L n s) y := by
    intro n s hs y
    obtain ⟨X, m, f, hf, -, hm, hlow, -⟩ := hreal n s hs
    rw [hm, metricScalarAt_scaleMetric, inv_inv, metricScalarAt_localPull]
    convert mul_le_mul_of_nonneg_left (hlow (f y)) (ht n).le using 1
    ring
  have hreal' : ∀ n, ∀ s ∈ Icc (-θ) 0, t n * (1 + s) ∉ F.observation.eventTimes →
      ∀ B : Set M, MeasurableSet B → ∀ κ : ℝ, 0 ≤ κ →
      (∀ y ∈ B, κ ≤ metricScalarAt (L n s) y +
        3 * t n / (2 * (t n * (1 + s) + Hp.scalarShift))) →
      Real.sqrt (t n) * κ * (riemannianVolumeMeasure ThreeModel M (L n s) B).toReal ≤
        metricDeficit_O7 (GC.LongTime.postMetric F.observation (t n * (1 + s)))
          Hp.scalarShift (t n * (1 + s)) := by
    intro n s hs _ B hB κ hκ hκB
    obtain ⟨X, m, f, hf, hinj, hm, hlow, hdef⟩ := hreal n s hs
    rw [hm] at hκB ⊢
    rw [← hdef]
    exact deficit_ge_of_pullback_O7 m
      (add_pos (mul_pos (ht n) (by linarith [hs.1])) Hp.scalarShift_pos)
      (ht n) (fun x => by simpa only [neg_div] using hlow x) f hf hinj hB hκ hκB
  have hric := ricci_limit_of_realizations_O7 Hp g L hθ hθ1 (Real.exp_pos (18 * K * θ)) hS
    (fun n s hs x v => inner_comparison_of_curvature_CX8 (L n) hθ.le hK (hLS n)
      (hcurv n) s hs x v) hconv' t ht httend hlow hreal'
  apply eventually_defect_lt_of_einstein_limit_CX8 (g 0) (fun n => L n 0) q
  · intro v w
    simpa using hric 0 ⟨by linarith, le_rfl⟩ q v w
  · intro ε hε
    obtain ⟨N, hN⟩ := hconv' {q} isCompact_singleton ε hε
    exact eventually_atTop.2 ⟨N, fun n hn k hk => hN n hn 0 ⟨by linarith, le_rfl⟩
      q (mem_singleton q) k hk⟩

end Realized

end GC.LongTime.Ch12
