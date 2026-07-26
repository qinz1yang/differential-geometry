import DifferentialGeometry.Analysis.Parabolic.Euclidean.HolderPath
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MetricHolderData

/-!
# Finite-chart Holder paths for metric differences

This file instantiates the analytic finite-family gauge from `HolderPath` on
the active POU charts and the finitely many `(0,2)` component pairs.  Its first
producer places every member of a uniformly `C^3` metric family, viewed as a
constant path, in one common parabolic Holder ball.  The ball constant is
chosen before both the family index and the time horizon.
-/

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff NNReal ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.HCGCompactness

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Finite set of active POU chart centres and covariant `(0,2)` component
indices. -/
def metricChartIdx :
    Finset (M × (Fin 2 → Fin (Module.finrank ℝ E))) := by
  classical
  exact (chartAtlasPOU_finset (I := I) (M := M)).product Finset.univ

/-- POU-weighted Euclidean component path of the difference from `gBase`. -/
def metricCompPath
    (gBase : SmoothRiemannianMetric I M)
    (gPath : ℝ → SmoothRiemannianMetric I M)
    (a : M × (Fin 2 → Fin (Module.finrank ℝ E)))
    (t : ℝ) (y : EuclN) : ℝ :=
  tensorChartComp (I := I) (M := M) gBase 0 2
    (metricDifferenceCcTensor (I := I) (M := M) gBase (gPath t))
    a.1 (![] : Fin 0 → Fin (Module.finrank ℝ E)) a.2 y

/-- Finite-chart parabolic `C^{2,1/2}` gauge of a metric path relative to a
fixed background. -/
def metricParGauge
    (gBase : SmoothRiemannianMetric I M) (τ : ℝ)
    (gPath : ℝ → SmoothRiemannianMetric I M) : ℝ≥0∞ :=
  eFinParC2Half (metricChartIdx (I := I) (M := M)) τ
    (metricCompPath (I := I) (M := M) gBase gPath)

/-- Metric-path version of the finite parabolic Holder ball. -/
def MetricInHolderBall
    (gBase : SmoothRiemannianMetric I M) (τ : ℝ) (C : ℝ≥0∞)
    (gPath : ℝ → SmoothRiemannianMetric I M) : Prop :=
  InHolderBall (metricChartIdx (I := I) (M := M)) τ C
    (metricCompPath (I := I) (M := M) gBase gPath)

/-- One order-at-most-three intrinsic family bound places all constant
initial paths in one finite-chart parabolic Holder ball.  The same ball works
for every time horizon. -/
theorem metricConst_ball
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B) :
    ∃ C : ℝ≥0, ∀ (k : ι) (τ : ℝ),
      MetricInHolderBall (I := I) (M := M) gBase τ C (fun _ => gSeq k) := by
  classical
  obtain ⟨C₀, hC₀, Cα, hdata⟩ :=
    metricDiff_c2half (I := I) (M := M) gBase gSeq B hbdd
  let C₀n : ℝ≥0 := ⟨C₀, hC₀⟩
  let Ce : ℝ≥0 := 3 * C₀n + Cα
  let A := metricChartIdx (I := I) (M := M)
  let C : ℝ≥0 := (A.card : ℝ≥0) * Ce
  refine ⟨C, ?_⟩
  intro k τ
  have hentry : ∀ a ∈ A,
      eParC2Half τ
        (metricCompPath (I := I) (M := M) gBase (fun _ => gSeq k) a) ≤
        (Ce : ℝ≥0∞) := by
    intro a ha
    have ha' : a ∈ metricChartIdx (I := I) (M := M) := by simpa only [A] using ha
    rcases Finset.mem_product.mp ha' with ⟨ha_chart, _ha_comp⟩
    obtain ⟨hjet, hhalf⟩ := hdata a.1 ha_chart k a.2
    let u : EuclN → ℝ :=
      tensorChartComp (I := I) (M := M) gBase 0 2
        (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
        a.1 (![] : Fin 0 → Fin (Module.finrank ℝ E)) a.2
    have hsup : ∀ j ∈ Finset.range 3,
        eSupNorm (iteratedFDeriv ℝ j u) ≤ (C₀n : ℝ≥0∞) := by
      intro j hj
      rw [eSupNorm_le]
      intro x
      rw [ENNReal.ofReal_le_coe]
      exact hjet j (by omega) x
    have hsum :
        (∑ j ∈ Finset.range 3, eSupNorm (iteratedFDeriv ℝ j u)) ≤
          (3 : ℝ≥0∞) * C₀n := by
      calc
        (∑ j ∈ Finset.range 3, eSupNorm (iteratedFDeriv ℝ j u))
            ≤ ∑ j ∈ Finset.range 3, (C₀n : ℝ≥0∞) := by
          exact Finset.sum_le_sum fun j hj => hsup j hj
        _ = (3 : ℝ≥0∞) * C₀n := by simp
    have hholder : eHolderNorm (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 u) ≤
        (Cα : ℝ≥0∞) := by
      exact hhalf.eHolderNorm_le
    have hspace : eC2Half u ≤ (Ce : ℝ≥0∞) := by
      unfold eC2Half
      calc
        (∑ j ∈ Finset.range 3, eSupNorm (iteratedFDeriv ℝ j u)) +
              eHolderNorm (1 / 2 : ℝ≥0) (iteratedFDeriv ℝ 2 u)
            ≤ (3 : ℝ≥0∞) * C₀n + Cα := add_le_add hsum hholder
        _ = (Ce : ℝ≥0∞) := by simp [Ce, C₀n]
    simpa only [eParC2Half, metricCompPath, u, iSup_const, eHolderNorm_const,
      add_zero] using hspace
  have hreg : ∀ a ∈ A,
      IsParC2Half τ
        (metricCompPath (I := I) (M := M) gBase (fun _ => gSeq k) a) := by
    intro a ha
    constructor
    · intro t _ht
      dsimp only [metricCompPath]
      exact (tensorChartComp_contDiff (I := I) (M := M) gBase 0 2
        (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
        a.1 (![] : Fin 0 → Fin (Module.finrank ℝ E)) a.2).of_le (by simp)
    · intro j hj x
      have hconst : Continuous
          (fun _ : ℝ => iteratedFDeriv ℝ j
            (tensorChartComp (I := I) (M := M) gBase 0 2
              (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
              a.1 (![] : Fin 0 → Fin (Module.finrank ℝ E)) a.2) x) :=
        continuous_const
      simpa only [metricCompPath] using hconst.continuousOn
  refine ⟨hreg, ?_⟩
  unfold eFinParC2Half
  change (∑ a ∈ A, eParC2Half τ
      (metricCompPath (I := I) (M := M) gBase (fun _ => gSeq k) a)) ≤
    (C : ℝ≥0∞)
  calc
    (∑ a ∈ A, eParC2Half τ
        (metricCompPath (I := I) (M := M) gBase (fun _ => gSeq k) a))
        ≤ ∑ a ∈ A, (Ce : ℝ≥0∞) := by
      exact Finset.sum_le_sum fun a ha => hentry a ha
    _ = (C : ℝ≥0∞) := by simp [C]

end DifferentialGeometry.PDE.RicciFlow
