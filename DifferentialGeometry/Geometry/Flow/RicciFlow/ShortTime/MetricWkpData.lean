import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CompactJetWkpBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkp
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponentRawNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Intrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MetricWkpTerms
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Uniform `W^{3,p}` data for bounded metric families

The order-at-most-three intrinsic metric bounds used by uniform short-time
existence also control the fixed-background metric differences in the concrete
chart-Sobolev model.  This file packages that implication in two steps:

* `metricDiff_comp_jet` gives one pointwise bound for all derivatives through
  order three of every POU-weighted scalar chart component;
* `metricDiff_wkp3_bdd` converts those bounds into `MemWkpTensor 3 p` and one
  common finite `wkpTensorNorm` radius.

The ellipticity hypothesis used by the later Ricci--DeTurck solver is not
needed for this data-size estimate.  It enters separately in uniform
parabolicity.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
private lemma secComp_to_smooth [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s S.toSection α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := rfl

omit [BoundarylessManifold I M] in
/-- Uniform intrinsic metric bounds through order three give one uniform
Frechet-jet bound for every POU-weighted scalar component of the
fixed-background metric difference.  The bound is also valid at inactive
chart centres, where the component is identically zero. -/
theorem metricDiff_comp_jet
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (k : ι)
        (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
        (j : ℕ), j ≤ 3 → ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤ C := by
  exact metricDiff_fam_jet (I := I) (M := M) gBase gSeq B hbdd
omit [BoundarylessManifold I M] in
/-- The intrinsic `C^3` metric-family bound gives one real radius containing
all fixed-background metric differences in chartwise `W^{3,p}`.  In
particular, the conclusion includes both the concrete tensor-Sobolev
membership and an explicit uniform bound for `wkpTensorNorm`. -/
theorem metricDiff_wkp3_bdd
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι,
      MemWkpTensor (I := I) (M := M) gBase 3 p
          (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection ∧
        wkpTensorNorm (I := I) (M := M) gBase 3 p
          (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection ≤
            ENNReal.ofReal C := by
  classical
  have hper : ∀ α : M, ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ w : ι × (Fin 2 → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    exact metricDiff_wkp_terms (I := I) (M := M) gBase gSeq B hbdd hp
  choose A hA_top hA using hper
  let R : ℝ≥0∞ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin 2 → Fin (Module.finrank ℝ E), A α
  have hR_top : R < ⊤ := by
    dsimp [R]
    refine ENNReal.sum_lt_top.mpr ?_
    intro α hα
    refine ENNReal.sum_lt_top.mpr ?_
    intro Idx hIdx
    refine ENNReal.sum_lt_top.mpr ?_
    intro Jdx hJdx
    exact hA_top α
  have hR_ne : R ≠ ⊤ := hR_top.ne
  refine ⟨R.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro k
  have hmem : MemWkpTensor (I := I) (M := M) gBase 3 p
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection := by
    intro α Idx Jdx
    have hIdx : Idx = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
      Subsingleton.elim _ _
    rw [hIdx, secComp_to_smooth]
    exact (hA α (k, Jdx)).1
  refine ⟨hmem, ?_⟩
  unfold wkpTensorNorm
  have hcollapse :
      (∑' α : M,
        ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 3 p
              (secChartComp (I := I) (M := M) 0 2
                (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 3 p
                (secChartComp (I := I) (M := M) 0 2
                  (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                  α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α) := by
    rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
    intro α hα
    refine Finset.sum_eq_zero ?_
    intro Idx hIdx
    refine Finset.sum_eq_zero ?_
    intro Jdx hJdx
    rw [secComp_zero_off (I := I) (M := M) 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
      hα Idx Jdx]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [hcollapse]
  calc
    (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 3 p
                (secChartComp (I := I) (M := M) 0 2
                  (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                  α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ≤ R := by
      dsimp [R]
      refine Finset.sum_le_sum ?_
      intro α hα
      refine Finset.sum_le_sum ?_
      intro Idx hIdx
      refine Finset.sum_le_sum ?_
      intro Jdx hJdx
      have hIdx0 : Idx = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
        Subsingleton.elim _ _
      rw [hIdx0, secComp_to_smooth]
      exact (hA α (k, Jdx)).2
    _ = ENNReal.ofReal R.toReal := (ENNReal.ofReal_toReal hR_ne).symm

end DifferentialGeometry.PDE.RicciFlow
