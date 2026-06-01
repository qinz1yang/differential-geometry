import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.ToLpChartBridge
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Geometry.Gradient
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Cauchy / `Lp`-limit infrastructure for chart-pushed partials of smooth approximating sequences

For a closed Riemannian manifold `(M, g)`, a chart `α : M`, and a Cauchy
approximating sequence `v_n : SmoothScalar g` (i.e., `smoothToH1Compl (v_n)`
is Cauchy in `H1Compl g`), we package:

* the chart-pulled `j`-th classical partial derivative `chartPushedPartial`
  of `chartPushed POU α v.toFun`, viewed as an `EuclN → ℝ` function;
* a `chartPushedPartialLp` `Lp ℝ 2` element when the partial is in
  `MemLp 2` against the chart-pulled weighted measure restricted to
  `chartTargetEuclid α`;
* the Cauchy property of the chart-pulled partials in `Lp`, given an
  externally-supplied Lipschitz bound that controls the chart-pushed-partial
  map by the `H¹`-pre seminorm on `SmoothScalar g`.

The Lipschitz bound governs the chain-rule + density + chart-pulled-volume
estimates needed for a quantitative bound on the chart-pushed partial in the
chart-weighted L² norm; once supplied, both the Cauchy property in `Lp`
(by linearity + uniform continuity) and the existence of an `Lp` limit
(by completeness of `Lp`) follow by standard arguments.

## Main results

* `chartPushedPartial`: the chart-pulled `j`-th classical partial derivative
  of `chartPushed POU α v.toFun` for a smooth scalar `v`.
* `chartPushedPartialLp`: the chart-pushed partial as an `Lp ℝ 2` element,
  available when the partial is in `MemLp 2` (provided as a hypothesis).
* `cauchy_in_Lp_of_h1Compl_cauchy_with_extension`: the headline Cauchy
  theorem in `Lp`, given a continuous linear extension of the
  chart-pushed-partial map (which packages the Lipschitz bound).
* `cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension`:
  existence of an `Lp` limit, given the continuous linear extension.
* `cauchy_eLpNorm_diff_chartPushedPartial_with_extension`: the corresponding
  Cauchy property of the chart-weighted `eLpNorm` of the difference
  `chartPushedPartial g α j (v n) - chartPushedPartial g α j (v m)`,
  formulated as an `ε-N` statement (since `ℝ≥0∞` lacks a `UniformSpace`
  instance compatible with the filter-`Cauchy` formulation).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace H1ComplGradientChartBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The chart-pulled `j`-th classical partial derivative of the chart-pushed
function, for a smooth scalar `v`. -/
noncomputable def chartPushedPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) : EuclN → ℝ :=
  fun y =>
    (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v.toFun) y)
      (EuclideanSpace.single j 1)

/-- Unfolding lemma for `chartPushedPartial`. -/
@[simp] lemma chartPushedPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) (y : EuclN) :
    chartPushedPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v.toFun) y)
        (EuclideanSpace.single j 1) := rfl

/-- The chart-pushed partial as an `Lp ℝ 2` element, requiring the partial
to be in `MemLp 2` against the chart-pulled weighted measure restricted to
`chartTargetEuclid α`. The `MemLp` hypothesis arises from the chain-rule +
density argument. -/
noncomputable def chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :=
  h.toLp _

/-- The norm of the chart-pushed-partial Lp element equals (the toReal of)
its eLpNorm. -/
lemma norm_chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    ‖chartPushedPartialLp (I := I) (M := M) g α j v h‖ =
      ENNReal.toReal (eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) := by
  unfold chartPushedPartialLp
  exact MeasureTheory.Lp.norm_toLp _ _

/-- The eLpNorm of the chart-pushed partial against the weighted measure
equals `ENNReal.ofReal` of the `Lp`-element norm. -/
lemma eLpNorm_chartPushedPartial_eq_ofReal_norm
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal ‖chartPushedPartialLp (I := I) (M := M) g α j v h‖ := by
  rw [norm_chartPushedPartialLp (I := I) (M := M) g α j v h]
  rw [ENNReal.ofReal_toReal]
  exact h.2.ne

/-- Headline Cauchy theorem in `Lp`: if the chart-pushed-partial map admits
a continuous linear extension `T : SmoothScalar g →L[ℝ] Lp ℝ 2 (weighted, chartTarget)`
that agrees with `chartPushedPartialLp g α j (v) h_v` on smooth scalars, then
for every `H1Compl g`-Cauchy approximating sequence `v_n`, the Lp images
`T (v n)` form a Cauchy sequence in `Lp`. -/
theorem cauchy_in_Lp_of_h1Compl_cauchy_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : SmoothScalar g →L[ℝ] Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {v : ℕ → SmoothScalar g}
    (h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))) :
    Cauchy (atTop.map fun n => T (v n)) := by
  classical
  have h_inducing : IsUniformInducing (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
    rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
        ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
        UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)
  have h_cauchy_smooth : Cauchy (atTop.map v) := by
    rw [(h_inducing.cauchy_map_iff).symm]
    exact h_cauchy_h1
  have hT_uc : UniformContinuous T := T.uniformContinuous
  exact h_cauchy_smooth.map hT_uc

/-- Existence of an `Lp` limit for the chart-pushed partials, given a
continuous linear extension `T`. The limit `g_j_α` is extracted via
completeness of `Lp` from the Cauchy sequence `T (v n)`. The limit is the
candidate chart-pulled weak `j`-th partial of the lifted `H1Compl g`
element `u_h`, characterized up to a.e.-equivalence by the convergence
`‖T (v n) - g_j_α‖_{Lp} → 0`. -/
theorem cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : SmoothScalar g →L[ℝ] Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h)) :
    ∃ g_j_α : Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)),
      Tendsto (fun n => ‖T (v n) - g_j_α‖) atTop (𝓝 0) := by
  classical
  have h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) := h_tendsto.cauchy_map
  have h_lp_cauchy : Cauchy (atTop.map fun n => T (v n)) :=
    cauchy_in_Lp_of_h1Compl_cauchy_with_extension (I := I) (M := M) g α T h_cauchy_h1
  have h_seq_cauchy : CauchySeq (fun n => T (v n)) := h_lp_cauchy
  obtain ⟨g_j_α, h_tendsto_lim⟩ := cauchySeq_tendsto_of_complete h_seq_cauchy
  refine ⟨g_j_α, ?_⟩
  have h_dist : Tendsto (fun n => dist (T (v n)) g_j_α) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp h_tendsto_lim
  have h_funext : (fun n => dist (T (v n)) g_j_α) =
      (fun n => ‖T (v n) - g_j_α‖) := by
    funext n; exact dist_eq_norm _ _
  rw [h_funext] at h_dist
  exact h_dist

theorem cauchy_eLpNorm_diff_chartPushedPartial_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (T : SmoothScalar g →L[ℝ] Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    (h_T_partial_normEq : ∀ v w : SmoothScalar g,
      ‖T v - T w‖ = ENNReal.toReal (eLpNorm
        (fun y => chartPushedPartial (I := I) (M := M) g α j v y -
          chartPushedPartial (I := I) (M := M) g α j w y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))))
    (h_partial_diff_memLp : ∀ v w : SmoothScalar g,
      MemLp (fun y => chartPushedPartial (I := I) (M := M) g α j v y -
          chartPushedPartial (I := I) (M := M) g α j w y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {v : ℕ → SmoothScalar g}
    (h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        < ε := by
  classical
  intro ε hε_pos hε_top
  have h_lp_cauchy : Cauchy (atTop.map fun n => T (v n)) :=
    cauchy_in_Lp_of_h1Compl_cauchy_with_extension (I := I) (M := M) g α T h_cauchy_h1
  have h_seq_cauchy : CauchySeq (fun n => T (v n)) := h_lp_cauchy
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε_pos) hε_top
  rw [Metric.cauchySeq_iff] at h_seq_cauchy
  obtain ⟨N, hN⟩ := h_seq_cauchy ε.toReal hε_real_pos
  refine ⟨N, fun n m hn hm => ?_⟩
  have h_dist : dist (T (v n)) (T (v m)) < ε.toReal := hN n hn m hm
  have h_norm : ‖T (v n) - T (v m)‖ < ε.toReal := by
    rw [← dist_eq_norm]; exact h_dist
  rw [h_T_partial_normEq] at h_norm
  have hLeR : eLpNorm
      (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
        chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) =
    ENNReal.ofReal (ENNReal.toReal (eLpNorm
      (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
        chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)))) :=
    (ENNReal.ofReal_toReal (h_partial_diff_memLp (v n) (v m)).2.ne).symm
  rw [hLeR]
  have hε_eq : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hε_top).symm
  rw [hε_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε_real_pos).mpr h_norm

end H1ComplGradientChartBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
