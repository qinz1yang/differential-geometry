import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.UniformConvergence


noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HalfLineMetricConvergenceData.tendstoUniformlyOn_chart_coefficients_at_zero
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (α : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I α).target)
    {a : ℝ} (ha : a < 0) (tau : ℕ → ℝ)
    (htau : ∀ n, tau n ∈ Icc a 0) (htend : Tendsto tau atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun n y (ijk : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E)) =>
        (chartGramOnE (co.gInf (tau n)) α ijk.1 ijk.2.1 y,
          chartRicciTensor (co.gInf (tau n)) α ijk.1 ijk.2.1 y,
          chartChristoffel (co.gInf (tau n)) α ijk.1 ijk.2.1 ijk.2.2 y))
      (fun y (ijk : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E)) =>
        (chartGramOnE (co.gInf 0) α ijk.1 ijk.2.1 y,
          chartRicciTensor (co.gInf 0) α ijk.1 ijk.2.1 y,
          chartChristoffel (co.gInf 0) α ijk.1 ijk.2.1 ijk.2.2 y))
      atTop K := by
  classical
  let S : SolutionOn (I := I) (M := P.M) X.D := { base := { metric := co.gInf } }
  have hS : IsSolutionOn S := co.isSolutionOn Phi hcarrier hregular
  have hslab : Icc (a - 1) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ioo (a - 1) 0 ⊆ X.D.regular :=
    Ioo_subset_Iio_self.trans hregular
  have hmet := solution_metricCLMSection_contMDiffOn_closed S hS
    (sub_lt_self a zero_lt_one) ha hslab hreg
  have hgram (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (co.gInf z.1) α i j z.2)
      (Icc a 0 ×ˢ interior (extChartAt I α).target) :=
    chartGramOnE_contDiffOn_of_contMDiffOn co.gInf hmet α i j
  have hwithin : chartGramFamilySmoothWithinOn co.gInf α (Icc a 0) := by
    intro i j t y ht hy
    exact hgram i j (t, y) ⟨ht, hy⟩
  let V : ℝ × E → (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) → ℝ × ℝ × ℝ) := fun z ijk =>
    (chartGramOnE (co.gInf z.1) α ijk.1 ijk.2.1 z.2,
      chartRicciTensor (co.gInf z.1) α ijk.1 ijk.2.1 z.2,
      chartChristoffel (co.gInf z.1) α ijk.1 ijk.2.1 ijk.2.2 z.2)
  have hV : ContinuousOn V (Icc a 0 ×ˢ interior (extChartAt I α).target) := by
    apply continuousOn_pi.mpr
    intro ijk
    apply (hgram ijk.1 ijk.2.1).continuousOn.prodMk
    apply ContinuousOn.prodMk
    · intro z hz
      exact (chartRicciTensor_contDiffWithinAt co.gInf α hwithin
        ijk.1 ijk.2.1 hz.1 hz.2).continuousWithinAt
    · intro z hz
      exact (chartChristoffel_contDiffWithinAt co.gInf α hwithin
        ijk.1 ijk.2.1 ijk.2.2 hz.1 hz.2).continuousWithinAt
  have hKi : K ⊆ interior (extChartAt I α).target := by
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  have hzero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  have htendWithin : Tendsto tau atTop (𝓝[Icc a 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall htau⟩
  change TendstoUniformlyOn (fun n y => V (tau n, y)) (fun y => V (0, y)) atTop K
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  obtain ⟨W, hW, hsmall⟩ := hK.mem_uniformity_of_prod
    (f := fun t y => V (t, y)) (hV.mono (prod_mono Subset.rfl hKi)) hzero
    (Metric.dist_mem_uniformity hepsilon)
  filter_upwards [htendWithin.eventually hW] with n hn
  intro y hy
  have hsmall' := hsmall (tau n) hn y hy
  change dist (V (tau n, y)) (V (0, y)) < epsilon at hsmall'
  rw [dist_comm]
  exact hsmall'

end DifferentialGeometry.CheegerGromovCompactness
