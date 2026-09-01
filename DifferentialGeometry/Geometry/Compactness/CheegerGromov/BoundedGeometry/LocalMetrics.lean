import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Defs


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.LocalMetrics

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]


omit [CompleteSpace E] in
theorem exists_chart_metric_limit_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd)
    (c : ∀ k : Nat, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hsub : ∀ k,
      U ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (c k) (X.obj k).basepoint))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) gInf U ∧
      MapCInfConvOnCompacts U
        (fun k => d.chartMetric (phi k) (c (phi k))) gInf ∧
      ∀ z ∈ U, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v ∧
          gInf z v v ≤ 2 * ‖v‖ ^ 2 := by
  apply exists_metricLimit_on hU (fun k => d.chartMetric k (c k))
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    simpa only [BoundedGeometryNormalChartData.chartMetric] using
      (d.chart k (c k)).metric_cont_diff_on (X.obj k).metric hU
        ((d.chart k (c k)).smooth_to.mono hrad)
  · intro p K hK hKU
    refine ⟨d.metricC p, ?_⟩
    intro k z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    simpa only [BoundedGeometryNormalChartData.chartMetric] using
      d.metric_deriv k p (c k) z (hrad (hKU hz))
  · intro k z hz v
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c k)).radius := by
      simpa only [d.radius_eq k (c k)] using hsub k
    simpa only [BoundedGeometryNormalChartData.chartMetric] using
      d.metric_equiv k (c k) z (hrad hz) v


omit [CompleteSpace E] in
theorem exists_finite_chart_metric_limit_subsequence
    {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd)
    (c : ι → ∀ k : Nat, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hsub : ∀ k i,
      U ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (c i k) (X.obj k).basepoint))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (ι → (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) gInf U ∧
      MapCInfConvOnCompacts U
        (fun k z i ↦ d.chartMetric (phi k) (c i (phi k)) z) gInf ∧
      ∀ z ∈ U, ∀ i v,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z i v v ∧
          gInf z i v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let gLoc : Nat → E → (ι → (E →L[Real] E →L[Real] Real)) :=
    fun k z i ↦ d.chartMetric k (c i k) z
  have hsmoothComp : ∀ k i,
      ContDiffOn Real (⊤ : ℕ∞) (fun z ↦ gLoc k z i) U := by
    intro k i
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c i k)).radius := by
      simpa only [d.radius_eq k (c i k)] using hsub k i
    simpa only [gLoc, BoundedGeometryNormalChartData.chartMetric] using
      (d.chart k (c i k)).metric_cont_diff_on (X.obj k).metric hU
        ((d.chart k (c i k)).smooth_to.mono hrad)
  have hsmooth : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (gLoc k) U :=
    fun k ↦ contDiffOn_pi.mpr (hsmoothComp k)
  have hbddComp : ∀ i, iteratedFDerivBoundsOnCompactsWithin U
      (fun k z ↦ gLoc k z i) := by
    intro i p K hK hKU
    refine ⟨d.metricC p, ?_⟩
    intro k z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (c i k)).radius := by
      simpa only [d.radius_eq k (c i k)] using hsub k i
    simpa only [gLoc, BoundedGeometryNormalChartData.chartMetric] using
      d.metric_deriv k p (c i k) z (hrad (hKU hz))
  have hbdd : iteratedFDerivBoundsOnCompactsWithin U gLoc :=
    iteratedFDerivBoundsOnCompactsWithin.pi hU hsmoothComp hbddComp
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on hU gLoc hsmooth hbdd
  refine ⟨phi, gInf, hphi, hginf, hconv, ?_⟩
  intro z hz i v
  have htendAll : Tendsto (fun k ↦ gLoc (phi k) z) atTop
      (nhds (gInf z)) :=
    tendsto_of_cInf hconv hz
  have htend : Tendsto (fun k ↦ gLoc (phi k) z i) atTop
      (nhds (gInf z i)) :=
    (tendsto_pi_nhds.mp htendAll) i
  have heval : Continuous
      (fun A : E →L[Real] E →L[Real] Real ↦ A v v) := by
    fun_prop
  have htendv : Tendsto (fun k ↦ gLoc (phi k) z i v v) atTop
      (nhds (gInf z i v v)) :=
    (heval.tendsto _).comp htend
  have hequiv : ∀ n,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gLoc (phi n) z i v v ∧
        gLoc (phi n) z i v v ≤ 2 * ‖v‖ ^ 2 := by
    intro n
    let : TopologicalSpace (X.obj (phi n)).M :=
      (X.obj (phi n)).topology
    let : ChartedSpace H (X.obj (phi n)).M :=
      (X.obj (phi n)).charted
    let : IsManifold I ∞ (X.obj (phi n)).M :=
      (X.obj (phi n)).smooth
    let : T2Space (TangentBundle I (X.obj (phi n)).M) :=
      (X.obj (phi n)).t2TangentBundle
    have hrad :
        U ⊆ Metric.ball (0 : E)
          (d.chart (phi n) (c i (phi n))).radius := by
      simpa only [d.radius_eq (phi n) (c i (phi n))] using hsub (phi n) i
    simpa only [gLoc, BoundedGeometryNormalChartData.chartMetric] using
      d.metric_equiv (phi n) (c i (phi n)) z (hrad hz) v
  exact ⟨
    ge_of_tendsto htendv
      (Filter.Eventually.of_forall fun n ↦ (hequiv n).1),
    le_of_tendsto htendv
      (Filter.Eventually.of_forall fun n ↦ (hequiv n).2)⟩

end HCGCompactness
end DifferentialGeometry
