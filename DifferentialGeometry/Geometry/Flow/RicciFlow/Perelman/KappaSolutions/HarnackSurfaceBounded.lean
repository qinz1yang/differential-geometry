import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSelectedInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackTerminalJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLineContradiction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance surfaceBoundedTopology : TopologicalSpace F.M := F.topology
local instance surfaceBoundedCharted : ChartedSpace H F.M := F.charted
local instance surfaceBoundedSmooth : IsManifold I ∞ F.M := F.smooth
local instance surfaceBoundedC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance surfaceBoundedSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance surfaceBoundedT2 : T2Space F.M := F.t2
local instance surfaceBoundedTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ} [NeZero (Module.finrank ℝ E)]

private theorem surfaceBounded_selected_metric_compactness
    (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop)
    (hinj : FlowScaleInjectivityBound (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ)) :
    ∃ P : MetricCompactLimit (I := I)
        ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let C := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := C.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := C.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := C.smooth
        C.referenceMetric = C.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  let X := terminalCurvatureNormalizedFlowSeq F hK x hQ
  have hcomplete : SeqMetricComplete (I := I) (X.atZero (I := I)) :=
    (terminalCurvatureNormalizedFlowSeq_complete F hK x hQ).at_time
      (by change (0 : ℝ) ≤ 0; exact le_rfl)
  apply exists_local_pointed_metric_compactness (X.atZero (I := I)) hcomplete
    (terminalCurvatureNormalizedFlowSeq_connected F hK x hQ) hinj
  intro A hA m
  refine ⟨4 * shiLocalUniformBound 2 m 4 1,
    mul_nonneg (by norm_num) (shiLocalUniformBound_nonneg _ _ _ _), ?_⟩
  filter_upwards [eventually_terminalCurvatureNormalizedFlowSeq_curvDerivNorm_bound
    F hK hdim x hQ r hlocal hexpand hA.le] with i hi
  dsimp only
  intro y hy
  change F.M at y
  exact hi 0 le_rfl m y hy

namespace KLim

variable {F}

omit [NeZero (Module.finrank ℝ E)] in
theorem surface_terminal_bddAbove (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2) : BddAbove (Set.range (F.S.scalar 0)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  by_contra hunbounded
  obtain ⟨x, r, hQ, _hr, _hQescape, hexpand, hdist, hscaled, hlocal,
    ⟨hinj⟩, _hbase⟩ :=
    exists_harnack_terminal_blowup_with_baseInjBound F hK hdim hunbounded F.basepoint
  obtain ⟨P, hcanonical, hreference, hconnected⟩ :=
    surfaceBounded_selected_metric_compactness F hK hdim x r hQ hlocal hexpand hinj
  exact false_of_harnack_terminal_normalized_metric_compactness F hK hdim
    F.basepoint x hQ hdist hscaled P hcanonical hreference hconnected

omit [NeZero (Module.finrank ℝ E)] in
theorem surface_exists_global_scalar_bound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ C : ℝ, 0 < C ∧ PointedFlowScalarBounded (I := I) F C := by
  obtain ⟨C, hC⟩ := hK.surface_terminal_bddAbove hdim
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  apply hK.scalarBounded_of_terminal_bound
  intro x
  exact (hC (Set.mem_range_self x)).trans (le_max_right _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem surface_exists_global_curvature_bound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ C : ℝ, 0 < C ∧ PointedFlowScalarBounded (I := I) F C ∧
      PointedFlowRmNormSqBounded (I := I) F (C ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := hK.surface_exists_global_scalar_bound hdim
  refine ⟨C, hCpos, hC, ?_⟩
  intro t ht x
  have hid : F.rmNormSq (I := I) t x = F.S.scalar t x ^ 2 := by
    simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq, SolutionOn.family,
      SolutionFamily.rm04, metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using
      metricRm_normSq_eq_scalar_sq_of_finrank_two (I := I)
        (F.S.base.metric t) hdim x
  rw [hid]
  exact pow_le_pow_left₀ (hC t ht x).1 (hC t ht x).2 2

omit [NeZero (Module.finrank ℝ E)] in
theorem surface_toIsAncientKappaSolution (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2) : IsAncientKappaSolution kappa F := by
  obtain ⟨C, hC⟩ := hK.surface_terminal_bddAbove hdim
  exact hK.toIsAncientKappaSolution (fun x => hC (Set.mem_range_self x))

end KLim

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
