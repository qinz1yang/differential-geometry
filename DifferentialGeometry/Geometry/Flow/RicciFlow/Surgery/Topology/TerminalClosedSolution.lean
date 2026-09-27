import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance (W : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

private local instance : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance (W : TopologicalSpace.Opens G.terminalRegularOpen) : IsManifold ThreeModel 1 W :=
  IsManifold.of_le (n := ∞) (by decide)


theorem TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, ((L.extendedMetric q.1).restrictOpen W).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc c s ×ˢ univ) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => (L.extendedMetric t).restrictOpen W) (Icc c s)
  intro p i j
  refine chartGramMatrix_joint_contMDiffOn_of_pullback L.extendedMetric (Icc c s)
    (L.extendedMetric_jointContMDiffOn hac hcs) (fun t => (L.extendedMetric t).restrictOpen W)
    Subtype.val contMDiff_subtype_val ?_ p i j
  intro t _ x v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]

theorem TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {t : ℝ} (ht : t ∈ Ioo a s) (x : W) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => ((L.extendedMetric u).restrictOpen W).inner x v w)
      (-2 * ricciTensor ((L.extendedMetric t).restrictOpen W) x v w) t := by
  have hd := L.extendedMetric_hasDerivAt ht x.val v w
  rw [Geometry.Curvature.ricciTensor_restrictOpen]
  simpa only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hd

def TerminalLimitMetric.closedSolution
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) : SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed c s hcs) where
  base := { metric := fun t => (L.extendedMetric t).restrictOpen W }

@[simp] theorem TerminalLimitMetric.closedSolution_metric
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) (t : ℝ) :
    (L.closedSolution W hcs).base.metric t = (L.extendedMetric t).restrictOpen W := rfl

theorem TerminalLimitMetric.closedSolution_before
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) {t : ℝ} (ht : t < s) :
    (L.closedSolution W hcs).base.metric t =
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).restrictOpen W := by
  rw [L.closedSolution_metric, L.extendedMetric_before ht]

theorem TerminalLimitMetric.closedSolution_terminal
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) :
    (L.closedSolution W hcs).base.metric s = L.metric.restrictOpen W := by
  rw [L.closedSolution_metric, L.extendedMetric_terminal]

theorem TerminalLimitMetric.closedSolution_isSolutionOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) : IsSolutionOn (L.closedSolution W hcs.le) := by
  apply isSolutionOn_of_joint_metric (RealTimeInterval.closed c s hcs.le)
    (uniqueDiffOn_Icc hcs) (fun t => (L.extendedMetric t).restrictOpen W)
    (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs)
  intro t ht x v w
  exact (L.extendedMetric_restrictOpen_hasDerivAt W
    ⟨hac.trans_lt ht.1, ht.2⟩ x v w).hasDerivWithinAt

theorem TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c t : ℝ} (hac : a ≤ c) (hcs : c < s) (ht : t ∈ Icc c s)
    (x : W) (v w : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun u => ((L.extendedMetric u).restrictOpen W).inner x v w)
      (-2 * ricciTensor ((L.extendedMetric t).restrictOpen W) x v w) (Icc c s) t := by
  have hd := metric_inner_hasDerivWithinAt_on_closed_interval (L.closedSolution W hcs.le)
    (L.closedSolution_isSolutionOn W hac hcs) hcs Subset.rfl Subset.rfl ht x v w
  have hr := metricRicciAt_apply_eq_ricciTensor ((L.extendedMetric t).restrictOpen W) x v w
  dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, closedSolution] at hd
  erw [hr] at hd
  exact hd


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section

open Set Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (p : W) :
    ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (fun y : ThreeSpace => chartGramOp (I := ThreeModel) (L.closedSolution W hcs.le).family p (z.1, y)) z.2)
      (Icc c s ×ˢ interior (extChartAt ThreeModel p).target) := by
  exact (L.closedSolution W hcs.le).chartGram_spatial_fderiv_continuousOn_of_joint_metric
    (Icc c s) (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs) p

theorem TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (p : W) :
    ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) p
        ((L.closedSolution W hcs.le).scalar z.1)) z.2)
      (Icc c s ×ˢ interior (extChartAt ThreeModel p).target) := by
  exact (L.closedSolution W hcs.le).scalarOnE_spatial_fderiv_continuousOn_of_joint_metric
    (Icc c s) (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs) p

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end
