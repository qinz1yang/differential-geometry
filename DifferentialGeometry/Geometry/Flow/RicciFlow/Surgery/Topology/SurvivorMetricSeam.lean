import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorLocalFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness

set_option autoImplicit false
noncomputable section

open Set Filter Manifold Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

private local instance : IsManifold ThreeModel 1 E.incoming.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) :
    IsManifold ThreeModel 1 W := IsManifold.of_le (n := ∞) (by decide)


theorem exists_survivor_solution_across_event
    (G : Q.IncomingSlab s b) (hmetric : G.flow.base.metric s = E.outputMetric)
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    {c d : ℝ} (hac : a ≤ c) (hcs : c < s) (hsd : s < d) (hdb : d < b) :
    letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel
          E.incoming.terminalRegularOpen Q.Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closedOpen s b G.lt)),
      F.source = W ∧ IsSolutionOn S ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      S.base.metric s = E.terminal.metric.restrictOpen W ∧
      (∀ t (x : W) (v w : TangentSpace ThreeModel x),
        (S.base.metric t).inner x v w =
          (G.flow.base.metric t).inner (F x)
            (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) ∧
      IsSolutionOn (E.terminal.closedSolution W hcs.le) ∧
      IsSolutionOn ({ base := { metric := fun t =>
          if t ≤ s then (E.terminal.extendedMetric t).restrictOpen W else S.base.metric t } } :
        SolutionOn (I := ThreeModel) (M := W)
          (RealTimeInterval.closed c d (hcs.trans hsd).le)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × W =>
          (⟨q.2, ((if q.1 ≤ s then (E.terminal.extendedMetric q.1).restrictOpen W
            else S.base.metric q.1)).inner q.2⟩ :
            TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
              (fun x => TangentSpace ThreeModel x →L[ℝ]
                TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc c d ×ˢ (univ : Set W)) ∧
      ∀ m : ℕ, ∀ x : W,
        iteratedDerivWithin m
          (fun t => Tensor0SBundle.metricTensorField
            ((E.terminal.extendedMetric t).restrictOpen W) x) (Icc c s) s =
        iteratedDerivWithin m
          (fun t => Tensor0SBundle.metricTensorField (S.base.metric t) x) (Icc s d) s := by
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  obtain ⟨F, S, hsource, hS, hcross, hstart, hpull⟩ :=
    E.exists_survivor_local_flow G hmetric W x₀ hW
  let gL := fun t => (E.terminal.extendedMetric t).restrictOpen W
  have hleft : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, (gL q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ]
            TangentSpace ThreeModel x →L[ℝ] ℝ))) (Icc c s ×ˢ univ) :=
    E.terminal.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs
  have hright : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ]
            TangentSpace ThreeModel x →L[ℝ] ℝ))) (Icc s d ×ˢ univ) := by
    have hFsmooth : ContMDiff ThreeModel ThreeModel ∞ (fun x : W => F x.val) :=
      F.contMDiffOn.comp_contMDiff contMDiff_subtype_val (by
        intro x
        rw [hsource]
        exact x.property)
    apply metricCLMSection_jointContMDiffOn_of_chartGram_on S.base.metric (Icc s d)
    intro p i j
    apply chartGramMatrix_joint_contMDiffOn_of_pullback G.flow.base.metric (Icc s d)
      (G.smoothUpTo.jointContMDiffOn.mono (fun q hq =>
        ⟨⟨hq.1.1, hq.1.2.trans_lt hdb⟩, hq.2⟩)) S.base.metric
      (fun x : W => F x.val) hFsmooth
    intro t ht x v w
    have hd := mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
      (F : E.incoming.terminalRegularOpen → Q.Carrier) W x
    have hv := DFunLike.congr_fun hd v
    have hw := DFunLike.congr_fun hd w
    exact (hpull t x v w).trans
      (congrArg₂ (fun v w : ThreeSpace => (G.flow.base.metric t).inner (F x) v w)
        hv.symm hw.symm)
  have hpdeL : ∀ t ∈ Ioo c s, ∀ x : W, ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun u => (gL u).inner x v w) (-2 * ricciTensor (gL t) x v w) t := by
    intro t ht x v w
    exact E.terminal.extendedMetric_restrictOpen_hasDerivAt W
      ⟨hac.trans_lt ht.1, ht.2⟩ x v w
  have hpdeR : ∀ t ∈ Ioo s d, ∀ x : W, ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun u => (S.base.metric u).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) t := by
    intro t ht x v w
    have hd := metricDerivAt S hS ⟨t, ⟨ht.1, ht.2.trans hdb⟩⟩ x v w
    have hr := metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
    erw [hr] at hd
    exact hd
  have hmatch : gL s = S.base.metric s := by
    simpa only [gL, OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
      using hstart.symm
  exact ⟨F, S, hsource, hS, hcross, hstart, hpull,
    E.terminal.closedSolution_isSolutionOn W hac hcs,
    isSolutionOn_ite_of_ricciFlow gL S.base.metric hcs hsd hleft hright hpdeL hpdeR hmatch,
    metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL S.base.metric
      hcs hsd hleft hright hpdeL hpdeR hmatch,
    fun m x => metricTensorField_iteratedDerivWithin_eq_of_ricciFlow gL S.base.metric
      hcs hsd hleft hright hpdeL hpdeR hmatch m x⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
