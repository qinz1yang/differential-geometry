import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathState_CX2
import DifferentialGeometry.Topology.Manifold.OpenTarget

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A nontrivial initial inhabitant of the path state, on every regular
closed prefix. This includes histories with no surgery events. -/
theorem pathState_initial_CX2 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (hregular : H.time (H.activeStage t) < t.val)
    {y x : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) y)
    {r B : ℝ} (hr : 0 < r)
    (hbound : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) q 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) q)) ≤ B)
    (γ : ℝ → (H.stageAt t).Carrier) (hγ0 : γ 0 = y) (hγ1 : γ 1 = x)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hclip : ∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z))
    (hlen : metricPathELength (H.stageMetric (H.activeStage t) t) γ 0 1 ≤ ENNReal.ofReal (3 * r)) :
    Nonempty (PathState_CX2 H a t hat.le Y x B r (H.activeStage t)) := by
  let C := H.closedPrefixAt t hregular
  let G := C.restrictIncoming le_rfl C.lt le_rfl
  let L := C.endpointTerminalLimitMetric (H.stageAt t)
  have hfull : G.terminalRegularRegion = univ := C.terminalRegularRegion_eq_univ (H.stageAt t)
  let η : ℝ → G.terminalRegularOpen := fun z => ⟨γ z, by
    change γ z ∈ G.terminalRegularRegion
    rw [hfull]
    trivial⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η :=
    (contMDiff_subtypeVal_comp_iff G.terminalRegularOpen η).mp hγ
  have hL : L.metric = (H.stageMetric (H.activeStage t) t).restrictOpen G.terminalRegularOpen := by
    change (C.flow.base.metric t).restrictOpen G.terminalRegularOpen = _
    rw [H.closedPrefixAt_metric]
  have hcurv : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) (γ z) 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) (γ z))) ≤ B := by
    intro z hz
    apply hbound
    have hd := edistOf_le_metricPathELength (H.stageMetric (H.activeStage t) t) hz.1
      (hγ.contMDiffOn.mono (Icc_subset_Icc le_rfl hz.2))
    rw [hγ0] at hd
    exact (hd.trans ((metricPathELength_mono _ _ le_rfl hz.2).trans hlen)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 20 * r)).mpr (by linarith))
  refine ⟨{
    lower := H.activeStage_mono hat.le
    upper := le_rfl
    top := t.val
    after_lower := hat
    before_top := le_rfl
    slab := G
    terminal := L
    active := fun v hv hvt => le_antisymm (H.activeStage_mono hvt.le) (H.le_activeStage v _ hv)
    metric := fun v _ => (H.closedPrefixAt_metric t hregular v).symm
    trace := BackwardPointTrace.singleton H (H.activeStage t) x
    curve := η
    smooth := hη
    clip := fun z => Subtype.ext (hclip z)
    center := by change γ 0 = _; rw [Y.endpoint_eq]; exact hγ0
    endpoint := hγ1
    length := ?_
    terminal_bound := ?_
    above := ?_
    seams := ?_ }⟩
  · rw [hL, pathLength_restrictOpen_CX2 _ _ _ hη]
    have hηval : (Subtype.val : G.terminalRegularOpen → (H.stageAt t).Carrier) ∘ η = γ := rfl
    rw [hηval]
    simpa only [pathBudget_CX2, sub_self, mul_zero, Real.exp_zero, mul_one] using hlen
  · intro z hz
    rw [hL, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
    exact hcurv z hz
  · intro v _ hvt htv
    have h : v = t := Subtype.ext (le_antisymm hvt htv)
    subst v
    change normSq0S (H.stageMetric (H.activeStage t) t) x 4
      (metricRm04At (H.stageMetric (H.activeStage t) t) x) ≤ B ^ 2
    have hc := hcurv 1 ⟨zero_le_one, le_rfl⟩
    rw [hγ1] at hc
    exact (Real.sqrt_le_iff.mp hc).2
  · intro i hf hl
    exact (not_le_of_gt i.castSucc_lt_succ (hl.trans hf)).elim

end GC.LongTime.Ch12
