import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import Mathlib.Topology.ContinuousMap.Ordered
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.ManifoldAbsolutelyContinuous
import DifferentialGeometry.Geometry.Metric.Comparison.CurveCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel
import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Compactness.LocallyCompact
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.IntervalLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import Mathlib.Topology.Sequences

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem exists_mapsTo_initial_interval
    {M : Type*} [TopologicalSpace M] {α : ℝ → M} {u v : ℝ}
    (huv : u < v) (hα : ContinuousOn α (Icc u v))
    (U : TopologicalSpace.Opens M) (hU : α u ∈ U) :
    ∃ d ∈ Ioo u v, MapsTo α (Icc u d) U := by
  have hn := (hα u ⟨le_rfl, huv.le⟩).preimage_mem_nhdsWithin (U.isOpen.mem_nhds hU)
  rw [nhdsWithin_Icc_eq_nhdsGE huv] at hn
  obtain ⟨e, hue, he⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hn
  obtain ⟨d, hud, hde⟩ := exists_between (lt_min hue huv)
  refine ⟨d, ⟨hud, hde.trans_le (min_le_right _ _)⟩, ?_⟩
  intro r hr
  exact he ⟨hr.1, hr.2.trans (hde.le.trans (min_le_left _ _))⟩

private theorem closedSolution_metric_eq_localPull
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c t : ℝ} (hcs : c ≤ s) (ht : t < s) :
    (L.closedSolution W hcs).base.metric t =
      localPullMetric (G.flow.base.metric t) (fun z : W => z.val.val)
        (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen)
          (isLocalDiffeomorph_subtype_val (I := ThreeModel) W)) := by
  rw [L.closedSolution_before W hcs ht,
    ← localPullMetric_subtype_val, ← localPullMetric_subtype_val,
    localPullMetric_comp]
  rfl

private theorem lagrangian_eq_of_eventuallyEq
    (T : ℝ) {α β : ℝ → P.Carrier} {r : ℝ} (heq : α =ᶠ[𝓝 r] β) :
    lRegularizedLagrangian G.flow T α r = lRegularizedLagrangian G.flow T β r := by
  have hval : α r = β r := heq.self_of_nhds
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
  have hvel : lVelocity (I := ThreeModel) α r = lVelocity (I := ThreeModel) β r := by
    exact congrArg (fun L => L (1 : ℝ)) hd
  simp only [lRegularizedLagrangian]
  rw [hval, hvel]

theorem TerminalLimitMetric.exists_absolutelyContinuous_closedSolution_collar
    (L : G.TerminalLimitMetric) {T u v : ℝ} {α : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hterminal : α u ∈ G.terminalRegularOpen) :
    ∃ d ∈ Ioo u v, ∃ hds : T - d ^ 2 < s,
      let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
      ∃ η : ℝ → W,
        Manifold.absolutelyContinuousOnInterval ThreeModel η u d ∧
        EqOn (fun r => (η r).val.val) α (Icc u d) ∧
        a ≤ T - d ^ 2 ∧
        IsSolutionOn (L.closedSolution W hds.le) ∧
        (∀ r ∈ Icc u d, T - r ^ 2 ∈ (RealTimeInterval.closed (T - d ^ 2) s hds.le).carrier) ∧
        (lRegularizedLagrangian (L.closedSolution W hds.le) T η =ᵐ[volume.restrict (Icc u d)]
          lRegularizedLagrangian G.flow T α) ∧
        lRegularizedAction (L.closedSolution W hds.le) T η u d =
          lRegularizedAction G.flow T α u d ∧
        (IntervalIntegrable (lRegularizedLagrangian (L.closedSolution W hds.le) T η) volume u d ↔
          IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u d) ∧
        (IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v →
          IntervalIntegrable (lRegularizedLagrangian (L.closedSolution W hds.le) T η) volume u d) := by
  obtain ⟨d, hd, hmaps⟩ := exists_mapsTo_initial_interval huv
    (by simpa only [uIcc_of_le huv.le] using hα.1) G.terminalRegularOpen hterminal
  have hd0 : 0 < d := hu.trans_lt hd.1
  have hds : T - d ^ 2 < s := by nlinarith [sq_lt_sq₀ hu hd0.le |>.2 hd.1]
  have had : a ≤ T - d ^ 2 := by nlinarith [sq_le_sq₀ hd0.le (hd0.le.trans hd.2.le) |>.2 hd.2.le]
  have hsub : uIcc u d ⊆ uIcc u v := by
    rw [uIcc_of_le hd.1.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc le_rfl hd.2.le
  have hαd := Manifold.absolutelyContinuousOnInterval_mono hα hsub
  obtain ⟨β, hβ, hβeq⟩ := Manifold.exists_absolutelyContinuousOnInterval_openSubtype
    G.terminalRegularOpen hαd (by simpa only [uIcc_of_le hd.1.le] using hmaps)
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  obtain ⟨η, hη, hηeq⟩ := Manifold.exists_absolutelyContinuousOnInterval_openSubtype W hβ
    (fun _ _ => mem_univ _)
  have hproj : EqOn (fun r => (η r).val.val) α (Icc u d) := by
    intro r hr
    have hr' : r ∈ uIcc u d := by simpa only [uIcc_of_le hd.1.le] using hr
    exact (congrArg Subtype.val (hηeq hr')).trans (hβeq hr')
  let : IsManifold ThreeModel 1 W := IsManifold.of_le (n := ∞) (by decide)
  have hdiff := Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hη
  rw [uIcc_of_le hd.1.le, ← restrict_Ioo_eq_restrict_Icc] at hdiff
  have hlag : lRegularizedLagrangian (L.closedSolution W hds.le) T η =ᵐ[volume.restrict (Icc u d)]
      lRegularizedLagrangian G.flow T α := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with r hdr hr
    have hr0 : 0 ≤ r := hu.trans hr.1.le
    have htr : T - r ^ 2 < s := by nlinarith [sq_lt_sq₀ hu hr0 |>.2 hr.1]
    let p : W → P.Carrier := fun z => z.val.val
    let hp := isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen)
      (isLocalDiffeomorph_subtype_val (I := ThreeModel) W)
    have hm : (L.closedSolution W hds.le).base.metric (T - r ^ 2) =
        (G.flow.localPullback p hp).base.metric (T - r ^ 2) :=
      closedSolution_metric_eq_localPull L W hds.le htr
    calc
      _ = lRegularizedLagrangian (G.flow.localPullback p hp) T η r := by
        unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
        rw [hm]
      _ = lRegularizedLagrangian G.flow T (p ∘ η) r :=
        lRegularizedLagrangian_localPullback G.flow p hp T hdr
      _ = _ := lagrangian_eq_of_eventuallyEq T (by
        filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
        exact hproj ⟨hx.1.le, hx.2.le⟩)
  have hlag' : lRegularizedLagrangian (L.closedSolution W hds.le) T η =ᵐ[volume.restrict (Ι u d)]
      lRegularizedLagrangian G.flow T α := by
    rw [uIoc_of_le hd.1.le]
    exact ae_mono (Measure.restrict_mono_set volume Ioc_subset_Icc_self) hlag
  refine ⟨d, hd, hds, η, hη, hproj, had, L.closedSolution_isSolutionOn W had hds,
    ?_, hlag, ?_, intervalIntegrable_congr_ae hlag', ?_⟩
  · intro r hr
    change T - d ^ 2 ≤ T - r ^ 2 ∧ T - r ^ 2 ≤ s
    constructor
    · nlinarith [sq_le_sq₀ (hu.trans hr.1) hd0.le |>.2 hr.2]
    · nlinarith [sq_le_sq₀ hu (hu.trans hr.1) |>.2 hr.1]
  · exact intervalIntegral.integral_congr_ae_restrict hlag'
  · intro hint
    exact (intervalIntegrable_congr_ae hlag').mpr (hint.mono_set hsub)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem TerminalLimitMetric.exists_contMDiff_action_lt_of_terminal_curve
    (L : G.TerminalLimitMetric) {T u v : ℝ} {α : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hterminal : α u ∈ G.terminalRegularOpen)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → P.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧ β u = α u ∧ β v = α v ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T β) volume u v ∧
      lRegularizedAction G.flow T β u v < lRegularizedAction G.flow T α u v + ε := by
  obtain ⟨d, hd, hds, η, hη, hproj, had, hS, hclock, _, haction, _, hηint⟩ :=
    L.exists_absolutelyContinuous_closedSolution_collar hu huv hTu ha hα hterminal
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W hds.le
  let p : W → P.Carrier := fun z => z.val.val
  have hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ p :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen)
      (isLocalDiffeomorph_subtype_val (I := ThreeModel) W)
  let : SecondCountableTopology P.Carrier := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : SecondCountableTopology G.terminalRegularOpen := inferInstance
  let : SecondCountableTopology W := inferInstance
  let : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace ThreeSpace W
  let : SigmaCompactSpace W := inferInstance
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace ThreeModel W
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  obtain ⟨η₁, hη₁, hη₁u, hη₁d, hη₁act, _, hη₁flat⟩ :=
    exists_lRegularizedAction_c1_lt_const_nhds_endpoints S hS.smoothMetric ⟨hS.scalarCont⟩ T u d hd.1.le
      η hη (hηint hint) hclock (half_pos hε)
  have hd0 : 0 < d := hu.trans_lt hd.1
  have htailClock (r : ℝ) (hr : r ∈ Icc d v) : T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s G.lt).carrier := by
    change a ≤ T - r ^ 2 ∧ T - r ^ 2 < s
    constructor
    · nlinarith [sq_le_sq₀ (hd0.le.trans hr.1) (hd0.le.trans hd.2.le) |>.2 hr.2]
    · nlinarith [sq_lt_sq₀ hu (hd0.le.trans hr.1) |>.2 (hd.1.trans_le hr.1)]
  have hsubTail : uIcc d v ⊆ uIcc u v := by
    rw [uIcc_of_le hd.2.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc hd.1.le le_rfl
  have htailAC := Manifold.absolutelyContinuousOnInterval_mono hα hsubTail
  have htailInt := hint.mono_set hsubTail
  obtain ⟨α₂, hα₂, hα₂d, hα₂v, hα₂act, hα₂flat, _⟩ :=
    exists_lRegularizedAction_c1_lt_const_nhds_endpoints G.flow G.equation.smoothMetric ⟨G.equation.scalarCont⟩
      T d v hd.2.le α htailAC htailInt htailClock (half_pos hε)
  let α₁ := p ∘ η₁
  have hα₁ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₁ :=
    (hp.contMDiff.of_le (by norm_num)).comp hη₁
  have hmatch : α₁ =ᶠ[𝓝 d] α₂ := by
    have hleft : α₁ =ᶠ[𝓝 d] fun _ => α d := by
      filter_upwards [hη₁flat] with r hr
      change p (η₁ r) = α d
      rw [hr]
      exact hproj ⟨hd.1.le, le_rfl⟩
    exact hleft.trans hα₂flat.symm
  let β := (Iic d).piecewise α₁ α₂
  have hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β := hα₁.piecewise_Iic hα₂ hmatch
  have hlag : EqOn (lRegularizedLagrangian S T η₁) (lRegularizedLagrangian G.flow T α₁) (uIoo u d) := by
    intro r hr
    rw [uIoo_of_le hd.1.le] at hr
    have htr : T - r ^ 2 < s := by nlinarith [sq_lt_sq₀ hu (hu.trans hr.1.le) |>.2 hr.1]
    have hm : S.base.metric (T - r ^ 2) = localPullMetric (G.flow.base.metric (T - r ^ 2)) p hp := by
      dsimp only [S]
      rw [L.closedSolution_before W hds.le htr, ← localPullMetric_subtype_val,
        ← localPullMetric_subtype_val, localPullMetric_comp]
      rfl
    have hh : lRegularizedLagrangian S T η₁ r = lRegularizedLagrangian (G.flow.localPullback p hp) T η₁ r := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
      rfl
    exact hh.trans (lRegularizedLagrangian_localPullback G.flow p hp T (hη₁.mdifferentiable one_ne_zero r))
  have hη₁int : IntervalIntegrable (lRegularizedLagrangian S T η₁) volume u d := by
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS η₁ hη₁
    exact (hc.comp (f := fun r : ℝ => (T, r)) (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc hd.1.le
  have hα₁int := hη₁int.congr_uIoo hlag
  have hact₁ : lRegularizedAction S T η₁ u d = lRegularizedAction G.flow T α₁ u d := intervalIntegral.integral_congr_uIoo hlag
  have hα₂int : IntervalIntegrable (lRegularizedLagrangian G.flow T α₂) volume d v := by
    have hc := lRegularizedLagrangian_continuousOn_carrier G.flow G.equation α₂ hα₂
    exact (hc.comp (f := fun r : ℝ => (T, r)) (continuous_const.prodMk continuous_id).continuousOn htailClock).intervalIntegrable_of_Icc hd.2.le
  have hβleft : EqOn β α₁ (Icc u d) := fun r hr => ite_eq_left hr.2
  have hβright : EqOn β α₂ (Icc d v) := by
    intro r hr
    rcases hr.1.eq_or_lt with heq | hlt
    · subst r
      exact ((Iic d).piecewise_eq_of_mem α₁ α₂ (by simp : d ∈ Iic d)).trans hmatch.self_of_nhds
    · exact ite_eq_right (not_le.mpr hlt)
  have hβLagLeft : EqOn (lRegularizedLagrangian G.flow T β) (lRegularizedLagrangian G.flow T α₁) (uIoo u d) := by
    intro r hr
    rw [uIoo_of_le hd.1.le] at hr
    have hn : β =ᶠ[𝓝 r] α₁ := by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht; exact hβleft (Ioo_subset_Icc_self ht)
    exact lagrangian_eq_of_eventuallyEq T hn
  have hβLagRight : EqOn (lRegularizedLagrangian G.flow T β) (lRegularizedLagrangian G.flow T α₂) (uIoo d v) := by
    intro r hr
    rw [uIoo_of_le hd.2.le] at hr
    have hn : β =ᶠ[𝓝 r] α₂ := by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht; exact hβright (Ioo_subset_Icc_self ht)
    exact lagrangian_eq_of_eventuallyEq T hn
  have hβintLeft := hα₁int.congr_uIoo hβLagLeft.symm
  have hβintRight := hα₂int.congr_uIoo hβLagRight.symm
  refine ⟨β, hβ, (hβleft ⟨le_rfl, hd.1.le⟩).trans ?_, (hβright ⟨hd.2.le, le_rfl⟩).trans hα₂v,
    hβintLeft.trans hβintRight, ?_⟩
  · change p (η₁ u) = α u
    rw [hη₁u]
    exact hproj ⟨le_rfl, hd.1.le⟩
  · have hleftAct : lRegularizedAction G.flow T β u d = lRegularizedAction G.flow T α₁ u d :=
      intervalIntegral.integral_congr_uIoo hβLagLeft
    have hrightAct : lRegularizedAction G.flow T β d v = lRegularizedAction G.flow T α₂ d v :=
      intervalIntegral.integral_congr_uIoo hβLagRight
    rw [← lRegularizedAction_add G.flow T β u d v hβintLeft hβintRight, hleftAct, hrightAct]
    have hsplit := lRegularizedAction_add G.flow T α u d v (hint.mono_set (by
      rw [uIcc_of_le hd.1.le, uIcc_of_le huv.le]; exact Icc_subset_Icc le_rfl hd.2.le)) htailInt
    rw [haction, hact₁] at hη₁act
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem TerminalLimitMetric.exists_lRegularizedMinC1_of_compact_action_sublevel
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (T : ℝ) {u v : ℝ} (huv : u < v)
    (hclock : ∀ r ∈ Icc u v, T - r ^ 2 ∈ Icc c s)
    (hregular : ∀ r ∈ Ioo u v, T - r ^ 2 ∈ Ioo c s)
    (x y : W) (α₀ : ℝ → W) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀)
    (hstart : α₀ u = x) (hend : α₀ v = y)
    (Q : Set W) (hQ : IsCompact Q)
    (hconf : ∀ α : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → α u = x → α v = y →
      lRegularizedAction (L.closedSolution W hcs.le) T α u v ≤
        lRegularizedAction (L.closedSolution W hcs.le) T α₀ u v → MapsTo α (Icc u v) Q) :
    ∃ η : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧ η v = y ∧
      MapsTo η (Icc u v) Q ∧
      ∀ δ : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ → δ u = x → δ v = y →
        lRegularizedAction (L.closedSolution W hcs.le) T η u v ≤
          lRegularizedAction (L.closedSolution W hcs.le) T δ u v := by
  let : SigmaCompactSpace G.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace W :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace ThreeModel W
  exact exists_lRegularizedMinC1_of_compact_action_sublevel_of_spatial_derivatives
    (L.closedSolution W hcs.le) (L.closedSolution_isSolutionOn W hac hcs) T huv
    (Icc c s) Subset.rfl hclock hregular
    (L.closedSolution_chartGram_spatial_fderiv_continuousOn W hac hcs)
    (L.closedSolution_scalarOnE_spatial_fderiv_continuousOn W hac hcs)
    x y α₀ hα₀ hstart hend Q hQ hconf

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_pos_frontier_distance_of_compact
    (g : SmoothRiemannianMetric ThreeModel P.Carrier)
    (K₀ K : Set P.Carrier) (hK₀ : IsCompact K₀) (hinside : K₀ ⊆ interior K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K₀, ∀ y ∈ frontier K,
      ENNReal.ofReal r ≤ riemannianEDistOf g x y := by
  let _ : LocallyCompactSpace P.Carrier := Manifold.locallyCompact_of_finiteDimensional (M := P.Carrier) ThreeModel
  let _ : RegularSpace P.Carrier := inferInstance
  let _ : RiemannianBundle (TangentSpace ThreeModel : P.Carrier → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace ThreeModel : P.Carrier → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace P.Carrier := EMetricSpace.ofRiemannianMetric ThreeModel P.Carrier
  have hdis : Disjoint K₀ (frontier K) := Set.disjoint_left.mpr fun x hx hy => hy.2 (hinside hx)
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hK₀ isClosed_frontier hdis
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro x hx y hy
  change ENNReal.ofReal (r : ℝ) ≤ edist x y
  simpa only [ENNReal.ofReal_coe_nnreal] using (hsep x hx y hy).le

private theorem TerminalLimitMetric.exists_uniform_terminal_compact_metric_buffer
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    {T r₀ vmax : ℝ} (hr₀ : 0 ≤ r₀) (hrv : r₀ < vmax)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - vmax ^ 2) :
    ∃ K : Set P.Carrier, IsCompact K ∧ K ⊆ G.terminalRegularOpen ∧
      ((Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀) ⊆ interior K ∧
      ∃ μ r d : ℝ, 0 < μ ∧ 0 < r ∧ 0 < d ∧ r₀ + d ≤ vmax ∧
        (∀ x ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀,
          ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf (G.flow.base.metric a) x y) ∧
        ∀ v ∈ Ioc r₀ (r₀ + d), ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
          μ * (G.flow.base.metric a).inner z w w ≤ (G.flow.base.metric (T - v ^ 2)).inner z w w := by
  let C₀ := (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀
  have hC₀ : IsCompact C₀ := hK₀.image continuous_subtype_val
  let _ : LocallyCompactSpace P.Carrier := Manifold.locallyCompact_of_finiteDimensional (M := P.Carrier) ThreeModel
  obtain ⟨K, hK, hinside, hKreg⟩ := exists_compact_between hC₀ G.terminalRegularOpen.isOpen
    (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  obtain ⟨r, hr, hfront⟩ := exists_pos_frontier_distance_of_compact (G.flow.base.metric a) C₀ K hC₀ hinside
  let b := (r₀ + vmax) / 2
  have hrb : r₀ < b := by dsimp [b]; linarith
  have hbmax : b < vmax := by dsimp [b]; linarith
  have hb : 0 < b := hr₀.trans_lt hrb
  let c := T - b ^ 2
  have hac : a ≤ c := by
    have hs := pow_le_pow_left₀ hb.le hbmax.le 2
    exact hpast.trans (sub_le_sub_left hs T)
  have hcs : c < s := by
    have hs := (sq_lt_sq₀ hr₀ hb.le).mpr hrb
    dsimp [c]
    linarith
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W hcs.le
  let f : W → P.Carrier := fun z => z.val.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val G.terminalRegularOpen) (isLocalDiffeomorph_subtype_val W)
  have hinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hS := L.closedSolution_isSolutionOn W hac hcs
  have hKrange : K ⊆ range f := by
    intro z hz
    exact ⟨⟨⟨z, hKreg hz⟩, mem_univ _⟩, rfl⟩
  have hmetric : ∀ t ∈ Ico c s, S.base.metric t = localPullMetric (G.flow.base.metric t) f hf := by
    intro t ht
    exact closedSolution_metric_eq_localPull L W hcs.le ht.2
  obtain ⟨μ, hμ, hbound⟩ := hS.smoothMetric.metric_lower_on_compact_of_localPullMetric
    G.flow.base.metric f hf hinj isCompact_Icc Subset.rfl Ico_subset_Icc_self hK hKrange
      (G.flow.base.metric a) hmetric
  refine ⟨K, hK, hKreg, hinside, μ, r, b - r₀, hμ, hr, sub_pos.mpr hrb,
    by linarith, hfront, ?_⟩
  intro v hv z hz w
  apply hbound (T - v ^ 2) ?_ z hz w
  have hvb : v ≤ b := by linarith [hv.2]
  have hv0 : 0 ≤ v := hr₀.trans hv.1.le
  have hs := pow_le_pow_left₀ hv0 hvb 2
  have hstrict := (sq_lt_sq₀ hr₀ hv0).mpr hv.1
  exact ⟨sub_le_sub_left hs T, by linarith⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem TerminalLimitMetric.exists_uniform_initial_interval_mapsTo_compact_of_action_le
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    {T r₀ vmax A B : ℝ} (hr₀ : 0 ≤ r₀) (hrv : r₀ < vmax)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - vmax ^ 2) (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ico a s, ∀ z : P.Carrier, -B ≤ G.flow.scalar t z) :
    ∃ K : Set P.Carrier, IsCompact K ∧ K ⊆ G.terminalRegularOpen ∧
      ((Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀) ⊆ interior K ∧
      ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ r₀ + δ ≤ vmax ∧
        (∀ p ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀,
          ∀ q ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf (G.flow.base.metric a) p q) ∧
        ∀ (b : ℝ), r₀ < b → b ≤ vmax → ∀ α : ℝ → P.Carrier,
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc r₀ b) →
          α r₀ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀ →
          IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume r₀ b →
          lRegularizedAction G.flow T α r₀ b ≤ A →
          MapsTo α (Icc r₀ (min b (r₀ + δ))) K := by
  obtain ⟨K, hK, hKreg, hinside, μ, r, d, hμ, hr, hd, hrd, hfront, hmetric⟩ :=
    L.exists_uniform_terminal_compact_metric_buffer K₀ hK₀ hr₀ hrv hterminal hpast
  have hvmax : 0 < vmax := hr₀.trans_lt hrv
  let C := max (A + 2 * B * vmax ^ 3) 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right (A + 2 * B * vmax ^ 3) 0]
  have hAC : A + 2 * B * vmax ^ 3 < C := by dsimp [C]; linarith [le_max_left (A + 2 * B * vmax ^ 3) 0]
  let δ := min d (μ * r ^ 2 / (4 * C))
  have hδ : 0 < δ := lt_min hd (div_pos (mul_pos hμ (sq_pos_of_pos hr)) (by positivity))
  have hδd : δ ≤ d := min_le_left _ _
  have hδsmall : 4 * C * δ ≤ μ * r ^ 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (min_le_right d (μ * r ^ 2 / (4 * C)))
    simpa only [δ, mul_comm] using hh
  refine ⟨K, hK, hKreg, hinside, r, δ, hr, hδ, by linarith, hfront, ?_⟩
  intro b hrb hbmax α hα hstart hint hact
  let e := min b (r₀ + δ)
  have hre : r₀ < e := lt_min hrb (by linarith)
  have heb : e ≤ b := min_le_left _ _
  have heδ : e - r₀ ≤ δ := by have := min_le_right b (r₀ + δ); dsimp [e]; linarith
  have hemax : e ≤ vmax := heb.trans hbmax
  have hfloor : ∀ q ∈ Ioo r₀ b, -B ≤ G.flow.scalar (T - q ^ 2) (α q) := by
    intro q hq
    have hq0 : 0 ≤ q := hr₀.trans hq.1.le
    have hqmax : q ≤ vmax := hq.2.le.trans hbmax
    have hsq := pow_le_pow_left₀ hq0 hqmax 2
    have hstrict := (sq_lt_sq₀ hr₀ hq0).mpr hq.1
    exact hscalar (T - q ^ 2) ⟨hpast.trans (sub_le_sub_left hsq T), by linarith⟩ (α q)
  have hprefix := lRegularizedAction_prefix_le_of_action_le G.flow T α hr₀ hre.le heb hbmax hB
    (fun q hq => hfloor q ⟨hre.le.trans_lt hq.1, hq.2⟩) hint hact
  have hintPrefix := hint.mono_set (by
    rw [uIcc_of_le hre.le, uIcc_of_le hrb.le]
    exact Icc_subset_Icc le_rfl heb)
  by_contra hnot
  have hlower := lRegularizedAction_ge_of_leaves_closed_set G.flow T α hr₀ hemax hμ.le hB hr.le
    (G.flow.base.metric a) hK.isClosed (hα.mono (Icc_subset_Icc le_rfl heb)) (hinside hstart)
    (fun q hq hqK => hmetric q ⟨hq.1, by linarith [hq.2, heδ, hδd]⟩ (α q) hqK (lVelocity α q))
    (fun q hq => hfloor q ⟨hq.1, hq.2.trans_le heb⟩) hintPrefix (hfront (α r₀) hstart) hnot
  have hquot : μ * r ^ 2 / (2 * (e - r₀)) ≤ A + 2 * B * vmax ^ 2 * (b - r₀) := by linarith
  have hlength : b - r₀ ≤ vmax := by linarith
  have hbudget : A + 2 * B * vmax ^ 2 * (b - r₀) ≤ A + 2 * B * vmax ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hlength (by positivity : 0 ≤ 2 * B * vmax ^ 2)]
  have hsmall : μ * r ^ 2 < C * (2 * (e - r₀)) :=
    (div_lt_iff₀ (by linarith : 0 < 2 * (e - r₀))).mp (hquot.trans_lt (hbudget.trans_lt hAC))
  have hshort : C * (2 * (e - r₀)) ≤ 2 * C * δ := by nlinarith
  nlinarith [mul_pos hC hδ]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem TerminalLimitMetric.exists_uniform_curveEnergy_bound_of_action_le
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    (g : SmoothRiemannianMetric ThreeModel P.Carrier)
    {T r₀ vmax A B : ℝ} (hr₀ : 0 ≤ r₀) (hrv : r₀ < vmax)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - vmax ^ 2) (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ico a s, ∀ z : P.Carrier, -B ≤ G.flow.scalar t z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, r₀ < b → b ≤ vmax → ∀ α : ℝ → P.Carrier,
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc r₀ b) →
      α r₀ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀ →
      IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume r₀ b →
      lRegularizedAction G.flow T α r₀ b ≤ A → curveEnergy g α r₀ b ≤ C := by
  obtain ⟨K, hK, hKreg, _, r, δ, _, hδ, hδmax, _, htrap⟩ :=
    L.exists_uniform_initial_interval_mapsTo_compact_of_action_le K₀ hK₀ hr₀ hrv hterminal hpast hB hscalar
  let c := T - (r₀ + δ) ^ 2
  have hac : a ≤ c := hpast.trans (sub_le_sub_left (pow_le_pow_left₀ (by linarith) hδmax 2) T)
  have hcs : c < s := by
    have hsq := (sq_lt_sq₀ hr₀ (show 0 ≤ r₀ + δ by linarith)).mpr (by linarith : r₀ < r₀ + δ)
    dsimp only [c]
    linarith
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W hcs.le
  let f : W → P.Carrier := fun z => z.val.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val G.terminalRegularOpen) (isLocalDiffeomorph_subtype_val W)
  have hinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hS := L.closedSolution_isSolutionOn W hac hcs
  have hKrange : K ⊆ range f := by
    intro z hz
    exact ⟨⟨⟨z, hKreg hz⟩, mem_univ _⟩, rfl⟩
  have hmetric : ∀ t ∈ Ico c s, S.base.metric t = localPullMetric (G.flow.base.metric t) f hf :=
    fun t ht => closedSolution_metric_eq_localPull L W hcs.le ht.2
  obtain ⟨μ₀, hμ₀, hnear⟩ := hS.smoothMetric.metric_lower_on_compact_of_localPullMetric
    G.flow.base.metric f hf hinj isCompact_Icc Subset.rfl Ico_subset_Icc_self hK hKrange g hmetric
  obtain ⟨μ₁, hμ₁, hearly⟩ := G.equation.smoothMetric.metric_lower_on_compact_time
    (show IsCompact (Icc a c) from isCompact_Icc)
    (fun t ht => show t ∈ (RealTimeInterval.closedOpen a s G.lt).carrier from ⟨ht.1, ht.2.trans_lt hcs⟩)
    (show IsCompact (univ : Set P.Carrier) from isCompact_univ) g
  let μ := min μ₀ μ₁
  have hμ : 0 < μ := lt_min hμ₀ hμ₁
  let C := 2 * max (A + 2 * B * vmax ^ 3) 0 / μ
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro b hrb hbmax α hα hstart hint hact
  have hstay := htrap b hrb hbmax α hα hstart hint hact
  have hcompare : ∀ q ∈ Ioo r₀ b,
      μ * g.inner (α q) (lVelocity α q) (lVelocity α q) ≤
        (G.flow.base.metric (T - q ^ 2)).inner (α q) (lVelocity α q) (lVelocity α q) := by
    intro q hq
    have hq0 : 0 ≤ q := hr₀.trans hq.1.le
    have htime : T - q ^ 2 ∈ Ico a s := by
      have hsq := pow_le_pow_left₀ hq0 (hq.2.le.trans hbmax) 2
      have hstrict := (sq_lt_sq₀ hr₀ hq0).mpr hq.1
      exact ⟨hpast.trans (sub_le_sub_left hsq T), by linarith⟩
    have hg := metric_inner_self_nonneg g (α q) (lVelocity α q)
    by_cases hqδ : q ≤ r₀ + δ
    · have hqK := hstay ⟨hq.1.le, le_min hq.2.le hqδ⟩
      have hsq := pow_le_pow_left₀ hq0 hqδ 2
      have hn := hnear (T - q ^ 2) ⟨sub_le_sub_left hsq T, htime.2⟩ (α q) hqK (lVelocity α q)
      exact (mul_le_mul_of_nonneg_right (min_le_left μ₀ μ₁) hg).trans hn
    · have hδq : r₀ + δ ≤ q := (lt_of_not_ge hqδ).le
      have hsq := pow_le_pow_left₀ (show 0 ≤ r₀ + δ by linarith) hδq 2
      have he := hearly (T - q ^ 2) ⟨htime.1, sub_le_sub_left hsq T⟩ (α q) (mem_univ _) (lVelocity α q)
      exact (mul_le_mul_of_nonneg_right (min_le_right μ₀ μ₁) hg).trans he
  have hpotential : ∀ q ∈ Ioo r₀ b,
      -(2 * B * vmax ^ 2) ≤ 2 * q ^ 2 * G.flow.scalar (T - q ^ 2) (α q) := by
    intro q hq
    have hq0 := hr₀.trans hq.1.le
    have hsq := pow_le_pow_left₀ hq0 (hq.2.le.trans hbmax) 2
    have hstrict := (sq_lt_sq₀ hr₀ hq0).mpr hq.1
    have hs := hscalar (T - q ^ 2) ⟨hpast.trans (sub_le_sub_left hsq T), by linarith⟩ (α q)
    have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * q ^ 2)
    have hBsq := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * B)
    nlinarith
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hα
  have href : IntervalIntegrable (fun q => g.inner (α q) (lVelocity α q) (lVelocity α q)) volume r₀ b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hrb.le, lVelocity] using hE
  have hcoerc := lRegularizedAction_ge_reference_energy_add_constant_of_interior_bounds G.flow T α g r₀ b
    μ (-(2 * B * vmax ^ 2)) hrb.le hcompare hpotential href hint
  rw [intervalIntegral.integral_const_mul] at hcoerc
  change μ / 2 * curveEnergy g α r₀ b + (-(2 * B * vmax ^ 2)) * (b - r₀) ≤ _ at hcoerc
  have hlen : b - r₀ ≤ vmax := by linarith
  have hbound := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ 2 * B * vmax ^ 2)
  apply (le_div_iff₀ hμ).mpr
  nlinarith [le_max_left (A + 2 * B * vmax ^ 3) 0]


theorem TerminalLimitMetric.exists_tendsto_subseq_of_action_le
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    {T r₀ b A B : ℝ} (hr₀ : 0 ≤ r₀) (hrb : r₀ < b)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - b ^ 2) (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ico a s, ∀ z : P.Carrier, -B ≤ G.flow.scalar t z)
    (α : ℕ → ℝ → P.Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc r₀ b))
    (hstart : ∀ n, α n r₀ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀)
    (hint : ∀ n, IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume r₀ b)
    (hact : ∀ n, lRegularizedAction G.flow T (α n) r₀ b ≤ A) :
    ∃ (φ : ℕ → ℕ) (γ : C(Icc r₀ b, P.Carrier)), StrictMono φ ∧
      Tendsto (fun n => (⟨fun r : Icc r₀ b => α (φ n) r.val,
        (hα (φ n)).continuousOn.domRestrict⟩ : C(Icc r₀ b, P.Carrier))) atTop (𝓝 γ) ∧
      γ ⟨r₀, le_rfl, hrb.le⟩ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀ := by
  let : _root_.TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := _root_.TopologicalSpace.metrizableSpaceMetric P.Carrier
  obtain ⟨C, _, hC⟩ := L.exists_uniform_curveEnergy_bound_of_action_le K₀ hK₀ (G.flow.base.metric a)
    hr₀ hrb hterminal hpast hB hscalar
  obtain ⟨φ, γ, hφ, hconv⟩ := exists_strictMono_tendstoUniformly_of_curveEnergy_le
    (G.flow.base.metric a) r₀ b C α hα
    (fun n => hC b hrb le_rfl (α n) (hα n) (hstart n) (hint n) (hact n))
    univ isCompact_univ (fun _ _ => mem_univ _)
  refine ⟨φ, γ, hφ, ContinuousMap.tendsto_iff_tendstoUniformly.mpr hconv, ?_⟩
  exact (hK₀.image continuous_subtype_val).isClosed.mem_of_tendsto
    (hconv.tendsto_at ⟨r₀, le_rfl, hrb.le⟩) (Eventually.of_forall fun n => hstart (φ n))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology Interval
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem TerminalLimitMetric.lagrangian_closedSolution_eq_of_projection
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c T r₀ d : ℝ} (hcs : c ≤ s) (hr₀ : 0 ≤ r₀)
    (hterminal : T - r₀ ^ 2 = s) (β : ℝ → W) (α : ℝ → P.Carrier)
    (hproj : EqOn (fun r => (β r).val.val) α (Icc r₀ d)) :
    EqOn (lRegularizedLagrangian (L.closedSolution W hcs) T β)
      (lRegularizedLagrangian G.flow T α) (Ioo r₀ d) := by
  intro r hr
  have hrpos : 0 ≤ r := hr₀.trans hr.1.le
  have htr : T - r ^ 2 < s := by
    have hh := (sq_lt_sq₀ hr₀ hrpos).mpr hr.1
    linarith
  have hlocal : (fun r => (β r).val.val) =ᶠ[𝓝 r] α := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with q hq
    exact hproj (Ioo_subset_Icc_self hq)
  let p : W → P.Carrier := fun z => z.val.val
  let hp := isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen)
    (isLocalDiffeomorph_subtype_val (I := ThreeModel) W)
  have hm : (L.closedSolution W hcs).base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) p hp :=
    closedSolution_metric_eq_localPull L W hcs htr
  have hvel : lVelocity (I := ThreeModel) (p ∘ β) r = lVelocity (I := ThreeModel) β r := by
    have h1 := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
      (I := 𝓘(ℝ, ℝ)) (J := ThreeModel) G.terminalRegularOpen (fun q => (β q).val) r
    have h2 := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
      (I := 𝓘(ℝ, ℝ)) (J := ThreeModel) W β r
    exact congrArg (fun D => D (1 : ℝ)) (h1.trans h2)
  have hpder (v : TangentSpace ThreeModel (β r)) : mfderiv ThreeModel ThreeModel p (β r) v = v := by
    dsimp only [p]
    change mfderiv ThreeModel ThreeModel ((Subtype.val : G.terminalRegularOpen → P.Carrier) ∘
      (Subtype.val : W → G.terminalRegularOpen)) (β r) v = v
    rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp]
    exact mfderiv_subtype_val_apply W (β r) v
  have hvelα : lVelocity (I := ThreeModel) β r = lVelocity (I := ThreeModel) α r := by
    rw [← hvel]
    exact congrArg (fun D => D (1 : ℝ)) (hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  have hpoint : p (β r) = α r := hlocal.self_of_nhds
  have hkin : (G.flow.base.metric (T - r ^ 2)).inner (p (β r))
      (lVelocity (I := ThreeModel) β r) (lVelocity (I := ThreeModel) β r) =
      (G.flow.base.metric (T - r ^ 2)).inner (α r)
        (lVelocity (I := ThreeModel) α r) (lVelocity (I := ThreeModel) α r) := by
    exact (congrArg (fun z : P.Carrier => (G.flow.base.metric (T - r ^ 2)).inner z
      (lVelocity (I := ThreeModel) β r : ThreeSpace) (lVelocity (I := ThreeModel) β r : ThreeSpace)) hpoint).trans
      (congrArg (fun v : ThreeSpace => (G.flow.base.metric (T - r ^ 2)).inner (α r) v v) hvelα)
  simp only [lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar, hm,
    metricScalarAt_localPull, localPullMetric_inner, hpder]
  exact congrArg₂ (· + ·) (congrArg ((1 / 2 : ℝ) * ·) hkin)
    (congrArg (fun z => 2 * r ^ 2 * metricScalarAt (G.flow.base.metric (T - r ^ 2)) z) hpoint)

private theorem TerminalLimitMetric.action_closedSolution_eq_of_projection
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c T r₀ d : ℝ} (hcs : c ≤ s) (hr₀ : 0 ≤ r₀) (hrd : r₀ ≤ d)
    (hterminal : T - r₀ ^ 2 = s) (β : ℝ → W) (α : ℝ → P.Carrier)
    (hproj : EqOn (fun r => (β r).val.val) α (Icc r₀ d)) :
    lRegularizedAction (L.closedSolution W hcs) T β r₀ d = lRegularizedAction G.flow T α r₀ d := by
  exact intervalIntegral.integral_congr_uIoo (by
    simpa only [uIoo_of_le hrd] using L.lagrangian_closedSolution_eq_of_projection W hcs hr₀ hterminal β α hproj)

private theorem TerminalLimitMetric.intervalIntegrable_closedSolution_iff_of_projection
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c T r₀ d : ℝ} (hcs : c ≤ s) (hr₀ : 0 ≤ r₀) (hrd : r₀ ≤ d)
    (hterminal : T - r₀ ^ 2 = s) (β : ℝ → W) (α : ℝ → P.Carrier)
    (hproj : EqOn (fun r => (β r).val.val) α (Icc r₀ d)) :
    IntervalIntegrable (lRegularizedLagrangian (L.closedSolution W hcs) T β) volume r₀ d ↔
      IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume r₀ d := by
  exact intervalIntegrable_congr_uIoo (by
    simpa only [uIoo_of_le hrd] using L.lagrangian_closedSolution_eq_of_projection W hcs hr₀ hterminal β α hproj)

private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance (W : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

theorem TerminalLimitMetric.exists_initial_lift_chartH1_action_le_liminf
    (L : G.TerminalLimitMetric) {T r₀ d A : ℝ} (hr₀ : 0 ≤ r₀) (hrd : r₀ < d)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - d ^ 2)
    (K : Set P.Carrier) (hK : IsCompact K) (hKreg : K ⊆ G.terminalRegularOpen)
    (α : ℕ → ℝ → P.Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc r₀ d))
    (hstay : ∀ n, MapsTo (α n) (Icc r₀ d) K)
    (hact : ∀ n, lRegularizedAction G.flow T (α n) r₀ d ≤ A)
    (γ : C(Icc r₀ d, P.Carrier))
    (hconv : Tendsto (fun n => (⟨fun r : Icc r₀ d => α n r.val,
      (hα n).continuousOn.domRestrict⟩ : C(Icc r₀ d, P.Carrier))) atTop (𝓝 γ)) :
    ∃ hds : T - d ^ 2 < s,
      let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤;
      ∃ β : ℝ → W, Continuous β ∧ EqOn (fun r => (β r).val.val) (IccExtend hrd.le γ) (Icc r₀ d) ∧
        MapsTo (fun r => (β r).val.val) (Icc r₀ d) K ∧
        ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → W)
          (v : (i : Fin m) → timeH1 ThreeSpace (partitionIntervalLength t i)),
          Monotone t ∧ t 0 = r₀ ∧ t (Fin.last m) = d ∧
          (∀ i, MapsTo β (Icc (t i.castSucc) (t i.succ)) (chartAt ThreeSpace (p i)).source) ∧
          (∀ i, EqOn (v i).toFun
            (fun r => extChartAt ThreeModel (p i) (β (t i.castSucc + r)))
            (Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
          IntervalIntegrable (lRegularizedLagrangian G.flow T (IccExtend hrd.le γ)) volume r₀ d ∧
          lRegularizedAction (L.closedSolution W hds.le) T β r₀ d = lRegularizedAction G.flow T (IccExtend hrd.le γ) r₀ d ∧
          ∃ χ : ℕ → ℕ, StrictMono χ ∧
            lRegularizedAction G.flow T (IccExtend hrd.le γ) r₀ d ≤
              liminf (fun n => lRegularizedAction G.flow T (α (χ n)) r₀ d) atTop := by
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  have hconvU : TendstoUniformly (fun n (r : Icc r₀ d) => α n r.val)
      (fun r => (IccExtend hrd.le γ) r.val) atTop := by
    have hh := ContinuousMap.tendsto_iff_tendstoUniformly.mp hconv
    have he : (fun r : Icc r₀ d => (IccExtend hrd.le γ) r.val) = γ := by
      funext r
      exact IccExtend_of_mem hrd.le γ r.property
    rw [he]
    exact hh
  have hds : T - d ^ 2 < s := by
    have hh := (sq_lt_sq₀ hr₀ (hr₀.trans hrd.le)).mpr hrd
    linarith
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  obtain ⟨β₀, γ₀, hβ₀, hγ₀, hβ₀eq, hγ₀eq, hβ₀K, hγ₀K, hpreK, hconv₀⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_lifts_tendstoUniformly_on_interval
      G.terminalRegularOpen hK hKreg hrd.le α hα hstay (IccExtend hrd.le γ) hconvU
  let β : ℕ → ℝ → W := fun n r => ⟨β₀ n r, mem_univ _⟩
  let γW : ℝ → W := fun r => ⟨γ₀ r, mem_univ _⟩
  have hβ (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (β n) (Icc r₀ d) := by
    intro r hr
    exact (DifferentialGeometry.Topology.contMDiffWithinAt_subtypeVal_comp_iff W (β n) (Icc r₀ d) r).mp (hβ₀ n r hr)
  have hγW : Continuous γW := hγ₀.subtype_mk _
  have hprojβ (n : ℕ) : EqOn (fun r => (β n r).val.val) (α n) (Icc r₀ d) := hβ₀eq n
  have hprojγ : EqOn (fun r => (γW r).val.val) (IccExtend hrd.le γ) (Icc r₀ d) := hγ₀eq
  let Q : Set W := (fun z : W => z.val.val) ⁻¹' K
  have hQ : IsCompact Q :=
    W.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hpreK
      (fun x hx => ⟨⟨x, mem_univ _⟩, rfl⟩)
  have hβQ (n : ℕ) : MapsTo (β n) (Icc r₀ d) Q := hβ₀K n
  have hγQ : MapsTo γW (Icc r₀ d) Q := hγ₀K
  have hconvW : TendstoUniformly (fun n (r : Icc r₀ d) => β n r.val) (fun r => γW r.val) atTop := by
    intro V hV
    change V ∈ Filter.comap (fun p : W × W => (p.1.val, p.2.val)) (uniformity G.terminalRegularOpen) at hV
    obtain ⟨V₀, hV₀, hsub⟩ := Filter.mem_comap.mp hV
    filter_upwards [hconv₀ V₀ hV₀] with n hn
    intro r
    exact hsub (hn r)
  let S := L.closedSolution W hds.le
  have hS := L.closedSolution_isSolutionOn W hpast hds
  have hclock (r : ℝ) (hr : r ∈ Icc r₀ d) : T - r ^ 2 ∈ (RealTimeInterval.closed (T - d ^ 2) s hds.le).carrier := by
    have hlo := pow_le_pow_left₀ hr₀ hr.1 2
    have hhi := pow_le_pow_left₀ (hr₀.trans hr.1) hr.2 2
    exact ⟨sub_le_sub_left hhi T, by linarith⟩
  have haction (n : ℕ) : lRegularizedAction S T (β n) r₀ d = lRegularizedAction G.flow T (α n) r₀ d :=
    L.action_closedSolution_eq_of_projection W hds.le hr₀ hrd.le hterminal (β n) (α n) (hprojβ n)
  obtain ⟨m, t, p, v, hmono, hzero, hend, hsrc, hrep, hint, χ, hχ, hlsc⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T r₀ d A hrd.le β hβ Q hQ
      (fun n r hr => hβQ n hr) (fun n => (haction n).trans_le (hact n)) γW hconvW hclock
  have hactγ := L.action_closedSolution_eq_of_projection W hds.le hr₀ hrd.le hterminal γW (IccExtend hrd.le γ) hprojγ
  have hintγ := (L.intervalIntegrable_closedSolution_iff_of_projection W hds.le hr₀ hrd.le hterminal γW (IccExtend hrd.le γ) hprojγ).mp hint
  refine ⟨hds, γW, hγW, hprojγ, hγQ, m, t, p, v, hmono, hzero, hend, hsrc, hrep,
    hintγ, hactγ, χ, hχ, ?_⟩
  change lRegularizedAction (L.closedSolution W hds.le) T γW r₀ d ≤ _ at hlsc
  rw [hactγ] at hlsc
  simpa only [haction] using hlsc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology Interval
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance (W : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

theorem TerminalLimitMetric.exists_split_chartH1_action_le_liminf
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    {T r₀ b A B : ℝ} (hr₀ : 0 ≤ r₀) (hrb : r₀ < b)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - b ^ 2) (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ico a s, ∀ z : P.Carrier, -B ≤ G.flow.scalar t z)
    (α : ℕ → ℝ → P.Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc r₀ b))
    (hstart : ∀ n, α n r₀ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀)
    (hint : ∀ n, IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume r₀ b)
    (hact : ∀ n, lRegularizedAction G.flow T (α n) r₀ b ≤ A)
    (γ : C(Icc r₀ b, P.Carrier))
    (hconv : Tendsto (fun n => (⟨fun r : Icc r₀ b => α n r.val,
      (hα n).continuousOn.domRestrict⟩ : C(Icc r₀ b, P.Carrier))) atTop (𝓝 γ)) :
    let γ' := IccExtend hrb.le γ;
    ∃ d : ℝ, d ∈ Ioo r₀ b ∧
      let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤;
      ∃ β : ℝ → W, Continuous β ∧ EqOn (fun r => (β r).val.val) γ' (Icc r₀ d) ∧
      (∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → W)
        (v : (i : Fin m) → timeH1 ThreeSpace (partitionIntervalLength t i)),
        Monotone t ∧ t 0 = r₀ ∧ t (Fin.last m) = d ∧
        (∀ i, MapsTo β (Icc (t i.castSucc) (t i.succ)) (chartAt ThreeSpace (p i)).source) ∧
        ∀ i, EqOn (v i).toFun (fun r => extChartAt ThreeModel (p i) (β (t i.castSucc + r)))
          (Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
      (∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → P.Carrier)
        (v : (i : Fin m) → timeH1 ThreeSpace (partitionIntervalLength t i)),
        Monotone t ∧ t 0 = d ∧ t (Fin.last m) = b ∧
        (∀ i, MapsTo γ' (Icc (t i.castSucc) (t i.succ)) (chartAt ThreeSpace (p i)).source) ∧
        ∀ i, EqOn (v i).toFun (fun r => extChartAt ThreeModel (p i) (γ' (t i.castSucc + r)))
          (Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T γ') volume r₀ b ∧
      ∃ χ : ℕ → ℕ, StrictMono χ ∧
        lRegularizedAction G.flow T γ' r₀ b ≤
          liminf (fun n => lRegularizedAction G.flow T (α (χ n)) r₀ b) atTop := by
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  let γ' := IccExtend hrb.le γ
  change ∃ d : ℝ, d ∈ Ioo r₀ b ∧ _
  obtain ⟨K, hK, hKreg, _, r, δ, _, hδ, hδb, _, htrap⟩ :=
    L.exists_uniform_initial_interval_mapsTo_compact_of_action_le K₀ hK₀ hr₀ hrb hterminal hpast hB hscalar
  let d := r₀ + δ / 2
  have hrd : r₀ < d := by dsimp [d]; linarith
  have hdb : d < b := by dsimp [d]; linarith
  have hαhead (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc r₀ d) :=
    (hα n).mono (Icc_subset_Icc le_rfl hdb.le)
  have hαtail (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc d b) :=
    (hα n).mono (Icc_subset_Icc hrd.le le_rfl)
  have hstay (n : ℕ) : MapsTo (α n) (Icc r₀ d) K := by
    intro q hq
    apply htrap b hrb le_rfl (α n) (hα n) (hstart n) (hint n) (hact n)
    exact ⟨hq.1, le_min (hq.2.trans hdb.le) (by have hh := hq.2; dsimp [d] at hh; linarith)⟩
  have hihead (n : ℕ) : IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume r₀ d :=
    (hint n).mono_set (by rw [uIcc_of_le hrd.le, uIcc_of_le hrb.le]; exact Icc_subset_Icc le_rfl hdb.le)
  have hitail (n : ℕ) : IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume d b :=
    (hint n).mono_set (by rw [uIcc_of_le hdb.le, uIcc_of_le hrb.le]; exact Icc_subset_Icc hrd.le le_rfl)
  have hfloor (n : ℕ) (q : ℝ) (hq : q ∈ Ioo r₀ b) : -B ≤ G.flow.scalar (T - q ^ 2) (α n q) := by
    have hq0 := hr₀.trans hq.1.le
    have hs := pow_le_pow_left₀ hq0 hq.2.le 2
    have ht := (sq_lt_sq₀ hr₀ hq0).mpr hq.1
    exact hscalar (T - q ^ 2) ⟨hpast.trans (sub_le_sub_left hs T), by linarith⟩ (α n q)
  let V := 2 * B * b ^ 2
  let D := b - r₀
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let head := fun n => lRegularizedAction G.flow T (α n) r₀ d
  let tail := fun n => lRegularizedAction G.flow T (α n) d b
  have hadd (n : ℕ) : head n + tail n = lRegularizedAction G.flow T (α n) r₀ b :=
    lRegularizedAction_add G.flow T (α n) r₀ d b (hihead n) (hitail n)
  have hlowhead (n : ℕ) : -V * D ≤ head n := by
    have hh := lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T (α n) hr₀ hrd.le hdb.le hB
      (fun q hq => hfloor n q ⟨hq.1, hq.2.trans_le hdb.le⟩) (hihead n)
    dsimp [head, V, D] at *
    nlinarith [mul_nonneg hV (sub_nonneg.mpr hdb.le)]
  have hlowtail (n : ℕ) : -V * D ≤ tail n := by
    have hh := lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T (α n) (hr₀.trans hrd.le) hdb.le le_rfl hB
      (fun q hq => hfloor n q ⟨hrd.le.trans_lt hq.1, hq.2⟩) (hitail n)
    dsimp [tail, V, D] at *
    nlinarith [mul_nonneg hV (sub_nonneg.mpr hrd.le)]
  have hupperhead (n : ℕ) : head n ≤ A + V * D := by linarith [hadd n, hact n, hlowtail n]
  have huppertail (n : ℕ) : tail n ≤ A + V * D := by linarith [hadd n, hact n, hlowhead n]
  obtain ⟨z, _, φ, hφ, hpair⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
    (fun n => show (head n, tail n) ∈ Icc (-V * D) (A + V * D) ×ˢ Icc (-V * D) (A + V * D) from
      ⟨⟨hlowhead n, hupperhead n⟩, ⟨hlowtail n, huppertail n⟩⟩)
  have hheadlim : Tendsto (fun n => head (φ n)) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hpair
  have htaillim : Tendsto (fun n => tail (φ n)) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hpair
  have huniform : TendstoUniformly (fun n (q : Icc r₀ b) => α n q.val) (fun q => γ' q.val) atTop := by
    have hh := ContinuousMap.tendsto_iff_tendstoUniformly.mp hconv
    have he : (fun q : Icc r₀ b => γ' q.val) = γ := funext fun q => IccExtend_of_mem hrb.le γ q.property
    rw [he]
    exact hh
  let γhead : C(Icc r₀ d, P.Carrier) :=
    ⟨fun q => γ ⟨q.val, q.property.1, q.property.2.trans hdb.le⟩,
      γ.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hγhead : EqOn (IccExtend hrd.le γhead) γ' (Icc r₀ d) := by
    intro q hq
    rw [IccExtend_of_mem hrd.le γhead hq]
    exact (IccExtend_of_mem hrb.le γ ⟨hq.1, hq.2.trans hdb.le⟩).symm
  have hconvhead : Tendsto (fun n => (⟨fun q : Icc r₀ d => α (φ n) q.val,
      (hαhead (φ n)).continuousOn.domRestrict⟩ : C(Icc r₀ d, P.Carrier))) atTop (𝓝 γhead) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    intro W hW
    have hh := hφ.tendsto_atTop.eventually (huniform W hW)
    filter_upwards [hh] with n hn
    intro q
    have h := hn ⟨q.val, q.property.1, q.property.2.trans hdb.le⟩
    have he := IccExtend_of_mem hrb.le γ ⟨q.property.1, q.property.2.trans hdb.le⟩
    change (γ' q.val, α (φ n) q.val) ∈ W at h
    change (γ ⟨q.val, q.property.1, q.property.2.trans hdb.le⟩, α (φ n) q.val) ∈ W
    exact he ▸ h
  have hpastd : a ≤ T - d ^ 2 := hpast.trans (sub_le_sub_left (pow_le_pow_left₀ (hr₀.trans hrd.le) hdb.le 2) T)
  obtain ⟨hds, β, hβ, hproj, hβK, m₀, t₀, p₀, v₀, hmono₀, hzero₀, hend₀, hsrc₀, hrep₀,
    hinthead, hheadact, χ₀, hχ₀, hlsc₀⟩ := L.exists_initial_lift_chartH1_action_le_liminf
      hr₀ hrd hterminal hpastd K hK hKreg (fun n => α (φ n)) (fun n => hαhead (φ n))
      (fun n => hstay (φ n)) (fun n => hupperhead (φ n)) γhead hconvhead
  have hheadbound : lRegularizedAction G.flow T γ' r₀ d ≤ z.1 := by
    have hh := hheadlim.comp hχ₀.tendsto_atTop
    have heq := lRegularizedAction_congr G.flow T (IccExtend hrd.le γhead) γ' r₀ d
      (fun q hq => hγhead (by rw [uIoo_of_le hrd.le] at hq; exact Ioo_subset_Icc_self hq))
    rw [heq] at hlsc₀
    change Tendsto (fun n => lRegularizedAction G.flow T (α (φ (χ₀ n))) r₀ d) atTop (𝓝 z.1) at hh
    rwa [hh.liminf_eq] at hlsc₀
  have hlaghead : EqOn (lRegularizedLagrangian G.flow T (IccExtend hrd.le γhead))
      (lRegularizedLagrangian G.flow T γ') (uIoo r₀ d) := by
    intro q hq
    rw [uIoo_of_le hrd.le] at hq
    exact lagrangian_eq_of_eventuallyEq T (Filter.eventuallyEq_of_mem (Ioo_mem_nhds hq.1 hq.2)
      (fun t ht => hγhead (Ioo_subset_Icc_self ht)))
  have hinthead' := (intervalIntegrable_congr_uIoo hlaghead).mp hinthead
  have htailclock (q : ℝ) (hq : q ∈ Icc d b) : T - q ^ 2 ∈ (RealTimeInterval.closedOpen a s G.lt).carrier := by
    have hq0 := (hr₀.trans hrd.le).trans hq.1
    have hs := pow_le_pow_left₀ hq0 hq.2 2
    have ht := (sq_lt_sq₀ hr₀ hq0).mpr (hrd.trans_le hq.1)
    exact ⟨hpast.trans (sub_le_sub_left hs T), by linarith⟩
  have hconvtail : TendstoUniformly (fun n (q : Icc d b) => α (φ (χ₀ n)) q.val) (fun q => γ' q.val) atTop := by
    intro W hW
    have hh := (hφ.comp hχ₀).tendsto_atTop.eventually (huniform W hW)
    filter_upwards [hh] with n hn
    intro q
    exact hn ⟨q.val, hrd.le.trans q.property.1, q.property.2⟩
  obtain ⟨m₁, t₁, p₁, v₁, hmono₁, hzero₁, hend₁, hsrc₁, hrep₁, hinttail, χ₁, hχ₁, hlsc₁⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      G.flow G.equation.smoothMetric ⟨G.equation.scalarCont⟩ T d b (A + V * D) hdb.le
      (fun n => α (φ (χ₀ n))) (fun n => hαtail (φ (χ₀ n))) univ isCompact_univ
      (fun _ _ _ => mem_univ _) (fun n => huppertail (φ (χ₀ n))) γ' hconvtail htailclock
  have htailbound : lRegularizedAction G.flow T γ' d b ≤ z.2 := by
    have hh := htaillim.comp (hχ₀.comp hχ₁).tendsto_atTop
    change Tendsto (fun n => lRegularizedAction G.flow T (α (φ (χ₀ (χ₁ n)))) d b) atTop (𝓝 z.2) at hh
    rwa [hh.liminf_eq] at hlsc₁
  let χ := φ ∘ χ₀ ∘ χ₁
  have hχ : StrictMono χ := hφ.comp (hχ₀.comp hχ₁)
  have hwholelim : Tendsto (fun n => lRegularizedAction G.flow T (α (χ n)) r₀ b) atTop (𝓝 (z.1 + z.2)) := by
    have hh := (hheadlim.add htaillim).comp (hχ₀.comp hχ₁).tendsto_atTop
    change Tendsto (fun n => head (χ n) + tail (χ n)) atTop (𝓝 (z.1 + z.2)) at hh
    exact hh.congr' (Eventually.of_forall fun n => hadd (χ n))
  refine ⟨d, ⟨hrd, hdb⟩, β, hβ, hproj.trans hγhead,
    ⟨m₀, t₀, p₀, v₀, hmono₀, hzero₀, hend₀, hsrc₀, hrep₀⟩,
    ⟨m₁, t₁, p₁, v₁, hmono₁, hzero₁, hend₁, hsrc₁, hrep₁⟩,
    hinthead'.trans hinttail, χ, hχ, ?_⟩
  rw [hwholelim.liminf_eq, ← lRegularizedAction_add G.flow T γ' r₀ d b hinthead' hinttail]
  exact add_le_add hheadbound htailbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology Interval
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem absolutelyContinuousOnInterval_of_terminal_chartH1_partition
    (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {r₀ d : ℝ} (hrd : r₀ ≤ d) (β : ℝ → W) (γ : ℝ → P.Carrier)
    (hproj : EqOn (fun r => (β r).val.val) γ (Icc r₀ d))
    {m : ℕ} (t : Fin (m + 1) → ℝ) (p : Fin m → W)
    (v : (i : Fin m) → timeH1 ThreeSpace (partitionIntervalLength t i))
    (ht : Monotone t) (ht0 : t 0 = r₀) (htlast : t (Fin.last m) = d)
    (hsrc : ∀ i, MapsTo β (Icc (t i.castSucc) (t i.succ)) (chartAt ThreeSpace (p i)).source)
    (hrep : ∀ i, EqOn (v i).toFun (fun r => extChartAt ThreeModel (p i) (β (t i.castSucc + r)))
      (Icc 0 (partitionIntervalLength t i))) :
    Manifold.absolutelyContinuousOnInterval ThreeModel γ r₀ d := by
  have hh := Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition
    (I := ThreeModel) (γ := fun r => (β r).val.val) t ht (fun i => (p i).val.val) v ?_ ?_
  · apply Manifold.absolutelyContinuousOnInterval_congr (by simpa only [ht0, htlast] using hh)
    simpa only [uIcc_of_le hrd] using hproj
  · intro i r hr
    have hi := hsrc i hr
    simpa only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
      mem_preimage] using hi
  · intro i
    exact hrep i

theorem TerminalLimitMetric.absolutelyContinuousOnInterval_action_le_liminf_of_tendsto
    (L : G.TerminalLimitMetric) (K₀ : Set G.terminalRegularOpen) (hK₀ : IsCompact K₀)
    {T r₀ b A B : ℝ} (hr₀ : 0 ≤ r₀) (hrb : r₀ < b)
    (hterminal : T - r₀ ^ 2 = s) (hpast : a ≤ T - b ^ 2) (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ico a s, ∀ z : P.Carrier, -B ≤ G.flow.scalar t z)
    (α : ℕ → ℝ → P.Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc r₀ b))
    (hstart : ∀ n, α n r₀ ∈ (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K₀)
    (hint : ∀ n, IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume r₀ b)
    (hact : ∀ n, lRegularizedAction G.flow T (α n) r₀ b ≤ A)
    (γ : C(Icc r₀ b, P.Carrier))
    (hconv : Tendsto (fun n => (⟨fun r : Icc r₀ b => α n r.val,
      (hα n).continuousOn.domRestrict⟩ : C(Icc r₀ b, P.Carrier))) atTop (𝓝 γ)) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (IccExtend hrb.le γ) r₀ b ∧
    IntervalIntegrable (lRegularizedLagrangian G.flow T (IccExtend hrb.le γ)) volume r₀ b ∧
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      lRegularizedAction G.flow T (IccExtend hrb.le γ) r₀ b ≤
        liminf (fun n => lRegularizedAction G.flow T (α (χ n)) r₀ b) atTop := by
  obtain ⟨d, hd, β, _, hproj, hhead, htail, hintγ, χ, hχ, hlsc⟩ :=
    L.exists_split_chartH1_action_le_liminf K₀ hK₀ hr₀ hrb hterminal hpast hB hscalar
      α hα hstart hint hact γ hconv
  obtain ⟨m₀, t₀, p₀, v₀, ht₀, hz₀, hend₀, hsrc₀, hrep₀⟩ := hhead
  obtain ⟨m₁, t₁, p₁, v₁, ht₁, hz₁, hend₁, hsrc₁, hrep₁⟩ := htail
  have hAC₀ := absolutelyContinuousOnInterval_of_terminal_chartH1_partition
    (⊤ : TopologicalSpace.Opens G.terminalRegularOpen) hd.1.le β (IccExtend hrb.le γ)
      hproj t₀ p₀ v₀ ht₀ hz₀ hend₀ hsrc₀ hrep₀
  have hAC₁ : Manifold.absolutelyContinuousOnInterval ThreeModel (IccExtend hrb.le γ) d b := by
    have hh := Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition
      t₁ ht₁ p₁ v₁ hsrc₁ hrep₁
    simpa only [hz₁, hend₁] using hh
  have hAC := Manifold.absolutelyContinuousOnInterval_piecewise_Iic hAC₀ hAC₁ hd.1.le hd.2.le rfl
  exact ⟨by simpa only [Set.piecewise_same] using hAC, hintγ, χ, hχ, hlsc⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem closedSolution_lagrangian_ae_eq_of_projection
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c T u d : ℝ} (hcs : c ≤ s) (hu : 0 ≤ u) (hTu : T - u ^ 2 = s)
    (η : ℝ → W) (γ : ℝ → P.Carrier)
    (hproj : EqOn (fun r => (η r).val.val) γ (Icc u d)) :
    lRegularizedLagrangian (L.closedSolution W hcs) T η =ᵐ[volume.restrict (Icc u d)]
      lRegularizedLagrangian G.flow T γ := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact L.lagrangian_closedSolution_eq_of_projection W hcs hu hTu η γ hproj hr

private theorem metric_lower_on_terminal_compact
    (L : G.TerminalLimitMetric) (Q : Set P.Carrier) (hQ : IsCompact Q)
    (hQU : Q ⊆ G.terminalRegularOpen) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ t ∈ Ico a s, ∀ x ∈ Q, ∀ v : TangentSpace ThreeModel x,
      μ * (G.flow.base.metric a).inner x v v ≤ (G.flow.base.metric t).inner x v v := by
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W G.lt.le
  have hS : IsSolutionOn S := L.closedSolution_isSolutionOn W le_rfl G.lt
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let lift : Q → W := fun x => ⟨⟨x.val, hQU x.property⟩, mem_univ _⟩
  have hlift : Continuous lift := by fun_prop
  let gRef := ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen).restrictOpen W
  obtain ⟨μ, hμ, hmetric⟩ := hS.smoothMetric.metric_lower_on_compact_time
    isCompact_Icc (show Icc a s ⊆ (RealTimeInterval.closed a s G.lt.le).carrier from Subset.rfl)
    (isCompact_range hlift) gRef
  refine ⟨μ, hμ, ?_⟩
  intro t ht x hx v
  have hm := hmetric t ⟨ht.1, ht.2.le⟩ (lift ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ v
  change μ * gRef.inner (lift ⟨x, hx⟩) v v ≤
    ((L.closedSolution W G.lt.le).base.metric t).inner (lift ⟨x, hx⟩) v v at hm
  rw [L.closedSolution_before W G.lt.le ht.2] at hm
  exact hm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_terminal_collar_of_compact_neighborhood
    (L : G.TerminalLimitMetric) (K Q : Set P.Carrier) (hQ : IsCompact Q)
    (hKQ : K ⊆ interior Q) (hQU : Q ⊆ G.terminalRegularOpen)
    {r : ℝ} (hr : 0 < r)
    (hfront : ∀ x ∈ K, ∀ y ∈ frontier Q,
      ENNReal.ofReal r ≤ riemannianEDistOf (G.flow.base.metric a) x y)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s)
    (ha : a ≤ T - v ^ 2) (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d C : ℝ, d ∈ Ioo u v ∧ 0 < C ∧
      ∀ α : ℝ → P.Carrier, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc u v) → α u ∈ K →
        IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v →
        (∀ t ∈ Ioo u v, -B ≤ G.flow.scalar (T - t ^ 2) (α t)) →
        lRegularizedAction G.flow T α u v ≤ A →
        MapsTo α (Icc u d) Q ∧ curveEnergy (G.flow.base.metric a) α u d ≤ C := by
  obtain ⟨μ, hμ, hmetric⟩ := metric_lower_on_terminal_compact L Q hQ hQU
  let P₀ := max (A + 2 * B * v ^ 2 * (v - u)) 0 + 1
  have hP₀ : 0 < P₀ := by dsimp only [P₀]; positivity
  have hgap : 0 < μ * r ^ 2 / (2 * P₀) := by positivity
  let e := min ((v - u) / 2) (μ * r ^ 2 / (2 * P₀))
  have he : 0 < e := lt_min (half_pos (sub_pos.mpr huv)) hgap
  let d := u + e
  have hud : u < d := by dsimp only [d]; linarith
  have hdv : d < v := by
    have hh : e ≤ (v - u) / 2 := min_le_left _ _
    dsimp only [d]
    linarith
  have hbudget : d - u ≤ μ * r ^ 2 / (2 * P₀) := by
    simpa only [d, add_sub_cancel_left] using (min_le_right ((v - u) / 2) (μ * r ^ 2 / (2 * P₀)))
  have hratio : P₀ ≤ μ * r ^ 2 / (2 * (d - u)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (d - u))).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * P₀)).mp hbudget
    nlinarith only [hh]
  have hlarge : A + 2 * B * v ^ 2 * (v - u) < P₀ := by
    dsimp only [P₀]
    linarith [le_max_left (A + 2 * B * v ^ 2 * (v - u)) 0]
  refine ⟨d, 2 * P₀ / μ, ⟨hud, hdv⟩, by positivity, ?_⟩
  intro α hα hstart hint hscalar hact
  have htime (t : ℝ) (ht : t ∈ Ioo u v) : T - t ^ 2 ∈ Ico a s := by
    have htv : t ^ 2 ≤ v ^ 2 :=
      (sq_le_sq₀ (hu.trans ht.1.le) (hu.trans huv.le)).mpr ht.2.le
    have hut : u ^ 2 < t ^ 2 := (sq_lt_sq₀ hu (hu.trans ht.1.le)).mpr ht.1
    constructor <;> nlinarith only [ha, hTu, htv, hut]
  have hpre : uIcc u d ⊆ uIcc u v := by
    rw [uIcc_of_le hud.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc le_rfl hdv.le
  have htail : uIcc d v ⊆ uIcc u v := by
    rw [uIcc_of_le hdv.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc hud.le le_rfl
  have hintpre := hint.mono_set hpre
  have hinttail := hint.mono_set htail
  have htailLower := lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T α
    (hu.trans hud.le) hdv.le le_rfl hB
    (fun t ht => hscalar t ⟨hud.trans ht.1, ht.2⟩) hinttail
  have hadd := lRegularizedAction_add G.flow T α u d v hintpre hinttail
  have hstay : MapsTo α (Icc u d) Q := by
    by_contra hn
    have hprefix := lRegularizedAction_ge_of_leaves_closed_set G.flow T α hu hdv.le hμ.le hB hr.le
      (G.flow.base.metric a) hQ.isClosed (hα.mono (Icc_subset_Icc le_rfl hdv.le))
      (hKQ hstart) (fun t ht hQt =>
        hmetric (T - t ^ 2) (htime t ⟨ht.1, ht.2.trans hdv⟩) (α t) hQt (lVelocity α t))
      (fun t ht => hscalar t ⟨ht.1, ht.2.trans hdv⟩) hintpre
      (hfront (α u) hstart) hn
    nlinarith only [hprefix, htailLower, hadd, hact, hlarge, hratio]
  refine ⟨hstay, ?_⟩
  have href : IntervalIntegrable (fun t => (G.flow.base.metric a).inner (α t)
      (lVelocity α t) (lVelocity α t)) volume u d := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hud.le, lVelocity] using
      integrableOn_inner_mfderiv_self_of_contMDiffOn (G.flow.base.metric a)
        (hα.mono (Icc_subset_Icc le_rfl hdv.le))
  have henergy := lRegularizedAction_ge_reference_energy_add_constant_of_interior_bounds
    G.flow T α (G.flow.base.metric a) u d μ (-2 * B * v ^ 2) hud.le
    (fun t ht => hmetric (T - t ^ 2) (htime t ⟨ht.1, ht.2.trans hdv⟩)
      (α t) (hstay ⟨ht.1.le, ht.2.le⟩) (lVelocity α t))
    (fun t ht => by
      have htv : t ^ 2 ≤ v ^ 2 :=
        (sq_le_sq₀ (hu.trans ht.1.le) (hu.trans huv.le)).mpr (ht.2.trans hdv).le
      have hb := mul_le_mul_of_nonneg_left htv hB
      have hs := mul_le_mul_of_nonneg_left (hscalar t ⟨ht.1, ht.2.trans hdv⟩) (sq_nonneg t)
      nlinarith only [hb, hs]) href hintpre
  rw [intervalIntegral.integral_const_mul] at henergy
  change μ / 2 * curveEnergy (G.flow.base.metric a) α u d +
    (-2 * B * v ^ 2) * (d - u) ≤ lRegularizedAction G.flow T α u d at henergy
  apply (le_div_iff₀ hμ).mpr
  nlinarith only [henergy, htailLower, hadd, hact, hlarge]

private theorem exists_uniform_incoming_tail_energy_bound
    {T u d v : ℝ} (hu : 0 ≤ u) (hud : u < d) (hdv : d ≤ v)
    (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2) (A B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ → P.Carrier, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc u v) →
        IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v →
        (∀ t ∈ Ioo u v, -B ≤ G.flow.scalar (T - t ^ 2) (α t)) →
        lRegularizedAction G.flow T α u v ≤ A →
        curveEnergy (G.flow.base.metric a) α d v ≤ C := by
  have hd : 0 ≤ d := hu.trans hud.le
  have hv : 0 ≤ v := hd.trans hdv
  have htime : Icc a (T - d ^ 2) ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier := by
    have hsq : u ^ 2 < d ^ 2 := (sq_lt_sq₀ hu hd).mpr hud
    intro t ht
    exact ⟨ht.1, by nlinarith only [ht.2, hTu, hsq]⟩
  have hback (t : ℝ) (ht : t ∈ Icc d v) : T - t ^ 2 ∈ Icc a (T - d ^ 2) := by
    have ht0 : 0 ≤ t := hd.trans ht.1
    have hdt : d ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hd ht0).mpr ht.1
    have htv : t ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ht0 hv).mpr ht.2
    constructor <;> nlinarith only [ha, hdt, htv]
  obtain ⟨c, C₀, hc, henergy⟩ := exists_curveEnergy_le_of_lRegularizedAction_le
    G.flow G.equation T a (T - d ^ 2) (G.flow.base.metric a) d v
    (A + 2 * B * v ^ 2 * (d - u)) hdv htime hback
  let C := max ((2 / c) * (A + 2 * B * v ^ 2 * (d - u) - C₀ * (v - d))) 0 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro α hα hint hscalar hact
  have hpre : uIcc u d ⊆ uIcc u v := by
    rw [uIcc_of_le hud.le, uIcc_of_le (hud.le.trans hdv)]
    exact Icc_subset_Icc le_rfl hdv
  have htail : uIcc d v ⊆ uIcc u v := by
    rw [uIcc_of_le hdv, uIcc_of_le (hud.le.trans hdv)]
    exact Icc_subset_Icc hud.le le_rfl
  have hintpre := hint.mono_set hpre
  have hinttail := hint.mono_set htail
  have hpreLower := lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T α
    hu hud.le hdv hB (fun t ht => hscalar t ⟨ht.1, ht.2.trans_le hdv⟩) hintpre
  have hadd := lRegularizedAction_add G.flow T α u d v hintpre hinttail
  have htailAction : lRegularizedAction G.flow T α d v ≤
      A + 2 * B * v ^ 2 * (d - u) := by
    linarith only [hpreLower, hadd, hact]
  have href : IntervalIntegrable (fun t => (G.flow.base.metric a).inner (α t)
      (lVelocity α t) (lVelocity α t)) volume d v := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hdv, lVelocity] using
      integrableOn_inner_mfderiv_self_of_contMDiffOn (G.flow.base.metric a)
        (hα.mono (Icc_subset_Icc hud.le le_rfl))
  exact (henergy α href hinttail htailAction).trans
    ((le_max_left _ 0).trans (le_add_of_nonneg_right zero_le_one))


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem TerminalLimitMetric.exists_uniform_terminal_collar_of_action_le
    (L : G.TerminalLimitMetric) (K : Set G.terminalRegularOpen) (hK : IsCompact K)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s)
    (ha : a ≤ T - v ^ 2) (A B : ℝ) (hB : 0 ≤ B) :
    ∃ (Q : Set P.Carrier) (d C : ℝ), IsCompact Q ∧
      Subtype.val '' K ⊆ interior Q ∧ Q ⊆ G.terminalRegularOpen ∧ d ∈ Ioo u v ∧ 0 < C ∧
      ∀ α : ℝ → P.Carrier, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc u v) →
        α u ∈ Subtype.val '' K →
        IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v →
        (∀ t ∈ Ioo u v, -B ≤ G.flow.scalar (T - t ^ 2) (α t)) →
        lRegularizedAction G.flow T α u v ≤ A →
        MapsTo α (Icc u d) Q ∧ curveEnergy (G.flow.base.metric a) α u v ≤ C := by
  have hKc : IsCompact (Subtype.val '' K : Set P.Carrier) := hK.image continuous_subtype_val
  have hKU : (Subtype.val '' K : Set P.Carrier) ⊆ G.terminalRegularOpen := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hbuffer : ∃ (Q : Set P.Carrier) (r : ℝ), IsCompact Q ∧
      Subtype.val '' K ⊆ interior Q ∧ Q ⊆ G.terminalRegularOpen ∧ 0 < r ∧
      ∀ x ∈ Subtype.val '' K, ∀ y ∈ frontier Q,
        ENNReal.ofReal r ≤ riemannianEDistOf (G.flow.base.metric a) x y := by
    let g := G.flow.base.metric a
    let : RiemannianBundle (TangentSpace ThreeModel : P.Carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle ThreeSpace (TangentSpace ThreeModel : P.Carrier → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : LocallyCompactSpace P.Carrier := Manifold.locallyCompact_of_finiteDimensional
      (M := P.Carrier) ThreeModel
    let : RegularSpace P.Carrier := inferInstance
    let : PseudoEMetricSpace P.Carrier := PseudoEMetricSpace.ofRiemannianMetric ThreeModel P.Carrier
    have hed : ∀ x y : P.Carrier, edist x y = riemannianEDistOf g x y := fun _ _ => rfl
    obtain ⟨Q, hQ, hKQ, hQU⟩ := exists_compact_between hKc G.terminalRegularOpen.isOpen hKU
    have hdisjoint : Disjoint (Subtype.val '' K) (frontier Q) :=
      disjoint_left.mpr fun x hx hy => hy.2 (hKQ hx)
    obtain ⟨r, hr, hgap⟩ :=
      _root_.Metric.exists_pos_forall_lt_edist hKc isClosed_frontier hdisjoint
    refine ⟨Q, r, hQ, hKQ, hQU, NNReal.coe_pos.mpr hr, ?_⟩
    intro x hx y hy
    simpa only [ENNReal.ofReal_coe_nnreal, hed] using (hgap x hx y hy).le
  obtain ⟨Q, r, hQ, hKQ, hQU, hr, hfront⟩ := hbuffer
  obtain ⟨d, C, hd, hC, hcollar⟩ := exists_terminal_collar_of_compact_neighborhood
    L (Subtype.val '' K) Q hQ hKQ hQU hr hfront hu huv hTu ha A B hB
  obtain ⟨Ctail, hCtail, htail⟩ := exists_uniform_incoming_tail_energy_bound
    (G := G) hu hd.1 hd.2.le hTu ha A B hB
  refine ⟨Q, d, C + Ctail, hQ, hKQ, hQU, hd, add_pos hC hCtail, ?_⟩
  intro α hα hstart hint hscalar hact
  obtain ⟨hstay, hprefixEnergy⟩ := hcollar α hα hstart hint hscalar hact
  have htailEnergy := htail α hα hint hscalar hact
  have href : IntervalIntegrable (fun t => (G.flow.base.metric a).inner (α t)
      (lVelocity α t) (lVelocity α t)) volume u v := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le huv.le, lVelocity] using
      integrableOn_inner_mfderiv_self_of_contMDiffOn (G.flow.base.metric a) hα
  have hrefpre := href.mono_set (show uIcc u d ⊆ uIcc u v by
    rw [uIcc_of_le hd.1.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc le_rfl hd.2.le)
  have hreftail := href.mono_set (show uIcc d v ⊆ uIcc u v by
    rw [uIcc_of_le hd.2.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc hd.1.le le_rfl)
  have henergyAdd : curveEnergy (G.flow.base.metric a) α u d +
      curveEnergy (G.flow.base.metric a) α d v = curveEnergy (G.flow.base.metric a) α u v :=
    intervalIntegral.integral_add_adjacent_intervals hrefpre hreftail
  exact ⟨hstay, henergyAdd ▸ add_le_add hprefixEnergy htailEnergy⟩

theorem TerminalLimitMetric.exists_subsequence_tendsto_of_action_le
    (L : G.TerminalLimitMetric) (K : Set G.terminalRegularOpen) (hK : IsCompact K)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s)
    (ha : a ≤ T - v ^ 2) (A B : ℝ) (hB : 0 ≤ B) :
    ∃ (Q : Set P.Carrier) (d : ℝ), IsCompact Q ∧
      Subtype.val '' K ⊆ interior Q ∧ Q ⊆ G.terminalRegularOpen ∧ d ∈ Ioo u v ∧
      ∀ (α : ℕ → ℝ → P.Carrier)
        (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc u v)),
        (∀ n, α n u ∈ Subtype.val '' K) →
        (∀ n, IntervalIntegrable (lRegularizedLagrangian G.flow T (α n)) volume u v) →
        (∀ n, ∀ t ∈ Ioo u v, -B ≤ G.flow.scalar (T - t ^ 2) (α n t)) →
        (∀ n, lRegularizedAction G.flow T (α n) u v ≤ A) →
        (∀ n, MapsTo (α n) (Icc u d) Q) ∧
        ∃ (φ : ℕ → ℕ) (γ : C(Icc u v, P.Carrier)), StrictMono φ ∧
          Tendsto (fun n => (⟨fun t => α (φ n) t.val,
            (hα (φ n)).continuousOn.domRestrict⟩ : C(Icc u v, P.Carrier))) atTop (𝓝 γ) ∧
          γ ⟨u, le_rfl, huv.le⟩ ∈ Subtype.val '' K ∧
          MapsTo γ {t : Icc u v | t.val ≤ d} Q := by
  obtain ⟨Q, d, C, hQ, hKQ, hQU, hd, _, hcollar⟩ :=
    L.exists_uniform_terminal_collar_of_action_le K hK hu huv hTu ha A B hB
  refine ⟨Q, d, hQ, hKQ, hQU, hd, ?_⟩
  intro α hα hstart hint hscalar hact
  have hbounds (n : ℕ) := hcollar (α n) (hα n) (hstart n) (hint n) (hscalar n) (hact n)
  refine ⟨fun n => (hbounds n).1, ?_⟩
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  obtain ⟨φ, γ, hφ, hconv⟩ := exists_strictMono_tendstoUniformly_of_curveEnergy_le
    (G.flow.base.metric a) u v C α hα (fun n => (hbounds n).2)
    univ isCompact_univ (fun _ _ => mem_univ _)
  refine ⟨φ, γ, hφ, ContinuousMap.tendsto_iff_tendstoUniformly.mpr hconv, ?_, ?_⟩
  · apply (hK.image continuous_subtype_val).isClosed.mem_of_tendsto
      (hconv.tendsto_at ⟨u, le_rfl, huv.le⟩)
    exact Eventually.of_forall fun n => hstart (φ n)
  · intro t ht
    apply hQ.isClosed.mem_of_tendsto (hconv.tendsto_at t)
    exact Eventually.of_forall fun n => (hbounds (φ n)).1 ⟨t.property.1, ht⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section

open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

private theorem exists_open_subtype_lifts_of_tendstoUniformlyOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [UniformSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (U : Opens M) (u d : ℝ) (hud : u ≤ d)
    (alpha : ℕ → ℝ → M) (gamma : ℝ → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (Icc u d))
    (hmap : ∀ n, MapsTo (alpha n) (Icc u d) U)
    (hgamma : MapsTo gamma (Icc u d) U)
    (hconv : TendstoUniformlyOn alpha gamma atTop (Icc u d)) :
    ∃ (etaSeq : ℕ → ℝ → U) (eta : ℝ → U),
      (∀ n, EqOn (Subtype.val ∘ etaSeq n) (alpha n) (Icc u d)) ∧
      EqOn (Subtype.val ∘ eta) gamma (Icc u d) ∧
      (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (etaSeq n) (Icc u d)) ∧
      TendstoUniformlyOn etaSeq eta atTop (Icc u d) ∧
      (∀ n t, t ∉ Icc u d → etaSeq n t = etaSeq n u) ∧
      (∀ t, t ∉ Icc u d → eta t = eta u) := by
  classical
  have hu : u ∈ Icc u d := ⟨le_rfl, hud⟩
  let etaSeq (n : ℕ) (t : ℝ) : U :=
    if ht : t ∈ Icc u d then ⟨alpha n t, hmap n ht⟩ else ⟨alpha n u, hmap n hu⟩
  let eta (t : ℝ) : U :=
    if ht : t ∈ Icc u d then ⟨gamma t, hgamma ht⟩ else ⟨gamma u, hgamma hu⟩
  have hseq : ∀ n, EqOn (Subtype.val ∘ etaSeq n) (alpha n) (Icc u d) := by
    intro n t ht
    simp only [Function.comp_apply, etaSeq, dite_eq_left ht]
  have heta : EqOn (Subtype.val ∘ eta) gamma (Icc u d) := by
    intro t ht
    simp only [Function.comp_apply, eta, dite_eq_left ht]
  refine ⟨etaSeq, eta, hseq, heta, ?_, ?_, ?_, ?_⟩
  · intro n r hr
    apply (DifferentialGeometry.Topology.contMDiffWithinAt_subtypeVal_comp_iff U (etaSeq n) (Icc u d) r).mp
    exact ((halpha n).congr (hseq n)) r hr
  · intro V hV
    rw [uniformity_subtype] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    filter_upwards [hconv W hW] with n hn t ht
    apply hWV
    change ((Subtype.val ∘ eta) t, (Subtype.val ∘ etaSeq n) t) ∈ W
    rw [heta ht, hseq n ht]
    exact hn t ht
  · intro n t ht
    simp only [etaSeq, dite_eq_right ht, dite_eq_left hu]
  · intro t ht
    simp only [eta, dite_eq_right ht, dite_eq_left hu]

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_subsequence_action_liminf_of_tendsto_on_terminal_compact
    (L : G.TerminalLimitMetric) {T u d : ℝ} (hu : 0 ≤ u) (hud : u < d)
    (hTu : T - u ^ 2 = s) (ha : a ≤ T - d ^ 2)
    (Q : Set P.Carrier) (hQ : IsCompact Q) (hQU : Q ⊆ G.terminalRegularOpen)
    (A : ℝ) (α : ℕ → ℝ → P.Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n) (Icc u d))
    (hval : ∀ n, MapsTo (α n) (Icc u d) Q)
    (hact : ∀ n, lRegularizedAction G.flow T (α n) u d ≤ A)
    (γ : ℝ → P.Carrier) (hγ : ContinuousOn γ (Icc u d))
    (hconv : Tendsto (fun n => (⟨fun t => α n t.val,
        (hα n).continuousOn.domRestrict⟩ : C(Icc u d, P.Carrier))) atTop
      (𝓝 (⟨fun t => γ t.val, hγ.domRestrict⟩ : C(Icc u d, P.Carrier)))) :
    Manifold.absolutelyContinuousOnInterval ThreeModel γ u d ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T γ) volume u d ∧
      ∃ χ : ℕ → ℕ, StrictMono χ ∧ lRegularizedAction G.flow T γ u d ≤
        liminf (fun n => lRegularizedAction G.flow T (α (χ n)) u d) atTop := by
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  have hconvU := ContinuousMap.tendsto_iff_tendstoUniformly.mp hconv
  have hγQ : MapsTo γ (Icc u d) Q := by
    intro r hr
    apply hQ.isClosed.mem_of_tendsto (hconvU.tendsto_at ⟨r, hr⟩)
    exact Eventually.of_forall fun n => hval n hr
  have hconvOn : TendstoUniformlyOn α γ atTop (Icc u d) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hconvU
  obtain ⟨βseq, β, hβseq, hβ, hβC1, hβconv, _, _⟩ :=
    exists_open_subtype_lifts_of_tendstoUniformlyOn ThreeModel G.terminalRegularOpen u d hud.le
      α γ hα (fun n => (hval n).mono_right hQU) (hγQ.mono_right hQU) hconvOn
  let W : Opens G.terminalRegularOpen := ⊤
  obtain ⟨ηseq, η, hηseq, hη, hηC1, hηconv, _, _⟩ :=
    exists_open_subtype_lifts_of_tendstoUniformlyOn ThreeModel W u d hud.le βseq β hβC1
      (fun _ _ _ => mem_univ _) (fun _ _ => mem_univ _) hβconv
  let p : W → P.Carrier := fun z => z.val.val
  have hprojSeq (n : ℕ) : EqOn (p ∘ ηseq n) (α n) (Icc u d) := by
    intro r hr
    exact (congrArg Subtype.val (hηseq n hr)).trans (hβseq n hr)
  have hproj : EqOn (p ∘ η) γ (Icc u d) := by
    intro r hr
    exact (congrArg Subtype.val (hη hr)).trans (hβ hr)
  have hds : T - d ^ 2 < s := by
    nlinarith [sq_lt_sq₀ hu (hu.trans hud.le) |>.2 hud]
  let S := L.closedSolution W hds.le
  have hS : IsSolutionOn S := L.closedSolution_isSolutionOn W ha hds
  have hclock : ∀ r ∈ Icc u d,
      T - r ^ 2 ∈ (RealTimeInterval.closed (T - d ^ 2) s hds.le).carrier := by
    intro r hr
    change T - d ^ 2 ≤ T - r ^ 2 ∧ T - r ^ 2 ≤ s
    constructor
    · nlinarith [sq_le_sq₀ (hu.trans hr.1) (hu.trans hud.le) |>.2 hr.2]
    · nlinarith [sq_le_sq₀ hu (hu.trans hr.1) |>.2 hr.1]
  have hQLift : IsCompact (p ⁻¹' Q) := by
    apply (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_preimage' hQ
    intro x hx
    exact ⟨⟨⟨x, hQU hx⟩, mem_univ _⟩, rfl⟩
  have hvalLift (n : ℕ) (r : ℝ) (hr : r ∈ Icc u d) : ηseq n r ∈ p ⁻¹' Q := by
    change p (ηseq n r) ∈ Q
    rw [show p (ηseq n r) = α n r from hprojSeq n hr]
    exact hval n hr
  let : IsManifold ThreeModel 1 W := IsManifold.of_le (n := ∞) (by decide)
  have hseqLag (n : ℕ) : lRegularizedLagrangian S T (ηseq n) =ᵐ[volume.restrict (Ι u d)]
      lRegularizedLagrangian G.flow T (α n) := by
    have hh := closedSolution_lagrangian_ae_eq_of_projection L W hds.le hu hTu
      (ηseq n) (α n) (hprojSeq n)
    rw [uIoc_of_le hud.le]
    exact ae_mono (Measure.restrict_mono_set volume Ioc_subset_Icc_self) hh
  have hseqAction (n : ℕ) : lRegularizedAction S T (ηseq n) u d =
      lRegularizedAction G.flow T (α n) u d :=
    intervalIntegral.integral_congr_ae_restrict (hseqLag n)
  obtain ⟨m, t, z, uLim, htmono, ht0, htlast, hsrc, hrep, hint, χ, hχ, hlsc⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T u d A hud.le ηseq hηC1 (p ⁻¹' Q) hQLift hvalLift
      (fun n => (hseqAction n).trans_le (hact n)) η
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hηconv) hclock
  have hγAC : Manifold.absolutelyContinuousOnInterval ThreeModel γ u d := by
    rw [← ht0, ← htlast]
    apply Manifold.absolutelyContinuousOnInterval_of_finite_partition t htmono
    intro i
    have hseg : t i.castSucc ≤ t i.succ := htmono i.castSucc_le_succ
    have hlen : 0 ≤ partitionIntervalLength t i := sub_nonneg.mpr hseg
    have hfull : Icc (t i.castSucc) (t i.succ) ⊆ Icc u d := by
      apply Icc_subset_Icc
      · rw [← ht0]
        exact htmono (Fin.zero_le _)
      · rw [← htlast]
        exact htmono (Fin.le_last _)
    have hsrcAmbient : MapsTo γ (uIcc (t i.castSucc) (t i.succ))
        (chartAt ThreeSpace (z i).val.val).source := by
      rw [uIcc_of_le hseg]
      intro r hr
      rw [← hproj (hfull hr)]
      simpa only [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
        mem_preimage, Function.comp_apply] using hsrc i hr
    have hmap : MapsTo (fun r => r - t i.castSucc) (uIcc (t i.castSucc) (t i.succ))
        (uIcc 0 (partitionIntervalLength t i)) := by
      rw [uIcc_of_le hseg, uIcc_of_le hlen]
      intro r hr
      exact ⟨sub_nonneg.mpr hr.1, sub_le_sub_right hr.2 _⟩
    have hLip : LipschitzWith 1 (fun r : ℝ => r - t i.castSucc) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have heq : (x - t i.castSucc) - (y - t i.castSucc) = x - y := by ring
      simp only [NNReal.coe_one, one_mul, Real.dist_eq, heq, le_refl]
    have hshift := ((uLim i).absolutelyContinuousOnInterval_toFun hlen).comp_monotone_lipschitzOn
      hLip.lipschitzOnWith (fun _ _ _ _ hrs => sub_le_sub_right hrs _) hmap
    apply Manifold.absolutelyContinuousOnInterval_of_extChartAt (z i).val.val
      hsrcAmbient (hshift.congr ?_)
    intro r hr
    have hcoord := hrep i (by simpa only [uIcc_of_le hlen] using hmap hr)
    change (uLim i).toFun (r - t i.castSucc) =
      extChartAt ThreeModel (z i).val.val (p (η (t i.castSucc + (r - t i.castSucc)))) at hcoord
    rw [add_sub_cancel, show p (η r) = γ r from hproj
      (hfull (by simpa only [uIcc_of_le hseg] using hr))] at hcoord
    exact hcoord
  have hlag := closedSolution_lagrangian_ae_eq_of_projection L W hds.le hu hTu η γ hproj
  have hlag' : lRegularizedLagrangian S T η =ᵐ[volume.restrict (Ι u d)]
      lRegularizedLagrangian G.flow T γ := by
    rw [uIoc_of_le hud.le]
    exact ae_mono (Measure.restrict_mono_set volume Ioc_subset_Icc_self) hlag
  have haction : lRegularizedAction S T η u d = lRegularizedAction G.flow T γ u d :=
    intervalIntegral.integral_congr_ae_restrict hlag'
  refine ⟨hγAC, (intervalIntegrable_congr_ae hlag').mp hint, χ, hχ, ?_⟩
  simpa only [haction, hseqAction] using hlsc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

private theorem exists_split_action_subsequence
    (f p q : ℕ → ℝ) (A cp cq ell : ℝ)
    (hsplit : ∀ n, p n + q n = f n)
    (hf : ∀ n, f n ≤ A) (hp : ∀ n, cp ≤ p n) (hq : ∀ n, cq ≤ q n)
    (hconv : Tendsto f atTop (𝓝 ell)) :
    ∃ (l : ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      Tendsto (p ∘ phi) atTop (𝓝 l) ∧ Tendsto (q ∘ phi) atTop (𝓝 (ell - l)) := by
  have hmem (n : ℕ) : p n ∈ Icc cp (A - cq) := by
    constructor
    · exact hp n
    · linarith only [hsplit n, hf n, hq n]
  obtain ⟨l, _, phi, hphi, hpre⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨l, phi, hphi, hpre, ?_⟩
  have htail := (hconv.comp hphi.tendsto_atTop).sub hpre
  apply htail.congr'
  exact Eventually.of_forall fun n => by
    simp only [Function.comp_apply]
    linarith only [hsplit (phi n)]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe uLimit
variable {P : OrientedThreeStage.{uLimit}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_subsequence_action_le_of_tendsto_action
    (L : G.TerminalLimitMetric) (K : Set G.terminalRegularOpen) (hK : IsCompact K)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s)
    (ha : a ≤ T - v ^ 2) (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → ℝ → P.Carrier)
    (halpha : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n) (Icc u v))
    (hstart : ∀ n, alpha n u ∈ Subtype.val '' K)
    (hint : ∀ n, IntervalIntegrable (lRegularizedLagrangian G.flow T (alpha n)) volume u v)
    (hscalar : ∀ n, ∀ r ∈ Ioo u v, -B ≤ G.flow.scalar (T - r ^ 2) (alpha n r))
    (hact : ∀ n, lRegularizedAction G.flow T (alpha n) u v ≤ A)
    (haction : Tendsto (fun n => lRegularizedAction G.flow T (alpha n) u v) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → P.Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) r.val,
        (halpha (phi n)).continuousOn.domRestrict⟩ : C(Icc u v, P.Carrier))) atTop
        (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      gamma u ∈ Subtype.val '' K ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T gamma) volume u v ∧
      lRegularizedAction G.flow T gamma u v ≤ ell := by
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  obtain ⟨Q, d, hQ, _, hQU, hd, hfamily⟩ :=
    L.exists_subsequence_tendsto_of_action_le K hK hu huv hTu ha A B hB
  obtain ⟨hstay, psi, hmap, hpsi, hconv, hmapStart, _⟩ :=
    hfamily alpha halpha hstart hint hscalar hact
  let gamma : ℝ → P.Carrier := Set.IccExtend huv.le hmap
  have hgamma : Continuous gamma := hmap.continuous.Icc_extend'
  have hgammaEq (r : ℝ) (hr : r ∈ Icc u v) : gamma r = hmap ⟨r, hr⟩ :=
    Set.IccExtend_of_mem huv.le hmap hr
  have hmapEq : (⟨fun r : Icc u v => gamma r.val,
      hgamma.comp continuous_subtype_val⟩ : C(Icc u v, P.Carrier)) = hmap := by
    ext r
    exact hgammaEq r.val r.property
  have hpre : uIcc u d ⊆ uIcc u v := by
    rw [uIcc_of_le hd.1.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc le_rfl hd.2.le
  have htail : uIcc d v ⊆ uIcc u v := by
    rw [uIcc_of_le hd.2.le, uIcc_of_le huv.le]
    exact Icc_subset_Icc hd.1.le le_rfl
  have hintPre (n : ℕ) := (hint n).mono_set hpre
  have hintTail (n : ℕ) := (hint n).mono_set htail
  have hsplit (n : ℕ) := lRegularizedAction_add G.flow T (alpha n) u d v (hintPre n) (hintTail n)
  let cp := -(2 * B * v ^ 2) * (d - u)
  let cq := -(2 * B * v ^ 2) * (v - d)
  have hlowerPre (n : ℕ) : cp ≤ lRegularizedAction G.flow T (alpha n) u d :=
    lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T (alpha n) hu hd.1.le hd.2.le hB
      (fun r hr => hscalar n r ⟨hr.1, hr.2.trans hd.2⟩) (hintPre n)
  have hlowerTail (n : ℕ) : cq ≤ lRegularizedAction G.flow T (alpha n) d v :=
    lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T (alpha n)
      (hu.trans hd.1.le) hd.2.le le_rfl hB
      (fun r hr => hscalar n r ⟨hd.1.trans hr.1, hr.2⟩) (hintTail n)
  have hupperPre (n : ℕ) : lRegularizedAction G.flow T (alpha n) u d ≤ A - cq := by
    linarith only [hsplit n, hact n, hlowerTail n]
  have hupperTail (n : ℕ) : lRegularizedAction G.flow T (alpha n) d v ≤ A - cp := by
    linarith only [hsplit n, hact n, hlowerPre n]
  obtain ⟨l, rho, hrho, hlimitPre, hlimitTail⟩ := exists_split_action_subsequence
    (fun n => lRegularizedAction G.flow T (alpha (psi n)) u v)
    (fun n => lRegularizedAction G.flow T (alpha (psi n)) u d)
    (fun n => lRegularizedAction G.flow T (alpha (psi n)) d v)
    A cp cq ell (fun n => hsplit (psi n)) (fun n => hact (psi n))
    (fun n => hlowerPre (psi n)) (fun n => hlowerTail (psi n))
    (haction.comp hpsi.tendsto_atTop)
  let phi := psi ∘ rho
  have hphi : StrictMono phi := hpsi.comp hrho
  let beta : ℕ → ℝ → P.Carrier := fun n => alpha (phi n)
  have hbeta (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (beta n) (Icc u v) := halpha (phi n)
  have hconvFull : Tendsto (fun n => (⟨fun r => beta n r.val,
      (hbeta n).continuousOn.domRestrict⟩ : C(Icc u v, P.Carrier))) atTop
      (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) := by
    rw [hmapEq]
    exact hconv.comp hrho.tendsto_atTop
  have hconvUniform := ContinuousMap.tendsto_iff_tendstoUniformly.mp hconvFull
  have hbetaPre (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (beta n) (Icc u d) :=
    (hbeta n).mono (Icc_subset_Icc le_rfl hd.2.le)
  have hbetaTail (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (beta n) (Icc d v) :=
    (hbeta n).mono (Icc_subset_Icc hd.1.le le_rfl)
  have hconvPre : Tendsto (fun n => (⟨fun r => beta n r.val,
      (hbetaPre n).continuousOn.domRestrict⟩ : C(Icc u d, P.Carrier))) atTop
      (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    exact hconvUniform.comp (fun r : Icc u d => (⟨r.val, r.property.1,
      r.property.2.trans hd.2.le⟩ : Icc u v))
  have hconvTail : TendstoUniformly (fun n (r : Icc d v) => beta n r.val)
      (fun r => gamma r.val) atTop :=
    hconvUniform.comp (fun r : Icc d v => (⟨r.val, hd.1.le.trans r.property.1,
      r.property.2⟩ : Icc u v))
  have haPre : a ≤ T - d ^ 2 := by
    have hsq := (sq_le_sq₀ (hu.trans hd.1.le) (hu.trans huv.le)).mpr hd.2.le
    linarith only [ha, hsq]
  have hclockTail (r : ℝ) (hr : r ∈ Icc d v) :
      T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s G.lt).carrier := by
    change a ≤ T - r ^ 2 ∧ T - r ^ 2 < s
    have hr0 := (hu.trans hd.1.le).trans hr.1
    have hsqv := (sq_le_sq₀ hr0 (hu.trans huv.le)).mpr hr.2
    have hsqu := (sq_lt_sq₀ hu hr0).mpr (hd.1.trans_le hr.1)
    constructor <;> nlinarith only [ha, hTu, hsqv, hsqu]
  obtain ⟨hACPre, hIntPre, chiPre, hchiPre, hactionPre⟩ :=
    L.exists_subsequence_action_liminf_of_tendsto_on_terminal_compact
      hu hd.1 hTu haPre Q hQ hQU (A - cq) beta hbetaPre
      (fun n r hr => hstay (phi n) hr) (fun n => hupperPre (phi n))
      gamma hgamma.continuousOn hconvPre
  have hboundPre : lRegularizedAction G.flow T gamma u d ≤ l := by
    have hlim := hlimitPre.comp hchiPre.tendsto_atTop
    rw [show liminf (fun n => lRegularizedAction G.flow T (beta (chiPre n)) u d) atTop = l from
      hlim.liminf_eq] at hactionPre
    exact hactionPre
  obtain ⟨m, times, centers, coord, htimes, htimes0, htimeslast, hsrcTail, hrepTail,
      hIntTail, chiTail, hchiTail, hactionTail⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      G.flow G.equation.smoothMetric ⟨G.equation.scalarCont⟩ T d v (A - cp) hd.2.le beta hbetaTail
      univ isCompact_univ (fun _ _ _ => mem_univ _) (fun n => hupperTail (phi n))
      gamma hconvTail hclockTail
  have hACTail : Manifold.absolutelyContinuousOnInterval ThreeModel gamma d v := by
    have hh := Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition
      times htimes centers coord hsrcTail hrepTail
    simpa only [htimes0, htimeslast] using hh
  have hboundTail : lRegularizedAction G.flow T gamma d v ≤ ell - l := by
    have hlim := hlimitTail.comp hchiTail.tendsto_atTop
    rw [show liminf (fun n => lRegularizedAction G.flow T (beta (chiTail n)) d v) atTop = ell - l from
      hlim.liminf_eq] at hactionTail
    exact hactionTail
  have hAC : Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v := by
    simpa only [Set.piecewise_same] using
      Manifold.absolutelyContinuousOnInterval_piecewise_Iic hACPre hACTail hd.1.le hd.2.le rfl
  refine ⟨phi, gamma, hgamma, hphi, hconvFull, ?_, hAC, hIntPre.trans hIntTail, ?_⟩
  · rw [hgammaEq u ⟨le_rfl, huv.le⟩]
    exact hmapStart
  · have hadd := lRegularizedAction_add G.flow T gamma u d v hIntPre hIntTail
    linarith only [hadd, hboundPre, hboundTail]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_lRegularizedAction_minimizer
    (L : G.TerminalLimitMetric) {T u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (x : G.terminalRegularOpen) (y : P.Carrier) (B : ℝ) (hB : 0 ≤ B)
    (hscalar : ∀ r ∈ Ioo u v, ∀ z : P.Carrier, -B ≤ G.flow.scalar (T - r ^ 2) z)
    (alpha₀ : ℝ → P.Carrier)
    (halpha₀ : Manifold.absolutelyContinuousOnInterval ThreeModel alpha₀ u v)
    (hstart₀ : alpha₀ u = x.val) (hend₀ : alpha₀ v = y)
    (hint₀ : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha₀) volume u v) :
    ∃ gamma : ℝ → P.Carrier, gamma u = x.val ∧ gamma v = y ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T gamma) volume u v ∧
      ∀ delta : ℝ → P.Carrier, Manifold.absolutelyContinuousOnInterval ThreeModel delta u v →
        delta u = x.val → delta v = y →
        IntervalIntegrable (lRegularizedLagrangian G.flow T delta) volume u v →
        lRegularizedAction G.flow T gamma u v ≤ lRegularizedAction G.flow T delta u v := by
  classical
  obtain ⟨beta₀, hbeta₀, hbeta₀U, hbeta₀V, hbeta₀Int, _⟩ :=
    L.exists_contMDiff_action_lt_of_terminal_curve hu huv hTu ha halpha₀
      (by rw [hstart₀]; exact x.property) hint₀ (by norm_num : (0 : ℝ) < 1)
  let A₀ := lRegularizedAction G.flow T beta₀ u v
  let costs : Set ℝ := {r | ∃ alpha : ℝ → P.Carrier,
    ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 alpha (Icc u v) ∧ alpha u = x.val ∧ alpha v = y ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume u v ∧
      lRegularizedAction G.flow T alpha u v = r ∧ r ≤ A₀}
  have hseed : A₀ ∈ costs := ⟨beta₀, hbeta₀.contMDiffOn, hbeta₀U.trans hstart₀,
    hbeta₀V.trans hend₀, hbeta₀Int, rfl, le_rfl⟩
  have hcosts : costs.Nonempty := ⟨A₀, hseed⟩
  have hbdd : BddBelow costs := by
    refine ⟨-(2 * B * v ^ 2) * (v - u), ?_⟩
    rintro r ⟨alpha, _, _, _, hint, rfl, _⟩
    exact lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T alpha hu huv.le le_rfl
      hB (fun r hr => hscalar r hr (alpha r)) hint
  have hbelow (alpha : ℝ → P.Carrier)
      (halpha : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 alpha (Icc u v))
      (hstart : alpha u = x.val) (hend : alpha v = y)
      (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume u v) :
      sInf costs ≤ lRegularizedAction G.flow T alpha u v := by
    by_cases hact : lRegularizedAction G.flow T alpha u v ≤ A₀
    · exact csInf_le hbdd ⟨alpha, halpha, hstart, hend, hint, rfl, hact⟩
    · exact (csInf_le hbdd hseed).trans (le_of_not_ge hact)
  obtain ⟨values, _, hlim, hvalues⟩ := exists_seq_tendsto_sInf hcosts hbdd
  choose alpha halpha hstart hend hint hvalue hbound using hvalues
  have haction : Tendsto (fun n => lRegularizedAction G.flow T (alpha n) u v) atTop
      (𝓝 (sInf costs)) := by
    simpa only [hvalue] using hlim
  obtain ⟨phi, gamma, hgamma, _, hconv, hgammaStart, hgammaAC, hgammaInt, hgammaAct⟩ :=
    L.exists_subsequence_action_le_of_tendsto_action {x} isCompact_singleton hu huv hTu ha
      A₀ B (sInf costs) hB alpha halpha
      (fun n => ⟨x, mem_singleton x, (hstart n).symm⟩) hint
      (fun n r hr => hscalar r hr (alpha n r))
      (fun n => by rw [hvalue n]; exact hbound n) haction
  have hgammaU : gamma u = x.val := by
    simpa only [image_singleton, mem_singleton_iff] using hgammaStart
  have hendlim : Tendsto (fun n => alpha (phi n) v) atTop (𝓝 (gamma v)) :=
    (continuous_eval_const (⟨v, huv.le, le_rfl⟩ : Icc u v)).continuousAt.tendsto.comp hconv
  have hgammaV : gamma v = y := tendsto_nhds_unique hendlim (by
    simpa only [hend] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)))
  refine ⟨gamma, hgammaU, hgammaV, hgammaAC, hgammaInt, ?_⟩
  intro delta hdelta hdeltaU hdeltaV hdeltaInt
  by_contra hn
  have hgap : 0 < lRegularizedAction G.flow T gamma u v -
      lRegularizedAction G.flow T delta u v := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨beta, hbeta, hbetaU, hbetaV, hbetaInt, hbetaAct⟩ :=
    L.exists_contMDiff_action_lt_of_terminal_curve hu huv hTu ha hdelta
      (by rw [hdeltaU]; exact x.property) hdeltaInt (half_pos hgap)
  have hbetaLower := hbelow beta hbeta.contMDiffOn (hbetaU.trans hdeltaU)
    (hbetaV.trans hdeltaV) hbetaInt
  linarith only [hgap, hgammaAct, hbetaLower, hbetaAct]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end


noncomputable section

open Set Filter Manifold MeasureTheory Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe uIncomingC1
variable {P : OrientedThreeStage.{uIncomingC1}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_contMDiffOn_one_collar_of_action_minimal
    (L : G.TerminalLimitMetric) {T u v : ℝ} {α : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = s) (ha : a ≤ T - v ^ 2)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v)
    (hterminal : α u ∈ G.terminalRegularOpen)
    (hmin : ∀ β : ℝ → P.Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel β u v →
      IntervalIntegrable (lRegularizedLagrangian G.flow T β) volume u v →
      β u = α u → β v = α v →
      lRegularizedAction G.flow T α u v ≤ lRegularizedAction G.flow T β u v) :
    ∃ d ∈ Ioo u v, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc u d) := by
  obtain ⟨d, hd, hds, η, hη, hproj, had, hS, hclock, _, hact, _, hηint⟩ :=
    L.exists_absolutelyContinuous_closedSolution_collar hu huv hTu ha hα hterminal
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let S := L.closedSolution W hds.le
  let : SigmaCompactSpace G.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace W :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace ThreeModel W
  have hreg (r : ℝ) (hr : r ∈ Ioo u d) :
      T - r ^ 2 ∈ (RealTimeInterval.closed (T - d ^ 2) s hds.le).regular := by
    change T - d ^ 2 < T - r ^ 2 ∧ T - r ^ 2 < s
    have hr0 := hu.trans hr.1.le
    constructor
    · nlinarith [sq_lt_sq₀ hr0 (hr0.trans hr.2.le) |>.2 hr.2]
    · nlinarith [sq_lt_sq₀ hu hr0 |>.2 hr.1]
  have hGramFd (p : W) : ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (fun y : ThreeSpace => chartGramOp (I := ThreeModel) S.family p (z.1, y)) z.2)
      (Icc (T - d ^ 2) s ×ˢ interior (extChartAt ThreeModel p).target) :=
    L.closedSolution_chartGram_spatial_fderiv_continuousOn W had hds p
  have hScalFd (p : W) : ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (scalarOnE (I := ThreeModel) p (S.scalar z.1)) z.2)
      (Icc (T - d ^ 2) s ×ˢ interior (extChartAt ThreeModel p).target) :=
    L.closedSolution_scalarOnE_spatial_fderiv_continuousOn W had hds p
  have hminη : ∀ δ : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ →
      δ u = η u → δ d = η d →
      lRegularizedAction S T η u d ≤ lRegularizedAction S T δ u d := by
    intro δ hδ hδu hδd
    let β : ℝ → P.Carrier := fun r => (δ r).val.val
    have hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β :=
      contMDiff_subtype_val.comp (contMDiff_subtype_val.comp hδ)
    have hδint : IntervalIntegrable (lRegularizedLagrangian S T δ) volume u d := by
      have hc := lRegularizedLagrangian_continuousOn_carrier S hS δ hδ
      exact (hc.comp (f := fun r : ℝ => (T, r))
        (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc hd.1.le
    have hlag := closedSolution_lagrangian_ae_eq_of_projection L W (d := d) hds.le hu hTu δ β
      (fun _ _ => rfl)
    have hlag' : lRegularizedLagrangian S T δ =ᵐ[volume.restrict (Ι u d)]
        lRegularizedLagrangian G.flow T β := by
      rw [uIoc_of_le hd.1.le]
      exact ae_mono (Measure.restrict_mono_set volume Ioc_subset_Icc_self) hlag
    have hβint := (intervalIntegrable_congr_ae hlag').mp hδint
    have hδact : lRegularizedAction S T δ u d = lRegularizedAction G.flow T β u d :=
      intervalIntegral.integral_congr_ae_restrict hlag'
    have hβu : β u = α u := by
      dsimp only [β]
      rw [hδu]
      exact hproj ⟨le_rfl, hd.1.le⟩
    have hβd : β d = α d := by
      dsimp only [β]
      rw [hδd]
      exact hproj ⟨hd.1.le, le_rfl⟩
    rw [hact, hδact]
    exact lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
      G.flow T u u d v le_rfl hd.1.le hd.2.le α hα hint hmin β
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hβ.contMDiffOn)
      hβint hβu hβd
  have hηC1 := lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives
    S hS T u d hd.1 η hη (hηint hint) (Icc (T - d ^ 2) s)
    Subset.rfl hclock hreg hGramFd hScalFd hminη
  have hprojC1 : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1
      (fun r => (η r).val.val) (Icc u d) :=
    contMDiff_subtype_val.comp_contMDiffOn
      (contMDiff_subtype_val.comp_contMDiffOn hηC1)
  exact ⟨d, hd, hprojC1.congr hproj.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end
