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
  have hβleft : EqOn β α₁ (Icc u d) := fun r hr => if_pos hr.2
  have hβright : EqOn β α₂ (Icc d v) := by
    intro r hr
    rcases hr.1.eq_or_lt with heq | hlt
    · subst r
      exact ((Iic d).piecewise_eq_of_mem α₁ α₂ (by simp : d ∈ Iic d)).trans hmatch.self_of_nhds
    · exact if_neg (not_le.mpr hlt)
  have hβLagLeft : EqOn (lRegularizedLagrangian G.flow T β) (lRegularizedLagrangian G.flow T α₁) (uIoo u d) := by
    intro r hr
    rw [uIoo_of_le hd.1.le] at hr
    have hn : β =ᶠ[𝓝 r] α₁ := by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht; exact hβleft (Ioo_subset_Icc_self ht)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
  have hβLagRight : EqOn (lRegularizedLagrangian G.flow T β) (lRegularizedLagrangian G.flow T α₂) (uIoo d v) := by
    intro r hr
    rw [uIoo_of_le hd.2.le] at hr
    have hn : β =ᶠ[𝓝 r] α₂ := by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht; exact hβright (Ioo_subset_Icc_self ht)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
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
