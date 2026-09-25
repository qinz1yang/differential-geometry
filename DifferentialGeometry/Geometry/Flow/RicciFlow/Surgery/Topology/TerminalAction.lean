import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel

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
