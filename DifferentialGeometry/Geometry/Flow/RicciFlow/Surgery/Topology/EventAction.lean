import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedRepresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel
import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.IntervalLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorMetricSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionJoin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)

def eventRegularizedC1ActionValues (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier) : Set ℝ :=
  {r | 0 ≤ d ∧ d ≤ v ∧ T - d ^ 2 = s ∧
    (∀ t ∈ Icc 0 d, T - t ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier) ∧
    (∀ t ∈ Ioc d v, T - t ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier) ∧
    ∃ (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier),
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α ∧ ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧
    IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume 0 d ∧
    IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T β) volume d v ∧
    α 0 = p ∧ β v = q ∧
    (∃ z : E.old, z.val.val = β d ∧ E.oldOutput z = α d) ∧
    lRegularizedAction G.flow T α 0 d + lRegularizedAction E.incoming.flow T β d v = r}

def eventRegularizedC1Cost (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier) : WithTop ℝ :=
  sInf ((fun r : ℝ => (r : WithTop ℝ)) '' E.eventRegularizedC1ActionValues G T d v p q)

theorem eventRegularizedC1Cost_eq_top_of_no_competitor
    (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier)
    (h : E.eventRegularizedC1ActionValues G T d v p q = ∅) :
    E.eventRegularizedC1Cost G T d v p q = ⊤ := by
  rw [eventRegularizedC1Cost, h, image_empty, WithTop.sInf_empty]

theorem eventRegularizedC1ActionValues_bddBelow_of_scalar_lower
    (T : ℝ) {d v B : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v) (hB : 0 ≤ B)
    (hplus : ∀ r ∈ Ioo 0 d, ∀ x : Q.Carrier, -B ≤ G.flow.scalar (T - r ^ 2) x)
    (hminus : ∀ r ∈ Ioo d v, ∀ x : P.Carrier, -B ≤ E.incoming.flow.scalar (T - r ^ 2) x)
    (p : Q.Carrier) (q : P.Carrier) :
    BddBelow (E.eventRegularizedC1ActionValues G T d v p q) := by
  let C := -(2 * B * v ^ 2)
  have hlowPlus (α : ℝ → Q.Carrier) (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume 0 d) :
      C * d ≤ lRegularizedAction G.flow T α 0 d := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo hd (intervalIntegrable_const (c := C)) hint (fun r hr => ?_)
    · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, lRegularizedAction] using hh
    have hs2 : r ^ 2 ≤ v ^ 2 := (sq_le_sq₀ hr.1.le (hd.trans hdv)).mpr (hr.2.le.trans hdv)
    have hsc := mul_le_mul_of_nonneg_left (hplus r hr (α r)) (by positivity : 0 ≤ 2 * r ^ 2)
    have hsq := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * B)
    have hkin := metric_inner_self_nonneg (G.flow.base.metric (T - r ^ 2)) (α r) (lVelocity α r)
    dsimp only [C, lRegularizedLagrangian]
    nlinarith
  have hlowMinus (β : ℝ → P.Carrier) (hint : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T β) volume d v) :
      C * (v - d) ≤ lRegularizedAction E.incoming.flow T β d v := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo hdv (intervalIntegrable_const (c := C)) hint (fun r hr => ?_)
    · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, lRegularizedAction] using hh
    have hs2 : r ^ 2 ≤ v ^ 2 := (sq_le_sq₀ (hd.trans hr.1.le) (hd.trans hdv)).mpr hr.2.le
    have hsc := mul_le_mul_of_nonneg_left (hminus r hr (β r)) (by positivity : 0 ≤ 2 * r ^ 2)
    have hsq := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * B)
    have hkin := metric_inner_self_nonneg (E.incoming.flow.base.metric (T - r ^ 2)) (β r) (lVelocity β r)
    dsimp only [C, lRegularizedLagrangian]
    nlinarith
  refine ⟨C * v, ?_⟩
  rintro r ⟨_, _, _, _, _, α, β, _, _, hα, hβ, _, _, _, rfl⟩
  have hαbound := hlowPlus α hα
  have hβbound := hlowMinus β hβ
  nlinarith


theorem eventRegularizedC1Cost_eq_of_minimum
    (T d v A : ℝ) (p : Q.Carrier) (q : P.Carrier)
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q)
    (hmin : ∀ r ∈ E.eventRegularizedC1ActionValues G T d v p q, A ≤ r) :
    E.eventRegularizedC1Cost G T d v p q = (A : WithTop ℝ) := by
  unfold eventRegularizedC1Cost
  let costs := (fun r : ℝ => (r : WithTop ℝ)) '' E.eventRegularizedC1ActionValues G T d v p q
  have hmem : (A : WithTop ℝ) ∈ costs := ⟨A, hA, rfl⟩
  have hlower : ∀ r ∈ costs, (A : WithTop ℝ) ≤ r := by
    rintro r ⟨t, ht, rfl⟩
    exact WithTop.coe_le_coe.mpr (hmin t ht)
  exact le_antisymm (csInf_le ⟨(A : WithTop ℝ), hlower⟩ hmem) (le_csInf ⟨_, hmem⟩ hlower)

theorem eventRegularizedC1Cost_le_of_competitor
    (T : ℝ) {d v B : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v) (hB : 0 ≤ B)
    (hplus : ∀ r ∈ Ioo 0 d, ∀ x : Q.Carrier, -B ≤ G.flow.scalar (T - r ^ 2) x)
    (hminus : ∀ r ∈ Ioo d v, ∀ x : P.Carrier, -B ≤ E.incoming.flow.scalar (T - r ^ 2) x)
    (p : Q.Carrier) (q : P.Carrier) {A : ℝ}
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q) :
    E.eventRegularizedC1Cost G T d v p q ≤ (A : WithTop ℝ) := by
  obtain ⟨L, hL⟩ := E.eventRegularizedC1ActionValues_bddBelow_of_scalar_lower G T hd hdv hB hplus hminus p q
  apply csInf_le
  · refine ⟨(L : WithTop ℝ), ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact WithTop.coe_le_coe.mpr (hL hr)
  · exact ⟨A, hA, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hcross in
omit [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] in
private theorem incoming_node_eq_of_admissible
    (z w : X) (hnode : ∃ p : E.old, p.val.val = f w ∧ E.oldOutput p = g z) : z = w := by
  obtain ⟨p, hp, hpout⟩ := hnode
  obtain ⟨q, _, hq, hqout⟩ := hcross z
  have heq : p = q := E.oldOutput_injective (hpout.trans hqout.symm)
  apply hfi
  exact hq.symm.trans ((congrArg (fun p : E.old => p.val.val) heq).symm.trans hp)

private theorem action_eq_of_metric_eqOn_localPullback
    {D D' : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (S' : SolutionOn (I := ThreeModel) (M := P.Carrier) D')
    (T u v : ℝ) (β : ℝ → X) (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β)
    (hmet : ∀ r ∈ uIoo u v, S.base.metric (T - r ^ 2) =
      localPullMetric (S'.base.metric (T - r ^ 2)) f hf) :
    lRegularizedAction S T β u v = lRegularizedAction S' T (f ∘ β) u v := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  have hh : lRegularizedLagrangian S T β r =
      lRegularizedLagrangian (S'.localPullback f hf) T β r := by
    unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
    rw [hmet r hr]
    rfl
  exact hh.trans (lRegularizedLagrangian_localPullback S' f hf T
    (hβ.mdifferentiable one_ne_zero r))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_survivor_curve_action_lt_of_confined_event_competitor
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β)
    (hαstay : MapsTo α (Icc 0 d) (range g))
    (hβstay : MapsTo β (Icc d v) (range f))
    (hnode : ∃ z : E.old, z.val.val = β d ∧ E.oldOutput z = α d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧
      g (γ 0) = α 0 ∧ f (γ v) = β v ∧
      lRegularizedAction S T γ 0 v <
        lRegularizedAction G.flow T α 0 d +
          lRegularizedAction E.incoming.flow T β d v + ε := by
  obtain ⟨α', hα', hαeq⟩ := Topology.Manifold.exists_contMDiff_interval_lift_of_injective_localDiffeomorph
    g hg hgi α hα hd hαstay
  obtain ⟨β', hβ', hβeq⟩ := Topology.Manifold.exists_contMDiff_interval_lift_of_injective_localDiffeomorph
    f hf hfi β hβ hdv hβstay
  have hmatch : α' d = β' d := by
    apply incoming_node_eq_of_admissible E f g hfi hcross
    obtain ⟨z, hzin, hzout⟩ := hnode
    refine ⟨z, hzin.trans (hβeq ⟨le_rfl, hdv.le⟩).symm,
      hzout.trans (hαeq ⟨hd.le, le_rfl⟩).symm⟩
  let : SecondCountableTopology P.Carrier := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  have hemb : _root_.Topology.IsOpenEmbedding f := .of_continuous_injective_isOpenMap hf.contMDiff.continuous hfi hf.isOpenMap
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let _ : MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  obtain ⟨γ, hγ, hzero, hend, hact⟩ := exists_lRegAction_join_lt_on_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T v hd hdv α' β' hα'.contMDiffOn hβ'.contMDiffOn hmatch
    htime ε hε
  have hin : lRegularizedAction S T β' d v = lRegularizedAction E.incoming.flow T β d v := by
    rw [action_eq_of_metric_eqOn_localPullback f hf S E.incoming.flow T d v β' hβ'
      (by simpa only [uIoo_of_le hdv.le] using hbefore)]
    apply lRegularizedAction_congr
    intro r hr
    rw [uIoo_of_le hdv.le] at hr
    exact hβeq (Ioo_subset_Icc_self hr)
  have hout : lRegularizedAction S T α' 0 d = lRegularizedAction G.flow T α 0 d := by
    have hh : lRegularizedAction S T α' 0 d = lRegularizedAction G.flow T (g ∘ α') 0 d := by
      unfold lRegularizedAction
      apply intervalIntegral.integral_congr_uIoo
      intro r hr
      rw [uIoo_of_le hd.le] at hr
      have hm : lRegularizedLagrangian S T α' r = lRegularizedLagrangian (G.flow.localPullback g hg) T α' r := by
        unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
        rw [hafter r hr]
        rfl
      exact hm.trans (lRegularizedLagrangian_localPullback G.flow g hg T
        (hα'.mdifferentiable one_ne_zero r))
    rw [hh]
    apply lRegularizedAction_congr
    intro r hr
    rw [uIoo_of_le hd.le] at hr
    exact hαeq (Ioo_subset_Icc_self hr)
  refine ⟨γ, hγ, ?_, ?_, ?_⟩
  · rw [hzero]
    exact hαeq ⟨le_rfl, hd.le⟩
  · rw [hend]
    exact hβeq ⟨hdv.le, le_rfl⟩
  · rwa [hin, hout] at hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

private local instance (W : Opens E.incoming.terminalRegularOpen) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_survivor_solution_approximating_event_competitors
    (G : Q.IncomingSlab s b) (hmetric : G.flow.base.metric s = E.outputMetric)
    (W : Opens E.incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    {c d : ℝ} (hac : a ≤ c) (hcs : c < s) (hsd : s < d) (hdb : d < b) :
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed c d (hcs.trans hsd).le)),
      F.source = W ∧ (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧ IsSolutionOn S ∧
      (∀ t ∈ Icc c s, S.base.metric t = (E.terminal.extendedMetric t).restrictOpen W) ∧
      (∀ t ∈ Ioo s d, ∀ (x : W) (v w : TangentSpace ThreeModel x),
        (S.base.metric t).inner x v w = (G.flow.base.metric t).inner (F x.val)
          (mfderiv ThreeModel ThreeModel F x.val v) (mfderiv ThreeModel ThreeModel F x.val w)) ∧
      ∀ (T ξ v : ℝ), 0 < ξ → ξ < v → T - ξ ^ 2 = s →
      (∀ r ∈ Icc 0 v, T - r ^ 2 ∈ Icc c d) →
      ∀ (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier),
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β →
      MapsTo α (Icc 0 ξ) (range (fun z : W => F z.val)) →
      MapsTo β (Icc ξ v) (range (fun z : W => z.val.val)) →
      (∃ z : E.old, z.val.val = β ξ ∧ E.oldOutput z = α ξ) →
      ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ → W,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ F (γ 0).val = α 0 ∧ (γ v).val.val = β v ∧
        lRegularizedAction S T γ 0 v <
          lRegularizedAction G.flow T α 0 ξ +
          lRegularizedAction E.incoming.flow T β ξ v + ε := by
  obtain ⟨F, Splus, hFsource, hSplus, hFcross, hstart, hpull, _, hS, _, _⟩ :=
    E.exists_survivor_solution_across_event G hmetric W x₀ hW hac hcs hsd hdb
  let S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed c d (hcs.trans hsd).le) :=
    { base.metric := fun t => if t ≤ s then (E.terminal.extendedMetric t).restrictOpen W else Splus.base.metric t }
  have hleft (t : ℝ) (ht : t ≤ s) : S.base.metric t = (E.terminal.extendedMetric t).restrictOpen W :=
    ite_eq_left ht
  have hright (t : ℝ) (ht : s < t) : S.base.metric t = Splus.base.metric t := ite_eq_right (not_le.mpr ht)
  refine ⟨F, S, hFsource, hFcross, hS, (fun t ht => hleft t ht.2), ?_, ?_⟩
  · intro t ht x v w
    rw [hright t ht.1]
    exact hpull t x v w
  intro T ξ v hξ hξv hclock htime α β hα hβ hαstay hβstay hnode ε hε
  let f : W → P.Carrier := fun z => z.val.val
  let g : W → Q.Carrier := fun z => F z.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val E.incoming.terminalRegularOpen)
      (isLocalDiffeomorph_subtype_val W)
  have hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g := by
    intro z
    have hFz : IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ F z.val :=
      ⟨F, (hFsource ▸ z.property), fun _ _ => rfl⟩
    exact (isLocalDiffeomorph_subtype_val W z).comp ThreeModel _ hFz
  have hfi : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hgi : Function.Injective g := by
    intro z y heq
    apply Subtype.ext
    exact F.toPartialEquiv.injOn (hFsource ▸ z.property) (hFsource ▸ y.property) heq
  have hcross : ∀ z : W, E.RegularCrossing (f z) (g z) := fun z => hFcross z.val z.property
  apply E.exists_survivor_curve_action_lt_of_confined_event_competitor G f g hf hg hfi hgi hcross
    S hS T hξ hξv htime ?_ ?_ α β hα hβ hαstay hβstay hnode hε
  · intro r hr
    have hts : T - r ^ 2 < s := by nlinarith [hr.1, hclock]
    rw [hleft _ hts.le, E.terminal.extendedMetric_before hts]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner]
    have hd : mfderiv ThreeModel ThreeModel f z = ContinuousLinearMap.id ℝ ThreeSpace := by
      have hh := mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
        (Subtype.val : W → E.incoming.terminalRegularOpen) z
      exact hh.trans (mfderiv_subtype_val W z)
    rw [hd]
    rfl
  · intro r hr
    have hts : s < T - r ^ 2 := by nlinarith [hr.1, hr.2, hclock]
    rw [hright _ hts]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner, hpull]
    have hd := mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
      (F : E.incoming.terminalRegularOpen → Q.Carrier) W z
    change mfderiv ThreeModel ThreeModel g z = mfderiv ThreeModel ThreeModel F z.val at hd
    rw [hd]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
theorem action_le_event_competitor_of_survivor_minimal
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      γ 0 = η 0 → γ v = η v → lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v)
    (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β)
    (hαstay : MapsTo α (Icc 0 d) (range g))
    (hβstay : MapsTo β (Icc d v) (range f))
    (hnode : ∃ z : E.old, z.val.val = β d ∧ E.oldOutput z = α d)
    (hzero : α 0 = g (η 0)) (hend : β v = f (η v)) :
    lRegularizedAction S T η 0 v ≤
      lRegularizedAction G.flow T α 0 d + lRegularizedAction E.incoming.flow T β d v := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ, hgzero, hfend, hact⟩ :=
    E.exists_survivor_curve_action_lt_of_confined_event_competitor G f g hf hg hfi hgi hcross
      S hS T hd hdv htime hbefore hafter α β hα hβ hαstay hβstay hnode hε
  have hγzero : γ 0 = η 0 := hgi (hgzero.trans hzero)
  have hγend : γ v = η v := hfi (hfend.trans hend)
  exact (hmin γ hγ hγzero hγend).trans hact.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

private theorem lagrangian_eq_localPullback_on_interval
    {D D' : RealTimeInterval} {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y] [T2Space Y]
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (S' : SolutionOn (I := ThreeModel) (M := Y) D') (p : X → Y)
    (hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ p)
    (T u v : ℝ) (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hmet : ∀ r ∈ uIoo u v, S.base.metric (T - r ^ 2) =
      localPullMetric (S'.base.metric (T - r ^ 2)) p hp) :
    EqOn (lRegularizedLagrangian S T γ) (lRegularizedLagrangian S' T (p ∘ γ)) (uIoo u v) := by
  intro r hr
  have hm : lRegularizedLagrangian S T γ r = lRegularizedLagrangian (S'.localPullback p hp) T γ r := by
    unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
    rw [hmet r hr]
    rfl
  exact hm.trans (lRegularizedLagrangian_localPullback S' p hp T (hγ.mdifferentiable one_ne_zero r))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventRegularizedC1Cost_eq_of_survivor_minimum_and_action_gap
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v A : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      γ 0 = η 0 → γ v = η v → lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v)
    (hηlow : lRegularizedAction S T η 0 v < A)
    (hgap : ∀ (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier),
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β →
      IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume 0 d →
      IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T β) volume d v →
      α 0 = g (η 0) → β v = f (η v) →
      (∃ z : E.old, z.val.val = β d ∧ E.oldOutput z = α d) →
      (¬ MapsTo α (Icc 0 d) (range g) ∨ ¬ MapsTo β (Icc d v) (range f)) →
      A ≤ lRegularizedAction G.flow T α 0 d + lRegularizedAction E.incoming.flow T β d v)
    :
    E.eventRegularizedC1Cost G T d v (g (η 0)) (f (η v)) =
      (lRegularizedAction S T η 0 v : WithTop ℝ) := by
  have hint (u w : ℝ) (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ v) :
      IntervalIntegrable (lRegularizedLagrangian S T η) volume u w := by
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS η hη
    have hh := hc.comp (s := Icc u w) (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => htime r ⟨hu.trans hr.1, hr.2.trans hw⟩)
    exact hh.intervalIntegrable_of_Icc huw
  have hLagOut := lagrangian_eq_localPullback_on_interval S G.flow g hg T 0 d η hη
    (by simpa only [uIoo_of_le hd.le] using hafter)
  have hLagIn := lagrangian_eq_localPullback_on_interval S E.incoming.flow f hf T d v η hη
    (by simpa only [uIoo_of_le hdv.le] using hbefore)
  have hout : lRegularizedAction S T η 0 d = lRegularizedAction G.flow T (g ∘ η) 0 d :=
    intervalIntegral.integral_congr_uIoo hLagOut
  have hin : lRegularizedAction S T η d v = lRegularizedAction E.incoming.flow T (f ∘ η) d v :=
    intervalIntegral.integral_congr_uIoo hLagIn
  have hηPlus := (hint 0 d le_rfl hd.le hdv.le).congr_uIoo hLagOut
  have hηMinus := (hint d v hd.le hdv.le le_rfl).congr_uIoo hLagIn
  have haction : lRegularizedAction G.flow T (g ∘ η) 0 d +
      lRegularizedAction E.incoming.flow T (f ∘ η) d v = lRegularizedAction S T η 0 v := by
    rw [← hout, ← hin]
    exact lRegularizedAction_add S T η 0 d v (hint 0 d le_rfl hd.le hdv.le) (hint d v hd.le hdv.le le_rfl)
  apply E.eventRegularizedC1Cost_eq_of_minimum G
  · refine ⟨hd.le, hdv.le, hclock, htimePlus, htimeMinus, g ∘ η, f ∘ η,
      (hg.contMDiff.of_le (by norm_num)).comp hη, (hf.contMDiff.of_le (by norm_num)).comp hη,
      hηPlus, hηMinus, rfl, rfl, ?_, haction⟩
    obtain ⟨z, _, hz, hzg⟩ := hcross (η d)
    exact ⟨z, hz, hzg⟩
  · rintro r ⟨_, _, _, _, _, α, β, hα, hβ, hiα, hiβ, hzero, hend, hnode, rfl⟩
    by_cases hαstay : MapsTo α (Icc 0 d) (range g)
    · by_cases hβstay : MapsTo β (Icc d v) (range f)
      · exact E.action_le_event_competitor_of_survivor_minimal G f g hf hg hfi hgi hcross
          S hS T hd hdv htime hbefore hafter η hmin α β hα hβ hαstay hβstay hnode hzero hend
      · exact hηlow.le.trans (hgap α β hα hβ hiα hiβ hzero hend hnode (Or.inr hβstay))
    · exact hηlow.le.trans (hgap α β hα hβ hiα hiβ hzero hend hnode (Or.inl hαstay))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem event_competitor_action_ge_of_leaves_closed_sets
    (T : ℝ) {d v μ B r : ℝ} (hd : 0 < d) (hdv : d < v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (gPlus : Q.Metric) (gMinus : P.Metric)
    {KPlus : Set Q.Carrier} {KMinus : Set P.Carrier}
    (hKPlus : IsClosed KPlus) (hKMinus : IsClosed KMinus)
    (α : ℝ → Q.Carrier) (β : ℝ → P.Carrier)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α (Icc 0 d))
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 β (Icc d v))
    (hαLag : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume 0 d)
    (hβLag : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T β) volume d v)
    (hstart : α 0 ∈ interior KPlus) (hend : β v ∈ interior KMinus)
    (hmetricPlus : ∀ t ∈ Ioo 0 d, α t ∈ KPlus →
      μ * gPlus.inner (α t) (lVelocity α t) (lVelocity α t) ≤
        (G.flow.base.metric (T - t ^ 2)).inner (α t) (lVelocity α t) (lVelocity α t))
    (hmetricMinus : ∀ t ∈ Ioo d v, β t ∈ KMinus →
      μ * gMinus.inner (β t) (lVelocity β t) (lVelocity β t) ≤
        (E.incoming.flow.base.metric (T - t ^ 2)).inner (β t) (lVelocity β t) (lVelocity β t))
    (hscalarPlus : ∀ t ∈ Ioo 0 d, -B ≤ G.flow.scalar (T - t ^ 2) (α t))
    (hscalarMinus : ∀ t ∈ Ioo d v, -B ≤ E.incoming.flow.scalar (T - t ^ 2) (β t))
    (hfrontPlus : ∀ y ∈ frontier KPlus, ENNReal.ofReal r ≤ riemannianEDistOf gPlus (α 0) y)
    (hfrontMinus : ∀ y ∈ frontier KMinus, ENNReal.ofReal r ≤ riemannianEDistOf gMinus y (β v))
    (hexit : ¬ MapsTo α (Icc 0 d) KPlus ∨ ¬ MapsTo β (Icc d v) KMinus) :
    μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 ≤
      lRegularizedAction G.flow T α 0 d + lRegularizedAction E.incoming.flow T β d v := by
  have hv : 0 < v := hd.trans hdv
  rcases hexit with h | h
  · have hgap := lRegularizedAction_ge_of_leaves_closed_set G.flow T α le_rfl hdv.le
      hμ hB hr gPlus hKPlus hα hstart hmetricPlus hscalarPlus hαLag hfrontPlus h
    have hrest := lRegularizedAction_ge_of_scalar_lower_on_interior E.incoming.flow T β
      hd.le hdv.le le_rfl hB hscalarMinus hβLag
    have hratio : μ * r ^ 2 / (2 * v) ≤ μ * r ^ 2 / (2 * d) :=
      div_le_div_of_nonneg_left (mul_nonneg hμ (sq_nonneg r)) (by positivity) (by linarith)
    simp only [sub_zero] at hgap
    nlinarith
  · have hgap := lRegularizedAction_ge_of_enters_closed_set E.incoming.flow T β hd.le le_rfl
      hμ hB hr gMinus hKMinus hβ hend hmetricMinus hscalarMinus hβLag hfrontMinus h
    have hrest := lRegularizedAction_ge_of_scalar_lower_on_interior G.flow T α le_rfl
      hd.le hdv.le hB hscalarPlus hαLag
    have hratio : μ * r ^ 2 / (2 * v) ≤ μ * r ^ 2 / (2 * (v - d)) :=
      div_le_div_of_nonneg_left (mul_nonneg hμ (sq_nonneg r)) (by positivity) (by linarith)
    simp only [sub_zero] at hrest
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventRegularizedC1Cost_eq_of_survivor_minimum_and_frontier_separation
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v μ B r : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      γ 0 = η 0 → γ v = η v → lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (gPlus : Q.Metric) (gMinus : P.Metric)
    {KPlus : Set Q.Carrier} {KMinus : Set P.Carrier}
    (hKPlus : IsClosed KPlus) (hKMinus : IsClosed KMinus)
    (hKPlusRange : KPlus ⊆ range g) (hKMinusRange : KMinus ⊆ range f)
    (hstart : g (η 0) ∈ interior KPlus) (hend : f (η v) ∈ interior KMinus)
    (hmetricPlus : ∀ t ∈ Ioo 0 d, ∀ y ∈ KPlus, ∀ w : TangentSpace ThreeModel y,
      μ * gPlus.inner y w w ≤ (G.flow.base.metric (T - t ^ 2)).inner y w w)
    (hmetricMinus : ∀ t ∈ Ioo d v, ∀ y ∈ KMinus, ∀ w : TangentSpace ThreeModel y,
      μ * gMinus.inner y w w ≤ (E.incoming.flow.base.metric (T - t ^ 2)).inner y w w)
    (hscalarPlus : ∀ t ∈ Ioo 0 d, ∀ y : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) y)
    (hscalarMinus : ∀ t ∈ Ioo d v, ∀ y : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) y)
    (hfrontPlus : ∀ y ∈ frontier KPlus, ENNReal.ofReal r ≤ riemannianEDistOf gPlus (g (η 0)) y)
    (hfrontMinus : ∀ y ∈ frontier KMinus, ENNReal.ofReal r ≤ riemannianEDistOf gMinus y (f (η v)))
    (hηlow : lRegularizedAction S T η 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3) :
    E.eventRegularizedC1Cost G T d v (g (η 0)) (f (η v)) =
      (lRegularizedAction S T η 0 v : WithTop ℝ) := by
  apply E.eventRegularizedC1Cost_eq_of_survivor_minimum_and_action_gap G f g hf hg hfi hgi hcross
    S hS T hd hdv hclock htime htimePlus htimeMinus hbefore hafter η hη hmin hηlow
  intro α β hα hβ hαLag hβLag hzero hvend _ hescape
  apply E.event_competitor_action_ge_of_leaves_closed_sets G T hd hdv hμ hB hr gPlus gMinus
    hKPlus hKMinus α β hα.contMDiffOn hβ.contMDiffOn hαLag hβLag
    (hzero.symm ▸ hstart) (hvend.symm ▸ hend)
    (fun t ht hy => hmetricPlus t ht (α t) hy (lVelocity α t))
    (fun t ht hy => hmetricMinus t ht (β t) hy (lVelocity β t))
    (fun t ht => hscalarPlus t ht (α t)) (fun t ht => hscalarMinus t ht (β t))
    (by simpa only [hzero] using hfrontPlus) (by simpa only [hvend] using hfrontMinus)
  rcases hescape with h | h
  · exact Or.inl (fun hstay => h (fun t ht => hKPlusRange (hstay ht)))
  · exact Or.inr (fun hstay => h (fun t ht => hKMinusRange (hstay ht)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)

include hfi hgi in
theorem exists_compact_balls_metric_lower_across_event
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧
      IsCompact (riemannianClosedBallOf gPlus (g x) r) ∧
      IsCompact (riemannianClosedBallOf gMinus (f y) r) ∧
      riemannianClosedBallOf gPlus (g x) r ⊆ range g ∧
      riemannianClosedBallOf gMinus (f y) r ⊆ range f ∧
      (∀ t ∈ Ioo 0 d, ∀ z ∈ riemannianClosedBallOf gPlus (g x) r,
        ∀ w : TangentSpace ThreeModel z,
        μ * gPlus.inner z w w ≤ (G.flow.base.metric (T - t ^ 2)).inner z w w) ∧
      (∀ t ∈ Ioo d v, ∀ z ∈ riemannianClosedBallOf gMinus (f y) r,
        ∀ w : TangentSpace ThreeModel z,
        μ * gMinus.inner z w w ≤ (E.incoming.flow.base.metric (T - t ^ 2)).inner z w w) := by
  have hclock : ContinuousOn (fun t : ℝ => T - t ^ 2) (Icc 0 v) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  obtain ⟨rp, cp, hrp, hcp, hKp, hKprange, hboundp⟩ :=
    hS.smoothMetric.exists_pos_isCompact_riemannianClosedBallOf_metric_lower_of_localPullMetric
      G.flow.base.metric g hg hgi (g x) ⟨x, rfl⟩ isCompact_Icc
      (show Ioo 0 d ⊆ Icc 0 v from fun t ht => ⟨ht.1.le, ht.2.le.trans hdv⟩)
      (fun t => T - t ^ 2) hclock htime gPlus hafter
  obtain ⟨rm, cm, hrm, hcm, hKm, hKmrange, hboundm⟩ :=
    hS.smoothMetric.exists_pos_isCompact_riemannianClosedBallOf_metric_lower_of_localPullMetric
      E.incoming.flow.base.metric f hf hfi (f y) ⟨y, rfl⟩ isCompact_Icc
      (show Ioo d v ⊆ Icc 0 v from fun t ht => ⟨hd.trans ht.1.le, ht.2.le⟩)
      (fun t => T - t ^ 2) hclock htime gMinus hbefore
  let r := min rp rm
  let μ := min cp cm
  have hsubp : riemannianClosedBallOf gPlus (g x) r ⊆ riemannianClosedBallOf gPlus (g x) rp :=
    riemannianClosedBallOf_mono gPlus (g x) (min_le_left _ _)
  have hsubm : riemannianClosedBallOf gMinus (f y) r ⊆ riemannianClosedBallOf gMinus (f y) rm :=
    riemannianClosedBallOf_mono gMinus (f y) (min_le_right _ _)
  refine ⟨r, μ, lt_min hrp hrm, lt_min hcp hcm,
    hKp.of_isClosed_subset (isClosed_riemannianClosedBallOf _ _ _) hsubp,
    hKm.of_isClosed_subset (isClosed_riemannianClosedBallOf _ _ _) hsubm,
    hsubp.trans hKprange, hsubm.trans hKmrange, ?_, ?_⟩
  · intro t ht z hz w
    exact (mul_le_mul_of_nonneg_right (min_le_left cp cm)
      (metric_inner_self_nonneg gPlus z w)).trans (hboundp t ht z (hsubp hz) w)
  · intro t ht z hz w
    exact (mul_le_mul_of_nonneg_right (min_le_right cp cm)
      (metric_inner_self_nonneg gMinus z w)).trans (hboundm t ht z (hsubm hz) w)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventRegularizedC1Cost_eq_of_low_survivor_minimum
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧ ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η → η 0 = x → η v = y →
      (∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
        γ 0 = x → γ v = y → lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v) →
      lRegularizedAction S T η 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      E.eventRegularizedC1Cost G T d v (g x) (f y) =
        (lRegularizedAction S T η 0 v : WithTop ℝ) := by
  obtain ⟨r, μ, hr, hμ, hKp, hKm, hKprange, hKmrange, hboundp, hboundm⟩ :=
    E.exists_compact_balls_metric_lower_across_event G f g hf hg hfi hgi S hS T hd.le hdv.le
      htime hbefore hafter x y gPlus gMinus
  refine ⟨r, μ, hr, hμ, ?_⟩
  intro B hB hscalarPlus hscalarMinus η hη hηzero hηend hmin hηlow
  have hcost := E.eventRegularizedC1Cost_eq_of_survivor_minimum_and_frontier_separation
    G f g hf hg hfi hgi hcross S hS T hd hdv hclock htime htimePlus htimeMinus
    hbefore hafter η hη
    (fun γ hγ hzero hend => hmin γ hγ (hzero.trans hηzero) (hend.trans hηend))
    hμ.le hB hr.le gPlus gMinus
    (isClosed_riemannianClosedBallOf gPlus (g x) r)
    (isClosed_riemannianClosedBallOf gMinus (f y) r) hKprange hKmrange
    (by simpa only [hηzero] using mem_interior_riemannianClosedBallOf gPlus (g x) hr)
    (by simpa only [hηend] using mem_interior_riemannianClosedBallOf gMinus (f y) hr)
    hboundp hboundm hscalarPlus hscalarMinus ?_ ?_ hηlow
  · simpa only [hηzero, hηend] using hcost
  · intro z hz
    rw [hηzero, riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf gPlus (g x) hz]
  · intro z hz
    rw [hηend, riemannianEDistOf_comm gMinus z (f y),
      riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf gMinus (f y) hz]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)

private theorem le_on_Icc_of_le_on_split_Ioo
    {F : ℝ → ℝ} {d v C : ℝ} (hd : 0 < d) (hdv : d < v)
    (hF : ContinuousOn F (Icc 0 v))
    (hplus : ∀ t ∈ Ioo 0 d, C ≤ F t) (hminus : ∀ t ∈ Ioo d v, C ≤ F t) :
    ∀ t ∈ Icc 0 v, C ≤ F t := by
  intro t ht
  by_cases htd : t ≤ d
  · have hclosure : closure (Ioo (0 : ℝ) d) = Icc 0 d := closure_Ioo hd.ne
    apply le_on_closure hplus continuousOn_const
      (hF.mono (by rw [hclosure]; exact Icc_subset_Icc le_rfl hdv.le))
    rw [hclosure]
    exact ⟨ht.1, htd⟩
  · have hclosure : closure (Ioo d v) = Icc d v := closure_Ioo hdv.ne
    apply le_on_closure hminus continuousOn_const
      (hF.mono (by rw [hclosure]; exact Icc_subset_Icc hd.le le_rfl))
    rw [hclosure]
    exact ⟨le_of_not_ge htd, ht.2⟩

private theorem scalar_eq_of_metric_eq_localPullMetric
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y] [T2Space Y]
    {D D' : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (S' : SolutionOn (I := ThreeModel) (M := Y) D')
    (p : X → Y) (hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ p)
    {t : ℝ} (hmetric : S.base.metric t = localPullMetric (S'.base.metric t) p hp) (z : X) :
    S.scalar t z = S'.scalar t (p z) := by
  simpa only [SolutionOn.scalar, SolutionFamily.scalar, hmetric] using
    metricScalarAt_localPull (S'.base.metric t) p hp z

private theorem scalar_clock_continuousOn
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T v : ℝ)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier) (z : X) :
    ContinuousOn (fun t : ℝ => S.scalar (T - t ^ 2) z) (Icc 0 v) := by
  have hmap : ContinuousOn (fun t : ℝ => (T - t ^ 2, z)) (Icc 0 v) :=
    ((continuous_const.sub (continuous_id.pow 2)).prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun t : ℝ => (T - t ^ 2, z)) (Icc 0 v) (D.carrier ×ˢ (univ : Set X)) :=
    fun t ht => ⟨htime t ht, mem_univ z⟩
  exact hS.scalarCont.comp (f := fun t : ℝ => (T - t ^ 2, z)) hmap hmaps

theorem scalar_lower_across_event_of_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v C : ℝ} (hd : 0 < d) (hdv : d < v)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (hscalarPlus : ∀ r ∈ Ioo 0 d, ∀ z : Q.Carrier, C ≤ G.flow.scalar (T - r ^ 2) z)
    (hscalarMinus : ∀ r ∈ Ioo d v, ∀ z : P.Carrier, C ≤ E.incoming.flow.scalar (T - r ^ 2) z) :
    ∀ r ∈ Icc 0 v, ∀ z : X, C ≤ S.scalar (T - r ^ 2) z := by
  intro r hr z
  apply le_on_Icc_of_le_on_split_Ioo hd hdv (scalar_clock_continuousOn S hS T v htime z) _ _ r hr
  · intro t ht
    rw [scalar_eq_of_metric_eq_localPullMetric S G.flow g hg (hafter t ht) z]
    exact hscalarPlus t ht (g z)
  · intro t ht
    rw [scalar_eq_of_metric_eq_localPullMetric S E.incoming.flow f hf (hbefore t ht) z]
    exact hscalarMinus t ht (f z)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventRegularizedC1Cost_minimizer_of_low_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hreg : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.regular)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧ ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ α₀ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀ → α₀ 0 = x → α₀ v = y →
      lRegularizedAction S T α₀ 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧ η v = y ∧
        E.eventRegularizedC1Cost G T d v (g x) (f y) =
          (lRegularizedAction S T η 0 v : WithTop ℝ) ∧
        ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ 0 = x → γ v = y →
          lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have htime (r : ℝ) (hr : r ∈ Icc 0 v) := D.regular_subset (hreg r hr)
  have hv : 0 < v := hd.trans hdv
  obtain ⟨re, μe, hre, hμe, hevent⟩ := E.exists_eventRegularizedC1Cost_eq_of_low_survivor_minimum
    G f g hf hg hfi hgi hcross S hS T hd hdv hclock htime htimePlus htimeMinus
    hbefore hafter x y gPlus gMinus
  obtain ⟨rl, μl, hrl, hμl, _, _, hlocal⟩ := exists_compact_ball_lRegularizedMinC1_of_action_lt
    S hS T (a := 0) (b := v) (v := v) le_rfl hv le_rfl hreg x (S.base.metric T)
    (show (univ : Set X) ∈ 𝓝 x from Filter.univ_mem)
  let r := min re rl
  let μ := min μe μl
  refine ⟨r, μ, lt_min hre hrl, lt_min hμe hμl, ?_⟩
  intro B hB hplus hminus α₀ hα₀ hzero hend hseed
  have hbound (r' μ' : ℝ) (hr' : r ≤ r') (hμ' : μ ≤ μ') :
      μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 ≤ μ' * r' ^ 2 / (2 * v) - 2 * B * v ^ 3 := by
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul hμ' (pow_le_pow_left₀ (lt_min hre hrl).le hr' 2)
      (sq_nonneg r) (le_trans (lt_min hμe hμl).le hμ')
  have hsmallLocal := hseed.trans_le (hbound rl μl (min_le_right _ _) (min_le_right _ _))
  have hcommon := E.scalar_lower_across_event_of_localPullMetric G f g hf hg S hS T hd hdv
    htime hbefore hafter hplus hminus
  obtain ⟨η, hη, hηzero, hηend, _, hmin⟩ := hlocal B hB
    (fun t ht z => hcommon t (Ioo_subset_Icc_self ht) z) y α₀ hα₀ hzero hend
    (by simpa only [sub_zero, mul_assoc, pow_succ] using hsmallLocal)
  have hηlow : lRegularizedAction S T η 0 v < μe * re ^ 2 / (2 * v) - 2 * B * v ^ 3 :=
    (hmin α₀ hα₀ hzero hend).trans_lt
      (hseed.trans_le (hbound re μe (min_le_left _ _) (min_le_left _ _)))
  exact ⟨η, hη, hηzero, hηend,
    hevent B hB hplus hminus η hη hηzero hηend hmin hηlow, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem action_mem_eventRegularizedC1ActionValues_of_survivor_curve
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η) :
    lRegularizedAction S T η 0 v ∈ E.eventRegularizedC1ActionValues G T d v (g (η 0)) (f (η v)) := by
  have hint (u w : ℝ) (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ v) :
      IntervalIntegrable (lRegularizedLagrangian S T η) volume u w := by
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS η hη
    have hh := hc.comp (s := Icc u w) (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => htime r ⟨hu.trans hr.1, hr.2.trans hw⟩)
    exact hh.intervalIntegrable_of_Icc huw
  have hLagOut := lagrangian_eq_localPullback_on_interval S G.flow g hg T 0 d η hη
    (by simpa only [uIoo_of_le hd.le] using hafter)
  have hLagIn := lagrangian_eq_localPullback_on_interval S E.incoming.flow f hf T d v η hη
    (by simpa only [uIoo_of_le hdv.le] using hbefore)
  have hout : lRegularizedAction S T η 0 d = lRegularizedAction G.flow T (g ∘ η) 0 d :=
    intervalIntegral.integral_congr_uIoo hLagOut
  have hin : lRegularizedAction S T η d v = lRegularizedAction E.incoming.flow T (f ∘ η) d v :=
    intervalIntegral.integral_congr_uIoo hLagIn
  have hηPlus := (hint 0 d le_rfl hd.le hdv.le).congr_uIoo hLagOut
  have hηMinus := (hint d v hd.le hdv.le le_rfl).congr_uIoo hLagIn
  have haction : lRegularizedAction G.flow T (g ∘ η) 0 d +
      lRegularizedAction E.incoming.flow T (f ∘ η) d v = lRegularizedAction S T η 0 v := by
    rw [← hout, ← hin]
    exact lRegularizedAction_add S T η 0 d v (hint 0 d le_rfl hd.le hdv.le) (hint d v hd.le hdv.le le_rfl)
  refine ⟨hd.le, hdv.le, hclock, htimePlus, htimeMinus, g ∘ η, f ∘ η,
    (hg.contMDiff.of_le (by norm_num)).comp hη, (hf.contMDiff.of_le (by norm_num)).comp hη,
    hηPlus, hηMinus, rfl, rfl, ?_, haction⟩
  obtain ⟨z, _, hz, hzg⟩ := hcross (η d)
  exact ⟨z, hz, hzg⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_pos_volume_eventRegularizedC1Cost_lt_of_survivor_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v B L : ℝ} (hd : 0 < d) (hdv : d < v) (hB : 0 ≤ B)
    (hclock : T - d ^ 2 = s)
    (hreg : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.regular)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (hscalarPlus : ∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z)
    (hscalarMinus : ∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hseed : lRegularizedAction S T η 0 v < L) :
    ∃ U : Set P.Carrier, IsOpen U ∧ f (η v) ∈ U ∧ U ⊆ range f ∧
      (∀ y ∈ U, E.eventRegularizedC1Cost G T d v (g (η 0)) y < (L : WithTop ℝ)) ∧
      0 < riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U := by
  obtain ⟨V, hV, hηV, α, hα, hstart, hend, _, hact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T (hd.trans hdv)
      (fun t ht => D.regular_subset (hreg t ht)) η hη hseed
  have hopen : IsOpen (f '' V) := hf.isOpenMap V hV
  refine ⟨f '' V, hopen, ⟨η v, hηV, rfl⟩, image_subset_range _ _, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    have hmem := E.action_mem_eventRegularizedC1ActionValues_of_survivor_curve G f g hf hg hcross
      S hS T hd hdv hclock (fun t ht => D.regular_subset (hreg t ht)) htimePlus htimeMinus
      hbefore hafter (α z) (hα z hz)
    rw [hstart z hz, hend z hz] at hmem
    have hcost := E.eventRegularizedC1Cost_le_of_competitor G T hd.le hdv.le hB
      hscalarPlus hscalarMinus (g (η 0)) (f z) hmem
    exact hcost.trans_lt (WithTop.coe_lt_coe.mpr (hact z hz))
  · let _ : (riemannianVolumeMeasure ThreeModel P.Carrier
        (E.incoming.flow.base.metric (T - v ^ 2))).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure _
    exact hopen.measure_pos _ ⟨_, ⟨η v, hηV, rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventRegularizedC1Cost_minimizingVector_of_low_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hreg : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.regular)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧ ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ α₀ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀ → α₀ 0 = x → α₀ v = y →
      lRegularizedAction S T α₀ 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      ∃ Z : TangentSpace ThreeModel x, (Z, v ^ 2) ∈ lMinDomain S T x ∧
        lExp S T x Z (v ^ 2) = y ∧
        E.eventRegularizedC1Cost G T d v (g x) (f y) =
          (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v : WithTop ℝ) ∧
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v ≤ lRegularizedAction S T α₀ 0 v := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨r, μ, hr, hμ, hall⟩ := E.exists_eventRegularizedC1Cost_minimizer_of_low_seed
    G f g hf hg hfi hgi hcross S hS T hd hdv hclock hreg htimePlus htimeMinus hbefore hafter x y gPlus gMinus
  refine ⟨r, μ, hr, hμ, ?_⟩
  intro B hB hplus hminus α₀ hα₀ hzero hend hlow
  obtain ⟨η, hη, hηzero, hηend, hcost, hmin⟩ := hall B hB hplus hminus α₀ hα₀ hzero hend hlow
  have hm : ∀ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ → δ 0 = η 0 → δ v = η v →
      lRegularizedAction S T η 0 v ≤ lRegularizedAction S T δ 0 v :=
    fun δ hδ hδzero hδend => hmin δ hδ (hδzero.trans hηzero) (hδend.trans hηend)
  cases hηzero
  obtain ⟨Z, hZ, hZend, _, hact⟩ := exists_lMinimizingVector_of_minimal S hS T (hd.trans hdv) hreg η hη hm
  rw [hηend] at hZend
  exact ⟨Z, hZ, hZend, hcost.trans (congrArg (fun r : ℝ => (r : WithTop ℝ)) hact.symm),
    hact.trans_le (hmin α₀ hα₀ hzero hend)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_eventRegularizedC1Cost_eq_of_low_survivor_minimum
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (htime : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y₀ : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ U : Set X, IsOpen U ∧ y₀ ∈ U ∧ ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧
      ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ y ∈ U, ∀ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η → η 0 = x → η v = y →
      (∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
        γ 0 = x → γ v = y → lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v) →
      lRegularizedAction S T η 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      E.eventRegularizedC1Cost G T d v (g x) (f y) =
        (lRegularizedAction S T η 0 v : WithTop ℝ) := by
  obtain ⟨R, μ, hR, hμ, hKp, hKm, hKprange, hKmrange, hboundp, hboundm⟩ :=
    E.exists_compact_balls_metric_lower_across_event G f g hf hg hfi hgi S hS T hd.le hdv.le
      htime hbefore hafter x y₀ gPlus gMinus
  let U : Set X := f ⁻¹' riemannianBallOf gMinus (f y₀) (R / 2)
  have hU : IsOpen U :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist gMinus (f y₀)) continuous_const).preimage
      hf.contMDiff.continuous
  have hy₀ : y₀ ∈ U := by
    change riemannianEDistOf gMinus (f y₀) (f y₀) < ENNReal.ofReal (R / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hR)
  refine ⟨U, hU, hy₀, R / 2, μ, half_pos hR, hμ, ?_⟩
  intro B hB hscalarPlus hscalarMinus y hy η hη hηzero hηend hmin hηlow
  have hyInterior : f y ∈ interior (riemannianClosedBallOf gMinus (f y₀) R) := by
    apply riemannianBallOf_subset_interior_riemannianClosedBallOf gMinus (f y₀) R
    exact (riemannianBallOf_mono gMinus (f y₀) (by linarith : R / 2 ≤ R)) hy
  have hcost := E.eventRegularizedC1Cost_eq_of_survivor_minimum_and_frontier_separation
    G f g hf hg hfi hgi hcross S hS T hd hdv hclock htime htimePlus htimeMinus
    hbefore hafter η hη
    (fun γ hγ hzero hend => hmin γ hγ (hzero.trans hηzero) (hend.trans hηend))
    hμ.le hB (half_pos hR).le gPlus gMinus
    (isClosed_riemannianClosedBallOf gPlus (g x) R)
    (isClosed_riemannianClosedBallOf gMinus (f y₀) R) hKprange hKmrange
    (by simpa only [hηzero] using mem_interior_riemannianClosedBallOf gPlus (g x) hR)
    (by simpa only [hηend] using hyInterior)
    hboundp hboundm hscalarPlus hscalarMinus ?_ ?_ hηlow
  · simpa only [hηzero, hηend] using hcost
  · intro z hz
    rw [hηzero, riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf gPlus (g x) hz]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro z hz
    rw [hηend]
    exact ofReal_half_le_riemannianEDistOf_of_mem_ball_of_mem_frontier gMinus (f y₀) hR hy hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_eventRegularizedC1Cost_minimizer_of_low_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hreg : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.regular)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y₀ : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ U : Set X, IsOpen U ∧ y₀ ∈ U ∧ ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧
      ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ y ∈ U, ∀ α₀ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀ → α₀ 0 = x → α₀ v = y →
      lRegularizedAction S T α₀ 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧ η v = y ∧
        E.eventRegularizedC1Cost G T d v (g x) (f y) =
          (lRegularizedAction S T η 0 v : WithTop ℝ) ∧
        ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ 0 = x → γ v = y →
          lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have htime (r : ℝ) (hr : r ∈ Icc 0 v) := D.regular_subset (hreg r hr)
  have hv : 0 < v := hd.trans hdv
  obtain ⟨U, hU, hy₀, re, μe, hre, hμe, hevent⟩ := E.exists_open_eventRegularizedC1Cost_eq_of_low_survivor_minimum
    G f g hf hg hfi hgi hcross S hS T hd hdv hclock htime htimePlus htimeMinus
    hbefore hafter x y₀ gPlus gMinus
  obtain ⟨rl, μl, hrl, hμl, _, _, hlocal⟩ := exists_compact_ball_lRegularizedMinC1_of_action_lt
    S hS T (a := 0) (b := v) (v := v) le_rfl hv le_rfl hreg x (S.base.metric T)
    (show (univ : Set X) ∈ 𝓝 x from Filter.univ_mem)
  let r := min re rl
  let μ := min μe μl
  refine ⟨U, hU, hy₀, r, μ, lt_min hre hrl, lt_min hμe hμl, ?_⟩
  intro B hB hplus hminus y hy α₀ hα₀ hzero hend hseed
  have hbound (r' μ' : ℝ) (hr' : r ≤ r') (hμ' : μ ≤ μ') :
      μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 ≤ μ' * r' ^ 2 / (2 * v) - 2 * B * v ^ 3 := by
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul hμ' (pow_le_pow_left₀ (lt_min hre hrl).le hr' 2)
      (sq_nonneg r) (le_trans (lt_min hμe hμl).le hμ')
  have hsmallLocal := hseed.trans_le (hbound rl μl (min_le_right _ _) (min_le_right _ _))
  have hcommon := E.scalar_lower_across_event_of_localPullMetric G f g hf hg S hS T hd hdv
    htime hbefore hafter hplus hminus
  obtain ⟨η, hη, hηzero, hηend, _, hmin⟩ := hlocal B hB
    (fun t ht z => hcommon t (Ioo_subset_Icc_self ht) z) y α₀ hα₀ hzero hend
    (by simpa only [sub_zero, mul_assoc, pow_succ] using hsmallLocal)
  have hηlow : lRegularizedAction S T η 0 v < μe * re ^ 2 / (2 * v) - 2 * B * v ^ 3 :=
    (hmin α₀ hα₀ hzero hend).trans_lt
      (hseed.trans_le (hbound re μe (min_le_left _ _) (min_le_left _ _)))
  exact ⟨η, hη, hηzero, hηend,
    hevent B hB hplus hminus y hy η hη hηzero hηend hmin hηlow, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hfi : Function.Injective f) (hgi : Function.Injective g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

include hfi hgi hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_eventRegularizedC1Cost_minimizing_vectors_of_low_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hreg : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.regular)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (x y₀ : X) (gPlus : Q.Metric) (gMinus : P.Metric) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧ ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo 0 d, ∀ z : Q.Carrier, -B ≤ G.flow.scalar (T - t ^ 2) z) →
      (∀ t ∈ Ioo d v, ∀ z : P.Carrier, -B ≤ E.incoming.flow.scalar (T - t ^ 2) z) →
      ∀ α₀ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀ → α₀ 0 = x → α₀ v = y₀ →
      lRegularizedAction S T α₀ 0 v < μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 →
      ∃ V : Set X, IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V,
        ∃ Z : TangentSpace ThreeModel x, (Z, v ^ 2) ∈ lMinDomain S T x ∧
          lExp S T x Z (v ^ 2) = y ∧
          E.eventRegularizedC1Cost G T d v (g x) (f y) =
            (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v : WithTop ℝ) ∧
          lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v <
            μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨U, hU, hyU, r, μ, hr, hμ, hminima⟩ :=
    E.exists_open_eventRegularizedC1Cost_minimizer_of_low_seed G f g hf hg hfi hgi hcross
      S hS T hd hdv hclock hreg htimePlus htimeMinus hbefore hafter x y₀ gPlus gMinus
  refine ⟨r, μ, hr, hμ, ?_⟩
  intro B hB hplus hminus α₀ hα₀ hstart hend hseed
  obtain ⟨W, hW, hyW, α, hα, hαstart, hαend, _, hαact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T (hd.trans hdv)
      (fun t ht => D.regular_subset (hreg t ht)) α₀ hα₀ hseed
  refine ⟨U ∩ W, hU.inter hW, ⟨hyU, hend ▸ hyW⟩, ?_⟩
  intro y hy
  obtain ⟨η, hη, hηzero, hηend, hcost, hmin⟩ :=
    hminima B hB hplus hminus y hy.1 (α y) (hα y hy.2)
      ((hαstart y hy.2).trans hstart) (hαend y hy.2) (hαact y hy.2)
  have hm : ∀ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ → δ 0 = η 0 → δ v = η v →
      lRegularizedAction S T η 0 v ≤ lRegularizedAction S T δ 0 v :=
    fun δ hδ hδzero hδend => hmin δ hδ (hδzero.trans hηzero) (hδend.trans hηend)
  cases hηzero
  obtain ⟨Z, hZ, hZend, _, hact⟩ := exists_lMinimizingVector_of_minimal S hS T (hd.trans hdv) hreg η hη hm
  rw [hηend] at hZend
  refine ⟨Z, hZ, hZend, hcost.trans (congrArg (fun r : ℝ => (r : WithTop ℝ)) hact.symm), ?_⟩
  exact (hact.trans_le (hmin (α y) (hα y hy.2) ((hαstart y hy.2).trans hstart) (hαend y hy.2))).trans_lt
    (hαact y hy.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe uSurvivorAC vSurvivorAC

theorem exists_survivor_curve_action_eq_of_confined_event_competitor
    {P Q : OrientedThreeStage.{uSurvivorAC}} {a s b : ℝ}
    (E : MetricCutCapEvent P Q a s) (G : Q.IncomingSlab s b)
    {X : Type vSurvivorAC} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (f : X → P.Carrier) (g : X → Q.Carrier)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
    (hfi : Function.Injective f)
    (hcross : ∀ x : X, E.RegularCrossing (f x) (g x))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (T : ℝ) {u d v : ℝ} (hud : u ≤ d) (hdv : d ≤ v)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo u d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (alpha : ℝ → Q.Carrier) (beta : ℝ → P.Carrier)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha u d)
    (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta d v)
    (halphaInt : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume u d)
    (hbetaInt : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume d v)
    (halphaStay : MapsTo alpha (Icc u d) (range g))
    (hbetaStay : MapsTo beta (Icc d v) (range f))
    (hnode : ∃ z : E.old, z.val.val = beta d ∧ E.oldOutput z = alpha d) :
    ∃ gamma : ℝ → X,
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      EqOn (g ∘ gamma) alpha (Icc u d) ∧
      EqOn (f ∘ gamma) beta (Icc d v) ∧
      IntervalIntegrable (lRegularizedLagrangian S T gamma) volume u v ∧
      lRegularizedAction S T gamma u v = lRegularizedAction G.flow T alpha u d +
        lRegularizedAction E.incoming.flow T beta d v := by
  classical
  have hgi : Function.Injective g := by
    intro x y hxy
    apply hfi
    exact E.regularCrossing_left_unique
      (by simpa only [hxy] using hcross x) (hcross y)
  let : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  obtain ⟨alpha', halpha', halphaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_absolutelyContinuousOnInterval_lift_of_injective_localDiffeomorph
      g hg hgi alpha halpha (by simpa only [uIcc_of_le hud] using halphaStay)
  obtain ⟨beta', hbeta', hbetaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_absolutelyContinuousOnInterval_lift_of_injective_localDiffeomorph
      f hf hfi beta hbeta (by simpa only [uIcc_of_le hdv] using hbetaStay)
  rw [uIcc_of_le hud] at halphaEq
  rw [uIcc_of_le hdv] at hbetaEq
  have hmatch : alpha' d = beta' d := by
    obtain ⟨z, hz, hzout⟩ := hnode
    obtain ⟨w, _, hw, hwout⟩ := hcross (alpha' d)
    have hzw : z = w := E.oldOutput_injective
      (hzout.trans ((halphaEq ⟨hud, le_rfl⟩).symm.trans hwout.symm))
    apply hfi
    exact hw.symm.trans ((congrArg (fun z : E.old => z.val.val) hzw).symm.trans
      (hz.trans (hbetaEq ⟨le_rfl, hdv⟩).symm))
  let gamma : ℝ → X := (Iic d).piecewise alpha' beta'
  have hgamma : Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic halpha' hbeta' hud hdv hmatch
  have hleft : EqOn (g ∘ gamma) alpha (Icc u d) := by
    intro r hr
    change g (gamma r) = alpha r
    rw [show gamma r = alpha' r from ite_eq_left hr.2]
    exact halphaEq hr
  have hright : EqOn (f ∘ gamma) beta (Icc d v) := by
    intro r hr
    have hright : gamma r = beta' r := by
      rcases hr.1.eq_or_lt with hrd | hrd
      · subst r
        exact (show gamma d = alpha' d from
          piecewise_eq_of_mem (Iic d) alpha' beta' (show d ∈ Iic d from le_refl d)).trans hmatch
      · exact ite_eq_right (not_le.mpr hrd)
    change f (gamma r) = beta r
    rw [hright]
    exact hbetaEq hr
  have hgammaLeft : Manifold.absolutelyContinuousOnInterval ThreeModel gamma u d :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [uIcc_of_le hud, uIcc_of_le (hud.trans hdv)] using Icc_subset_Icc le_rfl hdv)
  have hgammaRight : Manifold.absolutelyContinuousOnInterval ThreeModel gamma d v :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [uIcc_of_le hdv, uIcc_of_le (hud.trans hdv)] using Icc_subset_Icc hud le_rfl)
  have hlagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hud gamma alpha hgammaLeft (hleft.mono Ioo_subset_Icc_self) hafter
  have hlagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hdv gamma beta hgammaRight (hright.mono Ioo_subset_Icc_self) hbefore
  have hintLeft : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume u d :=
    (intervalIntegrable_congr_ae hlagLeft).mpr halphaInt
  have hintRight : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume d v :=
    (intervalIntegrable_congr_ae hlagRight).mpr hbetaInt
  refine ⟨gamma, hgamma, hleft, hright, hintLeft.trans hintRight, ?_⟩
  rw [← lRegularizedAction_add S T gamma u d v hintLeft hintRight]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (intervalIntegral.integral_congr_ae_restrict hlagLeft)
    (intervalIntegral.integral_congr_ae_restrict hlagRight)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe uLocalMin vLocalMin

theorem lRegularizedAction_le_of_minimal_event_competitor
    {P Q : OrientedThreeStage.{uLocalMin}} {a s b : ℝ}
    (E : MetricCutCapEvent P Q a s) (G : Q.IncomingSlab s b)
    {X : Type vLocalMin} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (f : X → P.Carrier) (g : X → Q.Carrier)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
    (hcross : ∀ x : X, E.RegularCrossing (f x) (g x))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (T : ℝ) {l c w d r : ℝ} (hlc : l ≤ c) (hcw : c ≤ w)
    (hwd : w ≤ d) (hdr : d ≤ r)
    (hbefore : ∀ t ∈ Ioo w d, S.base.metric (T - t ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - t ^ 2)) f hf)
    (hafter : ∀ t ∈ Ioo c w, S.base.metric (T - t ^ 2) =
      localPullMetric (G.flow.base.metric (T - t ^ 2)) g hg)
    (alpha : ℝ → Q.Carrier) (beta : ℝ → P.Carrier)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha l w)
    (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta w r)
    (halphaInt : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume l w)
    (hbetaInt : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume w r)
    (hmin : ∀ (alpha' : ℝ → Q.Carrier) (beta' : ℝ → P.Carrier),
      Manifold.absolutelyContinuousOnInterval ThreeModel alpha' l w →
      Manifold.absolutelyContinuousOnInterval ThreeModel beta' w r →
      IntervalIntegrable (lRegularizedLagrangian G.flow T alpha') volume l w →
      IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta') volume w r →
      alpha' l = alpha l → beta' r = beta r →
      (∃ z : E.old, z.val.val = beta' w ∧ E.oldOutput z = alpha' w) →
      lRegularizedAction G.flow T alpha l w + lRegularizedAction E.incoming.flow T beta w r ≤
        lRegularizedAction G.flow T alpha' l w + lRegularizedAction E.incoming.flow T beta' w r)
    (gamma : ℝ → X)
    (hgamma : Manifold.absolutelyContinuousOnInterval ThreeModel gamma c d)
    (hleft : EqOn (g ∘ gamma) alpha (Icc c w))
    (hright : EqOn (f ∘ gamma) beta (Icc w d)) :
    ∀ delta : ℝ → X, Manifold.absolutelyContinuousOnInterval ThreeModel delta c d →
      IntervalIntegrable (lRegularizedLagrangian S T delta) volume c d →
      delta c = gamma c → delta d = gamma d →
      lRegularizedAction S T gamma c d ≤ lRegularizedAction S T delta c d := by
  classical
  let : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  intro delta hdelta hdeltaInt hdeltaC hdeltaD
  have hcd := hcw.trans hwd
  have hlw := hlc.trans hcw
  have hwr := hwd.trans hdr
  have hacLeft (eta : ℝ → X)
      (heta : Manifold.absolutelyContinuousOnInterval ThreeModel eta c d) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta c w :=
    Manifold.absolutelyContinuousOnInterval_mono heta (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hacRight (eta : ℝ → X)
      (heta : Manifold.absolutelyContinuousOnInterval ThreeModel eta c d) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta w d :=
    Manifold.absolutelyContinuousOnInterval_mono heta (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  have hintLeft (eta : ℝ → X)
      (heta : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume c w :=
    heta.mono_set (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hintRight (eta : ℝ → X)
      (heta : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume w d :=
    heta.mono_set (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  have hgammaLagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hcw gamma alpha (hacLeft gamma hgamma) (hleft.mono Ioo_subset_Icc_self) hafter
  have hgammaLagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hwd gamma beta (hacRight gamma hgamma) (hright.mono Ioo_subset_Icc_self) hbefore
  have hdeltaLagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hcw delta (g ∘ delta) (hacLeft delta hdelta) (fun _ _ => rfl) hafter
  have hdeltaLagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hwd delta (f ∘ delta) (hacRight delta hdelta) (fun _ _ => rfl) hbefore
  have hgdelta := Manifold.absolutelyContinuousOnInterval_comp_contMDiff
    (hacLeft delta hdelta) (hg.contMDiff.of_le (by norm_num))
  have hfdelta := Manifold.absolutelyContinuousOnInterval_comp_contMDiff
    (hacRight delta hdelta) (hf.contMDiff.of_le (by norm_num))
  have hgdeltaInt := (intervalIntegrable_congr_ae hdeltaLagLeft).mp (hintLeft delta hdeltaInt)
  have hfdeltaInt := (intervalIntegrable_congr_ae hdeltaLagRight).mp (hintRight delta hdeltaInt)
  have halphaLeft : Manifold.absolutelyContinuousOnInterval ThreeModel alpha l c :=
    Manifold.absolutelyContinuousOnInterval_mono halpha (by
      simpa only [uIcc_of_le hlc, uIcc_of_le hlw] using Icc_subset_Icc le_rfl hcw)
  have hbetaRight : Manifold.absolutelyContinuousOnInterval ThreeModel beta d r :=
    Manifold.absolutelyContinuousOnInterval_mono hbeta (by
      simpa only [uIcc_of_le hdr, uIcc_of_le hwr] using Icc_subset_Icc hwd le_rfl)
  have hmatchLeft : alpha c = (g ∘ delta) c :=
    (hleft ⟨le_rfl, hcw⟩).symm.trans (congrArg g hdeltaC.symm)
  have hmatchRight : (f ∘ delta) d = beta d :=
    (congrArg f hdeltaD).trans (hright ⟨hwd, le_rfl⟩)
  let alpha' : ℝ → Q.Carrier := (Iic c).piecewise alpha (g ∘ delta)
  let beta' : ℝ → P.Carrier := (Iic d).piecewise (f ∘ delta) beta
  have halpha' : Manifold.absolutelyContinuousOnInterval ThreeModel alpha' l w :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic halphaLeft hgdelta hlc hcw hmatchLeft
  have hbeta' : Manifold.absolutelyContinuousOnInterval ThreeModel beta' w r :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic hfdelta hbetaRight hwd hdr hmatchRight
  have halphaEqLeft : EqOn alpha' alpha (Icc l c) := fun _ ht => ite_eq_left ht.2
  have halphaEqRight : EqOn alpha' (g ∘ delta) (Icc c w) := by
    intro t ht
    rcases ht.1.eq_or_lt with ht | ht
    · subst t
      exact (show alpha' c = alpha c from piecewise_eq_of_mem (Iic c) alpha (g ∘ delta) (show c ∈ Iic c from le_refl c)).trans hmatchLeft
    · exact ite_eq_right (not_le.mpr ht)
  have hbetaEqLeft : EqOn beta' (f ∘ delta) (Icc w d) := fun _ ht => ite_eq_left ht.2
  have hbetaEqRight : EqOn beta' beta (Icc d r) := by
    intro t ht
    rcases ht.1.eq_or_lt with ht | ht
    · subst t
      exact (show beta' d = (f ∘ delta) d from piecewise_eq_of_mem (Iic d) (f ∘ delta) beta (show d ∈ Iic d from le_refl d)).trans hmatchRight
    · exact ite_eq_right (not_le.mpr ht)
  have hlag {Y : Type uLocalMin} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
      [IsManifold ThreeModel ∞ Y] {D' : RealTimeInterval}
      (R : SolutionOn (I := ThreeModel) (M := Y) D')
      (eta zeta : ℝ → Y) (x y : ℝ) (hxy : x ≤ y) (heq : EqOn eta zeta (Icc x y)) :
      EqOn (lRegularizedLagrangian R T eta) (lRegularizedLagrangian R T zeta) (uIoo x y) := by
    intro t ht
    rw [uIoo_of_le hxy] at ht
    have hn : eta =ᶠ[𝓝 t] zeta := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
      exact heq (Ioo_subset_Icc_self hz)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold lRegularizedLagrangian lVelocity
    rw [hder, hv]
    rfl
  have halphaIntLeft : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume l c := halphaInt.mono_set (by
    simpa only [uIcc_of_le hlc, uIcc_of_le hlw] using Icc_subset_Icc le_rfl hcw)
  have halphaIntRight : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume c w := halphaInt.mono_set (by
    simpa only [uIcc_of_le hcw, uIcc_of_le hlw] using Icc_subset_Icc hlc le_rfl)
  have hbetaIntLeft : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume w d := hbetaInt.mono_set (by
    simpa only [uIcc_of_le hwd, uIcc_of_le hwr] using Icc_subset_Icc le_rfl hdr)
  have hbetaIntRight : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume d r := hbetaInt.mono_set (by
    simpa only [uIcc_of_le hdr, uIcc_of_le hwr] using Icc_subset_Icc hwd le_rfl)
  have hgammaInt : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume c d :=
    ((intervalIntegrable_congr_ae hgammaLagLeft).mpr halphaIntRight).trans
      ((intervalIntegrable_congr_ae hgammaLagRight).mpr hbetaIntLeft)
  have hlagAL := hlag G.flow alpha' alpha l c hlc halphaEqLeft
  have hlagAR := hlag G.flow alpha' (g ∘ delta) c w hcw halphaEqRight
  have hlagBL := hlag E.incoming.flow beta' (f ∘ delta) w d hwd hbetaEqLeft
  have hlagBR := hlag E.incoming.flow beta' beta d r hdr hbetaEqRight
  have hintAL := halphaIntLeft.congr_uIoo hlagAL.symm
  have hintAR := hgdeltaInt.congr_uIoo hlagAR.symm
  have hintBL := hfdeltaInt.congr_uIoo hlagBL.symm
  have hintBR := hbetaIntRight.congr_uIoo hlagBR.symm
  have hnode : ∃ z : E.old, z.val.val = beta' w ∧ E.oldOutput z = alpha' w := by
    obtain ⟨z, _, hz, hzout⟩ := hcross (delta w)
    exact ⟨z, hz.trans (hbetaEqLeft ⟨le_rfl, hwd⟩).symm,
      hzout.trans (halphaEqRight ⟨hcw, le_rfl⟩).symm⟩
  have hwhole := hmin alpha' beta' halpha' hbeta'
    (hintAL.trans hintAR) (hintBL.trans hintBR)
    (halphaEqLeft ⟨le_rfl, hlc⟩) (hbetaEqRight ⟨hdr, le_rfl⟩) hnode
  rw [← lRegularizedAction_add G.flow T alpha l c w halphaIntLeft halphaIntRight,
    ← lRegularizedAction_add E.incoming.flow T beta w d r hbetaIntLeft hbetaIntRight,
    ← lRegularizedAction_add G.flow T alpha' l c w hintAL hintAR,
    ← lRegularizedAction_add E.incoming.flow T beta' w d r hintBL hintBR,
    show lRegularizedAction G.flow T alpha' l c = lRegularizedAction G.flow T alpha l c from
      intervalIntegral.integral_congr_uIoo hlagAL,
    show lRegularizedAction G.flow T alpha' c w = lRegularizedAction G.flow T (g ∘ delta) c w from
      intervalIntegral.integral_congr_uIoo hlagAR,
    show lRegularizedAction E.incoming.flow T beta' w d =
        lRegularizedAction E.incoming.flow T (f ∘ delta) w d from
      intervalIntegral.integral_congr_uIoo hlagBL,
    show lRegularizedAction E.incoming.flow T beta' d r = lRegularizedAction E.incoming.flow T beta d r from
      intervalIntegral.integral_congr_uIoo hlagBR] at hwhole
  have hgact : lRegularizedAction S T gamma c d =
      lRegularizedAction G.flow T alpha c w + lRegularizedAction E.incoming.flow T beta w d := by
    rw [← lRegularizedAction_add S T gamma c w d (hintLeft gamma hgammaInt) (hintRight gamma hgammaInt)]
    exact congrArg₂ (fun x y : ℝ => x + y)
      (intervalIntegral.integral_congr_ae_restrict hgammaLagLeft)
      (intervalIntegral.integral_congr_ae_restrict hgammaLagRight)
  have hdact : lRegularizedAction S T delta c d =
      lRegularizedAction G.flow T (g ∘ delta) c w + lRegularizedAction E.incoming.flow T (f ∘ delta) w d := by
    rw [← lRegularizedAction_add S T delta c w d (hintLeft delta hdeltaInt) (hintRight delta hdeltaInt)]
    exact congrArg₂ (fun x y : ℝ => x + y)
      (intervalIntegral.integral_congr_ae_restrict hdeltaLagLeft)
      (intervalIntegral.integral_congr_ae_restrict hdeltaLagRight)
  rw [hgact, hdact]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
