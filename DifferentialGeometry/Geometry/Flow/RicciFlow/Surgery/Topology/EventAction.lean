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
    if_pos ht
  have hright (t : ℝ) (ht : s < t) : S.base.metric t = Splus.base.metric t := if_neg (not_le.mpr ht)
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
