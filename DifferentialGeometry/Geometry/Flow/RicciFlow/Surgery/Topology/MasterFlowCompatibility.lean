import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import DifferentialGeometry.Geometry.Metric.Conformal.Basic

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure MasterFlow (P : OrientedThreeStage.{u}) (J₁ J₂ : Set ℝ)
    (f₁ f₂ : ℝ → P.Metric) where
  metric : ℝ → P.Metric
  metric_eq_left : ∀ τ ∈ J₁, metric τ = f₁ τ
  metric_eq_right : ∀ τ ∈ J₂, metric τ = f₂ τ

namespace MasterFlow

variable {P : OrientedThreeStage.{u}} {J₁ J₂ : Set ℝ} {f₁ f₂ : ℝ → P.Metric}

theorem eq_of_mem (F : MasterFlow P J₁ J₂ f₁ f₂) {τ : ℝ}
    (h₁ : τ ∈ J₁) (h₂ : τ ∈ J₂) :
    f₁ τ = f₂ τ :=
  (F.metric_eq_left τ h₁).symm.trans (F.metric_eq_right τ h₂)

theorem not_nonempty_of_ne {τ : ℝ} (h₁ : τ ∈ J₁) (h₂ : τ ∈ J₂)
    (h : f₁ τ ≠ f₂ τ) :
    ¬ Nonempty (MasterFlow P J₁ J₂ f₁ f₂) :=
  fun ⟨F⟩ => h (F.eq_of_mem (τ := τ) h₁ h₂)

end MasterFlow

def masterFlowOfAgree {P : OrientedThreeStage.{u}} {J₁ J₂ : Set ℝ}
    {f₁ f₂ : ℝ → P.Metric} (h : ∀ τ ∈ J₁, τ ∈ J₂ → f₁ τ = f₂ τ) :
    MasterFlow P J₁ J₂ f₁ f₂ := by
  classical
  exact
    { metric := fun τ => if τ ∈ J₁ then f₁ τ else f₂ τ
      metric_eq_left := fun τ hτ => if_pos hτ
      metric_eq_right := fun τ hτ => by
        by_cases h₁ : τ ∈ J₁
        · rw [if_pos h₁]
          exact h τ h₁ hτ
        · rw [if_neg h₁] }

theorem nonempty_masterFlow_iff {P : OrientedThreeStage.{u}} {J₁ J₂ : Set ℝ}
    {f₁ f₂ : ℝ → P.Metric} :
    Nonempty (MasterFlow P J₁ J₂ f₁ f₂) ↔
      ∀ τ ∈ J₁, τ ∈ J₂ → f₁ τ = f₂ τ :=
  ⟨fun ⟨F⟩ τ h₁ h₂ => F.eq_of_mem (τ := τ) h₁ h₂,
    fun h => ⟨masterFlowOfAgree h⟩⟩

namespace ObservedHistory

variable {H : ObservedHistory.{u}}

theorem stageMetric_last_of_lt {h : H.time (Fin.last H.eventCount) < H.horizon} (τ : ℝ) :
    H.stageMetric (Fin.last H.eventCount) τ =
      (H.finalSlab h).flow.base.metric τ := by
  rw [ObservedHistory.stageMetric, Fin.lastCases_last, dif_pos h]

theorem stageMetric_last_of_le (h : H.horizon ≤ H.time (Fin.last H.eventCount)) (τ : ℝ) :
    H.stageMetric (Fin.last H.eventCount) τ = H.initialMetric (Fin.last H.eventCount) := by
  rw [ObservedHistory.stageMetric, Fin.lastCases_last, dif_neg (not_lt.mpr h)]

theorem mem_stageDomain_last (H : ObservedHistory.{u}) (τ : ℝ) :
    τ ∈ H.stageDomain (Fin.last H.eventCount) ↔
      τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
  rw [ObservedHistory.stageDomain, Fin.lastCases_last]

theorem restrict_time_last (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (hb : K.activeStage b = Fin.last K.eventCount) :
    (K.restrict b).time (Fin.last (K.restrict b).eventCount) = K.time (Fin.last K.eventCount) := by
  have h := ObservedHistory.restrict_time_apply K b (Fin.last ((K.activeStage b).val))
  exact h.trans (congrArg K.time (Fin.ext (by simp [hb])))

end ObservedHistory

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

abbrev eventMasterFlow (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) :=
  MasterFlow (H.stage (Fin.last H.eventCount))
    (Icc (H.time (Fin.last H.eventCount)) s)
    (Icc (H.time (Fin.last H.eventCount)) H.horizon)
    E.incoming.flow.base.metric (fun τ => (H.toHistory).stageMetric (Fin.last H.eventCount) τ)

theorem appendEventCompatible_of_masterFlow (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (F : H.eventMasterFlow E)
    (hle : H.horizon ≤ s) : H.appendEventCompatible E := by
  intro hh τ hτ
  exact (F.metric_eq_left τ ⟨hτ.1, hτ.2.trans hle⟩).symm.trans
    ((F.metric_eq_right τ hτ).trans
      (ObservedHistory.stageMetric_last_of_lt (H := H.toHistory) (h := hh) τ))

theorem exists_eventMasterFlow_of_appendEventCompatible (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hne : H.time (Fin.last H.eventCount) < H.horizon)
    (hc : H.appendEventCompatible E) : Nonempty (H.eventMasterFlow E) := by
  refine ⟨masterFlowOfAgree ?_⟩
  intro τ _ h₂
  rw [ObservedHistory.stageMetric_last_of_lt (H := H.toHistory) (h := hne) τ]
  exact hc hne τ h₂

theorem appendEventCompatible_iff_nonempty_eventMasterFlow (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hne : H.time (Fin.last H.eventCount) < H.horizon) (hle : H.horizon ≤ s) :
    H.appendEventCompatible E ↔ Nonempty (H.eventMasterFlow E) :=
  ⟨exists_eventMasterFlow_of_appendEventCompatible H E hne,
    fun ⟨F⟩ => appendEventCompatible_of_masterFlow H E F hle⟩

theorem exists_eventMasterFlow_of_time_eq_horizon (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (htime : H.time (Fin.last H.eventCount) = H.horizon) :
    Nonempty (H.eventMasterFlow E) := by
  refine ⟨masterFlowOfAgree ?_⟩
  intro τ _ h₂
  have hτ : τ = H.time (Fin.last H.eventCount) := le_antisymm (htime ▸ h₂.2) h₂.1
  subst hτ
  exact hinit.trans (ObservedHistory.stageMetric_last_of_le (H := H.toHistory)
    (h := le_of_eq htime.symm) (H.time (Fin.last H.eventCount))).symm

theorem exists_eventMasterFlow_atZero (P : OrientedThreeStage.{u}) (g : P.Metric)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (E : RetainedCoreEvent P Q 0 s)
    (hinit : E.incoming.flow.base.metric 0 = g) :
    Nonempty ((RetainedCoreHistory.atZero P g).eventMasterFlow E) :=
  exists_eventMasterFlow_of_time_eq_horizon (RetainedCoreHistory.atZero P g) E hinit rfl

abbrev horizonMasterFlow (H : RetainedCoreHistory P) (T : ℝ)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T) :=
  MasterFlow (H.stage (Fin.last H.eventCount))
    (Icc (H.time (Fin.last H.eventCount)) T)
    (Icc (H.time (Fin.last H.eventCount)) H.horizon)
    S.flow.base.metric (fun τ => (H.toHistory).stageMetric (Fin.last H.eventCount) τ)

def extendHorizonCompatible (H : RetainedCoreHistory P) (T : ℝ)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T) : Prop :=
  ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon,
    S.flow.base.metric τ = (H.toHistory).stageMetric (Fin.last H.eventCount) τ

theorem exists_horizonMasterFlow_iff_extendHorizonCompatible (H : RetainedCoreHistory P) (T : ℝ)
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T) :
    Nonempty (H.horizonMasterFlow T S) ↔ H.extendHorizonCompatible T S := by
  rw [nonempty_masterFlow_iff]
  constructor
  · intro h τ hτ
    exact h τ ⟨hτ.1, hτ.2.trans hT⟩ hτ
  · intro h τ _ h₂
    exact h τ h₂

theorem exists_horizonMasterFlow_of_extendHorizonCompatible (H : RetainedCoreHistory P) (T : ℝ)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hcompat : H.extendHorizonCompatible T S) : Nonempty (H.horizonMasterFlow T S) :=
  ⟨masterFlowOfAgree fun τ _ h₂ => hcompat τ h₂⟩

theorem extendHorizonCompatible_of_time_eq_horizon (H : RetainedCoreHistory P) (T : ℝ)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (htime : H.time (Fin.last H.eventCount) = H.horizon) : H.extendHorizonCompatible T S := by
  intro τ hτ
  have hτeq : τ = H.time (Fin.last H.eventCount) := le_antisymm (htime ▸ hτ.2) hτ.1
  subst hτeq
  exact hS.trans (ObservedHistory.stageMetric_last_of_le (H := H.toHistory)
    (h := le_of_eq htime.symm) (H.time (Fin.last H.eventCount))).symm

theorem exists_horizonMasterFlow_finalSlab (H : RetainedCoreHistory P)
    (hh : H.time (Fin.last H.eventCount) < H.horizon) :
    Nonempty (H.horizonMasterFlow H.horizon (H.finalSlab hh)) :=
  exists_horizonMasterFlow_of_extendHorizonCompatible H H.horizon (H.finalSlab hh)
    fun τ _ => (ObservedHistory.stageMetric_last_of_lt (H := H.toHistory) (h := hh) τ).symm

theorem toHistory_extendHorizon_horizon (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).toHistory.horizon = T := rfl

theorem extendHorizon_stageMetric_last (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hcompat : H.extendHorizonCompatible T S) {τ : ℝ}
    (hτ : τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon) :
    (H.extendHorizon T hT S hS).toHistory.stageMetric (Fin.last H.eventCount) τ =
      H.toHistory.stageMetric (Fin.last H.eventCount) τ := by
  by_cases hlt : H.time (Fin.last H.eventCount) < H.horizon
  · exact (ObservedHistory.stageMetric_last_of_lt
        (H := (H.extendHorizon T hT S hS).toHistory) (h := hlt.trans_le hT) τ).trans
      (hcompat τ hτ)
  · have hle : H.horizon ≤ H.time (Fin.last H.eventCount) := not_lt.mp hlt
    have hτeq : τ = H.time (Fin.last H.eventCount) := le_antisymm (hτ.2.trans hle) hτ.1
    subst hτeq
    have hR := ObservedHistory.stageMetric_last_of_le (H := H.toHistory) (h := hle)
      (H.time (Fin.last H.eventCount))
    rw [hR]
    by_cases hT' : H.time (Fin.last H.eventCount) < T
    · exact (ObservedHistory.stageMetric_last_of_lt
          (H := (H.extendHorizon T hT S hS).toHistory) (h := hT')
          (H.time (Fin.last H.eventCount))).trans
        ((hcompat (H.time (Fin.last H.eventCount)) ⟨le_rfl, H.time_le_horizon⟩).trans hR)
    · exact ObservedHistory.stageMetric_last_of_le
        (H := (H.extendHorizon T hT S hS).toHistory) (h := not_lt.mp hT')
        (H.time (Fin.last H.eventCount))

theorem extendHorizon_restrict_samePresentation (H : RetainedCoreHistory P) (T : ℝ)
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hcompat : H.extendHorizonCompatible T S)
    (b : Icc (0 : ℝ) (H.extendHorizon T hT S hS).toHistory.horizon) (hb : b.1 = H.horizon) :
    (((H.extendHorizon T hT S hS).toHistory).restrict b).SamePresentation H.toHistory := by
  let E := (H.extendHorizon T hT S hS).toHistory
  have ha : E.activeStage b = Fin.last H.eventCount := by
    refine E.activeStage_eq_of_maximal b _ ?_ (fun _ _ => Fin.le_last _)
    rw [hb]
    exact H.time_le_horizon
  have hc : (E.restrict b).eventCount = H.eventCount := congrArg Fin.val ha
  let castE : Fin ((E.restrict b).eventCount) → Fin E.eventCount :=
    Fin.castLE (Nat.le_of_lt_succ (E.activeStage b).isLt)
  refine {
    horizon_eq := ?_
    count_eq := hc
    time_eq := fun _ => rfl
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun _ => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }
  · rw [ObservedHistory.restrict_horizon, hb]
  intro j t ht
  refine (E.restrict_stageMetric b j t ht).trans ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · change HEq (E.stageMetric ((castE i).castSucc) t)
      (H.toHistory.stageMetric ((Fin.cast hc i).castSucc) t)
    exact (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := E) (castE i) t)).trans
      (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := H.toHistory)
        (Fin.cast hc i) t)).symm
  · have hidxE : Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (E.activeStage b).isLt) 1)
        (Fin.last (E.restrict b).eventCount) =
        (Fin.last H.eventCount : Fin (E.eventCount + 1)) := by
      refine Fin.ext ?_
      have h1 : (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (E.activeStage b).isLt) 1)
          (Fin.last (E.restrict b).eventCount)).val = (E.restrict b).eventCount := rfl
      have h2 : ((Fin.last H.eventCount : Fin (E.eventCount + 1))).val = H.eventCount := rfl
      rw [h1, h2, hc]
    have hidxH : Fin.cast (congrArg (· + 1) hc) (Fin.last (E.restrict b).eventCount)
        = Fin.last H.eventCount := by
      refine Fin.ext ?_
      have h1 : (Fin.cast (congrArg (· + 1) hc)
          (Fin.last (E.restrict b).eventCount)).val = (E.restrict b).eventCount := rfl
      have h2 : (Fin.last H.eventCount).val = H.eventCount := rfl
      rw [h1, h2, hc]
    rw [hidxE, hidxH]
    have hmem : t ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      have h1 : t ∈ Icc ((E.restrict b).time (Fin.last (E.restrict b).eventCount))
          (E.restrict b).horizon :=
        (ObservedHistory.mem_stageDomain_last (E.restrict b) t).mp ht
      rw [ObservedHistory.restrict_horizon, hb] at h1
      have hEtime : E.time = H.time := rfl
      have ht' := ObservedHistory.restrict_time_last E b ha
      rw [hEtime] at ht'
      exact ⟨show H.time (Fin.last H.eventCount) ≤ t from (le_of_eq ht'.symm).trans h1.1,
        show t ≤ H.horizon from h1.2⟩
    exact heq_of_eq (extendHorizon_stageMetric_last H T hT S hS hcompat hmem)

theorem extendHorizon_isPrefixOf (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hcompat : H.extendHorizonCompatible T S) :
    H.toHistory.IsPrefixOf (H.extendHorizon T hT S hS).toHistory :=
  ⟨hT.trans (le_of_eq (toHistory_extendHorizon_horizon H T hT S hS).symm),
    extendHorizon_restrict_samePresentation H T hT S hS hcompat
      (⟨H.horizon, H.horizon_nonneg,
        hT.trans (le_of_eq (toHistory_extendHorizon_horizon H T hT S hS).symm)⟩ :
        Icc (0 : ℝ) (H.extendHorizon T hT S hS).toHistory.horizon) rfl⟩

theorem appendEvent_extendHorizon_successor (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s T : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
      (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hhor : H.horizon < s) (hT : s ≤ T)
    (S : ((H.appendEvent hs E hinit).stage
        (Fin.last (H.appendEvent hs E hinit).eventCount)).ClosedSlab
      ((H.appendEvent hs E hinit).time (Fin.last (H.appendEvent hs E hinit).eventCount)) T)
    (hS : S.flow.base.metric ((H.appendEvent hs E hinit).time
        (Fin.last (H.appendEvent hs E hinit).eventCount)) =
      (H.appendEvent hs E hinit).initialMetric (Fin.last (H.appendEvent hs E hinit).eventCount))
    (hcompat : H.appendEventCompatible E)
    (hslab : (H.appendEvent hs E hinit).extendHorizonCompatible T S) :
    (((H.appendEvent hs E hinit).extendHorizon T hT S hS).toHistory.restrict
      ⟨H.horizon, H.horizon_nonneg, hhor.le.trans hT⟩).SamePresentation H.toHistory :=
  ((appendEvent_isPrefixOf H hs E hinit hhor hcompat).trans
    (extendHorizon_isPrefixOf (H.appendEvent hs E hinit) T hT S hS hslab)).presentation

theorem exists_tangentVector_ne_zero (P : OrientedThreeStage.{u}) (p : P.Carrier) :
    ∃ v : TangentSpace ThreeModel p, v ≠ 0 := by
  classical
  have hb := mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  refine ⟨(tangentChartEquiv (M := P.Carrier) p p hb).symm
    (EuclideanSpace.single 0 (1 : ℝ)), ?_⟩
  intro h0
  have h1 := congrArg (tangentChartEquiv (M := P.Carrier) p p hb) h0
  simp only [LinearEquiv.apply_symm_apply, map_zero] at h1
  have h2 : (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have hv := congrArg (fun f : EuclideanSpace ℝ (Fin 3) => f.ofLp 0) h
    rw [PiLp.single_apply] at hv
    simp at hv
  exact h2 h1

theorem conformalMetric_const_one_ne (P : OrientedThreeStage.{u}) (g : P.Metric)
    (p : P.Carrier) :
    DifferentialGeometry.conformalMetric g (ContMDiffMap.const (1 : ℝ)) ≠ g := by
  obtain ⟨v, hv⟩ := exists_tangentVector_ne_zero P p
  intro h
  have hpos := g.pos p v hv
  have h2 : Real.exp 2 * g.inner p v v = g.inner p v v := by
    have h3 := congrArg (fun m : P.Metric => m.inner p v v) h
    rw [DifferentialGeometry.conformalMetric_inner] at h3
    have h4 : ((ContMDiffMap.const (1 : ℝ) : C^∞⟮ThreeModel, P.Carrier; ℝ⟯)) p = 1 := rfl
    rw [h4, mul_one] at h3
    exact h3
  have h4 : Real.exp 2 = 1 :=
    mul_right_cancel₀ (ne_of_gt hpos) (by rw [h2, one_mul])
  have h5 : (2 : ℝ) = 0 := by
    have := congrArg Real.log h4
    rw [Real.log_exp, Real.log_one] at this
    exact this
  norm_num at h5

theorem not_nonempty_masterFlow_conformalMetric_const_one (P : OrientedThreeStage.{u})
    (g : P.Metric) (p : P.Carrier) :
    ¬ Nonempty (MasterFlow P Set.univ Set.univ
      (fun _ => DifferentialGeometry.conformalMetric g (ContMDiffMap.const (1 : ℝ)))
      (fun _ => g)) :=
  MasterFlow.not_nonempty_of_ne (Set.mem_univ 0) (Set.mem_univ 0)
    (conformalMetric_const_one_ne P g p)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
