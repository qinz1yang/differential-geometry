import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

theorem metric_eq_of_isEmpty (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g h : P.Metric) : g = h :=
  SmoothRiemannianMetric.ext_inner fun x => isEmptyElim x

def emptyClosedSlab (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) {a b : ℝ} (hab : a < b) : P.ClosedSlab a b where
  lt := hab
  flow := ⟨⟨fun _ => g⟩⟩
  equation := {
    smoothMetric := {
      coeff := fun x => isEmptyElim x
      coeff_cont := fun x => isEmptyElim x
      metricTensor_cont := continuous_iff_continuousAt.mpr fun q => isEmptyElim q.2
      frameCompSmooth := by
        intro Idx _ frame U hframe i j q hq
        exact isEmptyElim q.2 }
    smoothConnection := fun _ =>
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative g
    equation := fun _ x => isEmptyElim x
    scalarCont := fun q _ => isEmptyElim q.2
    scalarTime := fun _ _ x => isEmptyElim x
    ricciCont := continuous_iff_continuousAt.mpr fun q => isEmptyElim q.2
    rm04Cont := continuous_iff_continuousAt.mpr fun q => isEmptyElim q.2
    ricciNormSpace := fun _ _ x => isEmptyElim x
    ricciNormGrad := fun _ _ x => isEmptyElim x }
  smoothUpTo := fun x => isEmptyElim x

end OrientedThreeStage

namespace ObservedHistory

variable (H : ObservedHistory.{u})

def emptyExtension [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : ObservedHistory.{u} :=
  { H with
    horizon := B
    horizon_nonneg := H.horizon_nonneg.trans hB
    time_le_horizon := H.time_le_horizon.trans hB
    finalSlab := fun h => (H.stage (Fin.last H.eventCount)).emptyClosedSlab
      (H.initialMetric (Fin.last H.eventCount)) h
    final_initial := fun _ => rfl }

@[simp] theorem emptyExtension_horizon
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : (H.emptyExtension B hB).horizon = B := rfl

theorem isPrefixOf_emptyExtension
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : H.IsPrefixOf (H.emptyExtension B hB) := by
  let E := H.emptyExtension B hB
  let b : Icc (0 : ℝ) E.horizon := ⟨H.horizon, H.horizon_nonneg, hB⟩
  have ha : E.activeStage b = Fin.last H.eventCount :=
    E.activeStage_eq_of_maximal b _ H.time_le_horizon (fun _ _ => Fin.le_last _)
  have hc : (E.restrict b).eventCount = H.eventCount := congrArg Fin.val ha
  refine ⟨hB, {
    horizon_eq := rfl
    count_eq := hc
    time_eq := fun _ => rfl
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun _ => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }⟩
  intro j t ht
  have hm := E.restrict_stageMetric b j t ht
  apply hm.trans
  let k : Fin (H.eventCount + 1) := Fin.cast (congrArg (· + 1) hc) j
  change HEq (E.stageMetric k t) (H.stageMetric k t)
  cases k using Fin.lastCases with
  | cast i =>
    simp only [E, emptyExtension] at *
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl
  | last =>
    apply heq_of_eq
    exact (H.stage (Fin.last H.eventCount)).metric_eq_of_isEmpty _ _

theorem IsPrefixOf.eventCount_eq_of_empty {H K : ObservedHistory.{u}}
    (h : H.IsPrefixOf K) [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] :
    K.eventCount = H.eventCount := by
  let a : Icc (0 : ℝ) H.horizon := ⟨H.horizon, H.horizon_nonneg, le_rfl⟩
  let b : Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩
  have he : H.stage (Fin.last H.eventCount) = K.stageAt b := by
    have hs := h.stageAt_eq a
    simpa only [a, b, stageAt, activeStage_at_horizon] using hs
  let : IsEmpty (K.stageAt b).Carrier := he ▸ inferInstance
  have hb := K.empty_stage_is_last (K.activeStage b)
  have hc := h.presentation.count_eq
  change (K.activeStage b).val = H.eventCount at hc
  rw [hb] at hc
  exact hc

theorem emptyExtension_unique
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) (K : ObservedHistory.{u})
    (hK : H.IsPrefixOf K) (horizon_eq : K.horizon = B) :
    (H.emptyExtension B hB).SamePresentation K := by
  let E := H.emptyExtension B hB
  let b : Icc (0 : ℝ) K.horizon :=
    ⟨H.horizon, H.horizon_nonneg, hK.horizon_le⟩
  have R := hK.presentation.symm
  have hc : H.eventCount = K.eventCount := hK.eventCount_eq_of_empty.symm
  refine {
    horizon_eq := horizon_eq.symm
    count_eq := hc
    time_eq := fun j => R.time_eq j
    stage_eq := fun j => R.stage_eq j
    initialMetric_heq := fun j => R.initialMetric_heq j
    event_eq := fun i => R.event_eq i
    metric_heq := ?_ }
  intro j t ht
  cases j using Fin.lastCases with
  | cast i =>
    change Fin H.eventCount at i
    dsimp only [emptyExtension] at *
    have htime : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
      simpa only [emptyExtension, stageDomain, Fin.lastCases_castSucc] using ht
    have hevent : (H.event i).SamePresentation (K.event (Fin.cast hc i)) := R.event_eq i
    have hm := hevent.incomingMetric_heq t htime
    have hi : Fin.cast (congrArg (· + 1) hc) i.castSucc =
        (Fin.cast hc i).castSucc := Fin.ext rfl
    let iE : Fin (H.emptyExtension B hB).eventCount := ⟨i.val, i.isLt⟩
    change HEq ((H.emptyExtension B hB).stageMetric iE.castSucc t)
      (K.stageMetric (Fin.cast (congrArg (· + 1) hc) i.castSucc) t)
    rw [hi]
    simp only [stageMetric, Fin.lastCases_castSucc]
    exact hm
  | last =>
    have he := R.stage_eq (Fin.last H.eventCount)
    have hmetrics : ∀ (P Q : OrientedThreeStage.{u}), P = Q →
        IsEmpty P.Carrier → ∀ (g : P.Metric) (k : Q.Metric), HEq g k := by
      intro P Q he hempty g k
      subst Q
      let := hempty
      exact heq_of_eq (P.metric_eq_of_isEmpty g k)
    exact hmetrics _ _ he inferInstance _ _

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

def emptyExtension (A : InitialIdentification P g H)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : InitialIdentification P g (H.emptyExtension B hB) where
  map := A.map
  positive := A.positive
  metric_eq := A.metric_eq

theorem isPrefixOf_emptyExtension (A : InitialIdentification P g H)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : A.IsPrefixOf (A.emptyExtension B hB) :=
  ⟨H.isPrefixOf_emptyExtension B hB, HEq.rfl⟩

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
