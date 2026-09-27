import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCompatibility

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable {H K L : ObservedHistory.{u}}

def IsPrefixOf (H K : ObservedHistory.{u}) : Prop :=
  ∃ h : H.horizon ≤ K.horizon,
    (K.restrict ⟨H.horizon, H.horizon_nonneg, h⟩).SamePresentation H

theorem IsPrefixOf.horizon_le (h : H.IsPrefixOf K) : H.horizon ≤ K.horizon := h.choose

theorem IsPrefixOf.presentation (h : H.IsPrefixOf K) :
    (K.restrict ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩).SamePresentation H :=
  h.choose_spec

@[refl] theorem IsPrefixOf.refl (H : ObservedHistory.{u}) : H.IsPrefixOf H :=
  ⟨le_rfl, H.restrict_self⟩

theorem restrict_isPrefixOf (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) : (H.restrict t).IsPrefixOf H :=
  ⟨t.2.2, SamePresentation.refl _⟩

@[trans] theorem IsPrefixOf.trans (h : H.IsPrefixOf K) (k : K.IsPrefixOf L) :
    H.IsPrefixOf L := by
  rcases h with ⟨hHK, R⟩
  rcases k with ⟨hKL, S⟩
  let b : Icc (0 : ℝ) L.horizon := ⟨K.horizon, K.horizon_nonneg, hKL⟩
  let a : Icc (0 : ℝ) (L.restrict b).horizon :=
    ⟨H.horizon, H.horizon_nonneg, hHK⟩
  refine ⟨hHK.trans hKL, ?_⟩
  exact ((L.restrict_restrict b a).symm.trans
    (SamePresentation.restrict (L.restrict b) S a)).trans R

theorem IsPrefixOf.antisymm (h : H.IsPrefixOf K) (k : K.IsPrefixOf H) :
    H.SamePresentation K := by
  have he : H.horizon = K.horizon := le_antisymm h.horizon_le k.horizon_le
  have ht : (⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩ : Icc (0 : ℝ) K.horizon) =
      ⟨K.horizon, K.horizon_nonneg, le_rfl⟩ := Subtype.ext he
  have R := h.presentation
  rw [ht] at R
  exact R.symm.trans K.restrict_self

theorem SamePresentation.eventTimes_eq (R : H.SamePresentation K) :
    H.eventTimes = K.eventTimes := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast R.count_eq i, ?_⟩
    exact (R.time_eq i.succ).symm
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast R.count_eq.symm i, ?_⟩
    exact (R.symm.time_eq i.succ).symm

theorem IsPrefixOf.eventTimes (h : H.IsPrefixOf K) :
    H.eventTimes = K.eventTimes ∩ Ioc 0 H.horizon :=
  h.presentation.eventTimes_eq.symm.trans (K.restrict_eventTimes _)

theorem SamePresentation.stageAt_eq (R : H.SamePresentation K)
    (t : Icc (0 : ℝ) H.horizon) :
    H.stageAt t = K.stageAt
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ := by
  have hstage := R.stage_eq (H.activeStage t)
  rw [SamePresentation.activeStage H R t] at hstage
  exact hstage

theorem IsPrefixOf.stageAt_eq (h : H.IsPrefixOf K)
    (t : Icc (0 : ℝ) H.horizon) :
    H.stageAt t = K.stageAt ⟨t.1, t.2.1, t.2.2.trans h.horizon_le⟩ := by
  let b : Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩
  exact (SamePresentation.stageAt_eq h.presentation.symm t).trans
    (K.restrict_stageAt b ⟨t.1, t.2⟩)

theorem SamePresentation.sliceMetric_heq (R : H.SamePresentation K)
    (t : Icc (0 : ℝ) H.horizon) :
    HEq (H.stageMetric (H.activeStage t) t.1)
      (K.stageMetric (K.activeStage
        ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩) t.1) := by
  have hm := R.metric_heq (H.activeStage t) t.1 (H.activeStage_mem t)
  rw [SamePresentation.activeStage H R t] at hm
  exact hm

theorem IsPrefixOf.sliceMetric_heq (h : H.IsPrefixOf K)
    (t : Icc (0 : ℝ) H.horizon) :
    HEq (H.stageMetric (H.activeStage t) t.1)
      (K.stageMetric (K.activeStage ⟨t.1, t.2.1, t.2.2.trans h.horizon_le⟩) t.1) := by
  let b : Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩
  exact (SamePresentation.sliceMetric_heq h.presentation.symm t).trans
    (K.restrict_sliceMetric b ⟨t.1, t.2⟩)

theorem empty_absorbing (H : ObservedHistory.{u})
    (a b : Icc (0 : ℝ) H.horizon) (hab : a.1 ≤ b.1)
    [IsEmpty (H.stageAt a).Carrier] : IsEmpty (H.stageAt b).Carrier := by
  have ha := H.empty_stage_is_last (H.activeStage a)
  have hab' : H.activeStage a ≤ H.activeStage b := H.activeStage_mono hab
  have hb : H.activeStage b = Fin.last H.eventCount := by
    apply le_antisymm (Fin.le_last _)
    simpa only [ha] using hab'
  change IsEmpty (H.stage (H.activeStage b)).Carrier
  rw [hb, ← ha]
  exact inferInstanceAs (IsEmpty (H.stageAt a).Carrier)

theorem no_event_after_empty (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) [IsEmpty (H.stageAt a).Carrier]
    {s : ℝ} (hs : s ∈ H.eventTimes) : s ≤ a.1 := by
  obtain ⟨i, rfl⟩ := hs
  have ha := H.empty_stage_is_last (H.activeStage a)
  have ht := H.activeStage_time_le a
  rw [ha] at ht
  exact (H.time_strictMono.monotone (Fin.le_last i.succ)).trans ht

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
variable {H K L : ObservedHistory.{u}}

def IsPrefixOf (A : InitialIdentification P g H) (B : InitialIdentification P g K) : Prop :=
  H.IsPrefixOf K ∧ HEq A.map B.map

@[refl] theorem IsPrefixOf.refl (A : InitialIdentification P g H) : A.IsPrefixOf A :=
  ⟨ObservedHistory.IsPrefixOf.refl H, HEq.rfl⟩

@[trans] theorem IsPrefixOf.trans
    {A : InitialIdentification P g H} {B : InitialIdentification P g K}
    {C : InitialIdentification P g L} (h : A.IsPrefixOf B) (k : B.IsPrefixOf C) :
    A.IsPrefixOf C := ⟨h.1.trans k.1, h.2.trans k.2⟩

theorem IsPrefixOf.antisymm
    {A : InitialIdentification P g H} {B : InitialIdentification P g K}
    (h : A.IsPrefixOf B) (k : B.IsPrefixOf A) :
    H.SamePresentation K ∧ HEq A.map B.map := ⟨h.1.antisymm k.1, h.2⟩

theorem restrict_isPrefixOf (A : InitialIdentification P g H)
    (t : Icc (0 : ℝ) H.horizon) : (A.restrict t).IsPrefixOf A :=
  ⟨H.restrict_isPrefixOf t, HEq.rfl⟩

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
