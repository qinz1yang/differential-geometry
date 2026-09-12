import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound

set_option autoImplicit false

noncomputable section

open Set Filter
open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ENNReal Manifold ContDiff

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem Ici_eq_Icc_union_Ioi {e H : ℝ} (heb : e ≤ H) : Ici e = Icc e H ∪ Ioi H := by
  ext y
  constructor
  · intro hy
    rcases lt_or_ge y H with h | h
    · exact Or.inl ⟨hy, h.le⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact Or.inl ⟨hy, heq.ge⟩
      · exact Or.inr hlt
  · rintro (⟨h1, _⟩ | h2)
    · exact h1
    · exact heb.trans h2.le

def horizonClamp (H t : ℝ) : ℝ := max 0 (min t H)

theorem horizonClamp_mem {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    horizonClamp H t ∈ Icc (0 : ℝ) H :=
  ⟨le_max_left 0 (min t H), max_le hH (min_le_right t H)⟩

theorem horizonClamp_eq_self {H t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    horizonClamp H t = t := by
  unfold horizonClamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_horizonClamp (H : ℝ) : Continuous (horizonClamp H) := by
  unfold horizonClamp
  fun_prop

def horizonExtend (H : ℝ) (hH : 0 ≤ H) (f : Icc (0 : ℝ) H → ℝ) : ℝ → ℝ :=
  fun t => f ⟨horizonClamp H t, horizonClamp_mem hH t⟩

theorem horizonExtend_apply {H : ℝ} (hH : 0 ≤ H) (f : Icc (0 : ℝ) H → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    horizonExtend H hH f t = f ⟨t, ht⟩ := by
  rw [horizonExtend]
  exact congrArg f (Subtype.ext (horizonClamp_eq_self ht))

theorem horizonExtend_nonneg {H : ℝ} (hH : 0 ≤ H) (f : Icc (0 : ℝ) H → ℝ)
    (hf : ∀ t, 0 ≤ f t) (t : ℝ) : 0 ≤ horizonExtend H hH f t :=
  hf _

theorem continuousWithinAt_horizonExtend_Icc {H : ℝ} (hH : 0 ≤ H) {f : Icc (0 : ℝ) H → ℝ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hf : ContinuousAt f ⟨t, ht⟩) :
    ContinuousWithinAt (horizonExtend H hH f) (Icc (0 : ℝ) H) t := by
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ ht]
  have heq : (Icc (0 : ℝ) H).domRestrict (horizonExtend H hH f) = f :=
    funext fun y => horizonExtend_apply hH f y.2
  rw [heq]
  exact hf

theorem continuousAt_horizonClamp_subtype {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    ContinuousAt (fun s : ℝ => (⟨horizonClamp H s, horizonClamp_mem hH s⟩ : Icc (0 : ℝ) H)) t := by
  rw [ContinuousAt, nhds_subtype (Icc (0 : ℝ) H), tendsto_comap_iff]
  have hfun : Subtype.val ∘ (fun s : ℝ =>
      (⟨horizonClamp H s, horizonClamp_mem hH s⟩ : Icc (0 : ℝ) H)) = horizonClamp H := rfl
  rw [hfun]
  exact (continuous_horizonClamp H).continuousAt

theorem continuousAt_horizonExtend {H : ℝ} (hH : 0 ≤ H) {f : Icc (0 : ℝ) H → ℝ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hf : ContinuousAt f ⟨t, ht⟩) :
    ContinuousAt (horizonExtend H hH f) t := by
  have hsub : (⟨horizonClamp H t, horizonClamp_mem hH t⟩ : Icc (0 : ℝ) H) = ⟨t, ht⟩ :=
    Subtype.ext (horizonClamp_eq_self ht)
  have hf' : ContinuousAt f (⟨horizonClamp H t, horizonClamp_mem hH t⟩ : Icc (0 : ℝ) H) := by
    rw [hsub]
    exact hf
  exact hf'.comp (continuousAt_horizonClamp_subtype hH t)

theorem image_subtype_val_Ici_Icc {H e : ℝ} (he : e ∈ Icc (0 : ℝ) H) :
    (Subtype.val : Icc (0 : ℝ) H → ℝ) '' Ici (⟨e, he⟩ : Icc (0 : ℝ) H) = Icc e H := by
  ext y
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [← hyz]
    exact ⟨hz, z.2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨y, he.1.trans h1, h2⟩, h1, rfl⟩

theorem map_subtype_val_Ici {H e : ℝ} (he : e ∈ Icc (0 : ℝ) H) :
    map (Subtype.val : Icc (0 : ℝ) H → ℝ) (𝓝[Ici (⟨e, he⟩ : Icc (0 : ℝ) H)] ⟨e, he⟩) =
      𝓝[Icc e H] e := by
  rw [nhdsWithin_subtype, map_comap, image_subtype_val_Ici_Icc he]
  refine inf_eq_left.mpr (le_trans inf_le_right (principal_mono.mpr ?_))
  rintro y ⟨h1, h2⟩
  exact ⟨⟨y, he.1.trans h1, h2⟩, rfl⟩

theorem continuousWithinAt_horizonExtend_Ici {H : ℝ} (hH : 0 ≤ H) {f : Icc (0 : ℝ) H → ℝ}
    {e : ℝ} (he : e ∈ Ico (0 : ℝ) H)
    (hr : ContinuousWithinAt f (Ici (⟨e, ⟨he.1, he.2.le⟩⟩ : Icc (0 : ℝ) H))
      (⟨e, ⟨he.1, he.2.le⟩⟩ : Icc (0 : ℝ) H)) :
    ContinuousWithinAt (horizonExtend H hH f) (Ici e) e := by
  have heIcc : e ∈ Icc (0 : ℝ) H := ⟨he.1, he.2.le⟩
  have hp : (⟨e, ⟨he.1, he.2.le⟩⟩ : Icc (0 : ℝ) H) = ⟨e, heIcc⟩ := Subtype.ext rfl
  have hr' : ContinuousWithinAt f (Ici (⟨e, heIcc⟩ : Icc (0 : ℝ) H)) ⟨e, heIcc⟩ := by
    rw [← hp]
    exact hr
  have hIcc : Tendsto (horizonExtend H hH f) (𝓝[Icc e H] e)
      (𝓝 (horizonExtend H hH f e)) := by
    rw [← map_subtype_val_Ici heIcc, tendsto_map'_iff]
    have hfun : (horizonExtend H hH f) ∘ (Subtype.val : Icc (0 : ℝ) H → ℝ) = f :=
      funext fun y => horizonExtend_apply hH f y.2
    rw [hfun, horizonExtend_apply hH f heIcc]
    exact hr'
  have hunion : 𝓝[Icc e H] e = 𝓝[Ici e] e := by
    rw [Ici_eq_Icc_union_Ioi he.2.le, nhdsWithin_union]
    have hbot : 𝓝[Ioi H] e = ⊥ := by
      rw [nhdsWithin_restrict (Ioi H) (t := Iio H) he.2 isOpen_Iio]
      simp [Set.Ioi_inter_Iio]
    rw [hbot, sup_bot_eq]
  rw [ContinuousWithinAt, ← hunion]
  exact hIcc

theorem image_subtype_val_Iio_Ico {H e : ℝ} (he : e ∈ Ioc (0 : ℝ) H) :
    (Subtype.val : Icc (0 : ℝ) H → ℝ) '' Iio (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H) =
      Ico 0 e := by
  ext y
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [← hyz]
    exact ⟨z.2.1, hz⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨y, h1, h2.le.trans he.2⟩, h2, rfl⟩

theorem map_subtype_val_Iio {H e : ℝ} (he : e ∈ Ioc (0 : ℝ) H) :
    map (Subtype.val : Icc (0 : ℝ) H → ℝ)
        (𝓝[Iio (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H)]
          (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H)) = 𝓝[Iio e] e := by
  have hset : Ico (0 : ℝ) e ∩ Ioi (0 : ℝ) = Iio e ∩ Ioi (0 : ℝ) := by
    ext y
    simp only [mem_inter_iff, mem_Ico, mem_Iio, mem_Ioi]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨h3.le, h2⟩, h3⟩
  have hIco : 𝓝[Ico 0 e] e = 𝓝[Iio e] e :=
    nhdsWithin_eq_nhdsWithin (t := Ico 0 e) (u := Iio e) he.1 isOpen_Ioi hset
  rw [nhdsWithin_subtype, map_comap, image_subtype_val_Iio_Ico he]
  have hle : 𝓝[Ico 0 e] e ≤ 𝓟 (range (Subtype.val : Icc (0 : ℝ) H → ℝ)) :=
    le_trans inf_le_right (principal_mono.mpr (by
      rintro y ⟨h1, h2⟩
      exact ⟨⟨y, h1, h2.le.trans he.2⟩, rfl⟩))
  rw [inf_eq_left.mpr hle, hIco]

theorem liminf_coe_ennreal {α : Type*} {l : Filter α} [l.NeBot] {u : α → ℝ≥0∞} :
    ((l.liminf u : ℝ≥0∞) : EReal) = l.liminf (fun a => ((u a : ℝ≥0∞) : EReal)) :=
  Monotone.map_liminf_of_continuousAt EReal.coe_ennreal_strictMono.monotone u
    continuous_coe_ennreal_ereal.continuousAt
    (⟨⊤, fun _ _ => le_top⟩ : l.IsCoboundedUnder (fun x1 x2 : ℝ≥0∞ => x1 ≥ x2) u)
    (⟨⊥, Eventually.of_forall fun x => (bot_le : (⊥ : ℝ≥0∞) ≤ x)⟩ :
      l.IsBoundedUnder (fun x1 x2 : ℝ≥0∞ => x1 ≥ x2) u)

theorem liminf_coe_ofReal_toEReal {α : Type*} {l : Filter α} {w : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) :
    l.liminf (fun a => ((ENNReal.ofReal (w a) : ℝ≥0∞) : EReal)) =
      l.liminf (fun a => (w a : EReal)) :=
  Filter.liminf_congr (Eventually.of_forall fun a => by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (hw a)])

theorem horizonExtend_eventJump_ereal {H : ℝ} (hH : 0 ≤ H) {f : Icc (0 : ℝ) H → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {e : ℝ} (he : e ∈ Ioc (0 : ℝ) H)
    (hbase : ENNReal.ofReal (f ⟨e, ⟨he.1.le, he.2⟩⟩) ≤
      liminf (fun t : Icc (0 : ℝ) H => ENNReal.ofReal (f t))
        (𝓝[<] (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H))) :
    ((horizonExtend H hH f e : ℝ) : EReal) ≤
      liminf (fun s : ℝ => ((horizonExtend H hH f s : ℝ) : EReal)) (𝓝[<] e) := by
  set v : ℝ → ℝ := horizonExtend H hH f with hv
  have hv0 : ∀ s, 0 ≤ v s := fun s => horizonExtend_nonneg hH f hf0 s
  have hve : ∀ t : Icc (0 : ℝ) H, v t.1 = f t := fun t => horizonExtend_apply hH f t.2
  have hmap : map (Subtype.val : Icc (0 : ℝ) H → ℝ)
      (𝓝[<] (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H)) = 𝓝[<] e :=
    map_subtype_val_Iio he
  have hlim : liminf (fun s : ℝ => ENNReal.ofReal (v s)) (𝓝[<] e) =
      liminf (fun t : Icc (0 : ℝ) H => ENNReal.ofReal (f t))
        (𝓝[<] (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H)) := by
    rw [← hmap, ← liminf_comp (u := fun s : ℝ => ENNReal.ofReal (v s))
      (v := (Subtype.val : Icc (0 : ℝ) H → ℝ))
      (f := 𝓝[<] (⟨e, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H))]
    exact liminf_congr (Eventually.of_forall fun t => by
      rw [Function.comp_apply, hve t])
  have hbase' : ENNReal.ofReal (v e) ≤
      liminf (fun s : ℝ => ENNReal.ofReal (v s)) (𝓝[<] e) := by
    rw [hve ⟨e, ⟨he.1.le, he.2⟩⟩, hlim]
    exact hbase
  have hmono := EReal.coe_ennreal_strictMono.monotone hbase'
  rw [liminf_coe_ennreal] at hmono
  rw [liminf_coe_ofReal_toEReal (w := v) hv0] at hmono
  rw [EReal.coe_ennreal_ofReal, max_eq_left (hv0 e)] at hmono
  exact hmono

theorem historyWidth_eventJump_ereal (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (i : Fin H.eventCount) :
    ((horizonExtend H.horizon H.horizon_nonneg (Extinction.Width.historyWidth H h0 terminal)
        (H.time i.succ) : ℝ) : EReal) ≤
      liminf (fun s : ℝ => ((horizonExtend H.horizon H.horizon_nonneg
        (Extinction.Width.historyWidth H h0 terminal) s : ℝ) : EReal))
        (𝓝[<] (H.time i.succ)) := by
  have he : H.time i.succ ∈ Ioc (0 : ℝ) H.horizon :=
    ObservedHistory.eventTimes_subset_Ioc H ⟨i, rfl⟩
  have hp : Extinction.Width.historyStageTime H i.succ =
      (⟨H.time i.succ, ⟨he.1.le, he.2⟩⟩ : Icc (0 : ℝ) H.horizon) :=
    Subtype.ext rfl
  have hbase := Extinction.Width.historyWidth_event_jump H parameters cutoff h0 terminal i
  rw [hp] at hbase
  exact horizonExtend_eventJump_ereal H.horizon_nonneg
    (fun t => Extinction.Width.historyWidth_nonneg H h0 terminal t) he hbase


def observedHistoryWidthValue (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) : ℝ → ℝ :=
  horizonExtend H.horizon H.horizon_nonneg (Extinction.Width.historyWidth H h0 terminal)

theorem observedHistoryWidthValue_apply (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H.horizon) :
    observedHistoryWidthValue H h0 terminal t =
      Extinction.Width.historyWidth H h0 terminal ⟨t, ht⟩ :=
  horizonExtend_apply H.horizon_nonneg _ ht

theorem observedHistoryWidthValue_initial (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    observedHistoryWidthValue H h0 terminal 0 =
      Extinction.Width.historyWidth H h0 terminal (Extinction.Width.historyStageTime H 0) := by
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) H.horizon := ⟨le_rfl, H.horizon_nonneg⟩
  have hstage : Extinction.Width.historyStageTime H 0 =
      (⟨0, hmem⟩ : Icc (0 : ℝ) H.horizon) := Subtype.ext H.time_zero
  rw [observedHistoryWidthValue, horizonExtend_apply H.horizon_nonneg _ hmem, ← hstage]

theorem observedHistoryWidthValue_not_event_continuousAt (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : Icc (0 : ℝ) H.horizon) (ht : t.1 ∉ H.eventTimes) :
    ContinuousAt (Extinction.Width.historyWidth H h0 terminal) t :=
  Extinction.Width.historyWidth_continuousAt_of_not_event H h0 terminal t
    (fun i h => ht ⟨i, h.symm⟩)

theorem observedHistoryWidthValue_nonneg (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : ℝ) : 0 ≤ observedHistoryWidthValue H h0 terminal t :=
  horizonExtend_nonneg H.horizon_nonneg _
    (fun s => Extinction.Width.historyWidth_nonneg H h0 terminal s) t

theorem observedComparisonRecord_of_historyWidth (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hinitial : Extinction.Width.historyWidth H h0 terminal
      (Extinction.Width.historyStageTime H 0) ≤ A)
    (hcont : ∀ t : Icc (0 : ℝ) H.horizon, t.1 ∉ H.eventTimes →
      ContinuousAt (Extinction.Width.historyWidth H h0 terminal) t)
    (hrcont : ∀ i : Fin H.eventCount, H.time i.succ < H.horizon →
      ContinuousWithinAt (Extinction.Width.historyWidth H h0 terminal)
        (Ici (Extinction.Width.historyStageTime H i.succ))
        (Extinction.Width.historyStageTime H i.succ))
    (hjump : ∀ i : Fin H.eventCount,
      ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal
          (Extinction.Width.historyStageTime H i.succ)) ≤
        liminf (fun t : Icc (0 : ℝ) H.horizon =>
          ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal t))
          (𝓝[<] (Extinction.Width.historyStageTime H i.succ)))
    (hdini : ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c)))) :
    Nonempty (ObservedComparisonRecord H c A) :=
  ⟨{ value := observedHistoryWidthValue H h0 terminal
     hypotheses :=
       { c_pos := hc
         horizon_pos := hHpos
         finite_events := ObservedHistory.eventTimes_finite H
         events_subset := ObservedHistory.eventTimes_subset_Ioc H
         nonneg := fun t ht => by
           rw [observedHistoryWidthValue_apply H h0 terminal ht]
           exact Extinction.Width.historyWidth_nonneg H h0 terminal ⟨t, ht⟩
         continuous := fun t ht htE =>
           continuousWithinAt_horizonExtend_Icc H.horizon_nonneg ht
             (hcont ⟨t, ht⟩ htE)
         right_continuous := fun t ht => by
           by_cases htE : t ∈ H.eventTimes
           · obtain ⟨i, hi⟩ := htE
             have he0 : 0 ≤ H.time i.succ :=
               (ObservedHistory.eventTimes_subset_Ioc H ⟨i, rfl⟩).1.le
             have hlt : H.time i.succ < H.horizon := hi.trans_lt ht.2
             have hp : Extinction.Width.historyStageTime H i.succ =
                 (⟨H.time i.succ, ⟨he0, hlt.le⟩⟩ : Icc (0 : ℝ) H.horizon) :=
               Subtype.ext rfl
             rw [← hi]
             exact continuousWithinAt_horizonExtend_Ici H.horizon_nonneg
               ⟨he0, hlt⟩ (hp ▸ hrcont i hlt)
           · refine (continuousAt_horizonExtend H.horizon_nonneg
               (⟨ht.1, ht.2.le⟩ : t ∈ Icc (0 : ℝ) H.horizon)
               (hcont (⟨t, ⟨ht.1, ht.2.le⟩⟩ : Icc (0 : ℝ) H.horizon) htE)).continuousWithinAt
         incoming_jump := fun e he => by
           obtain ⟨i, hi⟩ := he
           have heIoc : H.time i.succ ∈ Ioc (0 : ℝ) H.horizon :=
             ObservedHistory.eventTimes_subset_Ioc H ⟨i, rfl⟩
           have hp : Extinction.Width.historyStageTime H i.succ =
               (⟨H.time i.succ, ⟨heIoc.1.le, heIoc.2⟩⟩ : Icc (0 : ℝ) H.horizon) :=
             Subtype.ext rfl
           rw [← hi]
           exact horizonExtend_eventJump_ereal H.horizon_nonneg
             (fun t => Extinction.Width.historyWidth_nonneg H h0 terminal t) heIoc
             (hp ▸ hjump i)
         dini := hdini }
     initial_le := by
       rw [observedHistoryWidthValue_initial H h0 terminal]
       exact hinitial }⟩


theorem observedComparisonRecord_of_historyWidthData (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hdata : (∀ t, 0 ≤ Extinction.Width.historyWidth H h0 terminal t ∧
        ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal t) < ⊤) ∧
      Extinction.Width.historyWidth H h0 terminal
          (Extinction.Width.historyStageTime H 0) ≤ A ∧
      (∀ t, (∀ i : Fin H.eventCount, t.1 ≠ H.time i.succ) →
        ContinuousAt (Extinction.Width.historyWidth H h0 terminal) t) ∧
      (∀ i : Fin H.eventCount,
        ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal
            (Extinction.Width.historyStageTime H i.succ)) ≤
          liminf (fun t : Icc (0 : ℝ) H.horizon =>
            ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal t))
            (𝓝[<] (Extinction.Width.historyStageTime H i.succ))) ∧
      ∀ i : Fin H.eventCount, H.time i.succ < H.horizon →
        ContinuousWithinAt (Extinction.Width.historyWidth H h0 terminal)
          (Ici (Extinction.Width.historyStageTime H i.succ))
          (Extinction.Width.historyStageTime H i.succ))
    (hdini : ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c)))) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidth H h0 terminal hc hHpos hdata.2.1
    (fun t htE => hdata.2.2.1 t (fun i h => htE ⟨i, h.symm⟩)) hdata.2.2.2.2 hdata.2.2.2.1 hdini

theorem exists_poincare_controlled_extinction_of_widthData
    (P : OrientedThreeStage.{u}) (g : P.Metric) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H) [Nonempty P.Carrier]
    [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ i : Fin H.eventCount, ∀ c : ConnectedComponents (H.event i).discarded.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        ((H.event i).discarded.toClosedOrientedManifold.component c).Carrier)
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A₀ : ℝ} (hcpos : 0 < c) (hA₀ : 0 ≤ A₀)
    (hthreshold : extinctionThreshold c A₀ < H.horizon)
    (hwidth : Extinction.Width.historyWidth H
      (Extinction.Width.initialIdentification_components_simplyConnected P g H A) terminal
      (Extinction.Width.historyStageTime H 0) ≤ A₀)
    (hdini : ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H
        (Extinction.Width.initialIdentification_components_simplyConnected P g H A) terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H
          (Extinction.Width.initialIdentification_components_simplyConnected P g H A) terminal t /
            (4 * (t + c)))) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  have hHpos : 0 < H.horizon :=
    (extinctionThreshold_nonneg hcpos hA₀).trans_lt hthreshold
  refine exists_poincare_controlled_extinction_of_uniform_records P g H A hc hout hctrl
    hthreshold (fun Q => ?_)
  exact observedComparisonRecord_of_historyWidthData H _ terminal hcpos hHpos
    ⟨fun t => ⟨Extinction.Width.historyWidth_nonneg H _ terminal t, ENNReal.ofReal_lt_top⟩,
      hwidth,
      fun t ht => Extinction.Width.historyWidth_continuousAt_of_not_event H _ terminal t ht,
      fun i => Extinction.Width.historyWidth_event_jump H parameters cutoff _ terminal i,
      fun i hi => Extinction.Width.historyWidth_rightContinuousAt_event H _ terminal i hi⟩
    hdini


theorem upperRightDiniLE_of_incrementBound {V W : ℝ → ℝ} {t m c : ℝ} (hc : 0 < c) (ht0 : 0 ≤ t)
    (hVW : V =ᶠ[𝓝[>] t] W) (hVt : V t = W t) (hWt : 0 ≤ W t)
    (hm : -3 / (4 * (t + c)) ≤ m)
    (hbound : ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ,
      (W (t + h) - W t) / h ≤ -2 * Real.pi - m * W t + ε) :
    UpperRightDiniLE V t (-2 * Real.pi + 3 * V t / (4 * (t + c))) := by
  have htc : 0 < 4 * (t + c) := by linarith
  have hmul : -m * W t ≤ 3 * V t / (4 * (t + c)) := by
    have h1 : -W t * m ≤ -W t * (-3 / (4 * (t + c))) :=
      mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hWt)
    have h2 : -W t * (-3 / (4 * (t + c))) = 3 * W t / (4 * (t + c)) := by
      field_simp
    rw [h2] at h1
    rw [hVt]
    linarith
  intro ε hε
  obtain ⟨δ, hδpos, hb⟩ := hbound (ε / 2) (by linarith)
  filter_upwards [hVW, Ioo_mem_nhdsGT (show t < t + δ by linarith)] with y hVy hy
  obtain ⟨hy1, hy2⟩ := hy
  have hsub : y - t ∈ Ioo (0 : ℝ) δ := ⟨by linarith, by linarith⟩
  have hstep := hb (y - t) hsub
  have hyt2 : t + (y - t) = y := by ring
  rw [hyt2] at hstep
  have hslope : slope V t y = (W y - W t) / (y - t) := by
    rw [slope_def_field, hVy, hVt]
  rw [hslope]
  linarith


theorem scalarLowerBarrier_three_neg_inv {c t : ℝ} (hc : c ≠ 0) (htc : t + c ≠ 0) :
    scalarLowerBarrier 3 (-3 / (2 * c)) t = -3 / (2 * (t + c)) := by
  unfold scalarLowerBarrier
  have hden : 1 - (2 / 3 : ℝ) * (-3 / (2 * c)) * t = (t + c) / c := by
    field_simp
    ring
  rw [hden]
  field_simp

def HistoryScalarLowerBound (H : ObservedHistory.{u}) (c : ℝ) : Prop :=
  ∀ t : Icc (0 : ℝ) H.horizon, t.1 ∉ H.eventTimes →
    ∀ x : (H.stage (Extinction.Width.historyStageAt H t)).Carrier,
      -3 / (2 * (t.1 + c)) ≤
        metricScalarAt (Extinction.Width.historyStageMetric H
          (Extinction.Width.historyStageAt H t) t.1) x

theorem historyScalarLowerBound_half {H : ObservedHistory.{u}} {c : ℝ} (hc : 0 < c)
    (h : HistoryScalarLowerBound H c) {t : Icc (0 : ℝ) H.horizon}
    (ht : t.1 ∉ H.eventTimes) (x : (H.stage (Extinction.Width.historyStageAt H t)).Carrier) :
    -3 / (4 * (t.1 + c)) ≤
      metricScalarAt (Extinction.Width.historyStageMetric H
        (Extinction.Width.historyStageAt H t) t.1) x / 2 := by
  have hb := h t ht x
  have htc : 0 < 2 * (t.1 + c) := by linarith [t.2.1, hc]
  have h2 : -3 / (4 * (t.1 + c)) = (-3 / (2 * (t.1 + c))) / 2 := by
    field_simp
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right hb (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
