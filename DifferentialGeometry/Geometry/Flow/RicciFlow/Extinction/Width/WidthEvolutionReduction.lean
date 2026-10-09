import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HistoryWidthJumpComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedWidthComparison

noncomputable section

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

def HistoryWidthEventJumpFrontier (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) : Prop :=
  ∀ i : Fin H.eventCount,
    ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) ≤
      liminf (fun t : Icc (0 : ℝ) H.horizon =>
        ENNReal.ofReal (historyWidth H h0 terminal t))
        (𝓝[<] (historyStageTime H i.succ))

def HistoryWidthIncrementFrontier (H : ObservedHistory.{u}) : Prop :=
  (∀ (i : Fin H.eventCount)
      (p : ConnectedComponents (H.stage i.castSucc).Carrier)
      (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier),
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ), ∀ ε > 0, ∃ δ > 0,
        ∀ h ∈ Ioo (0 : ℝ) δ, t + h < H.time i.succ →
          (componentWidth (H.stage i.castSucc)
              ((H.event i).incoming.flow.base.metric (t + h)) p hSC -
            componentWidth (H.stage i.castSucc)
              ((H.event i).incoming.flow.base.metric t) p hSC) / h ≤
            -2 * Real.pi - componentHalfScalar (H.stage i.castSucc)
              (H.event i).incoming.flow.base p t *
              componentWidth (H.stage i.castSucc)
                ((H.event i).incoming.flow.base.metric t) p hSC + ε) ∧
  (∀ (hfin : H.time (Fin.last H.eventCount) < H.horizon)
      (p : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (hSC : SimplyConnectedSpace
        ((H.stage (Fin.last H.eventCount)).component p).Carrier),
      ∀ t ∈ Ico (H.time (Fin.last H.eventCount)) H.horizon, ∀ ε > 0, ∃ δ > 0,
        ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ H.horizon →
          (componentWidth (H.stage (Fin.last H.eventCount))
              ((H.finalSlab hfin).flow.base.metric (t + h)) p hSC -
            componentWidth (H.stage (Fin.last H.eventCount))
              ((H.finalSlab hfin).flow.base.metric t) p hSC) / h ≤
            -2 * Real.pi - componentHalfScalar (H.stage (Fin.last H.eventCount))
              (H.finalSlab hfin).flow.base p t *
              componentWidth (H.stage (Fin.last H.eventCount))
                ((H.finalSlab hfin).flow.base.metric t) p hSC + ε)

def HistoryWidthDiniFrontier (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (c : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
    UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
      (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c)))

theorem historyWidthEventJumpFrontier_of_childComparison (H : ObservedHistory.{u})
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (hchild : ∀ i : Fin H.eventCount, ChildComparisonData (cutoff i)) :
    HistoryWidthEventJumpFrontier H h0 terminal :=
  fun i => historyWidth_event_jump_of_childComparison H parameters cutoff h0 terminal i (hchild i)

theorem historyWidthIncrementFrontier_of_rampDeformation (H : ObservedHistory.{u})
    (hinc : ∀ (i : Fin H.eventCount)
      (p : ConnectedComponents (H.stage i.castSucc).Carrier)
      (_hSC : SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage i.castSucc) (H.time i.castSucc)
        (H.time i.succ) (H.event i).incoming.lt p)
    (hclosed : ∀ (hfin : H.time (Fin.last H.eventCount) < H.horizon)
      (p : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (_hSC : SimplyConnectedSpace
        ((H.stage (Fin.last H.eventCount)).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage (Fin.last H.eventCount))
        (H.time (Fin.last H.eventCount)) H.horizon (H.finalSlab hfin).lt p) :
    HistoryWidthIncrementFrontier H :=
  ⟨fun i p hSC => incoming_component_incrementBound_of_rampFamilyDeformation
      (H.event i).incoming p hSC (hinc i p hSC),
    fun hfin p hSC => closed_component_incrementBound_of_rampFamilyDeformation
      (H.finalSlab hfin) p hSC (hclosed hfin p hSC)⟩

theorem historyWidthDiniFrontier_of_incrementFrontier (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c) (hscalar : HistoryScalarLowerBound H c)
    (hincrement : HistoryWidthIncrementFrontier H) :
    HistoryWidthDiniFrontier H h0 terminal c :=
  observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds H h0 terminal hc hscalar
    hincrement.1 hincrement.2

theorem observedComparisonRecord_of_historyWidthFrontiers (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hinitial : historyWidth H h0 terminal (historyStageTime H 0) ≤ A)
    (hjump : HistoryWidthEventJumpFrontier H h0 terminal)
    (hdini : HistoryWidthDiniFrontier H h0 terminal c) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidth H h0 terminal hc hHpos hinitial
    (fun t ht => observedHistoryWidthValue_not_event_continuousAt H h0 terminal t ht)
    (fun i hi => historyWidth_rightContinuousAt_event H h0 terminal i hi)
    hjump hdini

theorem scalarComparisonHypotheses_of_historyWidthFrontiers (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hjump : HistoryWidthEventJumpFrontier H h0 terminal)
    (hdini : HistoryWidthDiniFrontier H h0 terminal c) :
    ∃ W : ℝ → ℝ, ScalarComparisonHypotheses c H.horizon H.eventTimes W :=
  ⟨_, (observedComparisonRecord_of_historyWidthFrontiers H h0 terminal hc hHpos le_rfl
    hjump hdini).some.hypotheses⟩

theorem scalarWeightedWidth_antitoneOn_of_historyWidthFrontiers (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hjump : HistoryWidthEventJumpFrontier H h0 terminal)
    (hdini : HistoryWidthDiniFrontier H h0 terminal c) :
    ∃ W : ℝ → ℝ, AntitoneOn (scalarWeightedWidth c W) (Icc 0 H.horizon) := by
  obtain ⟨W, h⟩ :=
    scalarComparisonHypotheses_of_historyWidthFrontiers H h0 terminal hc hHpos hjump hdini
  exact ⟨W, scalarWeightedWidth_antitoneOn h⟩

theorem observedComparisonRecord_of_childComparison_of_incrementFrontier
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hscalar : HistoryScalarLowerBound H c)
    (hinitial : historyWidth H h0 terminal (historyStageTime H 0) ≤ A)
    (hchild : ∀ i : Fin H.eventCount, ChildComparisonData (cutoff i))
    (hincrement : HistoryWidthIncrementFrontier H) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidthFrontiers H h0 terminal hc hHpos hinitial
    (historyWidthEventJumpFrontier_of_childComparison H parameters cutoff h0 terminal hchild)
    (historyWidthDiniFrontier_of_incrementFrontier H h0 terminal hc hscalar hincrement)

theorem historyWidthEventJumpFrontier_of_eventCount_eq_zero (H : ObservedHistory.{u})
    (hcount : H.eventCount = 0)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    HistoryWidthEventJumpFrontier H h0 terminal :=
  fun i => Fin.elim0 (hcount ▸ i)

theorem historyWidthEventJumpFrontier_atZero (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h0 : ∀ c : ConnectedComponents ((ObservedHistory.atZero P g).stage 0).Carrier,
      SimplyConnectedSpace (((ObservedHistory.atZero P g).stage 0).component c).Carrier)
    (terminal : ConnectedComponents ((ObservedHistory.atZero P g).stage
      (Fin.last (ObservedHistory.atZero P g).eventCount)).Carrier) :
    HistoryWidthEventJumpFrontier (ObservedHistory.atZero P g) h0 terminal :=
  fun i => Fin.elim0 i

theorem historyWidthIncrementFrontier_atZero (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HistoryWidthIncrementFrontier (ObservedHistory.atZero P g) := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro hfin
  exact absurd hfin (lt_irrefl 0)

theorem historyWidthDiniFrontier_atZero (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h0 : ∀ c : ConnectedComponents ((ObservedHistory.atZero P g).stage 0).Carrier,
      SimplyConnectedSpace (((ObservedHistory.atZero P g).stage 0).component c).Carrier)
    (terminal : ConnectedComponents ((ObservedHistory.atZero P g).stage
      (Fin.last (ObservedHistory.atZero P g).eventCount)).Carrier) (c : ℝ) :
    HistoryWidthDiniFrontier (ObservedHistory.atZero P g) h0 terminal c := by
  intro t ht
  exact absurd ht.2 (not_lt_of_ge ht.1)

theorem upperRightDiniLE_const_iff {A x d : ℝ} :
    UpperRightDiniLE (fun _ : ℝ => A) x d ↔ 0 ≤ d := by
  constructor
  · intro h
    by_contra hlt
    simp only [not_le] at hlt
    have hε : 0 < -d / 2 := by linarith
    obtain ⟨y, hy⟩ := (h (-d / 2) hε).exists
    rw [slope_def_field, sub_self, zero_div] at hy
    linarith
  · intro hd ε hε
    filter_upwards with y
    rw [slope_def_field, sub_self, zero_div]
    linarith

theorem scalarComparisonHypotheses_const {c H A : ℝ} {E : Set ℝ}
    (hc : 0 < c) (hH : 0 < H) (hE : E.Finite) (hsub : E ⊆ Ioc 0 H)
    (hA : 8 * Real.pi * (H + c) / 3 ≤ A) :
    ScalarComparisonHypotheses c H E (fun _ : ℝ => A) where
  c_pos := hc
  horizon_pos := hH
  finite_events := hE
  events_subset := hsub
  nonneg := fun _ _ => by
    have hHc : 0 < H + c := by linarith
    have hpos : 0 < 8 * Real.pi * (H + c) / 3 := by positivity
    linarith
  continuous := fun _ _ _ => continuousWithinAt_const
  right_continuous := fun _ _ => continuousWithinAt_const
  incoming_jump := fun e he => by
    simp
  dini := fun t ht _ => by
    rw [upperRightDiniLE_const_iff]
    have htc : 0 < t + c := by linarith [ht.1]
    have h3 : 8 * Real.pi * (t + c) ≤ 3 * A := by
      have hA3 : 8 * Real.pi * (H + c) ≤ 3 * A := by linarith
      have hmono : 8 * Real.pi * (t + c) ≤ 8 * Real.pi * (H + c) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2.le]) (by positivity)
      linarith
    have h2 : 2 * Real.pi ≤ 3 * A / (4 * (t + c)) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (t + c))]
      linarith
    linarith

theorem not_scalarComparisonHypotheses_const_zero {c H : ℝ} (hH : 0 < H) :
    ¬ ScalarComparisonHypotheses c H (∅ : Set ℝ) (fun _ : ℝ => 0) := by
  intro h
  have hd := h.dini 0 ⟨le_rfl, hH⟩ (by simp)
  rw [upperRightDiniLE_const_iff] at hd
  simp only [mul_zero, zero_div, add_zero] at hd
  linarith [Real.pi_pos]

theorem exists_upperRightDiniLE_not_incomingJump :
    ∃ W : ℝ → ℝ, UpperRightDiniLE W 1 0 ∧
      ¬ ((W 1 : ℝ) : EReal) ≤
        liminf (fun s : ℝ => ((W s : ℝ) : EReal)) (𝓝[<] (1 : ℝ)) := by
  refine ⟨fun t => if (1 : ℝ) ≤ t then 1 else 0, ?_, ?_⟩
  · intro ε hε
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h0 : (if (1 : ℝ) ≤ y then (1 : ℝ) else 0) = 1 := ite_eq_left (le_of_lt hy)
    have h1 : (if (1 : ℝ) ≤ (1 : ℝ) then (1 : ℝ) else 0) = 1 := ite_eq_left le_rfl
    rw [slope_def_field, h0, h1, sub_self, zero_div]
    linarith
  · intro hj
    have hconst : (fun s : ℝ => (((fun t : ℝ => if (1 : ℝ) ≤ t then (1 : ℝ) else 0) s
        : ℝ) : EReal)) =ᶠ[𝓝[<] (1 : ℝ)] fun _ => (((0 : ℝ)) : EReal) := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
      have hs1 : ¬ ((1 : ℝ) ≤ s) := not_le.mpr hs.2
      simp [hs1]
    rw [Filter.liminf_congr hconst, liminf_const] at hj
    have h1 : (((fun t : ℝ => if (1 : ℝ) ≤ t then (1 : ℝ) else 0) 1 : ℝ) : EReal) =
        (((1 : ℝ)) : EReal) := by simp
    rw [h1, EReal.coe_le_coe_iff] at hj
    norm_num at hj

theorem exists_incomingJump_not_upperRightDiniLE :
    ∃ W : ℝ → ℝ, (((W 1 : ℝ)) : EReal) ≤
        liminf (fun s : ℝ => ((W s : ℝ) : EReal)) (𝓝[<] (1 : ℝ)) ∧
      ¬ UpperRightDiniLE W 1 0 := by
  refine ⟨fun t : ℝ => t, ?_, ?_⟩
  · have h : Tendsto (fun s : ℝ => ((s : ℝ) : EReal)) (𝓝[<] (1 : ℝ))
        (𝓝 (((1 : ℝ)) : EReal)) :=
      EReal.tendsto_coe.mpr ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
    rw [h.liminf_eq]
  · intro hd
    obtain ⟨y, hy, hygt⟩ := ((hd (1 / 2) (by norm_num)).and self_mem_nhdsWithin).exists
    have hyne : y ≠ 1 := ne_of_gt hygt
    have hslope : slope (fun t : ℝ => t) 1 y = 1 := by
      rw [slope_def_field]
      exact div_self (sub_ne_zero.mpr hyne)
    rw [hslope] at hy
    norm_num at hy


end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
