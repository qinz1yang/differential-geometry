import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathState_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A concrete constructor for the preceding state. The only event input
is the single-surgery path lifting theorem, separately proved from records. -/
theorem pathState_prepend_CX2 {H : ObservedHistory.{u}}
    {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t} {y x : (H.stageAt t).Carrier}
    {Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y}
    {B r : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hroom : pathBudget_CX2 B r t a < 20 * r)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
    (S : PathState_CX2 H a t hat Y x B r i.succ)
    (hprotect : ∀ γ : ℝ → (H.stage i.succ).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z)) →
      (∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (H.event i).outputMetric (γ z) 4
          (metricRm04At (H.event i).outputMetric (γ z))) ≤ B) →
      ∀ q : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing q.val (γ 0) →
      ∃ η : ℝ → (H.event i).incoming.terminalRegularOpen,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧
        (∀ z, η z = η (projIcc (0 : ℝ) 1 zero_le_one z)) ∧ η 0 = q ∧
        (∀ z ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η z).val (γ z)) ∧
        metricPathELength (H.event i).terminal.metric η 0 1 =
          metricPathELength (H.event i).outputMetric γ 0 1 ∧
        ∀ z ∈ Icc (0 : ℝ) 1,
          Real.sqrt (normSq0S (H.event i).terminal.metric (η z) 4
            (metricRm04At (H.event i).terminal.metric (η z))) ≤ B) :
    Nonempty (PathState_CX2 H a t hat Y x B r i.castSucc) := by
  have haj : H.activeStage a < i.succ := hai.trans_lt i.castSucc_lt_succ
  have hatime : a.val < H.time i.succ := time_lt_of_activeStage_lt_CX2 H a i.succ haj
  have he := history_path_slab_estimate_CX2 H (hat := hat) Y hr hB hroom hbound _ S.lower S.upper
    S.after_lower S.before_top S.slab S.terminal S.active S.metric S.curve S.smooth
    S.center S.length S.terminal_bound
  have hbirth : H.time i.succ ∈ Ico (max a.val (H.time i.succ)) S.top :=
    ⟨max_le hatime.le le_rfl, S.slab.lt⟩
  let γ : ℝ → (H.stage i.succ).Carrier := Subtype.val ∘ S.curve
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ := (contMDiff_subtype_val (n := 1)).comp S.smooth
  have hclip : ∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z) :=
    fun z => congrArg Subtype.val (S.clip z)
  have hmetric : S.slab.flow.base.metric (H.time i.succ) = (H.event i).outputMetric := by
    rw [← S.metric _ ⟨le_rfl, S.slab.lt⟩, H.stageMetric_initial, H.event_output]
  have hnorm : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.event i).outputMetric (γ z) 4 (metricRm04At (H.event i).outputMetric (γ z))) ≤ B := by
    intro z hz
    have h := (he _ hbirth).2 z hz
    change Real.sqrt (normSq0S (S.slab.flow.base.metric (H.time i.succ)) (γ z) 4
      (metricRm04At (S.slab.flow.base.metric (H.time i.succ)) (γ z))) ≤ B at h
    rwa [hmetric] at h
  let q : (H.event i).incoming.terminalRegularOpen :=
    ⟨Y.point i.castSucc hai (i.castSucc_lt_succ.le.trans S.upper),
      (Y.crossing i hai S.upper).mem_terminalRegularRegion (H.event i)⟩
  have hcross0 : (H.event i).RegularCrossing q.val (γ 0) := by
    change (H.event i).RegularCrossing _ (S.curve 0).val
    rw [S.center]
    exact Y.crossing i hai S.upper
  obtain ⟨η, hη, hηclip, hη0, hηcross, hηlen, hηnorm⟩ := hprotect γ hγ hclip hnorm q hcross0
  have hcross1 : (H.event i).RegularCrossing (η 1).val (S.trace.point i.succ le_rfl S.upper) := by
    rw [← S.endpoint]
    exact hηcross 1 ⟨zero_le_one, le_rfl⟩
  let A := S.trace.prepend (η 1).val hcross1
  have htail (j : Fin (H.eventCount + 1)) (hj : i.succ ≤ j) (hl : j ≤ H.activeStage t) :
      A.point j (i.castSucc_lt_succ.le.trans hj) hl = S.trace.point j hj hl :=
    prepend_point_tail_CX2 H S.trace _ hcross1 j hj hl
  refine ⟨{
    lower := hai
    upper := i.castSucc_lt_succ.le.trans S.upper
    top := H.time i.succ
    after_lower := hatime
    before_top := (H.time_strictMono.monotone S.upper).trans (H.activeStage_time_le t)
    slab := (H.event i).incoming
    terminal := (H.event i).terminal
    active := fun v hv hv' => activeStage_on_event_CX2 H i v ⟨hv, hv'⟩
    metric := fun v _ => by simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    trace := A
    curve := η
    smooth := hη
    clip := hηclip
    center := by rw [hη0]
    endpoint := (S.trace.prepend_point_first _ hcross1).symm
    length := ?_
    terminal_bound := hηnorm
    above := ?_
    seams := ?_ }⟩
  · rw [hηlen]
    have hb := (he _ hbirth).1
    rwa [hmetric] at hb
  · intro v hav hvt htop
    have hjv : i.succ ≤ H.activeStage v := H.le_activeStage v i.succ htop
    have hp := htail (H.activeStage v) hjv (H.activeStage_mono hvt)
    rw [hp]
    by_cases hvtop : S.top ≤ v.val
    · exact S.above v hav hvt hvtop
    · have hvtop' : v.val < S.top := lt_of_not_ge hvtop
      have hv : v.val ∈ Ico (max a.val (H.time i.succ)) S.top :=
        ⟨max_le hav htop, hvtop'⟩
      have hc := (he v hv).2 1 ⟨zero_le_one, le_rfl⟩
      change Real.sqrt (normSq0S (S.slab.flow.base.metric v) (S.curve 1).val 4
        (metricRm04At (S.slab.flow.base.metric v) (S.curve 1).val)) ≤ B at hc
      rw [← S.metric v ⟨htop, hvtop'⟩, S.endpoint] at hc
      exact (trace_rmNormSq_at_stage_CX2 H S.trace (S.active v htop hvtop')
        hjv (H.activeStage_mono hvt) le_rfl S.upper v).trans_le (Real.sqrt_le_iff.mp hc).2
  · intro k hf hl
    by_cases hki : k = i
    · subst k
      have hp := S.trace.prepend_point_first (η 1).val hcross1
      exact (terminalRmNormSq_congr_CX2 H i _ (η 1).property hp).trans_le
        (Real.sqrt_le_iff.mp (hηnorm 1 ⟨zero_le_one, le_rfl⟩)).2
    · have hik : i.succ ≤ k.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val + 1 ≤ k.val
        have hif : i.val ≤ k.val := hf
        have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
        omega
      have hp := htail k.castSucc hik (k.castSucc_lt_succ.le.trans hl)
      exact (terminalRmNormSq_congr_CX2 H k _ _ hp).trans_le (S.seams k hik hl)

end GC.LongTime.Ch12
