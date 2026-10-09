import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathInduction_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBarrier_S88
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

/-!
# CH12-S88, group 1e: the backward path induction with a ball-located `hprotect`

Copy of `pathState_prepend_CX2` / `bounded_trace_of_seed_path_CX2` (HistoryPathStep / HistoryPathInduction)
whose per-event clause `hprotect` additionally knows that the outgoing path lies in the `20 r`-ball of
the post-event metric about `Y.point i.succ` (the trace of the centre): in the step this follows from the
slab length estimate (`length ≤ pathBudget < 20 r` at the birth metric).  Everything else is unchanged.
-/

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
theorem pathState_prepend_ball_S88 {H : ObservedHistory.{u}}
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
      (∀ z ∈ Icc (0 : ℝ) 1, γ z ∈ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ S.lower S.upper) (20 * r)) →
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
  have hball : ∀ z ∈ Icc (0 : ℝ) 1, γ z ∈ riemannianBallOf (H.event i).outputMetric
      (Y.point i.succ S.lower S.upper) (20 * r) := by
    intro z hz
    have h1 := (he _ hbirth).1
    change metricPathELength (S.slab.flow.base.metric (H.time i.succ)) γ 0 1 ≤ _ at h1
    rw [hmetric] at h1
    have h0 : γ 0 = Y.point i.succ S.lower S.upper := by
      change (S.curve 0).val = _
      exact S.center
    have h2 := edistOf_le_metricPathELength (H.event i).outputMetric hz.1
      (hγ.contMDiffOn.mono (Set.subset_univ _))
    have h3 := metricPathELength_mono (H.event i).outputMetric γ (le_refl (0 : ℝ)) hz.2
    have h4 : pathBudget_CX2 B r t (H.time i.succ) < 20 * r :=
      (pathBudget_antitone_CX2 hB hr.le hatime.le).trans_lt hroom
    rw [h0] at h2
    change riemannianEDistOf (H.event i).outputMetric _ (γ z) < ENNReal.ofReal (20 * r)
    exact h2.trans_lt ((h3.trans h1).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith only [hr])).mpr h4))
  obtain ⟨η, hη, hηclip, hη0, hηcross, hηlen, hηnorm⟩ := hprotect γ hγ hclip hnorm hball q hcross0
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

/-- Finite backward induction across all actual events, with a single
cumulative path-length budget. -/
theorem bounded_trace_of_seed_path_ball_S88 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (hregular : H.time (H.activeStage t) < t.val)
    {y p : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) y)
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (hroom : pathBudget_CX2 B r t a < 20 * r)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (hprotect : ∀ (i : Fin H.eventCount) (hai' : H.activeStage a ≤ i.castSucc) (hli : i.succ ≤ H.activeStage t),
      ∀ γ : ℝ → (H.stage i.succ).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z)) →
      (∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (H.event i).outputMetric (γ z) 4
          (metricRm04At (H.event i).outputMetric (γ z))) ≤ B) →
      (∀ z ∈ Icc (0 : ℝ) 1, γ z ∈ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ (hai'.trans i.castSucc_lt_succ.le) hli) (20 * r)) →
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
            (metricRm04At (H.event i).terminal.metric (η z))) ≤ B)
    (x : (H.stageAt t).Carrier) (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (2 * r)) :
    ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) x,
      A.isRmBoundedBy (hat := hat.le) B := by
  have hfinish (j : Fin (H.eventCount + 1)) :
      PathState_CX2 H a t hat.le Y x B r j →
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) x,
        A.isRmBoundedBy (hat := hat.le) B := by
    induction j using Fin.inductionOn with
    | zero =>
      intro S
      have hj : (0 : Fin (H.eventCount + 1)) = H.activeStage a :=
        le_antisymm (Fin.zero_le _) S.lower
      let S' : PathState_CX2 H a t hat.le Y x B r (H.activeStage a) :=
        cast (congrArg (PathState_CX2 H a t hat.le Y x B r) hj) S
      exact ⟨S'.trace, pathState_finish_CX2 hr hB hroom hbound S'⟩
    | succ i ih =>
      intro S
      by_cases hj : i.succ = H.activeStage a
      · let S' : PathState_CX2 H a t hat.le Y x B r (H.activeStage a) :=
          cast (congrArg (PathState_CX2 H a t hat.le Y x B r) hj) S
        exact ⟨S'.trace, pathState_finish_CX2 hr hB hroom hbound S'⟩
      · have hai : H.activeStage a ≤ i.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          change (H.activeStage a).val ≤ i.val
          have hlo : (H.activeStage a).val ≤ i.val + 1 := S.lower
          have hne : i.val + 1 ≠ (H.activeStage a).val := fun h => hj (Fin.ext h)
          omega
        obtain ⟨S'⟩ := pathState_prepend_ball_S88 hr hB hroom hbound i hai S (hprotect i hai S.upper)
        exact ih S'
  obtain ⟨γ, hγ0, hγ1, hγ, hclip, hlen⟩ := exists_global_seed_path_CX2 (H.stageAt t)
    (H.stageMetric (H.activeStage t) t) hr hy hx
  have htop : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) q 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) q)) ≤ B := by
    have h := hbound t hat.le le_rfl
    rw [Y.endpoint_eq] at h
    exact h
  obtain ⟨S⟩ := pathState_initial_CX2 H hat hregular Y hr htop γ hγ0 hγ1 hγ hclip hlen.le
  exact hfinish _ S

/-- G3b on an actual history with the barrier asked only for sets `U` inside the `20 r`-ball (post-event
metric) about the trace point `Y.point i.succ` of the centre (`record_seed_tracedRegion_barrier_S88` with
a located barrier; the location is supplied by `bounded_trace_of_seed_path_ball_S88`). -/
theorem record_seed_tracedRegion_ball_S88 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} {τ r K : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K)
    (hexp : Real.exp (9 * K * τ) < 2)
    (ha : a.val = t.val - τ * r ^ 2) (hat : a ≤ t)
    (hregular : H.time (H.activeStage t) < t.val)
    {p y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hbar : ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput)) :
    H.isTracedRegion t p (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  have hdepth : 0 < τ * r ^ 2 := by positivity
  have hat' : a < t := show a.val < t.val from by rw [ha]; linarith
  have hroom : pathBudget_CX2 (K / r ^ 2) r t a < 20 * r := by
    have he : 9 * (K / r ^ 2) * (t.val - a.val) = 9 * K * τ := by
      rw [ha]
      field_simp
      ring
    unfold pathBudget_CX2
    rw [he]
    exact (six_radius_length_CX2 hr hexp).1.trans (six_radius_length_CX2 hr hexp).2
  refine ⟨by positivity, hdepth, a, hat, ha, ?_⟩
  intro x hx
  apply bounded_trace_of_seed_path_ball_S88 H hat' hregular Y hr (by positivity) hy hroom hbound ?_ x hx
  intro i hf hl γ hγ hclip hRm hball q hcross
  exact lift_outgoing_path_of_barrier_in_S88 _ (hbar i hf hl) γ hball hγ hclip hRm q hcross

end GC.LongTime.Ch12
