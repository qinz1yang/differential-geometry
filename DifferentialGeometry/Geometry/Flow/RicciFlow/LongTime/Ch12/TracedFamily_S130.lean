import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84EventSeed_S94
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBallPath_S88

/-!
# CH12-S130, group 1: the traced family of a centre trace (regular AND event times), ball-located barrier

`[FROZEN] CH12-S130 G1` (see DELIVERIES): `traced_family_of_trace_S130` -- a backward trace `Y` of the centre `y`
over `[a₀, t]` with `|Rm| ≤ K/r²` on the `20 r`-balls along it (`hbound`) and the located barrier at the events
crossed (`hbar`, the clause of `record_seed_tracedRegion_ball_S88`) gives `isTracedRegion u (Y u) (2r) (τ r²) (K/r²)`
for EVERY `u ∈ [a₀ + τ r², t]`.

`record_seed_tracedRegion_ball_S88` needs a regular start time (`H.time (H.activeStage t) < t`); at an event time
`t = H.time i.succ` the ball-located variant is a copy of the S94 event-time construction
(`pathState_initial_event_S94` / `bounded_trace_of_seed_path_event_S94`), with `hprotect` in the ball form of S88
(the ball hypothesis is automatic for the seed path: it has length `≤ 3 r < 20 r` about the centre).
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

theorem pathState_initial_event_ball_S130 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a < t) (i : Fin H.eventCount)
    (hk : H.activeStage t = i.succ) (hev : H.time i.succ = t.val)
    {y x : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) y)
    {r B : ℝ} (hr : 0 < r)
    (hbound : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) q 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) q)) ≤ B)
    (γ : ℝ → (H.stageAt t).Carrier) (hγ0 : γ 0 = y) (hγ1 : γ 1 = x)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hclip : ∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z))
    (hlen : metricPathELength (H.stageMetric (H.activeStage t) t) γ 0 1 ≤ ENNReal.ofReal (3 * r))
    (hprotect : ∀ γ' : ℝ → (H.stage i.succ).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ' →
      (∀ z, γ' z = γ' (projIcc (0 : ℝ) 1 zero_le_one z)) →
      (∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (H.event i).outputMetric (γ' z) 4
          (metricRm04At (H.event i).outputMetric (γ' z))) ≤ B) →
      (∀ z ∈ Icc (0 : ℝ) 1, γ' z ∈ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ ((activeStage_le_event_S94 H hat hev).trans i.castSucc_lt_succ.le) hk.symm.le)
        (20 * r)) →
      ∀ q : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing q.val (γ' 0) →
      ∃ η : ℝ → (H.event i).incoming.terminalRegularOpen,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧
        (∀ z, η z = η (projIcc (0 : ℝ) 1 zero_le_one z)) ∧ η 0 = q ∧
        (∀ z ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η z).val (γ' z)) ∧
        metricPathELength (H.event i).terminal.metric η 0 1 =
          metricPathELength (H.event i).outputMetric γ' 0 1 ∧
        ∀ z ∈ Icc (0 : ℝ) 1,
          Real.sqrt (normSq0S (H.event i).terminal.metric (η z) 4
            (metricRm04At (H.event i).terminal.metric (η z))) ≤ B) :
    Nonempty (PathState_CX2 H a t hat.le Y x B r i.castSucc) := by
  have hai : H.activeStage a ≤ i.castSucc := activeStage_le_event_S94 H hat hev
  have hupper : i.castSucc ≤ H.activeStage t := i.castSucc_lt_succ.le.trans hk.symm.le
  have hatime : a.val < H.time i.succ := by rw [hev]; exact hat
  have hcurv : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) (γ z) 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) (γ z))) ≤ B := by
    intro z hz
    apply hbound
    have hd := edistOf_le_metricPathELength (H.stageMetric (H.activeStage t) t) hz.1
      (hγ.contMDiffOn.mono (Icc_subset_Icc le_rfl hz.2))
    rw [hγ0] at hd
    exact (hd.trans ((metricPathELength_mono _ _ le_rfl hz.2).trans hlen)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 20 * r)).mpr (by linarith))
  obtain ⟨hγ', hclip', hcurv', hlen'⟩ :=
    event_path_transport_S94 H i t.val hev hk γ hγ hclip hcurv hlen
  obtain ⟨A0, hA0⟩ := event_trace_singleton_S94 H i hk x
  have hy' : (hk ▸ γ 0 : (H.stage i.succ).Carrier) = (hk ▸ y : (H.stage i.succ).Carrier) := by
    rw [hγ0]
  have hx' : (hk ▸ γ 1 : (H.stage i.succ).Carrier) = (hk ▸ x : (H.stage i.succ).Carrier) := by
    rw [hγ1]
  let q : (H.event i).incoming.terminalRegularOpen :=
    ⟨Y.point i.castSucc hai hupper,
      (Y.crossing i hai hk.symm.le).mem_terminalRegularRegion (H.event i)⟩
  have hcross0 : (H.event i).RegularCrossing q.val (hk ▸ γ 0 : (H.stage i.succ).Carrier) := by
    have h := Y.crossing i hai hk.symm.le
    rw [event_trace_point_S94 H i hk Y _ hk.symm.le, ← hy'] at h
    exact h
  have hball : ∀ z ∈ Icc (0 : ℝ) 1, (hk ▸ γ z : (H.stage i.succ).Carrier) ∈
      riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ ((activeStage_le_event_S94 H hat hev).trans i.castSucc_lt_succ.le) hk.symm.le)
        (20 * r) := by
    intro z hz
    have h2 := edistOf_le_metricPathELength (H.event i).outputMetric hz.1
      (hγ'.contMDiffOn.mono (Set.subset_univ _))
    have h3 := metricPathELength_mono (H.event i).outputMetric
      (fun z => (hk ▸ γ z : (H.stage i.succ).Carrier)) (le_refl (0 : ℝ)) hz.2
    have hc : Y.point i.succ ((activeStage_le_event_S94 H hat hev).trans i.castSucc_lt_succ.le)
        hk.symm.le = (hk ▸ γ 0 : (H.stage i.succ).Carrier) := by
      rw [event_trace_point_S94 H i hk Y _ hk.symm.le, ← hy']
    rw [hc]
    change riemannianEDistOf (H.event i).outputMetric (hk ▸ γ 0 : (H.stage i.succ).Carrier)
      (hk ▸ γ z : (H.stage i.succ).Carrier) < ENNReal.ofReal (20 * r)
    exact h2.trans_lt ((h3.trans hlen').trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 20 * r)).mpr (by linarith)))
  obtain ⟨η, hη, hηclip, hη0, hηcross, hηlen, hηnorm⟩ :=
    hprotect _ hγ' hclip' hcurv' hball q hcross0
  have hcross1 : (H.event i).RegularCrossing (η 1).val (A0.point i.succ le_rfl hk.symm.le) := by
    rw [hA0, ← hx']
    exact hηcross 1 ⟨zero_le_one, le_rfl⟩
  let A := A0.prepend (η 1).val hcross1
  have hpt : ∀ h1 h2, A.point (H.activeStage t) h1 h2 = x := fun _ _ => A.endpoint_eq
  refine ⟨{
    lower := hai
    upper := hupper
    top := H.time i.succ
    after_lower := hatime
    before_top := hev.le
    slab := (H.event i).incoming
    terminal := (H.event i).terminal
    active := fun v hv hv' => activeStage_on_event_CX2 H i v ⟨hv, hv'⟩
    metric := fun v _ => by simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    trace := A
    curve := η
    smooth := hη
    clip := hηclip
    center := by rw [hη0]
    endpoint := (A0.prepend_point_first _ hcross1).symm
    length := ?_
    terminal_bound := hηnorm
    above := ?_
    seams := ?_ }⟩
  · rw [hηlen]
    have h3 : metricPathELength (H.event i).outputMetric
        (fun z => (hk ▸ γ z : (H.stage i.succ).Carrier)) 0 1 ≤ ENNReal.ofReal (3 * r) := hlen'
    refine h3.trans (le_of_eq ?_)
    rw [hev]
    simp only [pathBudget_CX2, sub_self, mul_zero, Real.exp_zero, mul_one]
  · intro v _ hvt htop
    have h : v = t := Subtype.ext (le_antisymm hvt (hev ▸ htop))
    subst v
    rw [hpt]
    have hc := hcurv 1 ⟨zero_le_one, le_rfl⟩
    rw [hγ1] at hc
    exact (Real.sqrt_le_iff.mp hc).2
  · intro k' hf hl
    have hki : k' = i := le_antisymm (Fin.succ_le_succ_iff.mp (hl.trans hk.le))
      (Fin.castSucc_le_castSucc_iff.mp hf)
    subst k'
    have hp := A0.prepend_point_first (η 1).val hcross1
    exact (terminalRmNormSq_congr_CX2 H i _ (η 1).property hp).trans_le
      (Real.sqrt_le_iff.mp (hηnorm 1 ⟨zero_le_one, le_rfl⟩)).2

/-- The finite backward induction of `bounded_trace_of_seed_path_CX2`, started at an event time. -/
theorem bounded_trace_of_seed_path_ball_event_S130 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (hev : H.time (H.activeStage t) = t.val) (ht0 : 0 < t.val)
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
  have hne : H.activeStage t ≠ 0 := by
    intro h0
    rw [h0, H.time_zero] at hev
    linarith
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hne
  have hev' : H.time i.succ = t.val := by rw [hi]; exact hev
  have hai : H.activeStage a ≤ i.castSucc := activeStage_le_event_S94 H hat hev'
  obtain ⟨S⟩ := pathState_initial_event_ball_S130 H hat i hi.symm hev' Y hr htop γ hγ0 hγ1 hγ hclip hlen.le
    (hprotect i hai hi.le)
  exact hfinish _ S


/-- `record_seed_tracedRegion_ball_S88` at an event time: `hregular` replaced by
`H.time (H.activeStage t) = t`, `0 < t` (the S94 construction with the ball-located barrier). -/
theorem record_seed_tracedRegion_ball_event_S130 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} {τ r K : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K)
    (hexp : Real.exp (9 * K * τ) < 2)
    (ha : a.val = t.val - τ * r ^ 2) (hat : a ≤ t)
    (hev : H.time (H.activeStage t) = t.val) (ht0 : 0 < t.val)
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
  apply bounded_trace_of_seed_path_ball_event_S130 H hat' hev ht0 Y hr (by positivity) hy hroom hbound ?_ x hx
  intro i hf hl γ hγ hclip hRm hball q hcross
  exact lift_outgoing_path_of_barrier_in_S88 _ (hbar i hf hl) γ hball hγ hclip hRm q hcross

/-- **[FROZEN] CH12-S130 G1.**  The traced family of a centre trace: for every `u ∈ [a₀ + τ r², t]` (regular or
event time) the centre `Y u` has a traced region of radius `2 r`, depth `τ r²`, bound `K / r²`. -/
theorem traced_family_of_trace_S130 (H : ObservedHistory.{u})
    {a₀ t : Icc (0 : ℝ) H.horizon} (ha₀t : a₀ ≤ t) {τ r K : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hexp : Real.exp (9 * K * τ) < 2)
    {y : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a₀) (H.activeStage t) (H.activeStage_mono ha₀t) y)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a₀ ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hbar : ∀ (i : Fin H.eventCount) (hf : H.activeStage a₀ ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput))
    (u : Icc (0 : ℝ) H.horizon) (hau : a₀.val + τ * r ^ 2 ≤ u.val) (hut : u ≤ t) :
    H.isTracedRegion u
      (Y.point (H.activeStage u)
        (H.activeStage_mono (show a₀ ≤ u from show a₀.val ≤ u.val by
          have : 0 < τ * r ^ 2 := by positivity
          linarith only [hau, this]))
        (H.activeStage_mono hut))
      (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  have hdepth : 0 < τ * r ^ 2 := by positivity
  have ha₀u : a₀ ≤ u := show a₀.val ≤ u.val by linarith only [hau, hdepth]
  have h0 := a₀.property.1
  let au : Icc (0 : ℝ) H.horizon :=
    ⟨u.val - τ * r ^ 2, by linarith only [hau, h0], (sub_le_self _ hdepth.le).trans u.property.2⟩
  have hau0 : a₀ ≤ au := show a₀.val ≤ u.val - τ * r ^ 2 by linarith only [hau]
  have haue : au ≤ u := show u.val - τ * r ^ 2 ≤ u.val by linarith only [hdepth]
  let Yu := (Y.restrictLast (H.activeStage_mono ha₀u) (H.activeStage_mono hut)).restrictFirst
    (H.activeStage_mono hau0) (H.activeStage_mono haue)
  have hself : ∀ (z : (H.stageAt u).Carrier), z ∈ riemannianBallOf
      (H.stageMetric (H.activeStage u) u) z r := by
    intro z
    change riemannianEDistOf _ z z < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hb' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : au ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Yu.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2 :=
    fun v hav hvu q hq => hbound v (hau0.trans hav) (hvu.trans hut) q hq
  have hbar' : ∀ (i : Fin H.eventCount) (hf : H.activeStage au ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage u) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        (Yu.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput) :=
    fun i hf hl U hU => hbar i ((H.activeStage_mono hau0).trans hf) (hl.trans (H.activeStage_mono hut)) U hU
  rcases lt_or_eq_of_le (H.activeStage_time_le u) with hreg | hev
  · exact record_seed_tracedRegion_ball_S88 H hτ hr hK hexp (a := au) (t := u) rfl haue hreg
      (hself _) Yu hb' hbar'
  · exact record_seed_tracedRegion_ball_event_S130 H hτ hr hK hexp (a := au) (t := u) rfl haue hev
      (by linarith only [hau, h0, hdepth]) (hself _) Yu hb' hbar'

end GC.LongTime.Ch12
