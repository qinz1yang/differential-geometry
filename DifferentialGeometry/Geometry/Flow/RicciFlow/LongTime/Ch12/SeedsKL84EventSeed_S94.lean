import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.G3bTracedRegion_CX2

/-!
# CH12-S94 G1: the event-time seed `hev_S94` (Option A)

`record_seed_tracedRegion_CX2` needs `H.time (H.activeStage t) < t` (regular time).  At an event time
`t = H.time i.succ` (with `H.activeStage t = i.succ`) there is no closed prefix, so the initial
`PathState_CX2` sits one index lower, at `i.castSucc`: the seed path `γ` lives in stage `i.succ`
with metric `outputMetric` (`stageMetric_initial` + `event_output`), `hprotect` pulls it back through
event `i` to the terminal regular open of the incoming slab, and the trace is the singleton at `i.succ`
prepended by the pulled-back endpoint.  Everything stage-indexed is transported along
`H.activeStage t = i.succ` by `subst` on a generalised stage index.

* `pathState_initial_event_S94`: the state at `i.castSucc`;
* `bounded_trace_of_seed_path_event_S94`: the finite backward induction of `bounded_trace_of_seed_path_CX2`
  started from that state;
* `record_seed_tracedRegion_event_S94`: `record_seed_tracedRegion_CX2` with `hregular` replaced by
  `H.time (H.activeStage t) = t`, `0 < t` (exactly the `hev` binder of `b4_point_S87`).
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

/-- At an event time `t = H.time i.succ`, every earlier time lives in stage `≤ i.castSucc`. -/
theorem activeStage_le_event_S94 (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon}
    (hat : a < t) {i : Fin H.eventCount} (hev : H.time i.succ = t.val) :
    H.activeStage a ≤ i.castSucc := by
  by_contra hn
  have hs : i.succ ≤ H.activeStage a := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hn)
  have h1 := H.time_strictMono.monotone hs
  have h2 := H.activeStage_time_le a
  have h3 : a.val < t.val := hat
  linarith

/-- Transport a smooth clipped path with its curvature and length data along `k = i.succ`. -/
theorem event_path_transport_S94 (H : ObservedHistory.{u}) (i : Fin H.eventCount) (t : ℝ)
    (ht : H.time i.succ = t) {k : Fin (H.eventCount + 1)} (hk : k = i.succ)
    (γ0 : ℝ → (H.stage k).Carrier) {B : ℝ} {L : ℝ≥0∞}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ0)
    (hclip : ∀ z, γ0 z = γ0 (projIcc (0 : ℝ) 1 zero_le_one z))
    (hcurv : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.stageMetric k t) (γ0 z) 4 (metricRm04At (H.stageMetric k t) (γ0 z))) ≤ B)
    (hlen : metricPathELength (H.stageMetric k t) γ0 0 1 ≤ L) :
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (fun z => (hk ▸ γ0 z : (H.stage i.succ).Carrier)) ∧
    (∀ z, (hk ▸ γ0 z : (H.stage i.succ).Carrier) =
      (hk ▸ γ0 (projIcc (0 : ℝ) 1 zero_le_one z) : (H.stage i.succ).Carrier)) ∧
    (∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.event i).outputMetric (hk ▸ γ0 z : (H.stage i.succ).Carrier) 4
        (metricRm04At (H.event i).outputMetric (hk ▸ γ0 z : (H.stage i.succ).Carrier))) ≤ B) ∧
    metricPathELength (H.event i).outputMetric
      (fun z => (hk ▸ γ0 z : (H.stage i.succ).Carrier)) 0 1 ≤ L := by
  subst hk
  subst ht
  rw [H.stageMetric_initial, ← H.event_output] at hcurv hlen
  exact ⟨hγ, hclip, hcurv, hlen⟩

/-- A trace from `i.succ` to the stage `k = i.succ`: the singleton. -/
theorem event_trace_singleton_S94 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {k : Fin (H.eventCount + 1)} (hk : k = i.succ) (x : (H.stage k).Carrier) :
    ∃ A : BackwardPointTrace H i.succ k hk.symm.le x,
      A.point i.succ le_rfl hk.symm.le = (hk ▸ x : (H.stage i.succ).Carrier) := by
  subst hk
  exact ⟨BackwardPointTrace.singleton H i.succ x, rfl⟩

/-- A trace ending at stage `k = i.succ` has its `i.succ`-point equal to the transported endpoint. -/
theorem event_trace_point_S94 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {first k : Fin (H.eventCount + 1)} (hk : k = i.succ) {hle : first ≤ k} {y : (H.stage k).Carrier}
    (Y : BackwardPointTrace H first k hle y) (hf : first ≤ i.succ) (hl : i.succ ≤ k) :
    Y.point i.succ hf hl = (hk ▸ y : (H.stage i.succ).Carrier) := by
  subst hk
  exact Y.endpoint_eq

/-- The initial path state of the event-time induction sits at `i.castSucc`. -/
theorem pathState_initial_event_S94 (H : ObservedHistory.{u})
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
  obtain ⟨η, hη, hηclip, hη0, hηcross, hηlen, hηnorm⟩ :=
    hprotect _ hγ' hclip' hcurv' q hcross0
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
theorem bounded_trace_of_seed_path_event_S94 (H : ObservedHistory.{u})
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
    (hprotect : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ γ : ℝ → (H.stage i.succ).Carrier,
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
        obtain ⟨S'⟩ := pathState_prepend_CX2 hr hB hroom hbound i hai S (hprotect i hai S.upper)
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
  obtain ⟨S⟩ := pathState_initial_event_S94 H hat i hi.symm hev' Y hr htop γ hγ0 hγ1 hγ hclip hlen.le
    (hprotect i hai hi.le)
  exact hfinish _ S

/-- G3b at an event time: the `hev` binder of `b4_point_S87`. -/
theorem record_seed_tracedRegion_event_S94 (H : ObservedHistory.{u}) (params : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i params)
    {a t : Icc (0 : ℝ) H.horizon} {τ r K Λ : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hΛ : 1 ≤ Λ)
    (hKΛ : 2 * (9 * K) < Λ ^ 2) (hexp : Real.exp (9 * K * τ) < 2)
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
    (hδ : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ j, (records i).delta j ≤ 1 / 8646)
    (hnom : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ h, Λ * (records i).nominalRadius h ≤ r) :
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
  apply bounded_trace_of_seed_path_event_S94 H hat' hev ht0 Y hr (by positivity) hy hroom hbound ?_ x hx
  intro i hf hl γ hγ hclip hRm q hcross
  exact lift_global_outgoing_path_CX2 (records i) hr hΛ hKΛ (hδ i hf hl) (hnom i hf hl)
    γ hγ hclip hRm q hcross

end GC.LongTime.Ch12
