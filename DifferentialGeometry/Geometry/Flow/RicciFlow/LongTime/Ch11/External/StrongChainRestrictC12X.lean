import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

/-!
# Full history strong necks: restriction and same-presentation transports (C12X, S16 G4 / G1)

Two generic transports of `HistoryStrongNeckFull_C12X` (O-C12X-S16B), used by the chain layer
(`docs/geometrization/chapter8/out/CH12X-S16-chain-design.md` §3 (e), (f)):

* `historyStrongNeckFull_restrict_C12X` (TB): a full neck of `H` at the stage `castLE k` is a
  full neck of `H.restrict b` at `k` (stages, times and events of the restriction are those of
  `H`; the survivor domains coincide and so do the actual survivor maps);
* `HistoryStrongNeckFull_C12X.of_samePresentation_C12X` (TA): a full neck transports along
  `ObservedHistory.SamePresentation` (survivor domains equal through the `RegularCrossing` iff,
  event slab metrics equal on the closed slab through `extendedMetric`);
* the incoming-slab agreement clause of S16C's `hfull` transports along both
  (`incomingAgree_restrict_last_C12X`, `incomingAgree_of_samePresentation_last_C12X`).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- Body of `HistoryStrongNeckFull_C12X` over raw history data, with the survivor domain and the
terminal maps abstracted. -/
private def s16d_rawBody {n : ℕ} (times : Fin (n + 1) → ℝ)
    (stages : Fin (n + 1) → OrientedThreeStage.{u})
    (events : (i : Fin n) → MetricCutCapEvent (stages i.castSucc) (stages i.succ)
      (times i.castSucc) (times i.succ))
    (k : Fin (n + 1)) {s : ℝ} (G : (stages k).IncomingSlab (times k) s) (eps : ℝ)
    (y : (stages k).Carrier) (t : ℝ) (first : Fin (n + 1)) (O : Opens (stages k).Carrier)
    (f : ∀ (j : Fin n), first ≤ j.castSucc → j.succ ≤ k →
      O → (events j).incoming.terminalRegularOpen)
    (hf : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j hj hl)) : Prop :=
  ∃ (hts : times first < s) (gflow : ℝ → SmoothRiemannianMetric ThreeModel O),
    times k ≤ t ∧ times first ≤ t - (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin n) (hj : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (times j.castSucc) (times j.succ),
        gflow τ = localPullMetric ((events j).terminal.extendedMetric τ) (f j hj hl)
          (hf j hj hl)) ∧
    (∀ τ ∈ Ico (times k) s, gflow τ = (G.flow.base.metric τ).restrictOpen O) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen (times first) s hts)) ∧
    ∃ z : O, z.val = y ∧
      Nonempty (StrongNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := O)
          (RealTimeInterval.closedOpen (times first) s hts)) eps z t)

private theorem s16d_full_iff_rawBody {K : ObservedHistory.{u}} {k : Fin (K.eventCount + 1)}
    {s : ℝ} {G : (K.stage k).IncomingSlab (K.time k) s} {eps : ℝ} {y : (K.stage k).Carrier}
    {t : ℝ} :
    K.HistoryStrongNeckFull_C12X k G eps y t ↔ ∃ (first : Fin (K.eventCount + 1))
      (hle : first ≤ k),
      s16d_rawBody K.time K.stage K.event k G eps y t first
        (K.backwardSurvivorDomain first k hle) (K.backwardSurvivorTerminalMap first k hle)
        (K.backwardSurvivorTerminalMap_isLocalDiffeomorph first k hle) :=
  Iff.rfl

private theorem s16d_localPull_congr {P Q : OrientedThreeStage.{u}} {O : Opens Q.Carrier}
    {T₁ T₂ : Opens P.Carrier} (hT : T₁ = T₂)
    {m₁ : SmoothRiemannianMetric ThreeModel T₁} {m₂ : SmoothRiemannianMetric ThreeModel T₂}
    (hm : HEq m₁ m₂) (f₁ : O → T₁) (f₂ : O → T₂) (hf : ∀ x, (f₁ x).val = (f₂ x).val)
    (h₁ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f₁)
    (h₂ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f₂) :
    localPullMetric m₁ f₁ h₁ = localPullMetric m₂ f₂ h₂ := by
  subst hT
  cases eq_of_heq hm
  have : f₁ = f₂ := funext fun x => Subtype.ext (hf x)
  subst this
  rfl

private theorem s16d_restrictOpen_heq {P : OrientedThreeStage.{u}} (g : P.Metric)
    {T₁ T₂ : Opens P.Carrier} (hT : T₁ = T₂) : HEq (g.restrictOpen T₁) (g.restrictOpen T₂) := by
  subst hT
  rfl

private theorem s16d_extendedMetric_heq {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F) {τ : ℝ}
    (hτ : τ ∈ Icc a s) :
    HEq (E.terminal.extendedMetric τ) (F.terminal.extendedMetric τ) := by
  by_cases hlt : τ < s
  · rw [E.terminal.extendedMetric_before hlt, F.terminal.extendedMetric_before hlt,
      eq_of_heq (R.incomingMetric_heq τ ⟨hτ.1, hlt⟩)]
    exact s16d_restrictOpen_heq _ (eq_of_heq R.terminalRegion_heq)
  · obtain rfl : τ = s := le_antisymm hτ.2 (not_lt.mp hlt)
    rw [E.terminal.extendedMetric_terminal, F.terminal.extendedMetric_terminal]
    exact R.terminalMetric_heq

private theorem s16d_regularCrossing_iff {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F)
    {p : P.Carrier} {q : Q.Carrier} : E.RegularCrossing p q ↔ F.RegularCrossing p q := by
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq R.old_heq
  cases eq_of_heq R.oldCharts_heq
  cases eq_of_heq R.oldOutput_heq
  rfl

/-- Raw-body transfer: change the survivor domain along an equality and the events along
`SamePresentation`, given that the terminal maps agree pointwise. -/
private theorem s16d_rawBody_transfer {n : ℕ} {times : Fin (n + 1) → ℝ}
    {stages : Fin (n + 1) → OrientedThreeStage.{u}}
    {evH evK : (i : Fin n) → MetricCutCapEvent (stages i.castSucc) (stages i.succ)
      (times i.castSucc) (times i.succ)}
    (hev : ∀ i, (evH i).SamePresentation (evK i))
    {k : Fin (n + 1)} {s : ℝ} {G : (stages k).IncomingSlab (times k) s} {eps : ℝ}
    {y : (stages k).Carrier} {t : ℝ} {first : Fin (n + 1)} {O₁ O₂ : Opens (stages k).Carrier}
    (hO : O₁ = O₂)
    {f₁ : ∀ (j : Fin n), first ≤ j.castSucc → j.succ ≤ k →
      O₁ → (evH j).incoming.terminalRegularOpen}
    {hf₁ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₁ j hj hl)}
    {f₂ : ∀ (j : Fin n), first ≤ j.castSucc → j.succ ≤ k →
      O₂ → (evK j).incoming.terminalRegularOpen}
    {hf₂ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₂ j hj hl)}
    (hfv : ∀ j hj hl (x : O₁), (f₁ j hj hl x).val = (f₂ j hj hl ⟨x.val, hO ▸ x.property⟩).val)
    (h : s16d_rawBody times stages evH k G eps y t first O₁ f₁ hf₁) :
    s16d_rawBody times stages evK k G eps y t first O₂ f₂ hf₂ := by
  subst hO
  obtain ⟨hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, hnk⟩ := h
  refine ⟨hts, gflow, htk, hfirst, fun j hj hl τ hτ => ?_, hcur, hsol, z, hz, hnk⟩
  rw [hslab j hj hl τ hτ]
  exact s16d_localPull_congr (eq_of_heq (hev j).terminalRegion_heq)
    (s16d_extendedMetric_heq (hev j) hτ) _ _ (hfv j hj hl) _ _

/-! ## TB: restriction -/

theorem s16d_restrict_count_le (H : ObservedHistory.{u}) (b : Icc (0 : ℝ) H.horizon) :
    (H.restrict b).eventCount ≤ H.eventCount :=
  Nat.le_of_lt_succ (H.activeStage b).isLt

/-- A trace of the restriction is a trace of `H`. -/
private def s16d_traceOfRestrict (H : ObservedHistory.{u}) (b : Icc (0 : ℝ) H.horizon)
    {first last : Fin ((H.restrict b).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.restrict b).stage last).Carrier}
    (A : BackwardPointTrace (H.restrict b) first last hle x) :
    BackwardPointTrace H
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) first)
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) last)
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)) x where
  point m hm1 hm2 := A.point ⟨m.val, by
      have h1 : m.val ≤ last.val := hm2
      have h2 := last.isLt
      omega⟩ hm1 hm2
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing ⟨i.val, by
      have h1 : i.val + 1 ≤ last.val := hl
      have h2 := last.isLt
      omega⟩ hf hl

/-- A trace of `H` between restricted stages is a trace of the restriction. -/
private def s16d_traceToRestrict (H : ObservedHistory.{u}) (b : Icc (0 : ℝ) H.horizon)
    {first last : Fin ((H.restrict b).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.restrict b).stage last).Carrier}
    (A : BackwardPointTrace H
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) first)
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) last)
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)) x) :
    BackwardPointTrace (H.restrict b) first last hle x where
  point m hm1 hm2 := A.point (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) m)
    hm1 hm2
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing (Fin.castLE (H.s16d_restrict_count_le b) i) hf hl

/-- The survivor domains of the restriction are those of `H`. -/
theorem backwardSurvivorDomain_restrict_C12X (H : ObservedHistory.{u})
    (b : Icc (0 : ℝ) H.horizon) (first k : Fin ((H.restrict b).eventCount + 1))
    (hle : first ≤ k) :
    H.backwardSurvivorDomain (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) first)
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k)
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)) =
      (H.restrict b).backwardSurvivorDomain first k hle := by
  ext q
  exact ⟨fun ⟨A⟩ => ⟨s16d_traceToRestrict H b A⟩, fun ⟨A⟩ => ⟨s16d_traceOfRestrict H b A⟩⟩

/-- **TB**：a full neck of `H` at `castLE k` is a full neck of `H.restrict b` at `k`. -/
theorem historyStrongNeckFull_restrict_C12X (H : ObservedHistory.{u})
    (b : Icc (0 : ℝ) H.horizon) (k : Fin ((H.restrict b).eventCount + 1)) {s : ℝ}
    (G : ((H.restrict b).stage k).IncomingSlab ((H.restrict b).time k) s) {eps : ℝ}
    {y : ((H.restrict b).stage k).Carrier} {t : ℝ}
    (h : H.HistoryStrongNeckFull_C12X
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k) G eps y t) :
    (H.restrict b).HistoryStrongNeckFull_C12X k G eps y t := by
  obtain ⟨first, hle, hb⟩ := s16d_full_iff_rawBody.mp h
  have hfk : first.val ≤ k.val := hle
  let first' : Fin ((H.restrict b).eventCount + 1) := ⟨first.val, by
    have := k.isLt
    omega⟩
  have hle' : first' ≤ k := hfk
  have hO := H.backwardSurvivorDomain_restrict_C12X b first' k hle'
  refine s16d_full_iff_rawBody.mpr ⟨first', hle', ?_⟩
  obtain ⟨hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, hnk⟩ := hb
  have hre : s16d_rawBody (H.restrict b).time (H.restrict b).stage (H.restrict b).event k G eps y t
      first' _ (fun j hj hl => H.backwardSurvivorTerminalMap first _ hle
        (Fin.castLE (H.s16d_restrict_count_le b) j) hj hl)
      (fun j hj hl => H.backwardSurvivorTerminalMap_isLocalDiffeomorph first _ hle
        (Fin.castLE (H.s16d_restrict_count_le b) j) hj hl) :=
    ⟨hts, gflow, htk, hfirst,
      fun j hj hl τ hτ => hslab (Fin.castLE (H.s16d_restrict_count_le b) j) hj hl τ hτ,
      hcur, hsol, z, hz, hnk⟩
  refine s16d_rawBody_transfer (times := (H.restrict b).time) (stages := (H.restrict b).stage)
    (evH := (H.restrict b).event) (evK := (H.restrict b).event) (k := k)
    (fun _ => MetricCutCapEvent.SamePresentation.refl _) hO (fun j hj hl x => ?_) hre
  let A := Classical.choice x.property
  exact (H.backwardSurvivorMap_eq_point first _ hle _ hj (j.castSucc_lt_succ.le.trans hl) x
    A).trans ((H.restrict b).backwardSurvivorMap_eq_point first' k hle' j.castSucc hj
      (j.castSucc_lt_succ.le.trans hl) ⟨x.val, hO ▸ x.property⟩
      (s16d_traceToRestrict H b A)).symm

/-- Incoming-slab agreement clause, restricted to the last stage of `H.restrict b`. -/
theorem incomingAgree_restrict_last_C12X (H : ObservedHistory.{u})
    (b : Icc (0 : ℝ) H.horizon) {s : ℝ}
    (G : ((H.restrict b).stage (Fin.last (H.restrict b).eventCount)).IncomingSlab
      ((H.restrict b).time (Fin.last (H.restrict b).eventCount)) s) {t : ℝ}
    (htb : t ≤ (b : ℝ))
    (hG : ∀ τ ∈ Icc ((H.restrict b).time (Fin.last (H.restrict b).eventCount)) t,
      G.flow.base.metric τ = H.stageMetric
        (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b))
          (Fin.last (H.restrict b).eventCount)) τ) :
    ∀ τ ∈ Icc ((H.restrict b).time (Fin.last (H.restrict b).eventCount)) t,
      G.flow.base.metric τ =
        (H.restrict b).stageMetric (Fin.last (H.restrict b).eventCount) τ := by
  intro τ hτ
  have hdom : τ ∈ (H.restrict b).stageDomain (Fin.last (H.restrict b).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨hτ.1, hτ.2.trans htb⟩
  rw [hG τ hτ]
  exact (eq_of_heq (H.restrict_stageMetric b _ τ hdom)).symm

/-! ## TA: same presentation -/

/-- **TA**：a full neck transports along `SamePresentation` (matched stage index, `HEq` slab and
point). -/
theorem HistoryStrongNeckFull_C12X.of_samePresentation_C12X {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) {k : Fin (H.eventCount + 1)} {k' : Fin (K.eventCount + 1)}
    (hk : k.val = k'.val) {s : ℝ} {G : (H.stage k).IncomingSlab (H.time k) s}
    {G' : (K.stage k').IncomingSlab (K.time k') s} (hG : HEq G G')
    {y : (H.stage k).Carrier} {y' : (K.stage k').Carrier} (hy : HEq y y') {eps t : ℝ}
    (h : H.HistoryStrongNeckFull_C12X k G eps y t) :
    K.HistoryStrongNeckFull_C12X k' G' eps y' t := by
  rcases H with ⟨T, hT, n, times, htimes, hzero, hlast, stages, initH, evH, hinitH, houtH,
    finH, hfinH⟩
  rcases K with ⟨T', hT', n', times', htimes', hzero', hlast', stages', initK, evK, hinitK,
    houtK, finK, hfinK⟩
  obtain rfl : n = n' := R.count_eq
  obtain rfl : times = times' := funext fun j => R.time_eq j
  obtain rfl : stages = stages' := funext fun j => R.stage_eq j
  obtain rfl : k = k' := Fin.ext hk
  cases eq_of_heq hG
  cases eq_of_heq hy
  obtain ⟨first, hle, hb⟩ := s16d_full_iff_rawBody.mp h
  refine s16d_full_iff_rawBody.mpr ⟨first, hle, ?_⟩
  have hcross : ∀ i : Fin n, ∀ p q, (evH i).RegularCrossing p q ↔ (evK i).RegularCrossing p q :=
    fun i _ _ => s16d_regularCrossing_iff (R.event_eq i)
  let LH : ObservedHistory.{u} := ⟨T, hT, n, times, htimes, hzero, hlast, stages, initH, evH,
    hinitH, houtH, finH, hfinH⟩
  let KH : ObservedHistory.{u} := ⟨T', hT', n, times, htimes', hzero', hlast', stages, initK,
    evK, hinitK, houtK, finK, hfinK⟩
  let toK : ∀ {q : (stages k).Carrier}, BackwardPointTrace LH first k hle q →
      BackwardPointTrace KH first k hle q := fun A =>
    ⟨A.point, A.endpoint_eq, fun i hf hl => (hcross i _ _).mp (A.crossing i hf hl)⟩
  have hO : LH.backwardSurvivorDomain first k hle = KH.backwardSurvivorDomain first k hle := by
    ext q
    exact ⟨fun ⟨A⟩ => ⟨toK A⟩, fun ⟨A⟩ =>
      ⟨⟨A.point, A.endpoint_eq, fun i hf hl => (hcross i _ _).mpr (A.crossing i hf hl)⟩⟩⟩
  refine s16d_rawBody_transfer (fun i => R.event_eq i) hO (fun j hj hl x => ?_) hb
  let A := Classical.choice x.property
  exact (LH.backwardSurvivorMap_eq_point first k hle _ hj (j.castSucc_lt_succ.le.trans hl) x
    A).trans (KH.backwardSurvivorMap_eq_point first k hle j.castSucc hj
      (j.castSucc_lt_succ.le.trans hl) ⟨x.val, hO ▸ x.property⟩ (toK A)).symm

/-- Incoming-slab agreement clause at the last stage along `SamePresentation`. -/
theorem incomingAgree_of_samePresentation_last_C12X {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) {s t : ℝ}
    {G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s}
    {G' : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) s}
    (hG : HEq G G') (htT : t ≤ H.horizon)
    (hagree : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) t,
      G.flow.base.metric τ = H.stageMetric (Fin.last H.eventCount) τ) :
    ∀ τ ∈ Icc (K.time (Fin.last K.eventCount)) t,
      G'.flow.base.metric τ = K.stageMetric (Fin.last K.eventCount) τ := by
  rcases H with ⟨T, hT, n, times, htimes, hzero, hlast, stages, initH, evH, hinitH, houtH,
    finH, hfinH⟩
  rcases K with ⟨T', hT', n', times', htimes', hzero', hlast', stages', initK, evK, hinitK,
    houtK, finK, hfinK⟩
  obtain rfl : n = n' := R.count_eq
  obtain rfl : times = times' := funext fun j => R.time_eq j
  obtain rfl : stages = stages' := funext fun j => R.stage_eq j
  cases eq_of_heq hG
  intro τ hτ
  rw [hagree τ hτ]
  refine eq_of_heq (R.metric_heq (Fin.last n) τ ?_)
  simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
  exact ⟨hτ.1, hτ.2.trans htT⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
