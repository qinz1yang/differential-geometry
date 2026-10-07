import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainRestrictInvC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullCanonicalC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation

/-!
# Full history strong necks along an affine event prefix (C12X, S16 G4 / G3: TC)

`AffineEventPrefix K J c offset (last K)` presents the native history `K` as the translated tail of
the full history `J` (shift `c`, offset `offset`). A full neck of `K` at `(k, G, y, t)` is a full
neck of `J` at `(stageIndex k, G translated by c, y, t + c)`:

* survivor domains correspond through `AffineEventPrefix.traceEquiv` (the same points and
  crossings; `s16d_opens_heq`), and so do the actual survivor maps (R-S16 D-6);
* event slab metrics: `J`'s event at `eventIndex i` is the translated `K` event, whose
  `extendedMetric` at `τ` is `K`'s at `τ - c` (`s16d_translated_terminal`);
* the survivor flow, its `IsSolutionOn` and the depth-one `StrongNeck` are time-translated
  (`s16d_shift_core`, `s16d_strongNeck_shift`).

Main results: `AffineEventPrefix.historyStrongNeckFull_affine_C12X`,
`AffineEventPrefix.stronglyCanonicalAtFull_affine_C12X` (witness + neck clause) and
`AffineEventPrefix.incomingAgree_affine_C12X` (slab agreement clause).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## Generic casts -/

theorem s16d_opens_heq {P P' : OrientedThreeStage.{u}} (h : P' = P) {O' : Opens P'.Carrier}
    {O : Opens P.Carrier} (hmem : ∀ q : P.Carrier, s16d_castPoint h.symm q ∈ O' ↔ q ∈ O) :
    HEq O' O := by
  subst h
  exact heq_of_eq (Opens.ext (Set.ext fun q => hmem q))

theorem s16d_val_heq {P P' : OrientedThreeStage.{u}} (h : P' = P) {O' : Opens P'.Carrier}
    {O : Opens P.Carrier} (hO : HEq O' O) {x' : O'} {x : O} (hx : HEq x' x) :
    HEq x'.val x.val := by
  subst h
  cases eq_of_heq hO
  cases eq_of_heq hx
  rfl

theorem s16d_subtype_heq {P P' : OrientedThreeStage.{u}} (h : P' = P) {O' : Opens P'.Carrier}
    {O : Opens P.Carrier} (hO : HEq O' O) {x' : O'} {x : O} (hx : HEq x'.val x.val) :
    HEq x' x := by
  subst h
  cases eq_of_heq hO
  exact heq_of_eq (Subtype.ext (eq_of_heq hx))

theorem s16d_localPull_heq {P P' Q Q' : OrientedThreeStage.{u}} (hP : P' = P) (hQ : Q' = Q)
    {O' : Opens P'.Carrier} {O : Opens P.Carrier} (hO : HEq O' O)
    {T' : Opens Q'.Carrier} {T : Opens Q.Carrier} (hT : HEq T' T)
    {m' : SmoothRiemannianMetric ThreeModel T'} {m : SmoothRiemannianMetric ThreeModel T}
    (hm : HEq m' m) (f' : O' → T') (f : O → T) (hf : ∀ x' x, HEq x' x → HEq (f' x') (f x))
    (h' : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f')
    (h : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) :
    HEq (localPullMetric m' f' h') (localPullMetric m f h) := by
  subst hP hQ
  cases eq_of_heq hO
  cases eq_of_heq hT
  cases eq_of_heq hm
  have : f' = f := funext fun x => eq_of_heq (hf x x HEq.rfl)
  subst this
  rfl

theorem s16d_castSlab_metric_heq {P Q : OrientedThreeStage.{u}} {a a' s : ℝ} (hP : P = Q)
    (ha : a = a') (G : P.IncomingSlab a s) (τ : ℝ) :
    HEq ((s16d_castSlab hP ha G).flow.base.metric τ) (G.flow.base.metric τ) := by
  subst hP
  subst ha
  rfl

/-- Change the endpoint of a backward trace along an equality. -/
def s16d_traceEndpoint {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {p p' : (H.stage last).Carrier}
    (B : BackwardPointTrace H first last hle p) (h : p = p') :
    BackwardPointTrace H first last hle p' where
  point := B.point
  endpoint_eq := B.endpoint_eq.trans h
  crossing := B.crossing

/-! ## Time translation of the analytic part -/

/-- A depth-one strong neck of a time-translated solution. -/
def s16d_strongNeck_shift {P : OrientedThreeStage.{u}} {O : Opens P.Carrier}
    {D D' : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := O) D}
    {S' : SolutionOn (I := ThreeModel) (M := O) D'} {eps t c : ℝ} {x : O}
    (nk : StrongNeck S eps x t) (hmet : ∀ τ, S'.base.metric τ = S.base.metric (τ + -c))
    (hD : ∀ τ ∈ Icc (t - (S.scalar t x)⁻¹) t, τ + c ∈ D'.carrier) :
    StrongNeck S' eps x (t + c) := by
  have hQ : S'.scalar (t + c) x = S.scalar t x := by
    change metricScalarAt (S'.base.metric (t + c)) x = metricScalarAt (S.base.metric t) x
    rw [hmet, add_neg_cancel_right]
  have hQpos : 0 < S'.scalar (t + c) x := hQ ▸ nk.Q_pos
  have key : ∀ (Q Q' : ℝ) (hQ0 : 0 < Q) (hQ' : 0 < Q'), Q' = Q →
      Perelman.CanonicalNeighborhood.rescaledMetric S' (t + c) Q' hQ' =
        Perelman.CanonicalNeighborhood.rescaledMetric S t Q hQ0 := by
    intro Q Q' hQ0 hQ' e
    subst e
    funext τ
    simp only [Perelman.CanonicalNeighborhood.rescaledMetric, hmet]
    congr 2
    simp only [parabolicTime]
    ring
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQpos
      cylinder := nk.cylinder
      map := nk.map
      center := nk.center
      center_eq := nk.center_eq
      domain := nk.domain
      time_domain := ?_
      comparison := ?_ }
  · intro τ hτ
    rw [hQ] at hτ
    have h := hD (τ + -c) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    rwa [neg_add_cancel_right] at h
  · rw [key _ _ nk.Q_pos hQpos hQ]
    exact nk.comparison

/-- The analytic part of a full neck (window, current slab, solution, strong neck) moves along a
stage equality and a time translation by `c`. -/
theorem s16d_shift_core {P P' : OrientedThreeStage.{u}} (hP : P' = P) {O : Opens P.Carrier}
    {O' : Opens P'.Carrier} (hO : HEq O' O) {a s f t c eps a' s' f' : ℝ}
    (ha : a' = a + c) (hs : s' = s + c) (hf : f' = f + c)
    {G : P.IncomingSlab a s} {G' : P'.IncomingSlab a' s'} (hG : HEq G' (G.timeTranslate c))
    {y : P.Carrier} {y' : P'.Carrier} (hy : HEq y' y) (hts : f < s)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel O) (htk : a ≤ t)
    (hfirst : f ≤ t - (G.flow.scalar t y)⁻¹)
    (hcur : ∀ τ ∈ Ico a s, gflow τ = (G.flow.base.metric τ).restrictOpen O)
    (hsol : IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen f s hts)))
    (z : O) (hz : z.val = y)
    (nk : StrongNeck ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen f s hts)) eps z t) :
    ∃ (hts' : f' < s') (gflow' : ℝ → SmoothRiemannianMetric ThreeModel O'),
      (∀ τ, HEq (gflow' τ) (gflow (τ + -c))) ∧ a' ≤ t + c ∧
      f' ≤ t + c - (G'.flow.scalar (t + c) y')⁻¹ ∧
      (∀ τ ∈ Ico a' s', gflow' τ = (G'.flow.base.metric τ).restrictOpen O') ∧
      IsSolutionOn ({ base := { metric := gflow' } } :
        SolutionOn (I := ThreeModel) (M := O') (RealTimeInterval.closedOpen f' s' hts')) ∧
      ∃ z' : O', z'.val = y' ∧
        Nonempty (StrongNeck ({ base := { metric := gflow' } } :
          SolutionOn (I := ThreeModel) (M := O') (RealTimeInterval.closedOpen f' s' hts'))
          eps z' (t + c)) := by
  subst hP ha hs hf
  cases eq_of_heq hO.symm
  cases eq_of_heq hG
  cases eq_of_heq hy.symm
  have hts' : f + c < s + c := by linarith
  refine ⟨hts', fun τ => gflow (τ + -c), fun τ => HEq.rfl, by linarith, ?_, ?_, ?_, z, hz, ?_⟩
  · have hsc : ∀ w,
        (G.timeTranslate c).flow.scalar (t + c) w = G.flow.scalar t w := fun w => by
      change metricScalarAt ((G.timeTranslate c).flow.base.metric (t + c)) w =
        metricScalarAt (G.flow.base.metric t) w
      rw [G.timeTranslate_metric_add]
    rw [hsc]
    linarith
  · intro τ hτ
    change gflow (τ + -c) = _
    rw [hcur (τ + -c) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩]
    rfl
  · refine isSolutionOn_cast (isSolutionOn_timeShift hsol (-c)) ?_ ?_
    · ext τ
      change τ + -c ∈ Ico f s ↔ τ ∈ Ico (f + c) (s + c)
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    · ext τ
      change τ + -c ∈ Ioo f s ↔ τ ∈ Ioo (f + c) (s + c)
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · refine ⟨s16d_strongNeck_shift nk (fun _ => rfl) fun τ hτ => ?_⟩
    have h := nk.time_domain hτ
    change f ≤ τ ∧ τ < s at h
    change f + c ≤ τ + c ∧ τ + c < s + c
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## Translated events -/

theorem s16d_rec_heq {P : OrientedThreeStage.{u}} {T T' : Opens P.Carrier} (h : T = T')
    (m : SmoothRiemannianMetric ThreeModel T) :
    HEq (h ▸ m : SmoothRiemannianMetric ThreeModel T') m := by
  subst h
  rfl

/-- A translated event has the same terminal region, and its extended metric at `τ` is the
original one at `τ - c`. -/
theorem s16d_translated_terminal {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (GC.GeneralFlow.translate_retained_event E c)) (τ : ℝ) :
    HEq E'.incoming.terminalRegularOpen E.incoming.terminalRegularOpen ∧
      HEq (E'.terminal.extendedMetric τ) (E.terminal.extendedMetric (τ + -c)) := by
  subst hP hQ ha hs
  cases eq_of_heq hE
  have hT := GC.GeneralFlow.translated_terminal_open E.incoming c
  refine ⟨heq_of_eq hT, ?_⟩
  by_cases hτ : τ < s + c
  · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_before _ hτ,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_before _
        (by linarith : τ + -c < s)]
    change HEq ((E.incoming.flow.base.metric (τ + -c)).restrictOpen
      (E.incoming.timeTranslate c).terminalRegularOpen)
      ((E.incoming.flow.base.metric (τ + -c)).restrictOpen E.incoming.terminalRegularOpen)
    rw [hT]
  · have h1 : ¬ τ + -c < s := fun h => hτ (by linarith)
    simp only [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric, hτ, h1,
      ↓reduceIte]
    exact s16d_rec_heq hT.symm E.terminal.metric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow.AffineEventPrefix

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
  (A : GC.GeneralFlow.AffineEventPrefix K J c offset (Fin.last K.eventCount))

/-- The translated incoming slab in `J`. -/
def s16d_slab (k : Fin (K.eventCount + 1)) {s : ℝ} (G : (K.stage k).IncomingSlab (K.time k) s) :
    (J.stage (A.stageIndex k)).IncomingSlab (J.time (A.stageIndex k)) (s + c) :=
  s16d_castSlab (A.stageIndex_stage k).symm (A.stageIndex_time k).symm (G.timeTranslate c)

theorem s16d_exists_eventIndex {first : Fin (K.eventCount + 1)} (j : Fin J.eventCount)
    (hj : A.stageIndex first ≤ j.castSucc) : ∃ i : Fin K.eventCount, A.eventIndex i = j := by
  have ho : offset ≤ j.val := by
    have h : offset + first.val ≤ j.val := hj
    omega
  refine ⟨⟨j.val - offset, by
    have := j.isLt
    have h1 : J.eventCount = offset + K.eventCount := A.count_eq
    omega⟩, ?_⟩
  apply Fin.ext
  change offset + (j.val - offset) = j.val
  omega

/-- **TC**：a full neck of `K` at `(k, G, y, t)` is a full neck of `J` at
`(stageIndex k, G translated, y, t + c)`. -/
theorem historyStrongNeckFull_affine_C12X (k : Fin (K.eventCount + 1)) {s : ℝ}
    (G : (K.stage k).IncomingSlab (K.time k) s) {eps : ℝ} {y : (K.stage k).Carrier} {t : ℝ}
    (h : K.toHistory.HistoryStrongNeckFull_C12X k G eps y t) :
    J.toHistory.HistoryStrongNeckFull_C12X (A.stageIndex k) (A.s16d_slab k G) eps
      (s16d_castPoint (A.stageIndex_stage k).symm y) (t + c) := by
  obtain ⟨first, hle, hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, ⟨nk⟩⟩ := h
  have hle' : A.stageIndex first ≤ A.stageIndex k := (A.stageIndex_le_iff _ _).mpr hle
  have hO : HEq (J.toHistory.backwardSurvivorDomain (A.stageIndex first) (A.stageIndex k) hle')
      (K.toHistory.backwardSurvivorDomain first k hle) := by
    refine s16d_opens_heq (A.stageIndex_stage k) fun q => ?_
    exact ⟨fun ⟨B⟩ => ⟨(A.traceEquiv first k hle q).symm B⟩,
      fun ⟨B⟩ => ⟨A.traceEquiv first k hle q B⟩⟩
  obtain ⟨hts', gflow', hgf, htk', hfirst', hcur', hsol', z', hz', hnk'⟩ :=
    s16d_shift_core (A.stageIndex_stage k) hO (A.stageIndex_time k) rfl
      (A.stageIndex_time first) (s16d_castSlab_heq _ _ (G.timeTranslate c)).symm
      (s16d_castPoint_heq _ y) hts gflow htk hfirst hcur hsol z hz nk
  refine ⟨A.stageIndex first, hle', hts', gflow', htk', hfirst', ?_, hcur', hsol', z', hz', hnk'⟩
  intro j hj hl τ hτ
  obtain ⟨i, rfl⟩ := A.s16d_exists_eventIndex j hj
  have hi1 : first ≤ i.castSucc := by
    have h : offset + first.val ≤ offset + i.val := hj
    change first.val ≤ i.val
    omega
  have hi2 : i.succ ≤ k := by
    have h : offset + i.val + 1 ≤ offset + k.val := hl
    change i.val + 1 ≤ k.val
    omega
  have e1 : J.time (A.eventIndex i).castSucc = K.time i.castSucc + c :=
    A.stageIndex_time i.castSucc
  have e2 : J.time (A.eventIndex i).succ = K.time i.succ + c := A.stageIndex_time i.succ
  have hτ' : τ + -c ∈ Icc (K.time i.castSucc) (K.time i.succ) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  obtain ⟨hT, hm⟩ := s16d_translated_terminal (K.coreEvent i) c (A.stageIndex_stage i.castSucc)
    (A.stageIndex_stage i.succ) (A.stageIndex_time i.castSucc) (A.stageIndex_time i.succ)
    (A.event_heq i) τ
  refine eq_of_heq ((hgf τ).trans ((heq_of_eq (hslab i hi1 hi2 _ hτ')).trans
    (s16d_localPull_heq (A.stageIndex_stage k) (A.stageIndex_stage i.castSucc) hO hT hm _ _
      (fun x' x hx => ?_) _ _).symm))
  refine s16d_subtype_heq (A.stageIndex_stage i.castSucc) hT ?_
  let B := Classical.choice x.property
  have hend : s16d_castPoint (A.stageIndex_stage k).symm x.val = x'.val :=
    eq_of_heq ((s16d_castPoint_heq _ _).trans (s16d_val_heq (A.stageIndex_stage k) hO hx).symm)
  let B' := s16d_traceEndpoint (A.traceEquiv first k hle x.val B) hend
  exact (heq_of_eq (J.toHistory.backwardSurvivorMap_eq_point _ _ hle' _ hj
    ((Fin.castSucc_lt_succ (i := A.eventIndex i)).le.trans hl) x' B')).trans
    ((A.traceEquiv_point_heq B i.castSucc hi1 (i.castSucc_lt_succ.le.trans hi2)).trans
      (heq_of_eq (K.toHistory.backwardSurvivorMap_eq_point first k hle _ hi1
        (i.castSucc_lt_succ.le.trans hi2) x B).symm))

/-- Witness and neck clause (`StronglyCanonicalAtFull_C12X`) along the affine prefix. -/
theorem stronglyCanonicalAtFull_affine_C12X (k : Fin (K.eventCount + 1)) {s : ℝ}
    (G : (K.stage k).IncomingSlab (K.time k) s) {ε ε₁ C1 C2 : ℝ} {y : (K.stage k).Carrier}
    {t : ℝ} (h : K.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t) :
    J.StronglyCanonicalAtFull_C12X (A.stageIndex k) (A.s16d_slab k G) ε ε₁ C1 C2
      (s16d_castPoint (A.stageIndex_stage k).symm y) (t + c) := by
  obtain ⟨W, hW, himp⟩ := h
  have hmet : HEq (G.flow.base.metric t) ((A.s16d_slab k G).flow.base.metric (t + c)) :=
    (heq_of_eq (G.timeTranslate_metric_add c t)).symm.trans
      (s16d_castSlab_metric_heq _ _ (G.timeTranslate c) (t + c)).symm
  obtain ⟨W', hW', hrefl⟩ := s16d_witness_transport (A.stageIndex_stage k).symm hmet
    (s16d_castPoint_heq _ y).symm W hW
  refine ⟨W', hW', fun ⟨n', hn'⟩ => ?_⟩
  exact A.historyStrongNeckFull_affine_C12X k G (himp (hrefl n' hn'))

/-- Incoming-slab agreement clause along the affine prefix (needs the final-metric identity). -/
theorem incomingAgree_affine_C12X
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (k : Fin (K.eventCount + 1)) {s : ℝ} (G : (K.stage k).IncomingSlab (K.time k) s) {t : ℝ}
    (hagree : ∀ τ ∈ Icc (K.time k) t, G.flow.base.metric τ = K.toHistory.stageMetric k τ) :
    ∀ τ ∈ Icc (J.time (A.stageIndex k)) (t + c),
      (A.s16d_slab k G).flow.base.metric τ = J.toHistory.stageMetric (A.stageIndex k) τ := by
  intro τ hτ
  have e := A.stageIndex_time k
  have hm := A.stageMetric_shift_heq hfinal k (τ - c)
  rw [sub_add_cancel] at hm
  refine eq_of_heq ((s16d_castSlab_metric_heq _ _ (G.timeTranslate c) τ).trans ?_)
  rw [G.timeTranslate_metric, hagree (τ - c) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩]
  exact hm.symm

end GC.GeneralFlow.AffineEventPrefix

end
