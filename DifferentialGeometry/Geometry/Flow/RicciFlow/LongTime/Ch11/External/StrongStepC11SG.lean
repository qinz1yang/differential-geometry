import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainJoinC12X

/-!
# Strong-invariant maintenance along one prepared step (C11SG, S16 producer)

Producer spec v2 §3.5 (successor `hstrong`): the `strong` field of `PreparedSpatialState` is
maintained by a step on the old window `t < E` (from the old state through `SamePresentation`
(TA) and `restrict` (TB⁻¹)) and on the new window `E ≤ t < B` (from the old class
`strongControl` on the extended old native `Kplus`, through the affine prefix (TC)).

All statements here are about plain histories (no `PreparedSpatialState`), so the file only
imports the ch12 chain layer.

* `StrongAtC11SG X ε C1 C2 t x` is the body of the `strong` field at one point `(t, x)`;
* `strongAt_transport_C11SG`: stage-level transport (witness, constants enlarged, neck clause);
* `strongAt_of_slabs_C11SG`: the slab-level output of `strongControl` gives the pointwise clause.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace GC.GeneralFlow

universe u

/-- The body of the `strong` field of `PreparedSpatialState` at a stage index `k`, a real time `τ`
and a point `x` of the stage `k`. -/
def StrongAtIdxC11SG (X : ObservedHistory.{u}) (ε C1 C2 : ℝ) (k : Fin (X.eventCount + 1))
    (τ : ℝ) (x : (X.stage k).Carrier) : Prop :=
  ∃ W : SpatialCanonicalWitness (X.stageMetric k τ) ε C1 C2 x,
    W.capTubeHasNeckChart ε ∧
    ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
      ∃ (s' : ℝ) (G : (X.stage k).IncomingSlab (X.time k) s'),
        (∀ τ' ∈ Icc (X.time k) τ, G.flow.base.metric τ' = X.stageMetric k τ') ∧
        X.HistoryStrongNeckFull_C12X k G ε x τ

/-- The `strong` field body at a regular time `t` (active stage). -/
def StrongAtC11SG (X : ObservedHistory.{u}) (ε C1 C2 : ℝ) (t : Icc (0 : ℝ) X.horizon)
    (x : (X.stage (X.activeStage t)).Carrier) : Prop :=
  StrongAtIdxC11SG X ε C1 C2 (X.activeStage t) (t : ℝ) x

/-- The clause only depends on the stage index through equality (point cast along `HEq`). -/
theorem strongAtIdx_congr_C11SG {X : ObservedHistory.{u}} {ε C1 C2 : ℝ}
    {k k' : Fin (X.eventCount + 1)} (hk : k = k') {τ : ℝ} {y : (X.stage k).Carrier}
    {y' : (X.stage k').Carrier} (hy : HEq y y') (h : StrongAtIdxC11SG X ε C1 C2 k τ y) :
    StrongAtIdxC11SG X ε C1 C2 k' τ y' := by
  subst hk
  cases eq_of_heq hy
  exact h

/-- **Stage-level transport of the pointwise `strong` clause**: matched stage, metric and point;
the neck clause transports through the explicit `hneck`; the constants may be enlarged. -/
theorem strongAtIdx_transport_C11SG {X Y : ObservedHistory.{u}} {kX : Fin (X.eventCount + 1)}
    {kY : Fin (Y.eventCount + 1)} {τX τY : ℝ} (hstage : X.stage kX = Y.stage kY)
    (hmet : HEq (X.stageMetric kX τX) (Y.stageMetric kY τY))
    {x : (X.stage kX).Carrier} {y : (Y.stage kY).Carrier} (hxy : HEq x y)
    {ε C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (hneck : ∀ (s' : ℝ) (G : (X.stage kX).IncomingSlab (X.time kX) s'),
      (∀ τ ∈ Icc (X.time kX) τX, G.flow.base.metric τ = X.stageMetric kX τ) →
      X.HistoryStrongNeckFull_C12X kX G ε x τX →
      ∃ (s'' : ℝ) (G' : (Y.stage kY).IncomingSlab (Y.time kY) s''),
        (∀ τ ∈ Icc (Y.time kY) τY, G'.flow.base.metric τ = Y.stageMetric kY τ) ∧
        Y.HistoryStrongNeckFull_C12X kY G' ε y τY)
    (h : StrongAtIdxC11SG X ε C1 C2 kX τX x) : StrongAtIdxC11SG Y ε C1' C2' kY τY y := by
  obtain ⟨W, hW, himp⟩ := h
  obtain ⟨W', hW', hrefl⟩ := s16d_witness_transport hstage hmet hxy W hW
  refine ⟨W'.enlargeConstants hC1 hC2, hW'.enlarge_constants hC1 hC2, fun nk hnk => ?_⟩
  have hneckW : ∃ nk', W'.alternative = SpatialCanonicalAlternative.neck nk' := by
    change W'.alternative.monoConstant (zero_lt_one.trans_le W'.one_le_comparison_constant) hC2
      W'.Q_pos.le = SpatialCanonicalAlternative.neck nk at hnk
    cases halt : W'.alternative with
    | neck data => exact ⟨data, rfl⟩
    | cap data deep =>
      rw [halt] at hnk
      cases hnk
    | positive whole data sec =>
      rw [halt] at hnk
      cases hnk
    | round whole data =>
      rw [halt] at hnk
      cases hnk
  obtain ⟨nk', hnk'⟩ := hneckW
  obtain ⟨nk0, hnk0⟩ := hrefl nk' hnk'
  obtain ⟨s', G, hG, hN⟩ := himp nk0 hnk0
  exact hneck s' G hG hN

/-- Slab-level statement at a stage index `j` and a real time `τ` (the body of
`StrongAtC11SG` with `X.activeStage t` and `t` abstracted). -/
private theorem strongAt_of_slabs_aux (X : RetainedCoreHistory.{u}) {ε C1 C2 q : ℝ}
    (hev : X.EventSlabsStronglyCanonicalFull_C12X ε ε C1 C2 q (Fin.last X.eventCount))
    (hfin : ∀ hfinal : X.time (Fin.last X.eventCount) < X.horizon,
      X.StronglyCanonicalBeforeFull_C12X (Fin.last X.eventCount)
        ((X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1 C2 q X.horizon)
    (τ : ℝ) (hτH : τ < X.horizon) (j : Fin (X.eventCount + 1))
    (hnext : ∀ i : Fin X.eventCount, j = i.castSucc → τ < X.time i.succ)
    (hreg : X.time j < τ) (x : (X.stage j).Carrier)
    (hx : q < metricScalarAt (X.toHistory.stageMetric j τ) x) :
    StrongAtIdxC11SG X.toHistory ε C1 C2 j τ x := by
  unfold StrongAtIdxC11SG
  induction j using Fin.lastCases with
  | last =>
    have hfinal : X.time (Fin.last X.eventCount) < X.horizon := hreg.trans hτH
    have hGm : ∀ τ' : ℝ,
        ((X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).flow.base.metric τ' =
          X.toHistory.stageMetric (Fin.last X.eventCount) τ' := by
      intro τ'
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, hfinal, ↓reduceDIte]
      rfl
    have hq : q <
        ((X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).flow.scalar τ x := by
      change q < metricScalarAt
        (((X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).flow.base.metric τ) x
      rw [hGm τ]
      exact hx
    have h := hfin hfinal x τ ⟨hreg, hτH⟩ hq
    rw [← hGm τ]
    obtain ⟨W, hW, himp⟩ := h
    exact ⟨W, hW, fun nk hnk => ⟨_, (X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl,
      fun τ' _ => hGm τ', himp ⟨nk, hnk⟩⟩⟩
  | cast i =>
    have hGm : ∀ τ' : ℝ, (X.toHistory.event i).incoming.flow.base.metric τ' =
        X.toHistory.stageMetric i.castSucc τ' := fun τ' =>
      (ObservedHistory.stageMetric_castSucc_apply (H := X.toHistory) i τ').symm
    have hq : q < (X.toHistory.event i).incoming.flow.scalar τ x := by
      change q < metricScalarAt ((X.toHistory.event i).incoming.flow.base.metric τ) x
      rw [hGm τ]
      exact hx
    have h := hev i (Fin.castSucc_lt_last i) x τ ⟨hreg, hnext i rfl⟩ hq
    rw [← hGm τ]
    obtain ⟨W, hW, himp⟩ := h
    exact ⟨W, hW, fun nk hnk => ⟨_, (X.toHistory.event i).incoming,
      fun τ' _ => hGm τ', himp ⟨nk, hnk⟩⟩⟩

/-- **Slab level to pointwise**: the output of `strongControl` (event slabs and final slab of `X`
strongly canonical with full necks above `q`) gives the pointwise clause at every regular time
`t < X.horizon` and every point of the active stage above `q`. -/
theorem strongAt_of_slabs_C11SG (X : RetainedCoreHistory.{u}) {ε C1 C2 q : ℝ}
    (hev : X.EventSlabsStronglyCanonicalFull_C12X ε ε C1 C2 q (Fin.last X.eventCount))
    (hfin : ∀ hfinal : X.time (Fin.last X.eventCount) < X.horizon,
      X.StronglyCanonicalBeforeFull_C12X (Fin.last X.eventCount)
        ((X.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1 C2 q X.horizon)
    (t : Icc (0 : ℝ) X.toHistory.horizon) (htH : (t : ℝ) < X.horizon)
    (hreg : X.time (X.toHistory.activeStage t) < (t : ℝ))
    (x : (X.toHistory.stage (X.toHistory.activeStage t)).Carrier)
    (hx : q < metricScalarAt (X.toHistory.stageMetric (X.toHistory.activeStage t) t) x) :
    StrongAtC11SG X.toHistory ε C1 C2 t x := by
  have hmem := X.toHistory.activeStage_mem t
  have hnext : ∀ i : Fin X.eventCount, X.toHistory.activeStage t = i.castSucc →
      (t : ℝ) < X.time i.succ := by
    intro i hi
    rw [hi] at hmem
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hmem
    exact hmem.2
  exact strongAt_of_slabs_aux X hev hfin t htH _ hnext hreg x hx

/-! ## New window: the affine prefix (TC) -/

/-- **TC at the pointwise level**: the clause of the extended old native `Kp` at `(k, τ, y)` gives
the clause of the new full history `J` at `(stageIndex k, τ + c, y)`. -/
theorem strongAtIdx_affine_C11SG {Kp J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix Kp J c offset (Fin.last Kp.eventCount))
    (hfinal : ∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
      (Kp.toHistory.stageMetric (Fin.last Kp.eventCount) t))
    {ε C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (k : Fin (Kp.eventCount + 1)) (τ : ℝ) (y : (Kp.stage k).Carrier)
    (h : StrongAtIdxC11SG Kp.toHistory ε C1 C2 k τ y) :
    StrongAtIdxC11SG J.toHistory ε C1' C2' (A.stageIndex k) (τ + c)
      (s16d_castPoint (A.stageIndex_stage k).symm y) := by
  refine strongAtIdx_transport_C11SG (X := Kp.toHistory) (Y := J.toHistory)
    (A.stageIndex_stage k).symm (A.stageMetric_shift_heq hfinal k τ).symm
    (s16d_castPoint_heq _ y).symm hC1 hC2 (fun s' G hagree hN => ?_) h
  exact ⟨s' + c, A.s16d_slab k G, A.incomingAgree_affine_C12X hfinal k G hagree,
    A.historyStrongNeckFull_affine_C12X k G hN⟩

/-! ## Old window: `SamePresentation` (TA) and `restrict` (TB⁻¹) -/

/-- The stage domain is closed under lowering the time down to the stage start. -/
theorem stageDomain_of_ge_time_C11SG (X : ObservedHistory.{u}) (k : Fin (X.eventCount + 1))
    {τ τ' : ℝ} (hτ : τ ∈ X.stageDomain k) (h1 : X.time k ≤ τ') (h2 : τ' ≤ τ) :
    τ' ∈ X.stageDomain k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc] at hτ ⊢
    exact ⟨h1, h2.trans hτ.2⟩
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hτ ⊢
    exact ⟨h1, h2.trans_lt hτ.2⟩

/-- **TA at the pointwise level**: along `SamePresentation` (matched stage indices). -/
theorem strongAtIdx_samePresentation_C11SG {H K : ObservedHistory.{u}} (R : H.SamePresentation K)
    {k : Fin (H.eventCount + 1)} {k' : Fin (K.eventCount + 1)} (hk : k.val = k'.val) {τ : ℝ}
    (hdom : τ ∈ H.stageDomain k) {x : (H.stage k).Carrier} {y : (K.stage k').Carrier}
    (hxy : HEq x y) {ε C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (h : StrongAtIdxC11SG H ε C1 C2 k τ x) : StrongAtIdxC11SG K ε C1' C2' k' τ y := by
  have hkk : k' = Fin.cast (congrArg (· + 1) R.count_eq) k := Fin.ext hk.symm
  have hstage : H.stage k = K.stage k' := by
    rw [hkk]
    exact R.stage_eq k
  have htime : H.time k = K.time k' := by
    rw [hkk]
    exact R.time_eq k
  refine strongAtIdx_transport_C11SG hstage ?_ hxy hC1 hC2 (fun s' G hagree hN => ?_) h
  · rw [hkk]
    exact R.metric_heq k τ hdom
  · refine ⟨s', s16d_castSlab hstage htime G, ?_, ?_⟩
    · exact ObservedHistory.incomingAgree_of_samePresentation_C12X R hk
        (s16d_castSlab_heq hstage htime G)
        (fun τ' hτ' => stageDomain_of_ge_time_C11SG H k hdom hτ'.1 hτ'.2) hagree
    · exact ObservedHistory.HistoryStrongNeckFull_C12X.of_samePresentation_C12X R hk
        (s16d_castSlab_heq hstage htime G) hxy hN

/-- **TB⁻¹ at the pointwise level**: from `H.restrict b` to `H` (same point: the stages agree
definitionally). -/
theorem strongAtIdx_restrict_C11SG (H : ObservedHistory.{u}) (b : Icc (0 : ℝ) H.horizon)
    (k : Fin ((H.restrict b).eventCount + 1)) {τ : ℝ}
    (hdom : τ ∈ (H.restrict b).stageDomain k)
    {x : ((H.restrict b).stage k).Carrier} {ε C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1')
    (hC2 : C2 ≤ C2') (h : StrongAtIdxC11SG (H.restrict b) ε C1 C2 k τ x) :
    StrongAtIdxC11SG H ε C1' C2' (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k)
      τ x := by
  refine strongAtIdx_transport_C11SG (X := H.restrict b) (Y := H) rfl
    (H.restrict_stageMetric b k τ hdom) HEq.rfl hC1 hC2 (fun s' G hagree hN => ?_) h
  exact ⟨s', G, ObservedHistory.incomingAgree_of_restrict_C12X H b k G
    (fun τ' hτ' => stageDomain_of_ge_time_C11SG _ k hdom hτ'.1 hτ'.2) hagree,
    H.historyStrongNeckFull_of_restrict_C12X b k G hN⟩

/-- **Old window**: the clause of a prefix `H ⊑ J` at a time `tH` is the clause of `J` at the
same time (TA along `J.restrict ≅ H`, then TB⁻¹). -/
theorem strongAt_prefix_C11SG {H J : ObservedHistory.{u}} (hIJ : H.IsPrefixOf J)
    {ε C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (tH : Icc (0 : ℝ) H.horizon) (tJ : Icc (0 : ℝ) J.horizon) (htJ : (tJ : ℝ) = tH)
    (xH : (H.stage (H.activeStage tH)).Carrier) (xJ : (J.stage (J.activeStage tJ)).Carrier)
    (hxy : HEq xH xJ) (h : StrongAtC11SG H ε C1 C2 tH xH) :
    StrongAtC11SG J ε C1' C2' tJ xJ := by
  obtain rfl : tJ = ⟨tH.1, tH.2.1, tH.2.2.trans hIJ.horizon_le⟩ := Subtype.ext htJ
  let b : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hIJ.horizon_le⟩
  have R : (J.restrict b).SamePresentation H := hIJ.presentation
  let tR : Icc (0 : ℝ) (J.restrict b).horizon := ⟨tH.1, tH.2.1, tH.2.2⟩
  have hk : (H.activeStage tH).val = ((J.restrict b).activeStage tR).val :=
    congrArg Fin.val (ObservedHistory.SamePresentation.activeStage H R.symm tH)
  have hst : H.stage (H.activeStage tH) = (J.restrict b).stage ((J.restrict b).activeStage tR) :=
    R.symm.stageAt_eq tH
  have h1 := strongAtIdx_samePresentation_C11SG R.symm hk (H.activeStage_mem tH)
    (s16d_castPoint_heq hst xH).symm hC1 le_rfl h
  have h2 := strongAtIdx_restrict_C11SG J b ((J.restrict b).activeStage tR)
    ((J.restrict b).activeStage_mem tR) le_rfl hC2 h1
  refine strongAtIdx_congr_C11SG (J.restrict_activeStage b tR) ?_ h2
  exact (s16d_castPoint_heq hst xH).trans hxy

/-- **New window**: the slab-level output of `strongControl` on the extended old native `Kp`
(an affine tail of `J`) gives the clause of `J` at every regular time `tJ = t' + c` and every
point above `q`. -/
theorem strongAt_newWindow_C11SG {Kp J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix Kp J c offset (Fin.last Kp.eventCount))
    (hhor : J.horizon = Kp.horizon + c)
    (hfinal : ∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
      (Kp.toHistory.stageMetric (Fin.last Kp.eventCount) t))
    {ε C1 C2 C1' C2' q : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (hev : Kp.EventSlabsStronglyCanonicalFull_C12X ε ε C1 C2 q (Fin.last Kp.eventCount))
    (hfin : ∀ hfinal : Kp.time (Fin.last Kp.eventCount) < Kp.horizon,
      Kp.StronglyCanonicalBeforeFull_C12X (Fin.last Kp.eventCount)
        ((Kp.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1 C2 q Kp.horizon)
    (t' : Icc (0 : ℝ) Kp.toHistory.horizon) (tJ : Icc (0 : ℝ) J.toHistory.horizon)
    (htJ : (tJ : ℝ) = (t' : ℝ) + c) (ht'H : (t' : ℝ) < Kp.horizon)
    (hreg : Kp.time (Kp.toHistory.activeStage t') < (t' : ℝ))
    (xJ : (J.toHistory.stage (J.toHistory.activeStage tJ)).Carrier)
    (hx : q < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ) xJ) :
    StrongAtC11SG J.toHistory ε C1' C2' tJ xJ := by
  obtain rfl : tJ = A.shiftTime hhor t' := Subtype.ext htJ
  have hst : J.toHistory.stageAt (A.shiftTime hhor t') = Kp.toHistory.stageAt t' :=
    A.stageAt_shift_eq hhor t'
  let xK : (Kp.toHistory.stage (Kp.toHistory.activeStage t')).Carrier := s16d_castPoint hst xJ
  have hxK : HEq xK xJ := s16d_castPoint_heq hst xJ
  have hqK : q < metricScalarAt (Kp.toHistory.stageMetric (Kp.toHistory.activeStage t') t') xK := by
    rw [s16d_scalar_eq hst (A.sliceMetric_shift_heq hhor hfinal t') hxK.symm] at hx
    exact hx
  have hK := strongAt_of_slabs_C11SG Kp hev hfin t' ht'H hreg xK hqK
  have h1 := strongAtIdx_affine_C11SG A hfinal hC1 hC2 (Kp.toHistory.activeStage t') t' xK hK
  refine strongAtIdx_congr_C11SG (A.activeStage_shift_eq hhor t').symm ?_ h1
  exact (s16d_castPoint_heq _ xK).trans hxK

/-! ## Assembly for one prepared step -/

/-- The active stage and its time agree on a prefix (the same real time). -/
theorem prefix_activeTime_eq_C11SG {H J : ObservedHistory.{u}} (hIJ : H.IsPrefixOf J)
    (tH : Icc (0 : ℝ) H.horizon) (tJ : Icc (0 : ℝ) J.horizon) (htJ : (tJ : ℝ) = tH) :
    H.time (H.activeStage tH) = J.time (J.activeStage tJ) := by
  obtain rfl : tJ = ⟨tH.1, tH.2.1, tH.2.2.trans hIJ.horizon_le⟩ := Subtype.ext htJ
  let b : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hIJ.horizon_le⟩
  have R : (J.restrict b).SamePresentation H := hIJ.presentation
  let tR : Icc (0 : ℝ) (J.restrict b).horizon := ⟨tH.1, tH.2.1, tH.2.2⟩
  have hc := ObservedHistory.SamePresentation.activeStage H R.symm tH
  have e1 : H.time (H.activeStage tH) = (J.restrict b).time ((J.restrict b).activeStage tR) := by
    rw [← hc]
    exact R.symm.time_eq (H.activeStage tH)
  rw [e1, ← J.restrict_activeStage b tR]
  rfl

/-- Final-metric identity of the extended old native in the new full history. -/
theorem finalMetric_join_C11SG {N J Kp : ObservedHistory.{u}} {a b c : ℝ} (hba : b = a + c)
    (hJ : ∀ t : ℝ, HEq (J.stageMetric (Fin.last J.eventCount) (t + b))
      (N.stageMetric (Fin.last N.eventCount) t))
    (hK : ∀ t : ℝ, HEq (Kp.stageMetric (Fin.last Kp.eventCount) (t + a))
      (N.stageMetric (Fin.last N.eventCount) t)) (t : ℝ) :
    HEq (J.stageMetric (Fin.last J.eventCount) (t + c))
      (Kp.stageMetric (Fin.last Kp.eventCount) t) := by
  have e1 : t + c = (t - a) + b := by rw [hba]; ring
  have e2 : (t - a) + a = t := sub_add_cancel t a
  have h1 := hJ (t - a)
  have h2 := hK (t - a)
  rw [← e1] at h1
  rw [e2] at h2
  exact h1.trans h2.symm

/-- **Maintenance of the `strong` field by one prepared step** (producer spec v2 §3.5).
Old window `t < E`: the old state's clause through the prefix `H ⊑ J`; new window `E ≤ t < B`:
the old class `strongControl` output on the extended old native `Kp` (an affine tail of `J`).
`ρL ρ` are the neck-radius functions of the old / new state, `r` the old radius, `qS` the old
class's `qStrong`; the constants of the new state are any upper bounds `C1' C2'` of the old state's
and the old class's. -/
theorem step_strong_C11SG {H J Kp : RetainedCoreHistory.{u}}
    {c E B r qS ε C1 C2 C1c C2c C1' C2' : ℝ} {offset : ℕ} (ρL ρ : ℝ → ℝ)
    (hHE : H.horizon = E) (hJB : J.horizon = B)
    (hIJ : H.toHistory.IsPrefixOf J.toHistory)
    (A : AffineEventPrefix Kp J c offset (Fin.last Kp.eventCount))
    (hhor : J.horizon = Kp.horizon + c)
    (hfinal : ∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
      (Kp.toHistory.stageMetric (Fin.last Kp.eventCount) t))
    (hcE : c ≤ E) (hρpast : ∀ t : ℝ, t ≤ E → ρ t = ρL t)
    (hρpos : ∀ t : ℝ, 0 ≤ t → 0 < ρ t)
    (hρle : ∀ t : ℝ, E ≤ t → ρ t ≤ r) (hqS : qS ≤ (r ^ 2)⁻¹)
    (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hC1c : C1c ≤ C1') (hC2c : C2c ≤ C2')
    (hL : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < E →
      H.time (H.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρL t ^ 2)⁻¹ < metricScalarAt
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        StrongAtC11SG H.toHistory ε C1 C2 t x)
    (hev : Kp.EventSlabsStronglyCanonicalFull_C12X ε ε C1c C2c qS (Fin.last Kp.eventCount))
    (hfin : ∀ hfinal : Kp.time (Fin.last Kp.eventCount) < Kp.horizon,
      Kp.StronglyCanonicalBeforeFull_C12X (Fin.last Kp.eventCount)
        ((Kp.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1c C2c qS Kp.horizon) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < B →
      J.time (J.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρ t ^ 2)⁻¹ < metricScalarAt
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        StrongAtC11SG J.toHistory ε C1' C2' t x := by
  intro t htB hreg x hx
  by_cases htE : (t : ℝ) < E
  · have htH : (t : ℝ) ≤ H.horizon := htE.le.trans_eq hHE.symm
    let tH : Icc (0 : ℝ) H.toHistory.horizon := ⟨t, t.2.1, htH⟩
    have hstage : H.toHistory.stageAt tH = J.toHistory.stageAt t := hIJ.stageAt_eq tH
    let xH : (H.toHistory.stage (H.toHistory.activeStage tH)).Carrier :=
      s16d_castPoint hstage.symm x
    have hxH : HEq xH x := s16d_castPoint_heq hstage.symm x
    have hscal := s16d_scalar_eq hstage (hIJ.sliceMetric_heq tH) hxH
    have hregH : H.time (H.toHistory.activeStage tH) < (tH : ℝ) :=
      (prefix_activeTime_eq_C11SG hIJ tH t rfl).trans_lt hreg
    have hxH' : (ρL tH ^ 2)⁻¹ < metricScalarAt
        (H.toHistory.stageMetric (H.toHistory.activeStage tH) tH) xH := by
      rw [hscal]
      change (ρL t ^ 2)⁻¹ < _
      rw [← hρpast t htE.le]
      exact hx
    exact strongAt_prefix_C11SG hIJ hC1 hC2 tH t rfl xH x hxH (hL tH htE hregH xH hxH')
  · have hEt : E ≤ (t : ℝ) := not_lt.mp htE
    have hct : c ≤ (t : ℝ) := hcE.trans hEt
    have htJ' : (t : ℝ) ≤ Kp.horizon + c := hhor ▸ t.2.2
    let t' : Icc (0 : ℝ) Kp.toHistory.horizon :=
      ⟨(t : ℝ) - c, sub_nonneg.mpr hct, by linarith⟩
    have htJ : (t : ℝ) = (t' : ℝ) + c := (sub_add_cancel (t : ℝ) c).symm
    have ht'H : (t' : ℝ) < Kp.horizon := by
      have h : (t : ℝ) < Kp.horizon + c := by rw [← hhor, hJB]; exact htB
      change (t : ℝ) - c < Kp.horizon
      linarith
    have hshift : A.shiftTime hhor t' = t := Subtype.ext htJ.symm
    have hact : J.toHistory.activeStage t = A.stageIndex (Kp.toHistory.activeStage t') := by
      rw [← hshift]
      exact A.activeStage_shift_eq hhor t'
    have hregK : Kp.time (Kp.toHistory.activeStage t') < (t' : ℝ) := by
      have h := hreg
      rw [hact, A.stageIndex_time] at h
      change Kp.time (Kp.toHistory.activeStage t') + c < (t : ℝ) at h
      change Kp.time (Kp.toHistory.activeStage t') < (t : ℝ) - c
      linarith
    have hρt := hρpos t t.2.1
    have hq : qS < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x :=
      (hqS.trans (inv_anti₀ (pow_pos hρt 2)
        (pow_le_pow_left₀ hρt.le (hρle t hEt) 2))).trans_lt hx
    exact strongAt_newWindow_C11SG A hhor hfinal hC1c hC2c hev hfin t' t htJ ht'H hregK x hq

end GC.GeneralFlow

end
