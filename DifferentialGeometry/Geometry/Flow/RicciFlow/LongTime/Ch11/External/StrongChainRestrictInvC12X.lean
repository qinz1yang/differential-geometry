import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainRestrictC12X

/-!
# Full history strong necks: from a restriction back to the history; casts (C12X, S16 G4 / G2)

Companion of `StrongChainRestrictC12X` (G1):

* `historyStrongNeckFull_of_restrict_C12X` (TB⁻¹): a full neck of `H.restrict b` at `k` is a full
  neck of `H` at `castLE k` (the step's old-window maintenance `L.strong ↦ R.strong` goes through
  `L.history ≅ J.restrict E` (TA) and then TB⁻¹, `out/CH12X-S16-PRODUCER-SPEC.md` §3);
* `incomingAgree_of_restrict_C12X`, `incomingAgree_of_samePresentation_C12X`: the incoming-slab
  agreement clause at an arbitrary stage along TB⁻¹ / TA;
* casts along stage equalities (`s16d_castPoint`, `s16d_castSlab`), the scalar equality
  `s16d_scalar_eq`, and the witness transport `s16d_witness_transport` which also reflects the
  neck alternative (needed to keep "W is a neck ⇒ strong neck" through a cast).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.s16d_rawBody ObservedHistory.s16d_full_iff_rawBody
  ObservedHistory.s16d_rawBody_transfer ObservedHistory.s16d_traceOfRestrict from
  DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainRestrictC12X

universe u

namespace ObservedHistory

/-- **TB⁻¹**：a full neck of `H.restrict b` at `k` is a full neck of `H` at `castLE k`. -/
theorem historyStrongNeckFull_of_restrict_C12X (H : ObservedHistory.{u})
    (b : Icc (0 : ℝ) H.horizon) (k : Fin ((H.restrict b).eventCount + 1)) {s : ℝ}
    (G : ((H.restrict b).stage k).IncomingSlab ((H.restrict b).time k) s) {eps : ℝ}
    {y : ((H.restrict b).stage k).Carrier} {t : ℝ}
    (h : (H.restrict b).HistoryStrongNeckFull_C12X k G eps y t) :
    H.HistoryStrongNeckFull_C12X
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k) G eps y t := by
  obtain ⟨first', hle', hb⟩ := ObservedHistory.s16d_full_iff_rawBody.mp h
  have hO := H.backwardSurvivorDomain_restrict_C12X b first' k hle'
  refine ObservedHistory.s16d_full_iff_rawBody.mpr
    ⟨Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) first',
    Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle'), ?_⟩
  obtain ⟨hts, gflow, htk, hfirst, hslab, hcur, hsol, z, hz, hnk⟩ := hb
  have hidx : ∀ j : Fin H.eventCount,
      j.succ ≤ Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k →
      j.val < (H.restrict b).eventCount := by
    intro j hl
    have h1 : j.val + 1 ≤ k.val := hl
    have h2 := k.isLt
    omega
  have hre : ObservedHistory.s16d_rawBody H.time H.stage H.event
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k) G eps y t
      (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) first')
      ((H.restrict b).backwardSurvivorDomain first' k hle')
      (fun j hj hl => (H.restrict b).backwardSurvivorTerminalMap first' k hle'
        ⟨j.val, hidx j hl⟩ hj hl)
      (fun j hj hl => (H.restrict b).backwardSurvivorTerminalMap_isLocalDiffeomorph first' k hle'
        ⟨j.val, hidx j hl⟩ hj hl) :=
    ⟨hts, gflow, htk, hfirst, fun j hj hl τ hτ => hslab ⟨j.val, hidx j hl⟩ hj hl τ hτ,
      hcur, hsol, z, hz, hnk⟩
  refine ObservedHistory.s16d_rawBody_transfer (times := H.time) (stages := H.stage)
    (evH := H.event) (evK := H.event)
    (k := Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k)
    (fun _ => MetricCutCapEvent.SamePresentation.refl _) hO.symm (fun j hj hl x => ?_) hre
  let A := Classical.choice x.property
  exact ((H.restrict b).backwardSurvivorMap_eq_point first' k hle' _ hj
    ((Fin.castSucc_lt_succ (i := (⟨j.val, hidx j hl⟩ : Fin (H.restrict b).eventCount))).le.trans
      hl) x A).trans
    (H.backwardSurvivorMap_eq_point _ _ _ j.castSucc hj (j.castSucc_lt_succ.le.trans hl)
      ⟨x.val, hO.symm ▸ x.property⟩ (ObservedHistory.s16d_traceOfRestrict H b A)).symm

/-- Incoming-slab agreement clause along TB⁻¹ (any stage, on a window inside its domain). -/
theorem incomingAgree_of_restrict_C12X (H : ObservedHistory.{u}) (b : Icc (0 : ℝ) H.horizon)
    (k : Fin ((H.restrict b).eventCount + 1)) {s : ℝ}
    (G : ((H.restrict b).stage k).IncomingSlab ((H.restrict b).time k) s) {t : ℝ}
    (hdom : ∀ τ ∈ Icc ((H.restrict b).time k) t, τ ∈ (H.restrict b).stageDomain k)
    (hagree : ∀ τ ∈ Icc ((H.restrict b).time k) t,
      G.flow.base.metric τ = (H.restrict b).stageMetric k τ) :
    ∀ τ ∈ Icc (H.time (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k)) t,
      G.flow.base.metric τ =
        H.stageMetric (Fin.castLE (Nat.succ_le_succ (H.s16d_restrict_count_le b)) k) τ := by
  intro τ hτ
  rw [hagree τ hτ]
  exact eq_of_heq (H.restrict_stageMetric b k τ (hdom τ hτ))

/-- Incoming-slab agreement clause along `SamePresentation` (any matched stage). -/
theorem incomingAgree_of_samePresentation_C12X {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) {k : Fin (H.eventCount + 1)} {k' : Fin (K.eventCount + 1)}
    (hk : k.val = k'.val) {s t : ℝ} {G : (H.stage k).IncomingSlab (H.time k) s}
    {G' : (K.stage k').IncomingSlab (K.time k') s} (hG : HEq G G')
    (hdom : ∀ τ ∈ Icc (H.time k) t, τ ∈ H.stageDomain k)
    (hagree : ∀ τ ∈ Icc (H.time k) t, G.flow.base.metric τ = H.stageMetric k τ) :
    ∀ τ ∈ Icc (K.time k') t, G'.flow.base.metric τ = K.stageMetric k' τ := by
  rcases H with ⟨T, hT, n, times, htimes, hzero, hlast, stages, initH, evH, hinitH, houtH,
    finH, hfinH⟩
  rcases K with ⟨T', hT', n', times', htimes', hzero', hlast', stages', initK, evK, hinitK,
    houtK, finK, hfinK⟩
  obtain rfl : n = n' := R.count_eq
  obtain rfl : times = times' := funext fun j => R.time_eq j
  obtain rfl : stages = stages' := funext fun j => R.stage_eq j
  obtain rfl : k = k' := Fin.ext hk
  cases eq_of_heq hG
  intro τ hτ
  rw [hagree τ hτ]
  exact eq_of_heq (R.metric_heq k τ (hdom τ hτ))

end ObservedHistory

/-! ## Casts along stage equalities -/

/-- Cast a point along a stage equality. -/
def s16d_castPoint {P Q : OrientedThreeStage.{u}} (h : P = Q) (x : P.Carrier) : Q.Carrier :=
  h ▸ x

theorem s16d_castPoint_heq {P Q : OrientedThreeStage.{u}} (h : P = Q) (x : P.Carrier) :
    HEq (s16d_castPoint h x) x := by
  cases h
  rfl

/-- Cast an incoming slab along a stage equality and a start-time equality. -/
def s16d_castSlab {P Q : OrientedThreeStage.{u}} {a a' s : ℝ} (hP : P = Q) (ha : a = a')
    (G : P.IncomingSlab a s) : Q.IncomingSlab a' s := by
  subst hP
  subst ha
  exact G

theorem s16d_castSlab_heq {P Q : OrientedThreeStage.{u}} {a a' s : ℝ} (hP : P = Q)
    (ha : a = a') (G : P.IncomingSlab a s) : HEq G (s16d_castSlab hP ha G) := by
  subst hP
  subst ha
  rfl

/-- Scalar curvature agrees along a stage equality with `HEq` metrics and points. -/
theorem s16d_scalar_eq {P Q : OrientedThreeStage.{u}} (h : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y) :
    metricScalarAt g x = metricScalarAt g' y := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

/-- Witness transport along a stage equality; the neck alternative is reflected. -/
theorem s16d_witness_transport {P Q : OrientedThreeStage.{u}} (h : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y)
    {ε C1 C2 : ℝ} (W : SpatialCanonicalWitness g ε C1 C2 x) (hW : W.capTubeHasNeckChart ε) :
    ∃ W' : SpatialCanonicalWitness g' ε C1 C2 y, W'.capTubeHasNeckChart ε ∧
      ∀ nk', W'.alternative = SpatialCanonicalAlternative.neck nk' →
        ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact ⟨W, hW, fun nk hnk => ⟨nk, hnk⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
