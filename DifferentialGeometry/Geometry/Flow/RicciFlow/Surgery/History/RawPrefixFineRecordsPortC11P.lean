import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

/-!
# S-CH11-FIX7 port of astra `RawPrefixFineRecords`（`PortC11P`）

来源：donor `RawPrefixFineRecords.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 3 个 error 外加后续的级联；本 port 只做 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `prefixPullTrace`：`(I.stage_eq last) ▸ y` 与 `(I.stage_eq j) ▸ B.point …` 的期望类型是
  `(H.toHistory.stage last).Carrier`，不含等式两端的 `H.stage last`，`▸` 不识别；
  加类型标注 `( … : (H.stage last).Carrier)` 让 `▸` 看见它（目标类型 defeq，不变）。
* `open scoped … NNReal`：`ℝ≥0` 记号（`prefix_before_of_event_heq` /
  `prefix_incoming_before_iff` 的 `(C : ℝ≥0)`）在本树的 `open` 下被读成 `ℝ ≥ 0`。
* `exists_uniform_expiry_of_original_fine_prefix`：`Finset.mem_univ ⟨i, b⟩` 的匿名构造子
  期望类型未定，写成 `(⟨i, b⟩ : labels)`。
-/

/-! Original fine records under literal initial-history embeddings. The original
stage, event, clock, cap window and finite scale are retained. Supplied traces
can be pulled back; no future continuation or cross-seam analytic bound is
constructed by these structural statements. -/
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff BigOperators NNReal
namespace GC.GeneralFlow
universe u

/-- The structural old-event witness composes on the already chosen histories. -/
def rawPrefix_trans {H J K : RetainedCoreHistory.{u}}
    (I : RawInitialPrefix H J) (I' : RawInitialPrefix J K) : RawInitialPrefix H K where
  count_le := I.count_le.trans I'.count_le
  time_eq j := (I'.time_eq (j.castLE (Nat.succ_le_succ I.count_le))).trans (I.time_eq j)
  stage_eq j := (I'.stage_eq (j.castLE (Nat.succ_le_succ I.count_le))).trans (I.stage_eq j)
  event_heq j := (I'.event_heq (j.castLE I.count_le)).trans (I.event_heq j)

private theorem prefix_cast_point_heq {P Q : OrientedThreeStage.{u}} (h : P = Q)
    (x : P.Carrier) : HEq (h ▸ x) x := by
  cases h
  exact HEq.rfl

private theorem prefix_crossing_iff
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {x : P.Carrier} {y : Q.Carrier} {x' : P'.Carrier} {y' : Q'.Carrier}
    (hx : HEq x x') (hy : HEq y y') :
    E'.toMetricCutCapEvent.RegularCrossing x' y' ↔
      E.toMetricCutCapEvent.RegularCrossing x y := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

/-- Pull back exactly the old part of a supplied trace. Its points and actual
retained crossings are preserved; existence of a future continuation is not claimed. -/
def prefixPullTrace {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {y : (J.stage (last.castLE (Nat.succ_le_succ I.count_le))).Carrier}
    (B : BackwardPointTrace J.toHistory
      (first.castLE (Nat.succ_le_succ I.count_le))
      (last.castLE (Nat.succ_le_succ I.count_le)) hle y) :
    BackwardPointTrace H.toHistory first last hle
      (((I.stage_eq last) ▸ y : (H.stage last).Carrier)) where
  point j hf hl :=
    ((I.stage_eq j) ▸ B.point (j.castLE (Nat.succ_le_succ I.count_le)) hf hl :
      (H.stage j).Carrier)
  endpoint_eq := by
    apply eq_of_heq
    exact (prefix_cast_point_heq _ _).trans
      ((heq_of_eq B.endpoint_eq).trans (prefix_cast_point_heq _ _).symm)
  crossing i hf hl := by
    apply (prefix_crossing_iff (H.coreEvent i) (J.coreEvent (i.castLE I.count_le))
      (I.stage_eq i.castSucc) (I.stage_eq i.succ)
      (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i)
      (prefix_cast_point_heq _ _) (prefix_cast_point_heq _ _)).mp
    exact B.crossing (i.castLE I.count_le) hf hl

theorem prefixPullTrace_point_heq {H J : RetainedCoreHistory.{u}}
    (I : RawInitialPrefix H J) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {y : (J.stage (last.castLE (Nat.succ_le_succ I.count_le))).Carrier}
    (B : BackwardPointTrace J.toHistory
      (first.castLE (Nat.succ_le_succ I.count_le))
      (last.castLE (Nat.succ_le_succ I.count_le)) hle y)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    HEq ((prefixPullTrace I hle B).point j hf hl)
      (B.point (j.castLE (Nat.succ_le_succ I.count_le)) hf hl) :=
  prefix_cast_point_heq _ _

private theorem prefix_label_of_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {p : CutoffParameters}
    (S : ∀ b : E.toMetricCutCapEvent.RetainedBoundaryIndex,
      E.toMetricCutCapEvent.PresentedStaticCap p.fixed p.modelRadius p.modelOrder p.modelAccuracy b)
    (S' : ∀ b : E'.toMetricCutCapEvent.RetainedBoundaryIndex,
      E'.toMetricCutCapEvent.PresentedStaticCap p.fixed p.modelRadius p.modelOrder p.modelAccuracy b)
    (hS : HEq S' S)
    (ell : Nonempty E.transition.trace.tubes.Index → ℝ)
    (ell' : Nonempty E'.transition.trace.tubes.Index → ℝ) (hell : HEq ell' ell)
    (b' : E'.toMetricCutCapEvent.RetainedBoundaryIndex) :
    ∃ b : E.toMetricCutCapEvent.RetainedBoundaryIndex,
      HEq b b' ∧ (∀ z : standardCapWindow p.modelRadius,
        HEq ((S b).window z) ((S' b').window z)) ∧
      (S b).neck.scale = (S' b').neck.scale ∧ ell ⟨b.val.1⟩ = ell' ⟨b'.val.1⟩ := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hS
  cases eq_of_heq hell
  exact ⟨b', HEq.rfl, fun _ => HEq.rfl, rfl, rfl⟩

/-- The transported fine record has the original cap label, complete finite
window, scale and nominal radius. Its parameter may differ from the coarse family. -/
theorem prefix_fine_cap_label {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p)
    (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex) :
    ∃ b : (H.toHistory.event i).RetainedBoundaryIndex,
      HEq b b' ∧ (∀ z : standardCapWindow p.modelRadius,
        HEq ((R.static b).window z) (((I.transportRecord R).static b').window z)) ∧
      (R.static b).neck.scale = ((I.transportRecord R).static b').neck.scale ∧
      R.nominalRadius ⟨b.val.1⟩ = (I.transportRecord R).nominalRadius ⟨b'.val.1⟩ := by
  have hpres := I.transportRecord_preserves R
  exact prefix_label_of_event_heq (H.coreEvent i) (J.coreEvent (i.castLE I.count_le))
    (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i)
    R.static (I.transportRecord R).static hpres.2.2.2.2
    R.nominalRadius (I.transportRecord R).nominalRadius hpres.1 b'

/-- A supplied future trace is restricted at any original prefix stage, then
pulled back with its SAME original cap anchor. The future endpoint is not
identified with a point in the old prefix and no additional survival is inferred. -/
theorem prefix_part_of_fine_cap_trace
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p)
    (k : Fin (H.eventCount + 1)) (hik : i.succ ≤ k)
    (last : Fin (J.eventCount + 1))
    (hklast : k.castLE (Nat.succ_le_succ I.count_le) ≤ last)
    {y : (J.stage last).Carrier}
    (B : BackwardPointTrace J.toHistory (i.castLE I.count_le).succ last
      ((show (i.castLE I.count_le).succ ≤ k.castLE (Nat.succ_le_succ I.count_le) from hik).trans hklast) y)
    (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex)
    (z : standardCapWindow p.modelRadius)
    (hanchor : B.point (i.castLE I.count_le).succ le_rfl ((show (i.castLE I.count_le).succ ≤ k.castLE (Nat.succ_le_succ I.count_le) from hik).trans hklast) =
      ((I.transportRecord R).static b').window z) :
    ∃ (x : (H.stage k).Carrier) (B0 : BackwardPointTrace H.toHistory i.succ k hik x)
      (b : (H.toHistory.event i).RetainedBoundaryIndex),
      HEq x (B.point (k.castLE (Nat.succ_le_succ I.count_le)) hik hklast) ∧
      HEq b b' ∧ B0.point i.succ le_rfl hik = (R.static b).window z ∧
      (∀ j (hf : i.succ ≤ j) (hl : j ≤ k),
        HEq (B0.point j hf hl)
          (B.point (j.castLE (Nat.succ_le_succ I.count_le)) hf ((show j.castLE (Nat.succ_le_succ I.count_le) ≤ k.castLE (Nat.succ_le_succ I.count_le) from hl).trans hklast))) ∧
      (R.static b).neck.scale = ((I.transportRecord R).static b').neck.scale ∧
      R.nominalRadius ⟨b.val.1⟩ = (I.transportRecord R).nominalRadius ⟨b'.val.1⟩ ∧
      ∀ t : ℝ, t - J.time (i.castLE I.count_le).succ = t - H.time i.succ := by
  let Bcut := B.restrictLast hik hklast
  let B0 := prefixPullTrace I hik Bcut
  obtain ⟨b, hb, hwindow, hscale, hell⟩ := prefix_fine_cap_label I R b'
  refine ⟨_, B0, b, prefix_cast_point_heq _ _, hb, ?_, ?_, hscale, hell, ?_⟩
  · apply eq_of_heq
    exact (prefixPullTrace_point_heq I hik Bcut i.succ le_rfl hik).trans
      ((heq_of_eq hanchor).trans (hwindow z).symm)
  · intro j hf hl
    exact prefixPullTrace_point_heq I hik Bcut j hf hl
  · intro t
    rw [show J.time (i.castLE I.count_le).succ = H.time i.succ from I.time_eq i.succ]

private theorem prefix_before_of_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    (C : ℝ≥0) (q T : ℝ) :
    (E'.incoming.DerivativeBoundBefore C q T ↔ E.incoming.DerivativeBoundBefore C q T) ∧
    (E'.incoming.GradientBoundBefore C q T ↔ E.incoming.GradientBoundBefore C q T) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Existing incoming derivative/gradient obligations on every OLD event keep
exactly their coefficient, trigger and time cutoff. This says nothing about
new slabs, the changed final slab, or a later threshold at an old cap. -/
theorem prefix_incoming_before_iff {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount) (C : ℝ≥0) (q T : ℝ) :
    ((J.toHistory.event (i.castLE I.count_le)).incoming.DerivativeBoundBefore C q T ↔
      (H.toHistory.event i).incoming.DerivativeBoundBefore C q T) ∧
    ((J.toHistory.event (i.castLE I.count_le)).incoming.GradientBoundBefore C q T ↔
      (H.toHistory.event i).incoming.GradientBoundBefore C q T) :=
  prefix_before_of_event_heq (H.coreEvent i) (J.coreEvent (i.castLE I.count_le))
    (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i) C q T

/-- One original finite fine family has a single expiry cutoff in EVERY later
raw-prefix presentation. Labels/scales are transported from that original
family, not replaced by the joined coarse records. -/
theorem exists_uniform_expiry_of_original_fine_prefix
    (H : RetainedCoreHistory.{u}) (parameters : Fin H.eventCount → CutoffParameters)
    (records : ∀ i, GeometricCutoffRecord H.toHistory i (parameters i)) (θ : ℝ) :
    ∃ T : ℝ, H.horizon < T ∧ 0 < T ∧
      ∀ (J : RetainedCoreHistory.{u}) (I : RawInitialPrefix H J) (t : ℝ), T ≤ t →
      ∀ (i : Fin H.eventCount)
        (b' : (J.toHistory.event (i.castLE I.count_le)).RetainedBoundaryIndex),
        θ * (((I.transportRecord (records i)).static b').neck.scale)⁻¹ <
          t - J.time (i.castLE I.count_le).succ := by
  classical
  let labels := Σ i : Fin H.eventCount, (H.toHistory.event i).RetainedBoundaryIndex
  let expiry : labels → ℝ := fun a =>
    H.time a.1.succ + θ * ((records a.1).static a.2).neck.scale⁻¹
  let S : ℝ := ∑ a : labels, |expiry a|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let T := 1 + |H.horizon| + S
  refine ⟨T, ?_, ?_, ?_⟩
  · dsimp only [T]
    linarith [le_abs_self H.horizon]
  · dsimp only [T]
    positivity
  · intro J I t ht i b'
    obtain ⟨b, _, _, hscale, _⟩ := prefix_fine_cap_label I (records i) b'
    have he : expiry ⟨i, b⟩ ≤ S := (le_abs_self _).trans
      (Finset.single_le_sum (fun a _ => abs_nonneg (expiry a)) (Finset.mem_univ (⟨i, b⟩ : labels)))
    change H.time i.succ + θ * ((records i).static b).neck.scale⁻¹ ≤ S at he
    rw [← hscale, show J.time (i.castLE I.count_le).succ = H.time i.succ from I.time_eq i.succ]
    dsimp only [T] at ht
    linarith [abs_nonneg H.horizon]

/-- Compose the actual chosen successor embeddings on the same raw surgery. -/
def rawPrefixOfLE {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (step : ∀ n, RawInitialPrefix (F.tower.history n) (F.tower.history (n + 1)))
    (m n : ℕ) (hmn : m ≤ n) : RawInitialPrefix (F.tower.history m) (F.tower.history n) := by
  exact Nat.leRec (motive := fun n _ =>
    RawInitialPrefix (F.tower.history m) (F.tower.history n))
    (RawInitialPrefix.refl _) (fun {_n} _ ih => rawPrefix_trans ih (step _n)) hmn

end GC.GeneralFlow
