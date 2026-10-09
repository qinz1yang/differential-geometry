import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-!
# S-CH11-FIX7 port of astra `AffineEventDistanceScalar`（`PortC11P`）

来源：donor `AffineEventDistanceScalar.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 3 个 error；本 port 只做 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `AffineEventPrefix.hasUniformDistanceScalar_event` 陈述：行尾 `).` 换行后接字段名在本树
  parse 不过，字段 `HasUniformDistanceScalar` 挪到 `)` 同一行；匿名构造子里的 `by omega`
  面对 `J.toHistory.eventCount`，先 `change _ < J.eventCount`（defeq，omega 只认 `J.eventCount`）。
* `hasUniformDistanceScalar_at_affine_join` 的两处 `simpa only [hji] / [hki] using hcert`：
  目标类型依赖 `i`（stage 参数），simp 不能改写，换成 `rw [hji] at hcert; exact hcert`。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.GeneralFlow

universe u

/-- Equality of the actual terminal opens identifies the chosen point maps:
both are the inclusion of the same retained point into that open. -/
private theorem scalar_data_terminal_transport
    {P Q D M : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D M)
    (U V : TopologicalSpace.Opens P.Carrier) (hUV : U = V)
    (g : SmoothRiemannianMetric ThreeModel U) (output : Q.Metric)
    (i : C((X.retainedCoreOpens : Type u), U))
    (i' : C((X.retainedCoreOpens : Type u), V))
    (hi : ∀ x, (i x).1 = x.1.1) (hi' : ∀ x, (i' x).1 = x.1.1)
    (o : C((X.retainedCoreOpens : Type u), Q.Carrier)) {C : ℝ≥0}
    (h : ∀ (p : U) (N : ℝ≥0), ∃ G : Q.Carrier → ℝ,
      (∀ z : X.retainedCoreOpens, G (o z) =
        (min (riemannianEDistOf g (i z) p) (N : ℝ≥0∞)).toReal) ∧
      ∀ y z, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf output y z) :
    ∀ (p : V) (N : ℝ≥0), ∃ G : Q.Carrier → ℝ,
      (∀ z : X.retainedCoreOpens, G (o z) =
        (min (riemannianEDistOf (hUV ▸ g) (i' z) p) (N : ℝ≥0∞)).toReal) ∧
      ∀ y z, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf output y z := by
  cases hUV
  have hii : i' = i := ContinuousMap.ext fun x => Subtype.ext ((hi' x).trans (hi x).symm)
  rw [hii]
  exact h

/-- Time translation preserves the original terminal metric and output metric.
The chosen terminal-point map is identified using its actual inclusion equation. -/
theorem hasUniformDistanceScalar_translate_retained_event
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {C : ℝ≥0}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    (h : E.toMetricCutCapEvent.HasUniformDistanceScalar C) :
    (translate_retained_event E c).toMetricCutCapEvent.HasUniformDistanceScalar C := by
  exact scalar_data_terminal_transport E.transition E.incoming.terminalRegularOpen
    (E.incoming.timeTranslate c).terminalRegularOpen
    (translated_terminal_open E.incoming c).symm E.terminal.metric E.outputMetric
    E.oldTerminal (translate_retained_event E c).oldTerminal
    E.oldTerminal_eq (translate_retained_event E c).oldTerminal_eq E.oldOutput h

/-- Cast an actual retained event using the stage and clock identifications
carried by its affine presentation. -/
private theorem hasUniformDistanceScalar_of_retained_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ} {C : ℝ≥0}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hE : HEq E' E) (h : E.toMetricCutCapEvent.HasUniformDistanceScalar C) :
    E'.toMetricCutCapEvent.HasUniformDistanceScalar C := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact h

/-- Every actual event of the affine tail keeps the same certificate and
constant; no metric rescaling occurs in a clock translation. -/
theorem AffineEventPrefix.hasUniformDistanceScalar_event
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ} {C : ℝ≥0}
    {n : Fin (K.eventCount + 1)} (A : AffineEventPrefix K J c offset n)
    (i : Fin n.val)
    (h : (K.toHistory.event (i.castLE (Nat.le_of_lt_succ n.isLt))).HasUniformDistanceScalar C) :
    (J.toHistory.event ⟨offset + i.val, by
      have := A.count_eq
      change _ < J.eventCount
      omega⟩).HasUniformDistanceScalar C := by
  exact hasUniformDistanceScalar_of_retained_event_heq
    (A.stage_eq i.castSucc) (A.stage_eq i.succ)
    (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i)
    (hasUniformDistanceScalar_translate_retained_event
      (K.coreEvent (i.castLE (Nat.le_of_lt_succ n.isLt))) c h)

/-- Concrete receiving rule for an actual full join: each event is either an
unchanged old-prefix event or an event of the same selected translated tail. -/
theorem hasUniformDistanceScalar_at_affine_join
    {H K J : RetainedCoreHistory.{u}} {c : ℝ} {C : ℝ≥0}
    (hp : H.toHistory.IsPrefixOf J.toHistory)
    (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
    (hH : ∀ i : Fin H.eventCount, (H.toHistory.event i).HasUniformDistanceScalar C)
    (hK : ∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar C) :
    ∀ i : Fin J.eventCount, (J.toHistory.event i).HasUniformDistanceScalar C := by
  have hcount := A.count_eq
  have hn : H.eventCount ≤ J.eventCount := by omega
  intro i
  by_cases hpast : i.val < H.eventCount
  · let j : Fin H.eventCount := ⟨i.val, hpast⟩
    have hji : j.castLE hn = i := Fin.ext rfl
    have hcert := hp.hasUniformDistanceScalar_event hn j (hH j)
    rw [hji] at hcert
    exact hcert
  · let k : Fin K.eventCount := ⟨i.val - H.eventCount, by have := i.isLt; omega⟩
    have hki : A.eventIndex k = i := by
      apply Fin.ext
      change H.eventCount + (i.val - H.eventCount) = i.val
      omega
    have hcert := A.hasUniformDistanceScalar_event k (hK k)
    change (J.toHistory.event (A.eventIndex k)).HasUniformDistanceScalar C at hcert
    rw [hki] at hcert
    exact hcert

end GC.GeneralFlow
