import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.LargerBallAccuracyC11RA
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy

set_option autoImplicit false

/-!
# S-CH11-REPROVE-A (G4)：在 join 之后把 δ 钉成常值 `d` 的 records 重选（参数级 + record 级）

reference：`ST/CutoffAccuracyGluing.lean:96 exists_prescribed_accuracy_records_at_join`（连同 private
`affine_future_delta_budget`:52）。astra 版输入 `A : AffineEventPrefix K J …`（在
`SH/CutoffRecordConcatenation`，reference-only，W8 没有），并把 `q` 写死成
`pH.spliceAfter (translate_cutoff_parameters pK …) H.horizon`。
这里的**通用版**把两者都去掉：`J : ObservedHistory` 任意，`q` 任意，join 时刻 `T` 与常值 `d` 任意，
`AffineEventPrefix` 带来的「未来事件的 `q.delta ≤ d`」换成显式 binder `hcut`（astra 的
`affine_future_delta_budget` 正是在 `AffineEventPrefix` 下证明该 binder；那一步属于 record 拼接
（S3 / `CutoffRecordConcatenation`）的适配，不在本组）。

结论与 astra 逐条对应：`p := q.spliceAfter {q with delta := fun _ => d} T` 的 δ antitone、半径不变、
`t ≤ T` 处与 `q` 一致、`t > T` 处 `δ = d`；并且对 `q` 下的任意 records 族（带 canonical window）
重选出 `p` 下的 records 族，六个 record 字段（nominalRadius / delta / order / neck / backward / static）保留，
canonical window 保留。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set

namespace GC.LongTime.Ch11

universe u

/-- 常值 δ 的未来参数：`q` 只把 `delta` 换成常值 `d`（`0 < d < 1`）。 -/
def constDeltaAfter_C11RA (q : CutoffParameters) {d : ℝ} (hd : 0 < d) (hdone : d < 1) :
    CutoffParameters :=
  { q with
    delta := fun _ => d
    delta_pos := fun _ _ => hd
    delta_lt_one := fun _ _ => hdone }

/-- join `T` 之后 δ 钉成 `d` 的参数：`T` 之前是 `q`，之后是 `constDeltaAfter_C11RA`。 -/
def prescribedAccuracy_C11RA (q : CutoffParameters) (T : ℝ) {d : ℝ} (hd : 0 < d)
    (hdone : d < 1) : CutoffParameters :=
  q.spliceAfter (constDeltaAfter_C11RA q hd hdone) T

/-- **G4 主定理**：join `T` 之后把 δ 钉成 `d`（`0 < d < 1`，`d ≤ q.delta T`，未来事件 `q.delta ≤ d`），
参数与 records 同时重选。 -/
theorem exists_prescribed_accuracy_records_C11RA {J : ObservedHistory.{u}} (q : CutoffParameters)
    {T d : ℝ} (hd : 0 < d) (hdone : d < 1)
    (hanti : AntitoneOn q.delta (Icc 0 T)) (hjoin : d ≤ q.delta T)
    (hcut : ∀ i : Fin J.eventCount, T < J.time i.succ → q.delta (J.time i.succ) ≤ d) :
    AntitoneOn (prescribedAccuracy_C11RA q T hd hdone).delta (Ici 0) ∧
      (prescribedAccuracy_C11RA q T hd hdone).neckRadius = q.neckRadius ∧
      (prescribedAccuracy_C11RA q T hd hdone).protectedRadius = q.protectedRadius ∧
      (∀ t : ℝ, t ≤ T → (prescribedAccuracy_C11RA q T hd hdone).delta t = q.delta t ∧
        (prescribedAccuracy_C11RA q T hd hdone).neckRadius t = q.neckRadius t ∧
        (prescribedAccuracy_C11RA q T hd hdone).protectedRadius t = q.protectedRadius t) ∧
      (∀ t : ℝ, T < t → (prescribedAccuracy_C11RA q T hd hdone).delta t = d) ∧
      ∀ R : ∀ i : Fin J.eventCount, GeometricCutoffRecord J i q,
        (∀ i b, ((R i).static b).hasCanonicalWindow) →
        ∃ S : ∀ i : Fin J.eventCount,
            GeometricCutoffRecord J i (prescribedAccuracy_C11RA q T hd hdone),
          (∀ i, (S i).nominalRadius = (R i).nominalRadius ∧ (S i).delta = (R i).delta ∧
            (S i).order = (R i).order ∧ HEq (S i).neck (R i).neck ∧
            HEq (S i).backward (R i).backward ∧ HEq (S i).static (R i).static) ∧
          ∀ i b, ((S i).static b).hasCanonicalWindow := by
  classical
  let future := constDeltaAfter_C11RA q hd hdone
  let p := prescribedAccuracy_C11RA q T hd hdone
  have hneck : p.neckRadius = q.neckRadius := by
    funext t
    simp only [p, prescribedAccuracy_C11RA, constDeltaAfter_C11RA,
      CutoffParameters.spliceAfter, ite_self]
  have hprotected : p.protectedRadius = q.protectedRadius := by
    funext t
    simp only [p, prescribedAccuracy_C11RA, constDeltaAfter_C11RA,
      CutoffParameters.spliceAfter, ite_self]
  refine ⟨spliceAfter_delta_antitone_C11RA q future T hanti
    (fun _ _ _ _ _ => le_rfl) hjoin, hneck, hprotected, ?_, ?_, ?_⟩
  · intro t ht
    exact q.spliceAfter_eval_of_le future ht
  · intro t ht
    exact (q.spliceAfter_eval_of_lt future ht).1
  · intro R hwin
    have hbudget : ∀ i : Fin J.eventCount,
        q.delta (J.time i.succ) ≤ p.delta (J.time i.succ) := by
      intro i
      by_cases hi : J.time i.succ ≤ T
      · exact ((q.spliceAfter_eval_of_le future hi).1).symm.le
      · have hfuture := lt_of_not_ge hi
        have h := (q.spliceAfter_eval_of_lt future hfuture).1
        change q.delta (J.time i.succ) ≤ (q.spliceAfter future T).delta (J.time i.succ)
        rw [h]
        exact hcut i hfuture
    have hnew := fun i => (R i).exists_of_delta_le_of_neckRadius_le (q := p)
      (hbudget i) (congrFun hneck _).symm.le (congrFun hprotected _).symm
      rfl rfl rfl rfl rfl
    choose S hS using hnew
    refine ⟨S, hS, ?_⟩
    intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl rfl rfl rfl rfl
      (R i).static (S i).static (hS i).2.2.2.2.2 (hwin i)

/-- **Consumer（G4）**：显式参数 `quadParameters_C11RA`（`δ = 1/(2(t+1)²)`）在 `T = 1`、`d = 1/8`
处满足主定理的全部几何前提，所以对任意 history 与任意带 canonical window 的 records 族都能把 δ
在 `t > 1` 后钉成 `1/8`。 -/
theorem quadParameters_prescribed_C11RA {J : ObservedHistory.{u}}
    (R : ∀ i : Fin J.eventCount, GeometricCutoffRecord J i quadParameters_C11RA)
    (hwin : ∀ i b, ((R i).static b).hasCanonicalWindow) :
    ∃ p : CutoffParameters, AntitoneOn p.delta (Ici 0) ∧
      (∀ t : ℝ, 1 < t → p.delta t = 1 / 8) ∧ p.neckRadius = quadParameters_C11RA.neckRadius ∧
      ∃ S : ∀ i : Fin J.eventCount, GeometricCutoffRecord J i p,
        (∀ i, HEq (S i).static (R i).static) ∧ ∀ i b, ((S i).static b).hasCanonicalWindow := by
  have hd : (0 : ℝ) < 1 / 8 := by norm_num
  have hdone : (1 / 8 : ℝ) < 1 := by norm_num
  have hanti : AntitoneOn quadParameters_C11RA.delta (Icc 0 1) := fun s hs t ht hst =>
    quadParameters_antitone_C11RA (mem_Ici.2 hs.1) (mem_Ici.2 ht.1) hst
  have hjoin : (1 / 8 : ℝ) ≤ quadParameters_C11RA.delta 1 := by
    change (1 / 8 : ℝ) ≤ 1 / (2 * (1 + 1) ^ 2)
    norm_num
  have hcut : ∀ i : Fin J.eventCount, 1 < J.time i.succ →
      quadParameters_C11RA.delta (J.time i.succ) ≤ 1 / 8 := by
    intro i hi
    have h1 := quadParameters_antitone_C11RA (mem_Ici.2 zero_le_one)
      (mem_Ici.2 (zero_le_one.trans hi.le)) hi.le
    refine h1.trans ?_
    change 1 / (2 * (1 + 1) ^ 2) ≤ (1 / 8 : ℝ)
    norm_num
  obtain ⟨hanti', hneck, -, -, hafter, hrec⟩ :=
    exists_prescribed_accuracy_records_C11RA (J := J) quadParameters_C11RA hd hdone hanti hjoin
      hcut
  obtain ⟨S, hS, hSwin⟩ := hrec R hwin
  exact ⟨_, hanti', hafter, hneck, S, fun i => (hS i).2.2.2.2.2, hSwin⟩

end GC.LongTime.Ch11
