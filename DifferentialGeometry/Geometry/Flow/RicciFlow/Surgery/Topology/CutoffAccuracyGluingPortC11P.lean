import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy

/-!
O-CH11-FIX3B port（astra `Topology/CutoffAccuracyGluing` 的 elaboration 修补；陈述/证明逐字不变）：
两处 `{ q with … }` 续行字段对齐到首字段列（本树 struct-instance 续行缩进 parse error），每字段一行。
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters

/-- A prefix-compatible diagonal of antitone accuracy bounds is antitone. -/
theorem diagonal_delta_antitone (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ))) :
    AntitoneOn (diagonal p).delta (Ici 0) := by
  intro s hs t ht hst
  change (p (Nat.ceil t)).delta t ≤ (p (Nat.ceil s)).delta s
  rw [hcompat (Nat.ceil s) (Nat.ceil t) (Nat.ceil_mono hst) s ⟨hs, Nat.le_ceil s⟩]
  exact hanti (Nat.ceil t) ⟨hs, hst.trans (Nat.le_ceil t)⟩ ⟨ht, Nat.le_ceil t⟩ hst

/-- Splice accuracy bounds using the actual inequality at the join. -/
theorem spliceAfter_delta_antitone (p q : CutoffParameters) (T : ℝ)
    (hp : AntitoneOn p.delta (Icc 0 T))
    (hq : AntitoneOn q.delta (Ici T))
    (hjoin : q.delta T ≤ p.delta T) :
    AntitoneOn (p.spliceAfter q T).delta (Ici 0) := by
  intro s hs t ht hst
  change (if t ≤ T then p.delta t else q.delta t) ≤
    if s ≤ T then p.delta s else q.delta s
  by_cases hsT : s ≤ T
  · by_cases htT : t ≤ T
    · rw [ite_eq_left htT, ite_eq_left hsT]
      exact hp ⟨hs, hsT⟩ ⟨ht, htT⟩ hst
    · rw [ite_eq_right htT, ite_eq_left hsT]
      have hTt : T ≤ t := (lt_of_not_ge htT).le
      exact (hq (show T ∈ Ici T from le_refl T) hTt hTt).trans
        (hjoin.trans (hp ⟨hs, hsT⟩ ⟨hs.trans hsT, le_rfl⟩ hsT))
  · have hTt : T < t := (lt_of_not_ge hsT).trans_le hst
    rw [ite_eq_right (not_le.mpr hTt), ite_eq_right hsT]
    exact hq (lt_of_not_ge hsT).le hTt.le hst

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem affine_future_delta_budget
    {H K J : RetainedCoreHistory.{u}}
    (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK : CutoffParameters) {d : ℝ}
    (hcut : ∀ i : Fin K.eventCount, pK.delta (K.time i.succ) ≤ d) :
    let q := pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
    ∀ j : Fin J.eventCount, H.horizon < J.time j.succ →
      q.delta (J.time j.succ) ≤ d := by
  dsimp only
  intro j hfuture
  have hcount := A.count_eq
  have hboundary : H.eventCount < J.eventCount + 1 := by omega
  have hzero : J.time ⟨H.eventCount, hboundary⟩ = H.time (Fin.last H.eventCount) := by
    have h := A.time_eq 0
    change J.time ⟨H.eventCount, hboundary⟩ =
      K.time 0 + H.time (Fin.last H.eventCount) at h
    simpa only [K.time_zero, zero_add] using h
  have hj : H.eventCount ≤ j.val := by
    by_contra h
    have hle : j.succ ≤ (⟨H.eventCount, hboundary⟩ : Fin (J.eventCount + 1)) := by
      change j.val + 1 ≤ H.eventCount
      omega
    have hpast := (J.time_strictMono.monotone hle).trans
      (hzero.trans_le H.time_le_horizon)
    exact (not_le_of_gt hfuture) hpast
  let i : Fin K.eventCount := ⟨j.val - H.eventCount, by omega⟩
  have he : A.eventIndex i = j := by
    apply Fin.ext
    change H.eventCount + (j.val - H.eventCount) = j.val
    omega
  have htime : J.time j.succ = K.time i.succ + H.time (Fin.last H.eventCount) := by
    rw [← he]
    exact A.time_eq i.succ
  rw [(pH.spliceAfter_eval_of_lt
    (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) hfuture).1,
    htime]
  exact ((translate_cutoff_parameters_eval pK (H.time (Fin.last H.eventCount))
    (K.time i.succ) (K.toHistory.time_nonneg _)).1).trans_le (hcut i)

/-- Replace only the full joined accuracy bound by the old bound through the
join and a prescribed constant afterward. All six actual record fields and
canonical windows are retained; the native prepared class is unchanged. -/
theorem exists_prescribed_accuracy_records_at_join
    {H K J : RetainedCoreHistory.{u}}
    (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK : CutoffParameters) {d : ℝ} (hd : 0 < d) (hdone : d < 1)
    (hanti : AntitoneOn pH.delta (Icc 0 H.horizon))
    (hjoin : d ≤ pH.delta H.horizon)
    (hcut : ∀ i : Fin K.eventCount, pK.delta (K.time i.succ) ≤ d) :
    let q := pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
    let p := q.spliceAfter { q with delta := fun _ => d,
                                    delta_pos := fun _ _ => hd,
                                    delta_lt_one := fun _ _ => hdone } H.horizon
    AntitoneOn p.delta (Ici 0) ∧ p.neckRadius = q.neckRadius ∧
      p.protectedRadius = q.protectedRadius ∧
      (∀ t : ℝ, t ≤ H.horizon → p.delta t = pH.delta t ∧
        p.neckRadius t = pH.neckRadius t ∧ p.protectedRadius t = pH.protectedRadius t) ∧
      (∀ t : ℝ, H.horizon < t → p.delta t = d) ∧
      ∀ R : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q,
        (∀ i b, ((R i).static b).hasCanonicalWindow) →
        ∃ S : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i p,
          (∀ i, (S i).nominalRadius = (R i).nominalRadius ∧
            (S i).delta = (R i).delta ∧ (S i).order = (R i).order ∧
            HEq (S i).neck (R i).neck ∧ HEq (S i).backward (R i).backward ∧
            HEq (S i).static (R i).static) ∧
          ∀ i b, ((S i).static b).hasCanonicalWindow := by
  classical
  dsimp only
  let q := pH.spliceAfter
    (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
  let future : CutoffParameters := { q with delta := fun _ => d,
                                            delta_pos := fun _ _ => hd,
                                            delta_lt_one := fun _ _ => hdone }
  let p := q.spliceAfter future H.horizon
  have hneck : p.neckRadius = q.neckRadius := by
    funext t
    simp only [p, future, CutoffParameters.spliceAfter, ite_self]
  have hprotected : p.protectedRadius = q.protectedRadius := by
    funext t
    simp only [p, future, CutoffParameters.spliceAfter, ite_self]
  have hpast := fun t (ht : t ≤ H.horizon) =>
    pH.spliceAfter_eval_of_le
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) ht
  have hqanti : AntitoneOn q.delta (Icc 0 H.horizon) := by
    intro s hs t ht hst
    rw [(hpast t ht.2).1, (hpast s hs.2).1]
    exact hanti hs ht hst
  have hboundary : future.delta H.horizon ≤ q.delta H.horizon := by
    rw [(hpast H.horizon le_rfl).1]
    exact hjoin
  refine ⟨q.spliceAfter_delta_antitone future H.horizon hqanti
    (fun _ _ _ _ _ => le_rfl) hboundary, hneck, hprotected, ?_, ?_, ?_⟩
  · intro t ht
    have h := q.spliceAfter_eval_of_le future ht
    exact ⟨h.1.trans (hpast t ht).1, h.2.1.trans (hpast t ht).2.1,
      h.2.2.trans (hpast t ht).2.2⟩
  · intro t ht
    exact (q.spliceAfter_eval_of_lt future ht).1
  · intro R hwin
    have hbudget : ∀ i : Fin J.eventCount,
        q.delta (J.time i.succ) ≤ p.delta (J.time i.succ) := by
      intro i
      by_cases hi : J.time i.succ ≤ H.horizon
      · exact ((q.spliceAfter_eval_of_le future hi).1).symm.le
      · have hfuture := lt_of_not_ge hi
        rw [(q.spliceAfter_eval_of_lt future hfuture).1]
        exact affine_future_delta_budget A pH pK hcut i hfuture
    have hnew := fun i => (R i).exists_of_delta_le_of_neckRadius_le (q := p)
      (hbudget i) (congrFun hneck _).symm.le (congrFun hprotected _).symm
      rfl rfl rfl rfl rfl
    choose S hS using hnew
    refine ⟨S, hS, ?_⟩
    intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl rfl rfl rfl rfl
      (R i).static (S i).static (hS i).2.2.2.2.2 (hwin i)

end GC.GeneralFlow
