import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy

/-!
# S-CH11-FIX7 port of astra `CutoffRecordCanonicalRadius`（`PortC11P`）

来源：donor `CutoffRecordCanonicalRadius.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 1 个 parse error（`exists_canonical_radius_records_at_join` 陈述里的
struct-instance 续行）；本 port 只做 elaboration 层面修补（no statement / definition /
proof idea altered）：
* 陈述里 `q.spliceAfter { q with neckRadius := fun _ => ρ,` 换行后接 `neckRadius_pos := …`
  在本树 parse 不过，改成同一个 struct-instance 写在一行；证明里 `let future` 同样改法。
-/

set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- A positive radius chosen after a known analytic threshold and before a
new event can also respect the existing radius at the join. -/
theorem exists_canonical_radius_below {R q : ℝ} (hR : 0 < R) (hq : 0 < q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ q ≤ (ρ ^ 2)⁻¹ := by
  let ρ := min R (Real.sqrt q⁻¹)
  have hρ : 0 < ρ := lt_min hR (Real.sqrt_pos.mpr (inv_pos.mpr hq))
  have hsq : ρ ^ 2 ≤ q⁻¹ := by
    calc
      ρ ^ 2 ≤ (Real.sqrt q⁻¹) ^ 2 :=
        pow_le_pow_left₀ hρ.le (min_le_right _ _) 2
      _ = q⁻¹ := Real.sq_sqrt (inv_pos.mpr hq).le
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  simpa only [inv_inv] using inv_anti₀ (sq_pos_of_pos hρ) hsq

private theorem affine_future_neckRadius_budget
    {H K J : RetainedCoreHistory.{u}}
    (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK : CutoffParameters) {ρ : ℝ}
    (hcut : ∀ i : Fin K.eventCount, pK.neckRadius (K.time i.succ) ≤ ρ) :
    let q := pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
    ∀ j : Fin J.eventCount, H.horizon < J.time j.succ →
      q.neckRadius (J.time j.succ) ≤ ρ := by
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
    (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) hfuture).2.1,
    htime]
  exact ((translate_cutoff_parameters_eval pK (H.time (Fin.last H.eventCount))
    (K.time i.succ) (K.toHistory.time_nonneg _)).2.1).trans_le (hcut i)

/-- Enlarge only the new records' parameter radius to the prospectively chosen
constant. Every old radius value and all six actual geometric data fields are
retained; the joined radius is antitone by the true boundary inequality. -/
theorem exists_canonical_radius_records_at_join
    {H K J : RetainedCoreHistory.{u}}
    (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK : CutoffParameters) {ρ : ℝ} (hρ : 0 < ρ)
    (hanti : AntitoneOn pH.neckRadius (Icc 0 H.horizon))
    (hjoin : ρ ≤ pH.neckRadius H.horizon)
    (hcut : ∀ i : Fin K.eventCount, pK.neckRadius (K.time i.succ) ≤ ρ) :
    let q := pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
    let p := q.spliceAfter
      { q with neckRadius := fun _ => ρ, neckRadius_pos := fun _ _ => hρ } H.horizon
    AntitoneOn p.neckRadius (Ici 0) ∧ p.delta = q.delta ∧
      p.protectedRadius = q.protectedRadius ∧
      (∀ t : ℝ, t ≤ H.horizon → p.delta t = pH.delta t ∧
        p.neckRadius t = pH.neckRadius t ∧ p.protectedRadius t = pH.protectedRadius t) ∧
      (∀ t : ℝ, H.horizon < t → p.neckRadius t = ρ) ∧
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
  let future : CutoffParameters :=
    { q with neckRadius := fun _ => ρ, neckRadius_pos := fun _ _ => hρ }
  let p := q.spliceAfter future H.horizon
  have hδ : p.delta = q.delta := by
    funext t
    simp only [p, future, CutoffParameters.spliceAfter, ite_self]
  have hprotected : p.protectedRadius = q.protectedRadius := by
    funext t
    simp only [p, future, CutoffParameters.spliceAfter, ite_self]
  have hpast := fun t (ht : t ≤ H.horizon) =>
    pH.spliceAfter_eval_of_le
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) ht
  have hqanti : AntitoneOn q.neckRadius (Icc 0 H.horizon) := by
    intro s hs t ht hst
    rw [(hpast t ht.2).2.1, (hpast s hs.2).2.1]
    exact hanti hs ht hst
  have hboundary : future.neckRadius H.horizon ≤ q.neckRadius H.horizon := by
    rw [(hpast H.horizon le_rfl).2.1]
    exact hjoin
  refine ⟨q.spliceAfter_neckRadius_antitone future H.horizon hqanti
    (fun _ _ _ _ _ => le_rfl) hboundary, hδ, hprotected, ?_, ?_, ?_⟩
  · intro t ht
    have h := q.spliceAfter_eval_of_le future ht
    exact ⟨h.1.trans (hpast t ht).1, h.2.1.trans (hpast t ht).2.1,
      h.2.2.trans (hpast t ht).2.2⟩
  · intro t ht
    exact (q.spliceAfter_eval_of_lt future ht).2.1
  · intro R hwin
    have hbudget : ∀ i : Fin J.eventCount,
        q.neckRadius (J.time i.succ) ≤ p.neckRadius (J.time i.succ) := by
      intro i
      by_cases hi : J.time i.succ ≤ H.horizon
      · exact ((q.spliceAfter_eval_of_le future hi).2.1).symm.le
      · have hfuture := lt_of_not_ge hi
        rw [(q.spliceAfter_eval_of_lt future hfuture).2.1]
        exact affine_future_neckRadius_budget A pH pK hcut i hfuture
    have hnew := fun i => (R i).exists_of_delta_le_of_neckRadius_le (q := p)
      (congrFun hδ _).symm.le (hbudget i) (congrFun hprotected _).symm
      rfl rfl rfl rfl rfl
    choose S hS using hnew
    refine ⟨S, hS, ?_⟩
    intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl rfl rfl rfl rfl
      (R i).static (S i).static (hS i).2.2.2.2.2 (hwin i)

end GC.GeneralFlow
