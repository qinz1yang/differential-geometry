import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadius

/-!
S-CH11-FIX6 port（astra `Topology/CutoffRecordDelayedRadius` 的 elaboration 修补；陈述 / 定义 / 证明
逐字不变）：`open private affine_future_neckRadius_budget from …CutoffRecordCanonicalRadius` 改指
`…CutoffRecordCanonicalRadiusPortC11P`（FIX7 把 CutoffRecordCanonicalRadius 落成 port + 原路径 shim，
private 定理在 PortC11P 里）。
-/

set_option autoImplicit false
noncomputable section
open Set

namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

open private affine_future_neckRadius_budget from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadiusPortC11P

/-- Delay the full radius decrease until A while retaining the actual joined
records. The supplied q may already have a relabelled accuracy bound: only its
radius must equal the geometric join's radius. All other parameter fields and
all six physical record fields, including the complete static family, survive. -/
theorem exists_delayed_canonical_radius_records_at_join
    {H K J : RetainedCoreHistory.{u}}
    (F : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount))
    (pH pK q : CutoffParameters)
    (hqneck : q.neckRadius = (pH.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon).neckRadius)
    {rOld rNew A : ℝ} (hrNew : 0 < rNew) (hrNewOld : rNew ≤ rOld)
    (hanti : AntitoneOn pH.neckRadius (Ici 0))
    (hflat : ∀ t : ℝ, H.horizon ≤ t → pH.neckRadius t = rOld)
    (hA : H.horizon ≤ A)
    (hcut : ∀ i : Fin K.eventCount, pK.neckRadius (K.time i.succ) ≤ rNew) :
    let oldRadius : CutoffParameters := { q with
      neckRadius := pH.neckRadius, neckRadius_pos := pH.neckRadius_pos }
    let newRadius : CutoffParameters := { q with
      neckRadius := fun _ => rNew, neckRadius_pos := fun _ _ => hrNew }
    let p := oldRadius.spliceAfter newRadius A
    AntitoneOn p.neckRadius (Ici 0) ∧
      p.delta = q.delta ∧ p.protectedRadius = q.protectedRadius ∧
      p.fixed = q.fixed ∧ p.modelRadius = q.modelRadius ∧
      p.modelOrder = q.modelOrder ∧ p.modelAccuracy = q.modelAccuracy ∧
      p.recenterConstant = q.recenterConstant ∧
      (∀ t : ℝ, t ≤ A → p.neckRadius t = pH.neckRadius t) ∧
      (∀ t : ℝ, A < t → p.neckRadius t = rNew) ∧
      (∀ t : ℝ, t ≤ H.horizon → p.delta t = q.delta t ∧
        p.neckRadius t = q.neckRadius t ∧ p.protectedRadius t = q.protectedRadius t) ∧
      (∀ i : Fin J.eventCount,
        q.neckRadius (J.time i.succ) ≤ p.neckRadius (J.time i.succ)) ∧
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
  let oldRadius : CutoffParameters := { q with
    neckRadius := pH.neckRadius, neckRadius_pos := pH.neckRadius_pos }
  let newRadius : CutoffParameters := { q with
    neckRadius := fun _ => rNew, neckRadius_pos := fun _ _ => hrNew }
  let p := oldRadius.spliceAfter newRadius A
  have hdelta : p.delta = q.delta := by
    funext t
    simp only [p, oldRadius, newRadius, CutoffParameters.spliceAfter, ite_self]
  have hprotected : p.protectedRadius = q.protectedRadius := by
    funext t
    simp only [p, oldRadius, newRadius, CutoffParameters.spliceAfter, ite_self]
  have hbefore : ∀ t : ℝ, t ≤ A → p.neckRadius t = pH.neckRadius t := by
    intro t ht
    exact (oldRadius.spliceAfter_eval_of_le newRadius ht).2.1
  have hafter : ∀ t : ℝ, A < t → p.neckRadius t = rNew := by
    intro t ht
    exact (oldRadius.spliceAfter_eval_of_lt newRadius ht).2.1
  have hqbefore : ∀ t : ℝ, t ≤ H.horizon → q.neckRadius t = pH.neckRadius t := by
    intro t ht
    rw [hqneck]
    exact (pH.spliceAfter_eval_of_le
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) ht).2.1
  have hpast : ∀ t : ℝ, t ≤ H.horizon → p.delta t = q.delta t ∧
      p.neckRadius t = q.neckRadius t ∧ p.protectedRadius t = q.protectedRadius t := by
    intro t ht
    exact ⟨congrFun hdelta t, (hbefore t (ht.trans hA)).trans (hqbefore t ht).symm,
      congrFun hprotected t⟩
  have hboundary : newRadius.neckRadius A ≤ oldRadius.neckRadius A := by
    change rNew ≤ pH.neckRadius A
    rw [hflat A hA]
    exact hrNewOld
  have hantitone : AntitoneOn p.neckRadius (Ici 0) :=
    oldRadius.spliceAfter_neckRadius_antitone newRadius A
      (fun _ hs _ ht hst => hanti hs.1 ht.1 hst)
      (fun _ _ _ _ _ => le_rfl) hboundary
  have hfuture : ∀ i : Fin J.eventCount, H.horizon < J.time i.succ →
      q.neckRadius (J.time i.succ) ≤ rNew := by
    intro i hi
    rw [hqneck]
    exact affine_future_neckRadius_budget F pH pK hcut i hi
  have hbudget : ∀ i : Fin J.eventCount,
      q.neckRadius (J.time i.succ) ≤ p.neckRadius (J.time i.succ) := by
    intro i
    by_cases hi : J.time i.succ ≤ H.horizon
    · exact ((hpast _ hi).2.1).symm.le
    · have hHlt := lt_of_not_ge hi
      by_cases htimeA : J.time i.succ ≤ A
      · rw [hbefore _ htimeA, hflat _ hHlt.le]
        exact (hfuture i hHlt).trans hrNewOld
      · rw [hafter _ (lt_of_not_ge htimeA)]
        exact hfuture i hHlt
  refine ⟨hantitone, hdelta, hprotected, rfl, rfl, rfl, rfl, rfl,
    hbefore, hafter, hpast, hbudget, ?_⟩
  intro R hwin
  have hnew := fun i => (R i).exists_of_delta_le_of_neckRadius_le (q := p)
    (congrFun hdelta _).symm.le (hbudget i) (congrFun hprotected _).symm
    rfl rfl rfl rfl rfl
  choose S hS using hnew
  refine ⟨S, hS, ?_⟩
  intro i
  exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
    rfl rfl rfl rfl HEq.rfl rfl rfl rfl rfl
    (R i).static (S i).static (hS i).2.2.2.2.2 (hwin i)

end GC.GeneralFlow
