import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.FiniteChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.IntervalLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Joining
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Analysis.Integration.Integral.Comparison
import DifferentialGeometry.Topology.Order.InfimumAddition
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def stageEndTime (j : Fin (H.eventCount + 1)) : ℝ :=
  Fin.lastCases H.horizon (fun i => H.time i.succ) j

def regularizedStageStart (T u : ℝ) (j : Fin (H.eventCount + 1)) : ℝ :=
  Real.sqrt (T - min (T - u ^ 2) (H.stageEndTime j))

def regularizedStageEnd (T v : ℝ) (j : Fin (H.eventCount + 1)) : ℝ :=
  Real.sqrt (T - max (T - v ^ 2) (H.time j))

abbrev StageInterval (first last : Fin (H.eventCount + 1)) :=
  {j : Fin (H.eventCount + 1) // first ≤ j ∧ j ≤ last}

@[simp] theorem stageEndTime_castSucc (i : Fin H.eventCount) :
    H.stageEndTime i.castSucc = H.time i.succ := by
  simp only [stageEndTime, Fin.lastCases_castSucc]

@[simp] theorem stageEndTime_last : H.stageEndTime (Fin.last H.eventCount) = H.horizon := by
  simp only [stageEndTime, Fin.lastCases_last]

theorem time_le_stageEndTime (j : Fin (H.eventCount + 1)) : H.time j ≤ H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => simpa only [H.stageEndTime_last] using H.time_le_horizon
  | cast i => simpa only [H.stageEndTime_castSucc] using (H.time_strictMono i.castSucc_lt_succ).le

theorem stageEndTime_le_horizon (j : Fin (H.eventCount + 1)) : H.stageEndTime j ≤ H.horizon := by
  cases j using Fin.lastCases with
  | last => simp only [H.stageEndTime_last, le_refl]
  | cast i => simpa only [H.stageEndTime_castSucc] using H.time_le_horizon_at i.succ

theorem stageEndTime_mono : Monotone H.stageEndTime := by
  intro i j hij
  cases j using Fin.lastCases with
  | last => simpa only [H.stageEndTime_last] using H.stageEndTime_le_horizon i
  | cast j =>
    have hi : i.val < H.eventCount := lt_of_le_of_lt hij j.isLt
    let k : Fin H.eventCount := ⟨i.val, hi⟩
    have hik : i = k.castSucc := Fin.ext rfl
    rw [hik, H.stageEndTime_castSucc, H.stageEndTime_castSucc]
    apply H.time_strictMono.monotone
    change k.val + 1 ≤ j.val + 1
    simpa only [hik, Fin.val_castSucc] using Nat.add_le_add_right (show i.val ≤ j.val from hij) 1

theorem time_le_of_mem_stageDomain {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) : H.time j ≤ t := by
  cases j using Fin.lastCases with
  | last =>
    simp only [stageDomain, Fin.lastCases_last, mem_Icc] at ht
    exact ht.1
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    exact ht.1

theorem le_stageEndTime_of_mem_stageDomain {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) : t ≤ H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [stageDomain, Fin.lastCases_last, mem_Icc] at ht
    simpa only [H.stageEndTime_last] using ht.2
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    simpa only [H.stageEndTime_castSucc] using ht.2.le

theorem mem_stageDomain_of_mem_Ioo {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ Ioo (H.time j) (H.stageEndTime j)) : t ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [H.stageEndTime_last, mem_Ioo] at ht
    simpa only [stageDomain, Fin.lastCases_last, mem_Icc] using And.intro ht.1.le ht.2.le
  | cast i =>
    simp only [H.stageEndTime_castSucc, mem_Ioo] at ht
    simpa only [stageDomain, Fin.lastCases_castSucc, mem_Ico] using And.intro ht.1.le ht.2

theorem regularizedStageStart_eq_of_mem_Icc {last : Fin (H.eventCount + 1)} {T u : ℝ}
    (hu : 0 ≤ u) (hT : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last)) : H.regularizedStageStart T u last = u := by
  rw [regularizedStageStart, min_eq_left (hT.2),
    sub_sub_cancel, Real.sqrt_sq hu]

theorem regularizedStageEnd_eq_of_mem_stageDomain {first : Fin (H.eventCount + 1)} {T v : ℝ}
    (hv : 0 ≤ v) (hpast : T - v ^ 2 ∈ H.stageDomain first) : H.regularizedStageEnd T v first = v := by
  rw [regularizedStageEnd, max_eq_left (H.time_le_of_mem_stageDomain hpast), sub_sub_cancel, Real.sqrt_sq hv]

theorem regularizedStage_bounds
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hT : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last)) (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (j : H.StageInterval first last) :
    u ≤ H.regularizedStageStart T u j.val ∧
      H.regularizedStageStart T u j.val ≤ H.regularizedStageEnd T v j.val ∧
      H.regularizedStageEnd T v j.val ≤ v := by
  have huv2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
  have hjT : H.time j.val ≤ T - u ^ 2 :=
    (H.time_strictMono.monotone j.property.2).trans (hT.1)
  have hpj : T - v ^ 2 ≤ H.stageEndTime j.val :=
    (H.le_stageEndTime_of_mem_stageDomain hpast).trans (H.stageEndTime_mono j.property.1)
  have hmax : max (T - v ^ 2) (H.time j.val) ≤ min (T - u ^ 2) (H.stageEndTime j.val) := by
    apply max_le
    · exact le_min (sub_le_sub_left huv2 T) hpj
    · exact le_min hjT (H.time_le_stageEndTime j.val)
  refine ⟨?_, Real.sqrt_le_sqrt (sub_le_sub_left hmax T), ?_⟩
  · have hh : u ^ 2 ≤ T - min (T - u ^ 2) (H.stageEndTime j.val) := by
      have hm := min_le_left (T - u ^ 2) (H.stageEndTime j.val)
      linarith
    exact (Real.sqrt_sq hu).symm.trans_le (Real.sqrt_le_sqrt hh)
  · have hh : T - max (T - v ^ 2) (H.time j.val) ≤ v ^ 2 := by
      have hm := le_max_left (T - v ^ 2) (H.time j.val)
      linarith
    exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq (hu.trans huv))

theorem mapsTo_regularizedStage_Ioo (T u v : ℝ) (j : Fin (H.eventCount + 1)) :
    MapsTo (fun t : ℝ => T - t ^ 2)
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
      (H.stageDomain j) := by
  intro t ht
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht.1.le
  have hlo : T - min (T - u ^ 2) (H.stageEndTime j) < t ^ 2 := by
    have hnn : 0 ≤ T - min (T - u ^ 2) (H.stageEndTime j) := by
      have hh := min_le_left (T - u ^ 2) (H.stageEndTime j)
      linarith [sq_nonneg u]
    exact (Real.sqrt_lt hnn ht0).mp ht.1
  have hhi : t ^ 2 < T - max (T - v ^ 2) (H.time j) := (Real.lt_sqrt ht0).mp ht.2
  apply H.mem_stageDomain_of_mem_Ioo
  constructor
  · have hjmax := le_max_right (T - v ^ 2) (H.time j)
    linarith
  · have hminend := min_le_right (T - u ^ 2) (H.stageEndTime j)
    linarith

theorem regularizedStageStart_castSucc_eq_event_clock
    {last : Fin (H.eventCount + 1)} {T u : ℝ}
    (hT : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last)) (i : Fin H.eventCount) (hl : i.succ ≤ last) :
    H.regularizedStageStart T u i.castSucc = Real.sqrt (T - H.time i.succ) := by
  have hiT := (H.time_strictMono.monotone hl).trans (hT.1)
  simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hiT]

theorem regularizedStageEnd_succ_eq_event_clock
    {first : Fin (H.eventCount + 1)} {T v : ℝ}
    (hpast : T - v ^ 2 ∈ H.stageDomain first) (i : Fin H.eventCount) (hf : first ≤ i.castSucc) :
    H.regularizedStageEnd T v i.succ = Real.sqrt (T - H.time i.succ) := by
  have hpi : T - v ^ 2 ≤ H.time i.succ := by
    have hh := (H.le_stageEndTime_of_mem_stageDomain hpast).trans (H.stageEndTime_mono hf)
    simpa only [H.stageEndTime_castSucc] using hh
  simp only [regularizedStageEnd, max_eq_right hpi]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def stageRegularizedLagrangian (j : Fin (H.eventCount + 1)) (T : ℝ)
    (α : ℝ → (H.stage j).Carrier) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (H.stageMetric j (T - t ^ 2)).inner (α t) (lVelocity α t) (lVelocity α t) +
    2 * t ^ 2 * metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)

def stageRegularizedAction (j : Fin (H.eventCount + 1)) (T : ℝ)
    (α : ℝ → (H.stage j).Carrier) (a b : ℝ) : ℝ :=
  ∫ t in a..b, H.stageRegularizedLagrangian j T α t

def regularizedC1ActionValues (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : Set ℝ :=
  {A | 0 ≤ u ∧ u ≤ v ∧ T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧ T - v ^ 2 ∈ H.stageDomain first ∧
    ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      α ⟨last, hle, le_rfl⟩ u = p ∧ α ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) = A}

def regularizedC1Cost (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : WithTop ℝ :=
  sInf ((fun A : ℝ => (A : WithTop ℝ)) '' H.regularizedC1ActionValues first last hle T u v p q)

theorem regularizedC1Cost_eq_top_of_no_competitor
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (h : H.regularizedC1ActionValues first last hle T u v p q = ∅) :
    H.regularizedC1Cost first last hle T u v p q = ⊤ := by
  rw [regularizedC1Cost, h, image_empty, WithTop.sInf_empty]

theorem stageRegularizedLagrangian_castSucc (i : Fin H.eventCount) (T : ℝ)
    (α : ℝ → (H.stage i.castSucc).Carrier) (t : ℝ) :
    H.stageRegularizedLagrangian i.castSucc T α t = lRegularizedLagrangian (H.event i).incoming.flow T α t := by
  simp only [stageRegularizedLagrangian, stageMetric, Fin.lastCases_castSucc]
  rfl

theorem stageRegularizedAction_castSucc (i : Fin H.eventCount) (T : ℝ)
    (α : ℝ → (H.stage i.castSucc).Carrier) (a b : ℝ) :
    H.stageRegularizedAction i.castSucc T α a b = lRegularizedAction (H.event i).incoming.flow T α a b := by
  unfold stageRegularizedAction lRegularizedAction
  apply intervalIntegral.integral_congr
  intro t _
  exact H.stageRegularizedLagrangian_castSucc i T α t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageRegularizedLagrangian_last (h : H.time (Fin.last H.eventCount) < H.horizon)
    (T : ℝ) (α : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ) :
    H.stageRegularizedLagrangian (Fin.last H.eventCount) T α t =
      lRegularizedLagrangian (H.finalSlab h).flow T α t := by
  simp only [stageRegularizedLagrangian, stageMetric, Fin.lastCases_last, dif_pos h]
  rfl

theorem stageRegularizedAction_last (h : H.time (Fin.last H.eventCount) < H.horizon)
    (T : ℝ) (α : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) (a b : ℝ) :
    H.stageRegularizedAction (Fin.last H.eventCount) T α a b =
      lRegularizedAction (H.finalSlab h).flow T α a b := by
  unfold stageRegularizedAction lRegularizedAction
  apply intervalIntegral.integral_congr
  intro t _
  exact H.stageRegularizedLagrangian_last h T α t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v

variable (H : ObservedHistory.{u})

private theorem sum_stageInterval_split {A : Type v} [AddCommMonoid A]
    {first last : Fin (H.eventCount + 1)} (i : Fin H.eventCount)
    (hf : first ≤ i.succ) (hl : i.castSucc ≤ last)
    (F : H.StageInterval first last → A) :
    ∑ j : H.StageInterval first last, F j =
      (∑ j : H.StageInterval first i.castSucc,
        F ⟨j.val, j.property.1, j.property.2.trans hl⟩) +
      ∑ j : H.StageInterval i.succ last,
        F ⟨j.val, hf.trans j.property.1, j.property.2⟩ := by
  let e₁ : {j : H.StageInterval first last // j.val ≤ i.castSucc} ≃
      H.StageInterval first i.castSucc :=
    { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
      invFun := fun j =>
        ⟨⟨j.val, j.property.1, j.property.2.trans hl⟩, j.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {j : H.StageInterval first last // ¬ j.val ≤ i.castSucc} ≃
      H.StageInterval i.succ last :=
    { toFun := fun j => ⟨j.val.val, by
          have hj := j.property
          change i.val + 1 ≤ j.val.val.val
          change ¬ j.val.val.val ≤ i.val at hj
          omega, j.val.property.2⟩
      invFun := fun j =>
        ⟨⟨j.val, hf.trans j.property.1, j.property.2⟩, by
          have hj := j.property.1
          change i.val + 1 ≤ j.val.val at hj
          change ¬ j.val.val ≤ i.val
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h₁ := Fintype.sum_equiv e₁ (fun j => F j.val)
    (fun j => F ⟨j.val, j.property.1, j.property.2.trans hl⟩)
    (fun _ => rfl)
  have h₂ := Fintype.sum_equiv e₂ (fun j => F j.val)
    (fun j => F ⟨j.val, hf.trans j.property.1, j.property.2⟩)
    (fun _ => rfl)
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last =>
    j.val ≤ i.castSucc) F, h₁, h₂]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private instance stageInterval_self_subsingleton (j : Fin (H.eventCount + 1)) :
    Subsingleton (H.StageInterval j j) :=
  ⟨fun a b => Subtype.ext ((le_antisymm a.property.2 a.property.1).trans (le_antisymm b.property.2 b.property.1).symm)⟩

private theorem sum_stageInterval_self (j : Fin (H.eventCount + 1))
    (f : H.StageInterval j j → ℝ) : ∑ k, f k = f ⟨j, le_rfl, le_rfl⟩ := by
  classical
  exact Fintype.sum_eq_single (f := f) (⟨j, le_rfl, le_rfl⟩ : H.StageInterval j j) (by
    intro k hne
    exact False.elim (hne (Subsingleton.elim _ _)))


theorem mem_regularizedC1ActionValues_self
    (j : Fin (H.eventCount + 1)) {T u v A : ℝ} (p q : (H.stage j).Carrier) :
    A ∈ H.regularizedC1ActionValues j j le_rfl T u v p q ↔
      0 ≤ u ∧ u ≤ v ∧ T - u ^ 2 ∈ Icc (H.time j) (H.stageEndTime j) ∧ T - v ^ 2 ∈ H.stageDomain j ∧
      ∃ α : ℝ → (H.stage j).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α ∧
        IntervalIntegrable (H.stageRegularizedLagrangian j T α) volume u v ∧
        α u = p ∧ α v = q ∧ H.stageRegularizedAction j T α u v = A := by
  constructor
  · rintro ⟨hu, huv, hT, hpast, α, hα, hi, hzero, hend, _, hsum⟩
    let k : H.StageInterval j j := ⟨j, le_rfl, le_rfl⟩
    have hs := H.regularizedStageStart_eq_of_mem_Icc hu hT
    have he := H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast
    refine ⟨hu, huv, hT, hpast, α k, hα k, ?_, hzero, hend, ?_⟩
    · simpa only [k, hs, he] using hi k
    · rw [sum_stageInterval_self H j] at hsum
      simpa only [k, hs, he] using hsum
  · rintro ⟨hu, huv, hT, hpast, α, hα, hi, hzero, hend, hact⟩
    have hj (k : H.StageInterval j j) : k.val = j := le_antisymm k.property.2 k.property.1
    let β : (k : H.StageInterval j j) → ℝ → (H.stage k.val).Carrier :=
      fun k => (hj k).symm ▸ α
    have hβ : β ⟨j, le_rfl, le_rfl⟩ = α := rfl
    have hs := H.regularizedStageStart_eq_of_mem_Icc hu hT
    have he := H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast
    refine ⟨hu, huv, hT, hpast, β, ?_, ?_, hzero, hend, ?_, ?_⟩
    · intro k
      obtain rfl : k = ⟨j, le_rfl, le_rfl⟩ := Subsingleton.elim _ _
      exact hα
    · intro k
      obtain rfl : k = ⟨j, le_rfl, le_rfl⟩ := Subsingleton.elim _ _
      simpa only [hβ, hs, he] using hi
    · intro i hji hij
      exact False.elim ((not_lt_of_ge (hij.trans hji)) i.castSucc_lt_succ)
    · rw [sum_stageInterval_self H j]
      simpa only [hβ, hs, he] using hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem time_mem_stageDomain (j : Fin (H.eventCount + 1)) : H.time j ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    simpa only [stageDomain, Fin.lastCases_last, mem_Icc] using And.intro le_rfl H.time_le_horizon
  | cast i =>
    simpa only [stageDomain, Fin.lastCases_castSucc, mem_Ico] using
      And.intro le_rfl (H.time_strictMono i.castSucc_lt_succ)

theorem event_clock_bounds
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    u ≤ Real.sqrt (T - H.time i.succ) ∧ Real.sqrt (T - H.time i.succ) ≤ v ∧
      T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
  have hevent : H.time i.succ ≤ T - u ^ 2 := (H.time_strictMono.monotone hl).trans hupper.1
  have hpast : T - v ^ 2 ≤ H.time i.succ := by
    have h := (H.le_stageEndTime_of_mem_stageDomain hlower).trans (H.stageEndTime_mono hf)
    simpa only [H.stageEndTime_castSucc] using h
  have hnonneg : 0 ≤ T - H.time i.succ := by linarith [sq_nonneg u]
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.sqrt_sq hu).symm.trans_le (Real.sqrt_le_sqrt (by linarith))
  · exact (Real.sqrt_le_sqrt (by linarith : T - H.time i.succ ≤ v ^ 2)).trans_eq
      (Real.sqrt_sq (hu.trans huv))
  · rw [Real.sq_sqrt hnonneg]
    ring

theorem regularizedStageStart_eq_at_event_clock
    {last : Fin (H.eventCount + 1)} {T u : ℝ}
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (i : Fin H.eventCount) (hl : i.succ ≤ last) (j : Fin (H.eventCount + 1)) (hj : j ≤ i.castSucc) :
    H.regularizedStageStart T (Real.sqrt (T - H.time i.succ)) j = H.regularizedStageStart T u j := by
  have hevent : H.time i.succ ≤ T - u ^ 2 := (H.time_strictMono.monotone hl).trans hupper.1
  have hnonneg : 0 ≤ T - H.time i.succ := by linarith [sq_nonneg u]
  have hjend : H.stageEndTime j ≤ H.time i.succ := by
    simpa only [H.stageEndTime_castSucc] using H.stageEndTime_mono hj
  have hclock : T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt hnonneg]
    ring
  simp only [regularizedStageStart, hclock, min_eq_right hjend, min_eq_right (hjend.trans hevent)]

theorem regularizedStageEnd_eq_at_event_clock
    {first : Fin (H.eventCount + 1)} {T v : ℝ}
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
    (hiT : H.time i.succ ≤ T) (j : Fin (H.eventCount + 1)) (hj : i.succ ≤ j) :
    H.regularizedStageEnd T (Real.sqrt (T - H.time i.succ)) j = H.regularizedStageEnd T v j := by
  have hpast : T - v ^ 2 ≤ H.time i.succ := by
    have h := (H.le_stageEndTime_of_mem_stageDomain hlower).trans (H.stageEndTime_mono hf)
    simpa only [H.stageEndTime_castSucc] using h
  have hjtime : H.time i.succ ≤ H.time j := H.time_strictMono.monotone hj
  have hclock : T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hiT)]
    ring
  simp only [regularizedStageEnd, hclock, max_eq_right hjtime, max_eq_right (hpast.trans hjtime)]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private theorem split_values_forward
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T u v A : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q) :
    ∃ z : (H.event i).old, ∃ Aold Anew : ℝ,
      Aold ∈ H.regularizedC1ActionValues first i.castSucc hf T
        (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
      Anew ∈ H.regularizedC1ActionValues i.succ last hl T
        u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
      Aold + Anew = A := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  have hw := H.event_clock_bounds hu huv hupper hlower i hf hl
  have hw0 : 0 ≤ w := hu.trans hw.1
  have hiT : H.time i.succ ≤ T := by
    have hh := (H.time_strictMono.monotone hl).trans hupper.1
    linarith [sq_nonneg u]
  have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hw.2.2, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hvNew : T - w ^ 2 ∈ H.stageDomain i.succ := by
    rw [hw.2.2]
    exact H.time_mem_stageDomain i.succ
  let lo : H.StageInterval first i.castSucc → H.StageInterval first last :=
    fun j => ⟨j.val, j.property.1, j.property.2.trans (i.castSucc_le_succ.trans hl)⟩
  let hi : H.StageInterval i.succ last → H.StageInterval first last :=
    fun j => ⟨j.val, hf.trans (i.castSucc_le_succ.trans j.property.1), j.property.2⟩
  have hstart (j : H.StageInterval first i.castSucc) :
      H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
    H.regularizedStageStart_eq_at_event_clock hupper i hl j.val j.property.2
  have hend (j : H.StageInterval i.succ last) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val :=
    H.regularizedStageEnd_eq_at_event_clock hlower i hf hiT j.val j.property.1
  rcases hA with ⟨_, _, _, _, α, hα, hint, hp, hq, hnodes, hsum⟩
  obtain ⟨z, hzold, hznew⟩ := hnodes i hf hl
  let αold : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier := fun j => α (lo j)
  let αnew : (j : H.StageInterval i.succ last) → ℝ → (H.stage j.val).Carrier := fun j => α (hi j)
  let Aold := ∑ j : H.StageInterval first i.castSucc, H.stageRegularizedAction j.val T (αold j)
    (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)
  let Anew := ∑ j : H.StageInterval i.succ last, H.stageRegularizedAction j.val T (αnew j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
  refine ⟨z, Aold, Anew, ?_, ?_, ?_⟩
  · refine ⟨hw0, hw.2.1, huOld, hlower, αold, (fun j => hα (lo j)), ?_, hzold.symm, hq, ?_, rfl⟩
    · intro j
      change IntervalIntegrable (H.stageRegularizedLagrangian j.val T (αold j)) volume
        (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)
      rw [hstart j]
      exact hint (lo j)
    · intro k hfk hki
      exact hnodes k hfk (hki.trans (i.castSucc_le_succ.trans hl))
  · refine ⟨hu, hw.1, hupper, hvNew, αnew, (fun j => hα (hi j)), ?_, hp, hznew.symm, ?_, rfl⟩
    · intro j
      change IntervalIntegrable (H.stageRegularizedLagrangian j.val T (αnew j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
      rw [hend j]
      exact hint (hi j)
    · intro k hik hkl
      exact hnodes k (hf.trans (i.castSucc_le_succ.trans hik)) hkl
  · have hsplit := H.sum_stageInterval_split i (hf.trans i.castSucc_le_succ)
      (i.castSucc_le_succ.trans hl) (fun j => H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    rw [hsum] at hsplit
    rw [hsplit]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j _
      simp only [αold, lo, hstart j]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [αnew, hi, hend j]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem split_values_backward
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T u v A : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hsplit : ∃ z : (H.event i).old, ∃ Aold Anew : ℝ,
      Aold ∈ H.regularizedC1ActionValues first i.castSucc hf T
        (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
      Anew ∈ H.regularizedC1ActionValues i.succ last hl T
        u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
      Aold + Anew = A) :
    A ∈ H.regularizedC1ActionValues first last hle T u v p q := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  have hw := H.event_clock_bounds hu huv hupper hlower i hf hl
  have hw0 : 0 ≤ w := hu.trans hw.1
  have hiT : H.time i.succ ≤ T := by
    have hh := (H.time_strictMono.monotone hl).trans hupper.1
    linarith [sq_nonneg u]
  have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hw.2.2, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hvNew : T - w ^ 2 ∈ H.stageDomain i.succ := by
    rw [hw.2.2]
    exact H.time_mem_stageDomain i.succ
  let lo : H.StageInterval first i.castSucc → H.StageInterval first last :=
    fun j => ⟨j.val, j.property.1, j.property.2.trans (i.castSucc_le_succ.trans hl)⟩
  let hi : H.StageInterval i.succ last → H.StageInterval first last :=
    fun j => ⟨j.val, hf.trans (i.castSucc_le_succ.trans j.property.1), j.property.2⟩
  have hstart (j : H.StageInterval first i.castSucc) :
      H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
    H.regularizedStageStart_eq_at_event_clock hupper i hl j.val j.property.2
  have hend (j : H.StageInterval i.succ last) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val :=
    H.regularizedStageEnd_eq_at_event_clock hlower i hf hiT j.val j.property.1
  rcases hsplit with ⟨z, Aold, Anew, hOld, hNew, hsum⟩
  rcases hOld with ⟨_, _, _, _, αold, hold, hiold, hpold, hqold, hnold, hsumold⟩
  rcases hNew with ⟨_, _, _, _, αnew, hnew, hinew, hpnew, hqnew, hnnew, hsumnew⟩
  let α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun j => if hji : j.val ≤ i.castSucc then αold ⟨j.val, j.property.1, hji⟩
      else αnew ⟨j.val, by
        change i.val + 1 ≤ j.val.val
        change ¬ j.val.val ≤ i.val at hji
        omega, j.property.2⟩
  have hlo (j : H.StageInterval first i.castSucc) : α (lo j) = αold j := by
    simp only [α, lo, dif_pos j.property.2]
  have hhi (j : H.StageInterval i.succ last) : α (hi j) = αnew j := by
    have hn : ¬ j.val ≤ i.castSucc := not_le_of_gt (i.castSucc_lt_succ.trans_le j.property.1)
    simp only [α, hi, dif_neg hn]
  have hold_eq (j : H.StageInterval first last) (hj : j.val ≤ i.castSucc) :
      α j = αold ⟨j.val, j.property.1, hj⟩ := by simp only [α, dif_pos hj]
  have hnew_eq (j : H.StageInterval first last) (hj : i.succ ≤ j.val) :
      α j = αnew ⟨j.val, hj, j.property.2⟩ := by
    simp only [α, dif_neg (not_le_of_gt (i.castSucc_lt_succ.trans_le hj))]
  refine ⟨hu, huv, hupper, hlower, α, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val ≤ i.castSucc
    · rw [hold_eq j hj]
      exact hold ⟨j.val, j.property.1, hj⟩
    · have hj' : i.succ ≤ j.val := by
        change i.val + 1 ≤ j.val.val
        change ¬ j.val.val ≤ i.val at hj
        omega
      rw [hnew_eq j hj']
      exact hnew ⟨j.val, hj', j.property.2⟩
  · intro j
    by_cases hj : j.val ≤ i.castSucc
    · rw [hold_eq j hj, ← hstart ⟨j.val, j.property.1, hj⟩]
      exact hiold ⟨j.val, j.property.1, hj⟩
    · have hj' : i.succ ≤ j.val := by
        change i.val + 1 ≤ j.val.val
        change ¬ j.val.val ≤ i.val at hj
        omega
      rw [hnew_eq j hj', ← hend ⟨j.val, hj', j.property.2⟩]
      exact hinew ⟨j.val, hj', j.property.2⟩
  · rw [hnew_eq ⟨last, hle, le_rfl⟩ hl]
    exact hpnew
  · rw [hold_eq ⟨first, le_rfl, hle⟩ hf]
    exact hqold
  · intro k hfk hkl
    rcases lt_trichotomy k i with hki | rfl | hik
    · have hks : k.succ ≤ i.castSucc := by
        change k.val + 1 ≤ i.val
        change k.val < i.val at hki
        omega
      obtain ⟨z', hz', hz''⟩ := hnold k hfk hks
      refine ⟨z', ?_, ?_⟩
      · rw [hold_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ (k.castSucc_le_succ.trans hks)]
        exact hz'
      · rw [hold_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ hks]
        exact hz''
    · refine ⟨z, ?_, ?_⟩
      · rw [hold_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ le_rfl]
        exact hpold.symm
      · rw [hnew_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ le_rfl]
        exact hqnew.symm
    · have his : i.succ ≤ k.castSucc := by
        change i.val + 1 ≤ k.val
        change i.val < k.val at hik
        omega
      obtain ⟨z', hz', hz''⟩ := hnnew k his hkl
      refine ⟨z', ?_, ?_⟩
      · rw [hnew_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ his]
        exact hz'
      · rw [hnew_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ (his.trans k.castSucc_le_succ)]
        exact hz''
  · rw [H.sum_stageInterval_split i (hf.trans i.castSucc_le_succ) (i.castSucc_le_succ.trans hl)]
    rw [← hsum]
    apply congrArg₂ (· + ·)
    · convert hsumold using 1
      apply Finset.sum_congr rfl
      intro j _
      change H.stageRegularizedAction j.val T (α (lo j)) _ _ = _
      rw [hlo j, hstart j]
    · convert hsumnew using 1
      apply Finset.sum_congr rfl
      intro j _
      change H.stageRegularizedAction j.val T (α (hi j)) _ _ = _
      rw [hhi j, hend j]

theorem mem_regularizedC1ActionValues_split_at_event
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T u v A : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    A ∈ H.regularizedC1ActionValues first last hle T u v p q ↔
      ∃ z : (H.event i).old, ∃ Aold Anew : ℝ,
        Aold ∈ H.regularizedC1ActionValues first i.castSucc hf T
          (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
        Anew ∈ H.regularizedC1ActionValues i.succ last hl T
          u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
        Aold + Anew = A := by
  exact ⟨split_values_forward H hle i hf hl hu huv hupper hlower p q,
    split_values_backward H hle i hf hl hu huv hupper hlower p q⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageRegularizedAction_ge_of_scalar_lower_bound
    (j : Fin (H.eventCount + 1)) (T : ℝ) (α : ℝ → (H.stage j).Carrier)
    {a b B : ℝ} (hab : a ≤ b)
    (hscalar : ∀ t ∈ Ioo a b, -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t))
    (hint : IntervalIntegrable (H.stageRegularizedLagrangian j T α) volume a b) :
    -(2 * B / 3) * (b ^ 3 - a ^ 3) ≤ H.stageRegularizedAction j T α a b := by
  have hh := intervalIntegral.integral_ge_of_mul_sq_le hab hint (C := -(2 * B)) (fun t ht => ?_)
  · simpa only [neg_div, stageRegularizedAction] using hh
  have hs := mul_le_mul_of_nonneg_left (hscalar t ht) (by positivity : 0 ≤ 2 * t ^ 2)
  have hk := metric_inner_self_nonneg (H.stageMetric j (T - t ^ 2)) (α t) (lVelocity α t)
  dsimp only [stageRegularizedLagrangian]
  nlinarith


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private theorem sum_stageInterval_singleton {R : Type*} [AddCommMonoid R]
    (j : Fin (H.eventCount + 1)) (F : Fin (H.eventCount + 1) → R) :
    (∑ k : H.StageInterval j j, F k.val) = F j := by
  classical
  have hsingle (k : H.StageInterval j j) : k = ⟨j, le_rfl, le_rfl⟩ :=
    Subtype.ext (le_antisymm k.property.2 k.property.1)
  exact Fintype.sum_eq_single (f := fun k : H.StageInterval j j => F k.val)
    (⟨j, le_rfl, le_rfl⟩ : H.StageInterval j j) (by intro k hne; exact False.elim (hne (hsingle k)))

private theorem sum_stageInterval_sub {R : Type*} [AddCommGroup R]
    (A B : Fin (H.eventCount + 1) → R) (last : Fin (H.eventCount + 1)) :
    ∀ first : Fin (H.eventCount + 1), first ≤ last →
      (∀ i : Fin H.eventCount, first ≤ i.castSucc → i.succ ≤ last → A i.castSucc = B i.succ) →
      (∑ j : H.StageInterval first last, (B j.val - A j.val)) = B first - A last := by
  induction last using Fin.induction with
  | zero =>
    intro first hfirst _
    have hf : first = 0 := le_antisymm hfirst (Fin.zero_le _)
    subst first
    exact sum_stageInterval_singleton H 0 (fun j => B j - A j)
  | succ i ih =>
    intro first hfirst hadj
    by_cases hf : first = i.succ
    · subst first
      exact sum_stageInterval_singleton H i.succ (fun j => B j - A j)
    have hfi : first ≤ i.castSucc := by
      change first.val ≤ i.val
      have hh : first.val ≤ i.val + 1 := hfirst
      have hn : first.val ≠ i.val + 1 := fun h => hf (Fin.ext h)
      omega
    rw [H.sum_stageInterval_split i hfirst i.castSucc_lt_succ.le]
    have hleft := ih first hfi (fun j hj hji => hadj j hj (hji.trans i.castSucc_lt_succ.le))
    have hright := sum_stageInterval_singleton H i.succ (fun j => B j - A j)
    change (∑ j : H.StageInterval first i.castSucc, (B j.val - A j.val)) +
      (∑ j : H.StageInterval i.succ i.succ, (B j.val - A j.val)) = _
    rw [hleft, hright, hadj i hfi le_rfl]
    abel

theorem sum_regularizedStage_sub {R : Type*} [AddCommGroup R]
    (F : ℝ → R) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {T u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) :
    (∑ j : H.StageInterval first last,
      (F (H.regularizedStageEnd T v j.val) - F (H.regularizedStageStart T u j.val))) =
      F v - F u := by
  have hh := sum_stageInterval_sub H (fun j => F (H.regularizedStageStart T u j))
    (fun j => F (H.regularizedStageEnd T v j)) last first hle (fun i hf hl => ?_)
  · simpa only [H.regularizedStageStart_eq_of_mem_Icc hu hupper,
      H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower] using hh
  rw [H.regularizedStageStart_castSucc_eq_event_clock hupper i hl,
    H.regularizedStageEnd_succ_eq_event_clock hlower i hf]

theorem regularizedC1ActionValues_ge_of_scalar_lower
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T u v B : ℝ)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) {A : ℝ}
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q) :
    -(2 * B / 3) * (v ^ 3 - u ^ 3) ≤ A := by
  rcases hA with ⟨hu, huv, hupper, hlower, α, _, hint, _, _, _, rfl⟩
  have hh : (∑ j : H.StageInterval first last, -(2 * B / 3) *
      ((H.regularizedStageEnd T v j.val) ^ 3 - (H.regularizedStageStart T u j.val) ^ 3)) ≤
      ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    apply Finset.sum_le_sum
    intro j _
    exact H.stageRegularizedAction_ge_of_scalar_lower_bound j.val T (α j)
      (H.regularizedStage_bounds hu huv hupper hlower j).2.1
      (fun t ht => hscalar j t ht (α j t)) (hint j)
  simpa only [← Finset.mul_sum, H.sum_regularizedStage_sub (fun t : ℝ => t ^ 3) hle hu huv hupper hlower] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedC1ActionValues_bddBelow_of_scalar_lower
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T u v B : ℝ)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    BddBelow (H.regularizedC1ActionValues first last hle T u v p q) := by
  exact ⟨-(2 * B / 3) * (v ^ 3 - u ^ 3),
    fun _ hA => H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B hscalar p q hA⟩


theorem regularizedC1Cost_le_of_competitor
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T u v B : ℝ)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) {A : ℝ}
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q) :
    H.regularizedC1Cost first last hle T u v p q ≤ (A : WithTop ℝ) := by
  obtain ⟨L, hL⟩ := H.regularizedC1ActionValues_bddBelow_of_scalar_lower first last hle T u v B hscalar p q
  apply csInf_le
  · refine ⟨(L : WithTop ℝ), ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact WithTop.coe_le_coe.mpr (hL hr)
  · exact ⟨A, hA, rfl⟩

theorem regularizedC1Cost_eq_of_minimum
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T u v A : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q)
    (hmin : ∀ r ∈ H.regularizedC1ActionValues first last hle T u v p q, A ≤ r) :
    H.regularizedC1Cost first last hle T u v p q = (A : WithTop ℝ) := by
  unfold regularizedC1Cost
  let costs := (fun r : ℝ => (r : WithTop ℝ)) '' H.regularizedC1ActionValues first last hle T u v p q
  have hmem : (A : WithTop ℝ) ∈ costs := ⟨A, hA, rfl⟩
  have hlower : ∀ r ∈ costs, (A : WithTop ℝ) ≤ r := by
    rintro r ⟨t, ht, rfl⟩
    exact WithTop.coe_le_coe.mpr (hmin t ht)
  exact le_antisymm (csInf_le ⟨(A : WithTop ℝ), hlower⟩ hmem) (le_csInf ⟨_, hmem⟩ hlower)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem stageRegularizedLagrangian_comp_eq_of_localPullMetric
    (j : Fin (H.eventCount + 1)) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (f : X → (H.stage j).Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T : ℝ) {α : ℝ → X} {r : ℝ} (hα : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α r)
    (hmetric : S.base.metric (T - r ^ 2) = localPullMetric (H.stageMetric j (T - r ^ 2)) f hf) :
    H.stageRegularizedLagrangian j T (f ∘ α) r = lRegularizedLagrangian S T α r := by
  have hvel : lVelocity (f ∘ α) r = mfderiv ThreeModel ThreeModel f (α r) (lVelocity α r) := by
    unfold lVelocity
    rw [mfderiv_comp r ((hf (α r)).mdifferentiableAt (by simp)) hα]
    rfl
  have hscalar := metricScalarAt_localPull (H.stageMetric j (T - r ^ 2)) f hf (α r)
  simp only [stageRegularizedLagrangian, lRegularizedLagrangian, SolutionOn.scalar,
    SolutionFamily.scalar, hmetric, localPullMetric_inner, hvel, Function.comp_apply, hscalar]

theorem stageRegularizedAction_comp_eq_of_localPullMetric
    (j : Fin (H.eventCount + 1)) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (f : X → (H.stage j).Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T a b : ℝ) (α : ℝ → X) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hmetric : ∀ r ∈ uIoo a b,
      S.base.metric (T - r ^ 2) = localPullMetric (H.stageMetric j (T - r ^ 2)) f hf) :
    H.stageRegularizedAction j T (f ∘ α) a b = lRegularizedAction S T α a b := by
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  exact H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hf T
    (hα.mdifferentiable one_ne_zero r) (hmetric r hr)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem action_mem_regularizedC1ActionValues_of_common_curve
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    lRegularizedAction S T γ u v ∈ H.regularizedC1ActionValues first last hle T u v
      (f ⟨last, hle, le_rfl⟩ (γ u)) (f ⟨first, le_rfl, hle⟩ (γ v)) := by
  have hint (a b : ℝ) (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) :
      IntervalIntegrable (lRegularizedLagrangian S T γ) volume a b := by
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS γ hγ
    have hh := hc.comp (s := Icc a b) (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => htime t ⟨hua.trans ht.1, ht.2.trans hbv⟩)
    exact hh.intervalIntegrable_of_Icc hab
  have hbound (j : H.StageInterval first last) := H.regularizedStage_bounds hu huv hupper hlower j
  have hEq (j : H.StageInterval first last) :
      EqOn (lRegularizedLagrangian S T γ)
        (H.stageRegularizedLagrangian j.val T (f j ∘ γ))
        (uIoo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
    intro t ht
    rw [uIoo_of_le (hbound j).2.1] at ht
    exact (H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val S (f j) (hf j) T
      (hγ.mdifferentiable one_ne_zero t) (hmetric j t ht)).symm
  refine ⟨hu, huv, hupper, hlower, (fun j => f j ∘ γ), ?_, ?_, rfl, rfl, ?_, ?_⟩
  · intro j
    exact ((hf j).contMDiff.of_le (by norm_num)).comp hγ
  · intro j
    exact (hint _ _ (hbound j).1 (hbound j).2.1 (hbound j).2.2).congr_uIoo (hEq j)
  · intro i hi hl
    obtain ⟨z, _, hz, hzg⟩ := hcross i hi hl (γ (Real.sqrt (T - H.time i.succ)))
    exact ⟨z, hz, hzg⟩
  · have hsum := H.sum_regularizedStage_sub (fun t => lRegularizedAction S T γ u t) hle hu huv hupper hlower
    have hzero : lRegularizedAction S T γ u u = 0 := intervalIntegral.integral_same
    rw [hzero, sub_zero] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j _
    have hsegment : lRegularizedAction S T γ (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T v j.val) = H.stageRegularizedAction j.val T (f j ∘ γ)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) :=
      intervalIntegral.integral_congr_uIoo (hEq j)
    have hadd := lRegularizedAction_add S T γ u (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val)
      (hint _ _ le_rfl (hbound j).1 ((hbound j).2.1.trans (hbound j).2.2))
      (hint _ _ (hbound j).1 (hbound j).2.1 (hbound j).2.2)
    change lRegularizedAction S T γ _ _ = H.stageRegularizedAction j.val T (f j ∘ γ) _ _ at hsegment
    change H.stageRegularizedAction j.val T (f j ∘ γ) _ _ =
      lRegularizedAction S T γ u _ - lRegularizedAction S T γ u _
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedC1Cost_dynamic_programming_at_event
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T u v B : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedC1Cost first last hle T u v p q =
      sInf (Set.range fun z : (H.event i).old =>
        H.regularizedC1Cost first i.castSucc hf T (Real.sqrt (T - H.time i.succ)) v z.val.val q +
        H.regularizedC1Cost i.succ last hl T u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z)) := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  let A := H.regularizedC1ActionValues first last hle T u v p q
  let Ao (z : (H.event i).old) := H.regularizedC1ActionValues first i.castSucc hf T w v z.val.val q
  let An (z : (H.event i).old) := H.regularizedC1ActionValues i.succ last hl T u w p ((H.event i).oldOutput z)
  let F (z : (H.event i).old) : Set (WithTop ℝ) :=
    (fun r : ℝ => (r : WithTop ℝ)) '' Set.image2 (fun a b : ℝ => a + b) (Ao z) (An z)
  let U : Set (WithTop ℝ) := ⋃ z, F z
  have hsplit : A = ⋃ z, Set.image2 (fun a b : ℝ => a + b) (Ao z) (An z) := by
    ext r
    rw [H.mem_regularizedC1ActionValues_split_at_event hle i hf hl hu huv hupper hlower p q]
    simp only [Set.mem_iUnion, Set.mem_image2]
    constructor
    · rintro ⟨z, ao, an, ho, hn, heq⟩
      exact ⟨z, ao, ho, an, hn, heq⟩
    · rintro ⟨z, ao, ho, an, hn, heq⟩
      exact ⟨z, ao, an, ho, hn, heq⟩
  have hUeq : U = (fun r : ℝ => (r : WithTop ℝ)) '' A := by
    dsimp only [U, F]
    rw [← Set.image_iUnion, ← hsplit]
  have hUbdd : BddBelow U := by
    rw [hUeq]
    exact Monotone.map_bddBelow (fun _ _ h => WithTop.coe_mono h)
      (H.regularizedC1ActionValues_bddBelow_of_scalar_lower first last hle T u v B hscalar p q)
  have hFbdd (z : (H.event i).old) : BddBelow (F z) :=
    hUbdd.mono (fun _ hx => Set.mem_iUnion_of_mem z hx)
  have hFglb (z : (H.event i).old) : IsGLB (F z) (sInf (F z)) := WithTop.isGLB_sInf' (hFbdd z)
  have hRangeBdd : BddBelow (Set.range fun z => sInf (F z)) := by
    obtain ⟨c, hc⟩ := hUbdd
    refine ⟨c, ?_⟩
    rintro y ⟨z, rfl⟩
    apply (hFglb z).2
    intro y hy
    exact hc (Set.mem_iUnion_of_mem z hy)
  have hOuter : sInf U = sInf (Set.range fun z => sInf (F z)) :=
    (WithTop.isGLB_sInf' hUbdd).unique
      ((isGLB_iUnion_iff_of_isGLB hFglb _).mp (WithTop.isGLB_sInf' hRangeBdd))
  have hiT : H.time i.succ ≤ T := by
    have hh := (H.time_strictMono.monotone hl).trans hupper.1
    linarith [sq_nonneg u]
  have hbo (z : (H.event i).old) : BddBelow (Ao z) := by
    apply H.regularizedC1ActionValues_bddBelow_of_scalar_lower first i.castSucc hf T w v B _ _ _
    intro j t ht x
    rw [H.regularizedStageStart_eq_at_event_clock hupper i hl j.val j.property.2] at ht
    exact hscalar ⟨j.val, j.property.1, j.property.2.trans (i.castSucc_lt_succ.le.trans hl)⟩ t ht x
  have hbn (z : (H.event i).old) : BddBelow (An z) := by
    apply H.regularizedC1ActionValues_bddBelow_of_scalar_lower i.succ last hl T u w B _ _ _
    intro j t ht x
    rw [H.regularizedStageEnd_eq_at_event_clock hlower i hf hiT j.val j.property.1] at ht
    exact hscalar ⟨j.val, hf.trans (i.castSucc_lt_succ.le.trans j.property.1), j.property.2⟩ t ht x
  have hadd (z : (H.event i).old) :
      H.regularizedC1Cost first i.castSucc hf T w v z.val.val q +
        H.regularizedC1Cost i.succ last hl T u w p ((H.event i).oldOutput z) = sInf (F z) :=
    WithTop.sInf_coe_image_add (hbo z) (hbn z)
  change sInf ((fun r : ℝ => (r : WithTop ℝ)) '' A) = _
  rw [← hUeq, hOuter]
  exact congrArg (fun F : (H.event i).old → WithTop ℝ => sInf (Set.range F))
    (funext (fun z => (hadd z).symm))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end


set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedC1ActionValues_eq_eventRegularizedC1ActionValues
    (i : Fin H.eventCount) {b : ℝ} (G : (H.stage i.succ).IncomingSlab (H.time i.succ) b)
    {T d v : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v) (hclock : T - d ^ 2 = H.time i.succ)
    (hT : T ∈ H.stageDomain i.succ) (hpast : T - v ^ 2 ∈ H.stageDomain i.castSucc)
    (htimePlus : ∀ t ∈ Icc 0 d, T - t ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.succ) b G.lt).carrier)
    (hmetric : ∀ t ∈ Ioo 0 d, H.stageMetric i.succ (T - t ^ 2) = G.flow.base.metric (T - t ^ 2))
    (p : (H.stage i.succ).Carrier) (q : (H.stage i.castSucc).Carrier) :
    H.regularizedC1ActionValues i.castSucc i.succ i.castSucc_le_succ T 0 v p q =
      (H.event i).eventRegularizedC1ActionValues G T d v p q := by
  have hv : 0 ≤ v := hd.trans hdv
  have hupper : T - (0 : ℝ) ^ 2 ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) := by
    simp only [zero_pow two_ne_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hT, H.le_stageEndTime_of_mem_stageDomain hT⟩
  have hw : Real.sqrt (T - H.time i.succ) = d := by
    rw [show T - H.time i.succ = d ^ 2 by linarith, Real.sqrt_sq hd]
  have htimes : ∀ t ∈ Ioc d v,
      T - t ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.castSucc) (H.time i.succ) (H.event i).incoming.lt).carrier := by
    intro t ht
    have ht0 : 0 ≤ t := hd.trans ht.1.le
    have ht2v : t ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ht0 hv).mpr ht.2
    have hd2t : d ^ 2 < t ^ 2 := (sq_lt_sq₀ hd ht0).mpr ht.1
    have hleft := H.time_le_of_mem_stageDomain hpast
    exact ⟨by linarith, by linarith⟩
  have hlag (α : ℝ → (H.stage i.succ).Carrier) :
      EqOn (H.stageRegularizedLagrangian i.succ T α) (lRegularizedLagrangian G.flow T α) (uIoo 0 d) := by
    intro t ht
    rw [uIoo_of_le hd] at ht
    simp only [stageRegularizedLagrangian, lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar,
      hmetric t ht]
  have hact (α : ℝ → (H.stage i.succ).Carrier) :
      H.stageRegularizedAction i.succ T α 0 d = lRegularizedAction G.flow T α 0 d :=
    intervalIntegral.integral_congr_uIoo (hlag α)
  have huold : T - d ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hclock, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hvnew : T - d ^ 2 ∈ H.stageDomain i.succ := hclock ▸ H.time_mem_stageDomain i.succ
  ext A
  rw [H.mem_regularizedC1ActionValues_split_at_event i.castSucc_le_succ i le_rfl le_rfl le_rfl hv hupper hpast p q, hw]
  constructor
  · rintro ⟨z, Ao, An, ho, hn, hsum⟩
    rcases (H.mem_regularizedC1ActionValues_self i.castSucc z.val.val q).mp ho with
      ⟨_, _, _, _, β, hβ, hiβ, hβ0, hβv, hβa⟩
    rcases (H.mem_regularizedC1ActionValues_self i.succ p ((H.event i).oldOutput z)).mp hn with
      ⟨_, _, _, _, α, hα, hiα, hα0, hαd, hαa⟩
    refine ⟨hd, hdv, hclock, htimePlus, htimes, α, β, hα, hβ, hiα.congr_uIoo (hlag α), ?_, hα0, hβv,
      ⟨z, hβ0.symm, hαd.symm⟩, ?_⟩
    · simpa only [show H.stageRegularizedLagrangian i.castSucc T β = lRegularizedLagrangian (H.event i).incoming.flow T β from funext (H.stageRegularizedLagrangian_castSucc i T β)] using hiβ
    · rw [← hact α, hαa, ← H.stageRegularizedAction_castSucc i T β d v, hβa]
      linarith
  · rintro ⟨_, _, _, _, _, α, β, hα, hβ, hiα, hiβ, hα0, hβv, hnode, hsum⟩
    obtain ⟨z, hzβ, hzα⟩ := hnode
    refine ⟨z, H.stageRegularizedAction i.castSucc T β d v, H.stageRegularizedAction i.succ T α 0 d, ?_, ?_, ?_⟩
    · apply (H.mem_regularizedC1ActionValues_self i.castSucc z.val.val q).mpr
      refine ⟨hd, hdv, huold, hpast, β, hβ, ?_, hzβ.symm, hβv, rfl⟩
      simpa only [show H.stageRegularizedLagrangian i.castSucc T β = lRegularizedLagrangian (H.event i).incoming.flow T β from funext (H.stageRegularizedLagrangian_castSucc i T β)] using hiβ
    · apply (H.mem_regularizedC1ActionValues_self i.succ p ((H.event i).oldOutput z)).mpr
      exact ⟨le_rfl, hd, hupper, hvnew, α, hα, hiα.congr_uIoo (hlag α).symm, hα0, hzα.symm, rfl⟩
    · rw [H.stageRegularizedAction_castSucc, hact]
      linarith

theorem regularizedC1Cost_eq_eventRegularizedC1Cost
    (i : Fin H.eventCount) {b : ℝ} (G : (H.stage i.succ).IncomingSlab (H.time i.succ) b)
    {T d v : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v) (hclock : T - d ^ 2 = H.time i.succ)
    (hT : T ∈ H.stageDomain i.succ) (hpast : T - v ^ 2 ∈ H.stageDomain i.castSucc)
    (htimePlus : ∀ t ∈ Icc 0 d, T - t ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.succ) b G.lt).carrier)
    (hmetric : ∀ t ∈ Ioo 0 d, H.stageMetric i.succ (T - t ^ 2) = G.flow.base.metric (T - t ^ 2))
    (p : (H.stage i.succ).Carrier) (q : (H.stage i.castSucc).Carrier) :
    H.regularizedC1Cost i.castSucc i.succ i.castSucc_le_succ T 0 v p q =
      (H.event i).eventRegularizedC1Cost G T d v p q := by
  unfold regularizedC1Cost MetricCutCapEvent.eventRegularizedC1Cost
  rw [H.regularizedC1ActionValues_eq_eventRegularizedC1ActionValues i G hd hdv hclock hT hpast htimePlus hmetric p q]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v

variable (H : ObservedHistory.{u})
  {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]

theorem exists_contMDiff_stage_lifts_of_confined_curves
    (first last : Fin (H.eventCount + 1))
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hstay : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (range (f j)))
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    ∃ β : H.StageInterval first last → ℝ → X,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (β j)) ∧
      (∀ j, EqOn (f j ∘ β j) (α j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        β ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)) =
          β ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ))) := by
  have hbound (j : H.StageInterval first last) := H.regularizedStage_bounds hu huv hupper hlower j
  have hex (j : H.StageInterval first last) :
      ∃ β : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧ EqOn (f j ∘ β) (α j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
    rcases (hbound j).2.1.lt_or_eq with hlt | heq
    · exact DifferentialGeometry.Topology.Manifold.exists_contMDiff_interval_lift_of_injective_localDiffeomorph
        (f j) (hf j) (hinj j) (α j) (hα j) hlt (hstay j)
    · obtain ⟨x, hx⟩ := hstay j ⟨le_rfl, (hbound j).2.1⟩
      refine ⟨fun _ => x, contMDiff_const, ?_⟩
      intro t ht
      have ht' : t = H.regularizedStageStart T u j.val := le_antisymm (ht.2.trans_eq heq.symm) ht.1
      simpa only [Function.comp_apply, ht'] using hx
  choose β hβ hβeq using hex
  refine ⟨β, hβ, hβeq, ?_⟩
  intro i hi hl
  let jo : H.StageInterval first last := ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
  let jn : H.StageInterval first last := ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
  have hclocko : H.regularizedStageStart T u jo.val = Real.sqrt (T - H.time i.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
  have hclockn : H.regularizedStageEnd T v jn.val = Real.sqrt (T - H.time i.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hlower i hi
  have heqo := hβeq jo (show Real.sqrt (T - H.time i.succ) ∈
      Icc (H.regularizedStageStart T u jo.val) (H.regularizedStageEnd T v jo.val) by
    rw [← hclocko]
    exact ⟨le_rfl, (hbound jo).2.1⟩)
  have heqn := hβeq jn (show Real.sqrt (T - H.time i.succ) ∈
      Icc (H.regularizedStageStart T u jn.val) (H.regularizedStageEnd T v jn.val) by
    rw [← hclockn]
    exact ⟨(hbound jn).2.1, le_rfl⟩)
  obtain ⟨p, hp, hpout⟩ := hnode i hi hl
  obtain ⟨q, _, hq, hqout⟩ := hcross i hi hl (β jn (Real.sqrt (T - H.time i.succ)))
  have hpq : p = q := (H.event i).oldOutput_injective (hpout.trans (heqn.symm.trans hqout.symm))
  apply hinj jo
  exact hq.symm.trans ((congrArg (fun z : (H.event i).old => z.val.val) hpq).symm.trans
    (hp.trans heqo.symm))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u})

theorem stageRegularizedAction_congr
    (j : Fin (H.eventCount + 1)) (T a b : ℝ)
    (α β : ℝ → (H.stage j).Carrier) (heq : EqOn α β (uIoo a b)) :
    H.stageRegularizedAction j T α a b = H.stageRegularizedAction j T β a b := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have hev : α =ᶠ[𝓝 t] β := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact heq hr
  have hval : α t = β t := hev.self_of_nhds
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
  have hvel : lVelocity (I := ThreeModel) α t = lVelocity (I := ThreeModel) β t := by
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem sum_stageRegularizedAction_eq_of_localPullMetric
    (first last : Fin (H.eventCount + 1))
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (T u v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (β : H.StageInterval first last → ℝ → X)
    (hβ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (β j))
    (heq : ∀ j, EqOn (f j ∘ β j) (α j)
      (uIoo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ uIoo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j)) :
    (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) =
      ∑ j : H.StageInterval first last, lRegularizedAction S T (β j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  apply Finset.sum_congr rfl
  intro j _
  exact (H.stageRegularizedAction_congr j.val T _ _ (f j ∘ β j) (α j) (heq j)).symm.trans
    (H.stageRegularizedAction_comp_eq_of_localPullMetric j.val S (f j) (hf j) T _ _ (β j)
      (hβ j) (hmetric j))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})
  {X : Type*} [UniformSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
  {D : RealTimeInterval}

theorem exists_lRegularizedAction_lt_sum_stage_on_carrier
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hMet : MetricFamilySmoothOn (I := ThreeModel) (M := X) D S.family.metric)
    (hSc : ScalarSTContOn (I := ThreeModel) (M := X) S)
    (T : ℝ) (v : ℝ) (last : Fin (H.eventCount + 1)) :
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ last) (u : ℝ), 0 ≤ u → u ≤ v →
      T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) → T - v ^ 2 ∈ H.stageDomain first →
      (∀ r ∈ Icc u v, T - r ^ 2 ∈ D.carrier) →
      ∀ β : H.StageInterval first last → ℝ → X,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (β j)) →
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        β ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
        β ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))) →
      ∀ ε : ℝ, 0 < ε →
      ∃ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧
        γ u = β ⟨last, hle, le_rfl⟩ u ∧ γ v = β ⟨first, le_rfl, hle⟩ v ∧
        lRegularizedAction S T γ u v <
          (∑ j : H.StageInterval first last, lRegularizedAction S T (β j)
            (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) + ε := by
  induction last using Fin.induction with
  | zero =>
    intro first hle u hu huv hupper hlower hback β hβ hnode ε hε
    have hf : first = 0 := le_antisymm hle (Fin.zero_le _)
    subst first
    let j : H.StageInterval 0 0 := ⟨0, le_rfl, le_rfl⟩
    refine ⟨β j, hβ j, rfl, rfl, ?_⟩
    rw [sum_stageInterval_self H 0,
      H.regularizedStageStart_eq_of_mem_Icc hu hupper,
      H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower]
    exact lt_add_of_pos_right _ hε
  | succ i ih =>
    intro first hle u hu huv hupper hlower hback β hβ hnode ε hε
    by_cases hf : first = i.succ
    · subst first
      let j : H.StageInterval i.succ i.succ := ⟨i.succ, le_rfl, le_rfl⟩
      refine ⟨β j, hβ j, rfl, rfl, ?_⟩
      rw [sum_stageInterval_self H i.succ,
        H.regularizedStageStart_eq_of_mem_Icc hu hupper,
        H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower]
      exact lt_add_of_pos_right _ hε
    have hfi : first ≤ i.castSucc := by
      have ha : first.val ≤ i.val + 1 := hle
      have hb : first.val ≠ i.val + 1 := fun h => hf (Fin.ext h)
      change first.val ≤ i.val
      omega
    let w := Real.sqrt (T - H.time i.succ)
    have hw := H.event_clock_bounds hu huv hupper hlower i hfi le_rfl
    have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      rw [hw.2.2, H.stageEndTime_castSucc]
      exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
    let lo : H.StageInterval first i.castSucc → H.StageInterval first i.succ :=
      fun j => ⟨j.val, j.property.1, j.property.2.trans i.castSucc_lt_succ.le⟩
    let βold := fun j : H.StageInterval first i.castSucc => β (lo j)
    have hnodeOld (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hki : k.succ ≤ i.castSucc) :
        βold ⟨k.castSucc, hkf, k.castSucc_lt_succ.le.trans hki⟩ (Real.sqrt (T - H.time k.succ)) =
        βold ⟨k.succ, hkf.trans k.castSucc_lt_succ.le, hki⟩ (Real.sqrt (T - H.time k.succ)) :=
      hnode k hkf (hki.trans i.castSucc_lt_succ.le)
    obtain ⟨η, hη, hηstart, hηend, hηact⟩ := ih first hfi w (hu.trans hw.1) hw.2.1 huOld hlower
      (fun r hr => hback r ⟨hw.1.trans hr.1, hr.2⟩) βold (fun j => hβ (lo j)) hnodeOld
      (ε / 2) (half_pos hε)
    let jlast : H.StageInterval first i.succ := ⟨i.succ, hle, le_rfl⟩
    have hmatch : β jlast w = η w := (hnode i hfi le_rfl).symm.trans hηstart.symm
    obtain ⟨γ, hγ, hγstart, hγend, hγact⟩ :=
      exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff S hMet hSc T u w v hw.1 hw.2.1
        (β jlast) η (hβ jlast) hη hmatch hback (half_pos hε)
    refine ⟨γ, hγ, hγstart, hγend.trans hηend, ?_⟩
    have hstartOld (j : H.StageInterval first i.castSucc) :
        H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
      H.regularizedStageStart_eq_at_event_clock hupper i le_rfl j.val j.property.2
    have hsum : (∑ j : H.StageInterval first i.succ, lRegularizedAction S T (β j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) =
        (∑ j : H.StageInterval first i.castSucc, lRegularizedAction S T (βold j)
          (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)) +
          lRegularizedAction S T (β jlast) u w := by
      rw [H.sum_stageInterval_split i hle i.castSucc_lt_succ.le]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _
        rw [hstartOld j]
      · rw [sum_stageInterval_self H i.succ,
          H.regularizedStageStart_eq_of_mem_Icc hu hupper,
          H.regularizedStageEnd_succ_eq_event_clock hlower i hfi]
    rw [hsum]
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})
  {X : Type u} [TopologicalSpace X]
  [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_lRegularizedAction_lt_of_confined_history_curves
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hstay : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (range (f j)))
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧
      f ⟨last, hle, le_rfl⟩ (γ u) = α ⟨last, hle, le_rfl⟩ u ∧
      f ⟨first, le_rfl, hle⟩ (γ v) = α ⟨first, le_rfl, hle⟩ v ∧
      lRegularizedAction S T γ u v <
        (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) + ε := by
  let j : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let : SecondCountableTopology (H.stage j.val).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage j.val).Carrier
  have hemb : _root_.Topology.IsOpenEmbedding (f j) :=
    .of_continuous_injective_isOpenMap (hf j).contMDiff.continuous (hinj j) (hf j).isOpenMap
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨β, hβ, heq, hmatch⟩ := H.exists_contMDiff_stage_lifts_of_confined_curves
    first last f hf hinj hcross hu huv hupper hlower α hα hstay hnode
  have hbound (j : H.StageInterval first last) := H.regularizedStage_bounds hu huv hupper hlower j
  have hsum := (H.sum_stageRegularizedAction_eq_of_localPullMetric first last f hf S T u v
    α β hβ (fun j t ht => heq j (by
      rw [uIoo_of_le (hbound j).2.1] at ht
      exact Ioo_subset_Icc_self ht))
    (fun j t ht => hmetric j t (by rwa [uIoo_of_le (hbound j).2.1] at ht))).symm
  obtain ⟨γ, hγ, hzero, hend, hact⟩ := H.exists_lRegularizedAction_lt_sum_stage_on_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T v last first hle u hu huv hupper hlower htime β hβ
    (fun i hi hl => (hmatch i hi hl).symm) ε hε
  refine ⟨γ, hγ, ?_, ?_, ?_⟩
  · rw [hzero]
    apply heq ⟨last, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc hu hupper]
    exact ⟨le_rfl, (hbound ⟨last, hle, le_rfl⟩).1.trans (hbound ⟨last, hle, le_rfl⟩).2.1⟩
  · rw [hend]
    apply heq ⟨first, le_rfl, hle⟩
    rw [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower]
    exact ⟨(hbound ⟨first, le_rfl, hle⟩).2.1.trans (hbound ⟨first, le_rfl, hle⟩).2.2, le_rfl⟩
  · simpa only [hsum] using hact

theorem action_le_of_minimal_and_confined_history_curves
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hstay : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (range (f j)))
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (η : ℝ → X)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ u = η u → γ v = η v →
      lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v)
    (hstart : α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ (η u))
    (hend : α ⟨first, le_rfl, hle⟩ v = f ⟨first, le_rfl, hle⟩ (η v)) :
    lRegularizedAction S T η u v ≤
      ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ, hγzero, hγend, hact⟩ := H.exists_lRegularizedAction_lt_of_confined_history_curves
    first last hle f hf hinj hcross S hS T hu huv hupper hlower htime hmetric α hα hstay hnode hε
  have hzero := hinj ⟨last, hle, le_rfl⟩ (hγzero.trans hstart)
  have hlast := hinj ⟨first, le_rfl, hle⟩ (hγend.trans hend)
  exact (hmin γ hγ hzero hlast).trans hact.le

theorem regularizedC1Cost_eq_of_minimal_of_lower_action_confined
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ u = η u → γ v = η v →
      lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v)
    (hconf : ∀ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) →
      α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ (η u) →
      α ⟨first, le_rfl, hle⟩ v = f ⟨first, le_rfl, hle⟩ (η v) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))) →
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) < lRegularizedAction S T η u v →
      ∀ j, MapsTo (α j) (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (range (f j))) :
    H.regularizedC1Cost first last hle T u v (f ⟨last, hle, le_rfl⟩ (η u))
        (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η u v : WithTop ℝ) := by
  apply H.regularizedC1Cost_eq_of_minimum first last hle T u v _ _ _
  · exact H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross
      S hS T hu huv hupper hlower htime hmetric η hη
  · rintro A ⟨_, _, _, _, α, hα, hint, hstart, hend, hnode, rfl⟩
    by_contra hnot
    have hlow := lt_of_not_ge hnot
    exact (not_lt_of_ge (H.action_le_of_minimal_and_confined_history_curves first last hle
      f hf hinj hcross S hS T hu huv hupper hlower htime hmetric α hα
      (hconf α hα hint hstart hend hnode hlow) hnode η hmin hstart hend)) hlow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageRegularizedAction_le_of_sum_le
    {first last : Fin (H.eventCount + 1)} {T u v B A : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t))
    (hsum : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ A)
    (j : H.StageInterval first last) :
    H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤
      A + (2 * B / 3) * ((v ^ 3 - u ^ 3) -
        ((H.regularizedStageEnd T v j.val) ^ 3 - (H.regularizedStageStart T u j.val) ^ 3)) := by
  classical
  have hle : first ≤ last := j.property.1.trans j.property.2
  let action (k : H.StageInterval first last) := H.stageRegularizedAction k.val T (α k)
    (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)
  let weight (k : H.StageInterval first last) :=
    (H.regularizedStageEnd T v k.val) ^ 3 - (H.regularizedStageStart T u k.val) ^ 3
  have hnonneg (k : H.StageInterval first last) : 0 ≤ action k + (2 * B / 3) * weight k := by
    have hh := H.stageRegularizedAction_ge_of_scalar_lower_bound k.val T (α k)
      (H.regularizedStage_bounds hu huv hupper hlower k).2.1 (hscalar k) (hint k)
    dsimp only [action, weight]
    linarith
  have hsingle : action j + (2 * B / 3) * weight j ≤
      ∑ k : H.StageInterval first last, (action k + (2 * B / 3) * weight k) :=
    Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  have hweight : (∑ k : H.StageInterval first last, weight k) = v ^ 3 - u ^ 3 :=
    H.sum_regularizedStage_sub (fun r : ℝ => r ^ 3) hle hu huv hupper hlower
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hweight] at hsingle
  change (∑ k : H.StageInterval first last, action k) ≤ A at hsum
  change action j ≤ A + (2 * B / 3) * ((v ^ 3 - u ^ 3) - weight j)
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

namespace ObservedHistory

variable (H : ObservedHistory.{u})

theorem exists_last_nonconfined_stage {X : Type v}
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier) (K : Set X)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ x ∈ K, (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpole : α ⟨last, hle, le_rfl⟩ u ∈ f ⟨last, hle, le_rfl⟩ '' K)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hexit : ∃ j, ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ j : H.StageInterval first last,
      α j (H.regularizedStageStart T u j.val) ∈ f j '' K ∧
      (∃ t ∈ Ioc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
        α j t ∉ f j '' K) ∧
      ∀ k : H.StageInterval first last, j.val < k.val → MapsTo (α k)
        (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)) (f k '' K) := by
  classical
  let bad : Finset (H.StageInterval first last) := Finset.univ.filter fun j =>
    ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)
  have hbad : bad.Nonempty := by
    obtain ⟨j, hj⟩ := hexit
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmax⟩ := bad.exists_max_image (fun j => j.val) hbad
  have hnewer : ∀ k : H.StageInterval first last, j.val < k.val → MapsTo (α k)
      (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)) (f k '' K) := by
    intro k hjk
    by_contra hk
    exact (not_le_of_gt hjk) (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩))
  have hstart : α j (H.regularizedStageStart T u j.val) ∈ f j '' K := by
    by_cases hjlast : j.val = last
    · have hj' : j = ⟨last, hle, le_rfl⟩ := Subtype.ext hjlast
      subst j
      simpa only [H.regularizedStageStart_eq_of_mem_Icc hu hupper] using hpole
    · have hjlt : j.val < last := lt_of_le_of_ne j.property.2 hjlast
      let i : Fin H.eventCount := ⟨j.val.val, by have := last.isLt; omega⟩
      have hicast : i.castSucc = j.val := Fin.ext rfl
      have hi : first ≤ i.castSucc := hicast.symm ▸ j.property.1
      have hl : i.succ ≤ last := by change j.val.val + 1 ≤ last.val; exact hjlt
      let jo : H.StageInterval first last := ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
      let jn : H.StageInterval first last := ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
      have hjo : jo = j := Subtype.ext hicast
      have hjn : j.val < jn.val := by simpa only [jn, ← hicast] using i.castSucc_lt_succ
      have hclocko : H.regularizedStageStart T u jo.val = Real.sqrt (T - H.time i.succ) :=
        H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
      have hclockn : H.regularizedStageEnd T v jn.val = Real.sqrt (T - H.time i.succ) :=
        H.regularizedStageEnd_succ_eq_event_clock hlower i hi
      have hnend : α jn (Real.sqrt (T - H.time i.succ)) ∈ f jn '' K := by
        apply hnewer jn hjn
        rw [← hclockn]
        exact ⟨(H.regularizedStage_bounds hu huv hupper hlower jn).2.1, le_rfl⟩
      have hmem := ((H.event i).mem_image_iff_of_admissible_node (f jo) (f jn) K
        (hcross i hi hl) (hnode i hi hl)).mp hnend
      change α jo (Real.sqrt (T - H.time i.succ)) ∈ f jo '' K at hmem
      rw [← hclocko] at hmem
      exact hjo ▸ hmem
  refine ⟨j, hstart, ?_, hnewer⟩
  have hjbad := (Finset.mem_filter.mp hj).2
  simp only [MapsTo, not_forall] at hjbad
  obtain ⟨t, ht, hout⟩ := hjbad
  refine ⟨t, ⟨?_, ht.2⟩, hout⟩
  exact lt_of_le_of_ne ht.1 (by intro heq; exact hout (heq.symm ▸ hstart))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v

variable (H : ObservedHistory.{u})

theorem exists_contMDiff_stage_prefix_lift_to_frontier {X : Type v}
    [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ x ∈ K, (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hpole : α ⟨last, hle, le_rfl⟩ u ∈ f ⟨last, hle, le_rfl⟩ '' K)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hexit : ∃ j, ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ (j : H.StageInterval first last) (t : ℝ) (β : ℝ → X),
      t ∈ Ico (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧
      EqOn (f j ∘ β) (α j) (Icc (H.regularizedStageStart T u j.val) t) ∧
      MapsTo β (Icc (H.regularizedStageStart T u j.val) t) K ∧
      MapsTo β (Ico (H.regularizedStageStart T u j.val) t) (interior K) ∧
      β t ∈ frontier K ∧
      (α j (H.regularizedStageStart T u j.val) ∈ f j '' interior K →
        H.regularizedStageStart T u j.val < t) ∧
      ∀ k : H.StageInterval first last, j.val < k.val → MapsTo (α k)
        (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)) (f k '' K) := by
  obtain ⟨j, hstart, hexitj, hnewer⟩ :=
    H.exists_last_nonconfined_stage first last hle f K hcross hu huv hupper hlower α hpole hnode hexit
  have hbad : ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K) := by
    intro hstay
    obtain ⟨t, ht, hout⟩ := hexitj
    exact hout (hstay ⟨ht.1.le, ht.2⟩)
  obtain ⟨t, β, ht, hβ, hproj, hstay, hbefore, hfront, hstrict⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiff_first_exit_lift_of_compact
      (f j) (hf j) (hinj j) K hK (α j) (hα j) hstart hbad
  exact ⟨j, t, β, ht, hβ, hproj, hstay, hbefore, hfront, hstrict, hnewer⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v

variable (H : ObservedHistory.{u})

theorem regularizedStageEnd_monotoneOn (T : ℝ) (j : Fin (H.eventCount + 1)) :
    MonotoneOn (fun v => H.regularizedStageEnd T v j) (Ici 0) := by
  intro u hu v hv huv
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_left
  apply max_le_max_right
  exact sub_le_sub_left ((sq_le_sq₀ hu hv).mpr huv) T

theorem exists_confined_history_prefix_ending_on_frontier {X : Type v}
    [TopologicalSpace X]
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j)) (K : Set X)
    (hK : ∀ j, IsClosed (f j '' K))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ x ∈ K, (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContinuousOn (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hpole : α ⟨last, hle, le_rfl⟩ u ∈ f ⟨last, hle, le_rfl⟩ '' interior K)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hexit : ∃ j, ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ (k : H.StageInterval first last) (w : ℝ), w ∈ Icc u v ∧
      T - w ^ 2 ∈ H.stageDomain k.val ∧ α k w ∈ f k '' frontier K ∧
      ∀ l : H.StageInterval first last, k.val ≤ l.val → MapsTo (α l)
        (Icc (H.regularizedStageStart T u l.val) (H.regularizedStageEnd T w l.val)) (f l '' K) := by
  have hpoleK : α ⟨last, hle, le_rfl⟩ u ∈ f ⟨last, hle, le_rfl⟩ '' K :=
    image_mono interior_subset hpole
  obtain ⟨j, hstart, hexitj, hnewer⟩ :=
    H.exists_last_nonconfined_stage first last hle f K hcross hu huv hupper hlower α hpoleK hnode hexit
  have hbad : ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K) := by
    intro hstay
    obtain ⟨t, ht, hout⟩ := hexitj
    exact hout (hstay ⟨ht.1.le, ht.2⟩)
  obtain ⟨w, hw, hstay, _, hfront, hstrict⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_Icc_of_mem_of_not_mapsTo
      (hK j) (hα j) hstart hbad
  obtain ⟨x, hxK, hx⟩ := hstay ⟨hw.1, le_rfl⟩
  have hxfront : x ∈ frontier K := by
    have hprefront : f j ⁻¹' frontier (f j '' K) = frontier K := by
      rw [(hf j).isOpenMap.preimage_frontier_eq_frontier_preimage (hf j).continuous,
        Set.preimage_image_eq K (hf j).injective]
    rw [← hprefront]
    change f j x ∈ frontier (f j '' K)
    exact hx.symm ▸ hfront
  have hbounds := H.regularizedStage_bounds hu huv hupper hlower j
  have huw : u ≤ w := hbounds.1.trans hw.1
  have hwv : w ≤ v := hw.2.le.trans hbounds.2.2
  have hw0 : 0 ≤ w := hu.trans huw
  have hend (l : H.StageInterval first last) :
      H.regularizedStageEnd T w l.val ≤ H.regularizedStageEnd T v l.val :=
    H.regularizedStageEnd_monotoneOn T l.val hw0 (hu.trans huv) hwv
  have hnewerPrefix (l : H.StageInterval first last) (hjl : j.val < l.val) :
      MapsTo (α l) (Icc (H.regularizedStageStart T u l.val) (H.regularizedStageEnd T w l.val))
        (f l '' K) := fun t ht => hnewer l hjl ⟨ht.1, ht.2.trans (hend l)⟩
  rcases hw.1.lt_or_eq with hstrictw | heq
  · have htail := H.mapsTo_regularizedStage_Ioo T u v j.val ⟨hstrictw, hw.2⟩
    refine ⟨j, w, ⟨huw, hwv⟩, htail, ⟨x, hxfront, hx⟩, ?_⟩
    intro l hjl
    rcases hjl.lt_or_eq with hlt | heql
    · exact hnewerPrefix l hlt
    · have hlj : l = j := Subtype.ext heql.symm
      subst l
      rw [H.regularizedStageEnd_eq_of_mem_stageDomain hw0 htail]
      exact hstay
  · have hjne : j.val ≠ last := by
      intro hjlast
      have hj' : j = ⟨last, hle, le_rfl⟩ := Subtype.ext hjlast
      have hpolej : α j (H.regularizedStageStart T u j.val) ∈ f j '' interior K := by
        subst j
        simpa only [H.regularizedStageStart_eq_of_mem_Icc hu hupper] using hpole
      exact (not_lt_of_ge heq.ge) (hstrict ((hf j).isOpenMap.image_interior_subset K hpolej))
    have hjlt : j.val < last := lt_of_le_of_ne j.property.2 hjne
    let i : Fin H.eventCount := ⟨j.val.val, by have := last.isLt; omega⟩
    have hicast : i.castSucc = j.val := Fin.ext rfl
    have hi : first ≤ i.castSucc := hicast.symm ▸ j.property.1
    have hl : i.succ ≤ last := by change j.val.val + 1 ≤ last.val; exact hjlt
    let jo : H.StageInterval first last := ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
    let jn : H.StageInterval first last := ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
    have hjo : jo = j := Subtype.ext hicast
    have hjn : j.val < jn.val := by simpa only [jn, ← hicast] using i.castSucc_lt_succ
    have hclocko : H.regularizedStageStart T u jo.val = Real.sqrt (T - H.time i.succ) :=
      H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
    have hwclock : w = Real.sqrt (T - H.time i.succ) := heq.symm.trans (by
      simpa only [hjo] using hclocko)
    have htime : T - w ^ 2 = H.time i.succ := by
      rw [hwclock]
      exact (H.event_clock_bounds hu huv hupper hlower i hi hl).2.2
    have htail : T - w ^ 2 ∈ H.stageDomain jn.val := by
      rw [htime]
      exact H.time_mem_stageDomain i.succ
    have heqo : f jo x = α jo w := hjo.symm ▸ hx
    obtain ⟨z, hzold, hzout⟩ := hnode i hi hl
    have hzold' : z.val.val = f jo x := by
      rw [← hwclock] at hzold
      exact hzold.trans heqo.symm
    have hzout' : (H.event i).oldOutput z = f jn x :=
      ((H.event i).oldOutput_eq_iff_of_regularCrossing z (hcross i hi hl x hxK)).mpr hzold'
    have heqn : f jn x = α jn w := by
      rw [← hwclock] at hzout
      exact hzout'.symm.trans hzout
    exact ⟨jn, w, ⟨huw, hwv⟩, htail, ⟨x, hxfront, heqn⟩,
      fun l hnl => hnewerPrefix l (hjn.trans_le hnl)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem sum_stageRegularizedAction_prefix_le_of_sum_le
    {first last : Fin (H.eventCount + 1)} {T u v B A : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t))
    (hsum : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ A)
    (k : H.StageInterval first last) {w : ℝ} (hw : w ∈ Icc u v)
    (hkw : T - w ^ 2 ∈ H.stageDomain k.val) :
    (∑ j : H.StageInterval k.val last,
      H.stageRegularizedAction j.val T (α ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) ≤
      A + (2 * B / 3) * (v ^ 3 - w ^ 3) := by
  classical
  have hle : first ≤ last := k.property.1.trans k.property.2
  let embed : H.StageInterval k.val last → H.StageInterval first last :=
    fun j => ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩
  have hembed : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun j : H.StageInterval first last => j.val) h
  let total (j : H.StageInterval first last) :=
    H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) +
      (2 * B / 3) * ((H.regularizedStageEnd T v j.val) ^ 3 - (H.regularizedStageStart T u j.val) ^ 3)
  let partialCost (j : H.StageInterval k.val last) :=
    H.stageRegularizedAction j.val T (α (embed j))
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) +
      (2 * B / 3) * ((H.regularizedStageEnd T w j.val) ^ 3 - (H.regularizedStageStart T u j.val) ^ 3)
  have hnonneg (j : H.StageInterval first last) : 0 ≤ total j := by
    have h := H.stageRegularizedAction_ge_of_scalar_lower_bound j.val T (α j)
      (H.regularizedStage_bounds hu huv hupper hlower j).2.1 (hscalar j) (hint j)
    dsimp only [total]
    linarith
  have hprefix (j : H.StageInterval k.val last) : partialCost j ≤ total (embed j) := by
    have hbounds := H.regularizedStage_bounds hu hw.1 hupper hkw j
    have hwhole := H.regularizedStage_bounds hu huv hupper hlower (embed j)
    have hend : H.regularizedStageEnd T w j.val ≤ H.regularizedStageEnd T v j.val := by
      apply Real.sqrt_le_sqrt
      apply sub_le_sub_left
      apply max_le_max_right
      exact sub_le_sub_left (pow_le_pow_left₀ (hu.trans hw.1) hw.2 2) T
    have hpre : IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α (embed j))) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) := by
      apply (hint (embed j)).mono_set
      rw [uIcc_of_le hbounds.2.1, uIcc_of_le hwhole.2.1]
      exact Icc_subset_Icc le_rfl hend
    have htail : IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α (embed j))) volume
        (H.regularizedStageEnd T w j.val) (H.regularizedStageEnd T v j.val) := by
      apply (hint (embed j)).mono_set
      rw [uIcc_of_le hend, uIcc_of_le hwhole.2.1]
      exact Icc_subset_Icc hbounds.2.1 le_rfl
    have htailbound := H.stageRegularizedAction_ge_of_scalar_lower_bound j.val T (α (embed j)) hend
      (fun t ht => hscalar (embed j) t ⟨hbounds.2.1.trans_lt ht.1, ht.2⟩) htail
    have hadd := intervalIntegral.integral_add_adjacent_intervals hpre htail
    change H.stageRegularizedAction j.val T (α (embed j)) _ _ +
      H.stageRegularizedAction j.val T (α (embed j)) _ _ =
      H.stageRegularizedAction j.val T (α (embed j)) _ _ at hadd
    dsimp only [partialCost, total, embed] at *
    linarith
  have hsumle : (∑ j : H.StageInterval k.val last, partialCost j) ≤
      ∑ j : H.StageInterval first last, total j := by
    calc
      _ ≤ ∑ j : H.StageInterval k.val last, total (embed j) := Finset.sum_le_sum (fun j _ => hprefix j)
      _ = ∑ j ∈ Finset.univ.image embed, total j := by
        rw [Finset.sum_image]
        exact fun a _ b _ h => hembed h
      _ ≤ ∑ j : H.StageInterval first last, total j :=
        Finset.sum_le_univ_sum_of_nonneg hnonneg
  have hfullweights := H.sum_regularizedStage_sub (fun t : ℝ => t ^ 3) hle hu huv hupper hlower
  have hpreweights := H.sum_regularizedStage_sub (fun t : ℝ => t ^ 3) k.property.2 hu hw.1 hupper hkw
  dsimp only [partialCost, total] at hsumle
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hpreweights, hfullweights] at hsumle
  change (∑ j : H.StageInterval k.val last, H.stageRegularizedAction j.val T (α (embed j))
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) ≤ _
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

variable {E H' X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  [TopologicalSpace X] [ChartedSpace H' X] [IsManifold I ∞ X]

private theorem riemannianEDistOf_le_sum_stage_energy_sqrt
    (g : SmoothRiemannianMetric I X) (T v : ℝ) (last : Fin (H.eventCount + 1)) :
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ last) (u : ℝ), 0 ≤ u → u ≤ v →
      T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) → T - v ^ 2 ∈ H.stageDomain first →
      ∀ β : H.StageInterval first last → ℝ → X,
      (∀ j, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) →
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        β ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
        β ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))) →
      riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v) ≤
        ENNReal.ofReal (∑ j : H.StageInterval first last,
          Real.sqrt (H.regularizedStageEnd T v j.val - H.regularizedStageStart T u j.val) *
          Real.sqrt (curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) := by
  induction last using Fin.induction with
  | zero =>
    intro first hle u hu huv hupper hlower β hβ _
    have hf : first = 0 := le_antisymm hle (Fin.zero_le _)
    subst first
    let j : H.StageInterval 0 0 := ⟨0, le_rfl, le_rfl⟩
    have hs := H.regularizedStageStart_eq_of_mem_Icc hu hupper
    have he := H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j) (Icc u v) := by simpa only [j, hs, he] using hβ j
    have hb := edistOf_le_energy g huv hc (integrableOn_inner_mfderiv_self_of_contMDiffOn g hc)
    simpa only [sum_stageInterval_self H 0, hs, he, j] using hb
  | succ i ih =>
    intro first hle u hu huv hupper hlower β hβ hnode
    by_cases hf : first = i.succ
    · subst first
      let j : H.StageInterval i.succ i.succ := ⟨i.succ, le_rfl, le_rfl⟩
      have hs := H.regularizedStageStart_eq_of_mem_Icc hu hupper
      have he := H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower
      have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j) (Icc u v) := by simpa only [j, hs, he] using hβ j
      have hb := edistOf_le_energy g huv hc (integrableOn_inner_mfderiv_self_of_contMDiffOn g hc)
      simpa only [sum_stageInterval_self H i.succ, hs, he, j] using hb
    have hfi : first ≤ i.castSucc := by
      change first.val ≤ i.val
      have hle' : first.val ≤ i.val + 1 := hle
      have hn : first.val ≠ i.val + 1 := fun h => hf (Fin.ext h)
      omega
    let w := Real.sqrt (T - H.time i.succ)
    have hw := H.event_clock_bounds hu huv hupper hlower i hfi le_rfl
    have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      rw [hw.2.2, H.stageEndTime_castSucc]
      exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
    let lo : H.StageInterval first i.castSucc → H.StageInterval first i.succ :=
      fun j => ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
    let βold := fun j : H.StageInterval first i.castSucc => β (lo j)
    have hstartOld (j : H.StageInterval first i.castSucc) :
        H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
      H.regularizedStageStart_eq_at_event_clock hupper i le_rfl j.val j.property.2
    have hβold (j : H.StageInterval first i.castSucc) :
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 (βold j)
          (Icc (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)) := by
      rw [hstartOld j]
      exact hβ (lo j)
    have hnodeOld (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hki : k.succ ≤ i.castSucc) :
        βold ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hki⟩ (Real.sqrt (T - H.time k.succ)) =
        βold ⟨k.succ, hkf.trans k.castSucc_le_succ, hki⟩ (Real.sqrt (T - H.time k.succ)) :=
      hnode k hkf (hki.trans i.castSucc_le_succ)
    have hOld := ih first hfi w (hu.trans hw.1) hw.2.1 huOld hlower βold hβold hnodeOld
    let jlast : H.StageInterval first i.succ := ⟨i.succ, hle, le_rfl⟩
    have hlastStart : H.regularizedStageStart T u jlast.val = u :=
      H.regularizedStageStart_eq_of_mem_Icc hu hupper
    have hlastEnd : H.regularizedStageEnd T v jlast.val = w :=
      H.regularizedStageEnd_succ_eq_event_clock hlower i hfi
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β jlast) (Icc u w) := by
      simpa only [hlastStart, hlastEnd] using hβ jlast
    have hHead := edistOf_le_energy g hw.1 hc (integrableOn_inner_mfderiv_self_of_contMDiffOn g hc)
    have hmatch : β jlast w = βold ⟨i.castSucc, hfi, le_rfl⟩ w := (hnode i hfi le_rfl).symm
    rw [← hmatch] at hOld
    change riemannianEDistOf g (β jlast u) (β ⟨first, le_rfl, hle⟩ v) ≤ _
    have hsum : (∑ j : H.StageInterval first i.succ,
        Real.sqrt (H.regularizedStageEnd T v j.val - H.regularizedStageStart T u j.val) *
        Real.sqrt (curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) =
      (∑ j : H.StageInterval first i.castSucc,
        Real.sqrt (H.regularizedStageEnd T v j.val - H.regularizedStageStart T w j.val) *
        Real.sqrt (curveEnergy g (βold j) (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val))) +
      Real.sqrt (w - u) * Real.sqrt (curveEnergy g (β jlast) u w) := by
      rw [sum_stageInterval_split H i hle i.castSucc_le_succ]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _
        rw [hstartOld j]
      · rw [sum_stageInterval_self H i.succ, hlastStart, hlastEnd]
    rw [hsum, ENNReal.ofReal_add
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact (riemannianEDistOf_triangle g (β jlast u) (β jlast w) (β ⟨first, le_rfl, hle⟩ v)).trans
      ((add_le_add hHead hOld).trans_eq (add_comm _ _))

theorem riemannianEDistOf_le_sqrt_sum_stage_curveEnergy
    (g : SmoothRiemannianMetric I X) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (β : H.StageInterval first last → ℝ → X)
    (hβ : ∀ j, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      β ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
      β ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))) :
    riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v) ≤
      ENNReal.ofReal (Real.sqrt (v - u) *
        Real.sqrt (∑ j : H.StageInterval first last,
          curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) := by
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (H.StageInterval first last))
    (fun j => Real.sqrt (H.regularizedStageEnd T v j.val - H.regularizedStageStart T u j.val))
    (fun j => Real.sqrt (curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
  have hlength : (∑ j : H.StageInterval first last,
      Real.sqrt (H.regularizedStageEnd T v j.val - H.regularizedStageStart T u j.val) ^ 2) = v - u := by
    calc
      _ = ∑ j : H.StageInterval first last, (H.regularizedStageEnd T v j.val - H.regularizedStageStart T u j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Real.sq_sqrt (sub_nonneg.mpr (H.regularizedStage_bounds hu huv hupper hlower j).2.1)
      _ = _ := H.sum_regularizedStage_sub id hle hu huv hupper hlower
  have henergy : (∑ j : H.StageInterval first last,
      Real.sqrt (curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ^ 2) =
        ∑ j : H.StageInterval first last, curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Real.sq_sqrt (curveEnergy_nonneg g (H.regularizedStage_bounds hu huv hupper hlower j).2.1)
  rw [hlength, henergy] at hcauchy
  exact (riemannianEDistOf_le_sum_stage_energy_sqrt H g T v last first hle u hu huv hupper hlower β hβ hnode).trans
    (ENNReal.ofReal_le_ofReal hcauchy)

theorem riemannianEDistOf_ne_top_of_stage_curve_chain
    (g : SmoothRiemannianMetric I X) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (β : H.StageInterval first last → ℝ → X)
    (hβ : ∀ j, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      β ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
      β ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))) :
    riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (H.riemannianEDistOf_le_sqrt_sum_stage_curveEnergy g hle hu huv hupper hlower β hβ hnode)

theorem riemannianEDistOf_toReal_sq_le_sum_stage_curveEnergy
    (g : SmoothRiemannianMetric I X) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (β : H.StageInterval first last → ℝ → X)
    (hβ : ∀ j, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      β ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
      β ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))) :
    (riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v)).toReal ^ 2 ≤
      (v - u) * ∑ j : H.StageInterval first last,
        curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  have hdist := H.riemannianEDistOf_le_sqrt_sum_stage_curveEnergy g hle hu huv hupper hlower β hβ hnode
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hreal
  have hsum : 0 ≤ ∑ j : H.StageInterval first last,
      curveEnergy g (β j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) :=
    Finset.sum_nonneg (fun j _ => curveEnergy_nonneg g (H.regularizedStage_bounds hu huv hupper hlower j).2.1)
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hreal
  simpa only [mul_pow, Real.sq_sqrt (sub_nonneg.mpr huv), Real.sq_sqrt hsum] using hsq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]

theorem exists_contMDiff_confined_prefix_lifts_to_frontier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ x : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (x : X) (hx : x ∈ interior K) (hpole : α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ x)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hexit : ∃ j, ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ (k : H.StageInterval first last) (w : ℝ), w ∈ Icc u v ∧ T - w ^ 2 ∈ H.stageDomain k.val ∧
      ∃ β : H.StageInterval k.val last → ℝ → X,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (β j)) ∧
        (∀ j, EqOn ((f ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩) ∘ β j)
          (α ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩)
          (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val))) ∧
        (∀ j, MapsTo (β j)
          (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) K) ∧
        β ⟨last, k.property.2, le_rfl⟩ u = x ∧ β ⟨k.val, le_rfl, k.property.2⟩ w ∈ frontier K ∧
        (∀ (i : Fin H.eventCount) (hi : k.val ≤ i.castSucc) (hl : i.succ ≤ last),
          β ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)) =
            β ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ))) := by
  have hemb (j : H.StageInterval first last) : _root_.Topology.IsOpenEmbedding (f j) :=
    .of_continuous_injective_isOpenMap (hf j).contMDiff.continuous (hinj j) (hf j).isOpenMap
  obtain ⟨k, w, hw, htail, hfront, hstay⟩ :=
    H.exists_confined_history_prefix_ending_on_frontier first last hle f hemb K
      (fun j => (hK.image (hf j).contMDiff.continuous).isClosed)
      (fun i hi hl z _ => hcross i hi hl z) hu huv hupper hlower α
      (fun j => (hα j).continuous.continuousOn) ⟨x, hx, hpole.symm⟩ hnode hexit
  let inc : H.StageInterval k.val last → H.StageInterval first last :=
    fun j => ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩
  let f' := fun j : H.StageInterval k.val last => f (inc j)
  let α' := fun j : H.StageInterval k.val last => α (inc j)
  obtain ⟨β, hβ, heq, hmatch⟩ := H.exists_contMDiff_stage_lifts_of_confined_curves k.val last f'
    (fun j => hf (inc j)) (fun j => hinj (inc j))
    (fun i hi hl z => hcross i (k.property.1.trans hi) hl z)
    hu hw.1 hupper htail α' (fun j => hα (inc j))
    (fun j t ht => image_subset_range _ _ (hstay (inc j) j.property.1 ht))
    (fun i hi hl => hnode i (k.property.1.trans hi) hl)
  have hb (j : H.StageInterval k.val last) := H.regularizedStage_bounds hu hw.1 hupper htail j
  refine ⟨k, w, hw, htail, β, hβ, heq, ?_, ?_, ?_, hmatch⟩
  · intro j t ht
    obtain ⟨y, hy, he⟩ := hstay (inc j) j.property.1 ht
    have hh := heq j ht
    exact (hinj (inc j) (hh.trans he.symm)) ▸ hy
  · apply hinj ⟨last, hle, le_rfl⟩
    have hh := heq ⟨last, k.property.2, le_rfl⟩ (show u ∈ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T w last) by
      rw [H.regularizedStageStart_eq_of_mem_Icc hu hupper]
      exact ⟨le_rfl, (hb ⟨last, k.property.2, le_rfl⟩).1.trans (hb ⟨last, k.property.2, le_rfl⟩).2.1⟩)
    exact hh.trans hpole
  · obtain ⟨y, hy, he⟩ := hfront
    have hh := heq ⟨k.val, le_rfl, k.property.2⟩ (show w ∈ Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val) by
      rw [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans hw.1) htail]
      exact ⟨(hb ⟨k.val, le_rfl, k.property.2⟩).2.1.trans (hb ⟨k.val, le_rfl, k.property.2⟩).2.2, le_rfl⟩)
    exact (hinj k (hh.trans he.symm)) ▸ hy

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type*}
  [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]

theorem sum_lRegularizedAction_ge_of_stage_curve_separation
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (g : SmoothRiemannianMetric ThreeModel X) {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) {T u v μ B r : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (β : H.StageInterval first last → ℝ → X)
    (hβ : ∀ j, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (β j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      β ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)) =
      β ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hmetric : ∀ j, ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      μ * g.inner (β j t) (lVelocity (β j) t) (lVelocity (β j) t) ≤
        (S.base.metric (T - t ^ 2)).inner (β j t) (lVelocity (β j) t) (lVelocity (β j) t))
    (hscalar : ∀ j, ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      -B ≤ S.scalar (T - t ^ 2) (β j t))
    (hint : ∀ j, IntervalIntegrable (lRegularizedLagrangian S T (β j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hsep : ENNReal.ofReal r ≤ riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v)) :
    μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3) ≤
      ∑ j : H.StageInterval first last, lRegularizedAction S T (β j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  have hfinite := H.riemannianEDistOf_ne_top_of_stage_curve_chain g hle hu huv.le hupper hlower β hβ hnode
  have hdist : r ≤ (riemannianEDistOf g (β ⟨last, hle, le_rfl⟩ u) (β ⟨first, le_rfl, hle⟩ v)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsep
  have henergy := (pow_le_pow_left₀ hr hdist 2).trans
    (H.riemannianEDistOf_toReal_sq_le_sum_stage_curveEnergy g hle hu huv.le hupper hlower β hβ hnode)
  have hkin : μ * r ^ 2 / (2 * (v - u)) ≤ μ / 2 *
      ∑ j : H.StageInterval first last, curveEnergy g (β j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v - u))).mpr
    nlinarith [mul_le_mul_of_nonneg_left henergy (div_nonneg hμ (by norm_num : (0 : ℝ) ≤ 2))]
  have hlower := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    lRegularizedAction_ge_reference_energy_sub_scalar_bound S T g (β j)
      (H.regularizedStage_bounds hu huv.le hupper hlower j).2.1
      (show IntervalIntegrable (fun t => g.inner (β j t) (lVelocity (β j) t) (lVelocity (β j) t)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) from by
          apply IntegrableOn.intervalIntegrable
          rw [uIcc_of_le (H.regularizedStage_bounds hu huv.le hupper hlower j).2.1]
          exact integrableOn_inner_mfderiv_self_of_contMDiffOn g (hβ j))
      (hmetric j) (hscalar j) (hint j))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    H.sum_regularizedStage_sub (fun t : ℝ => t ^ 3) hle hu huv.le hupper] at hlower
  · exact (sub_le_sub_right hkin _).trans hlower
  · assumption

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem sum_stageRegularizedAction_ge_of_leaves_common_compact_set
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ x : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j, ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t))
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z) (hpole : α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ x)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hexit : ∃ j, ¬ MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3) ≤
      ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  classical
  obtain ⟨k, w, hw, hkw, β, hβ, heq, hstay, hstart, hfrontEnd, hmatch⟩ :=
    H.exists_contMDiff_confined_prefix_lifts_to_frontier first last hle f hf hinj K hK hcross
      hu huv hupper hlower α hα x hx hpole hnode hexit
  let inc : H.StageInterval k.val last → H.StageInterval first last :=
    fun j => ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩
  let α' := fun j : H.StageInterval k.val last => α (inc j)
  have hb (j : H.StageInterval k.val last) := H.regularizedStage_bounds hu hw.1 hupper hkw j
  have hwb (j : H.StageInterval k.val last) := H.regularizedStage_bounds hu huv hupper hlower (inc j)
  have hend (j : H.StageInterval k.val last) : H.regularizedStageEnd T w j.val ≤ H.regularizedStageEnd T v j.val := by
    apply Real.sqrt_le_sqrt
    apply sub_le_sub_left
    apply max_le_max_right
    exact sub_le_sub_left (pow_le_pow_left₀ (hu.trans hw.1) hw.2 2) T
  have hsub (j : H.StageInterval k.val last) :
      Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) ⊆
        Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) :=
    fun _ ht => ⟨ht.1, ht.2.trans_le (hend j)⟩
  have hmet (j : H.StageInterval k.val last) (t : ℝ)
      (ht : t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) :
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f (inc j)) (hf (inc j)) :=
    hmetric (inc j) t (hsub j ht)
  have hfinite := H.riemannianEDistOf_ne_top_of_stage_curve_chain g k.property.2 hu hw.1 hupper hkw β
    (fun j => (hβ j).contMDiffOn) (fun i hi hl => (hmatch i hi hl).symm)
  have hsep : ENNReal.ofReal r ≤ riemannianEDistOf g
      (β ⟨last, k.property.2, le_rfl⟩ u) (β ⟨k.val, le_rfl, k.property.2⟩ w) := by
    rw [hstart]
    exact hfront _ hfrontEnd
  have hreal : r ≤ (riemannianEDistOf g
      (β ⟨last, k.property.2, le_rfl⟩ u) (β ⟨k.val, le_rfl, k.property.2⟩ w)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsep
  have henergy := (pow_le_pow_left₀ hr.le hreal 2).trans
    (H.riemannianEDistOf_toReal_sq_le_sum_stage_curveEnergy g k.property.2 hu hw.1 hupper hkw β
      (fun j => (hβ j).contMDiffOn) (fun i hi hl => (hmatch i hi hl).symm))
  have huw : u < w := by
    apply lt_of_le_of_ne hw.1
    intro hequal
    rw [← hequal, sub_self, zero_mul] at henergy
    exact (not_le_of_gt (sq_pos_of_pos hr)) henergy
  have hlag (j : H.StageInterval k.val last) :
      EqOn (lRegularizedLagrangian S T (β j)) (H.stageRegularizedLagrangian j.val T (α' j))
        (uIoo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) := by
    intro t ht
    rw [uIoo_of_le (hb j).2.1] at ht
    have hnear : f (inc j) ∘ β j =ᶠ[nhds t] α' j := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      exact heq j (Ioo_subset_Icc_self hr)
    have hv := hnear.self_of_nhds
    have hd := hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have he : H.stageRegularizedLagrangian j.val T (f (inc j) ∘ β j) t = H.stageRegularizedLagrangian j.val T (α' j) t := by
      unfold stageRegularizedLagrangian lVelocity
      rw [hv, hd]
    exact (H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val S (f (inc j)) (hf (inc j)) T
      ((hβ j).mdifferentiable one_ne_zero t) (hmet j t ht)).symm.trans he
  have hi (j : H.StageInterval k.val last) :
      IntervalIntegrable (lRegularizedLagrangian S T (β j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) := by
    have hh := (hint (inc j)).mono_set (show uIcc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) ⊆
        uIcc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le (hb j).2.1, uIcc_of_le (hwb j).2.1]
      exact Icc_subset_Icc le_rfl (hend j))
    exact hh.congr_uIoo (hlag j).symm
  have hsc (j : H.StageInterval k.val last) (t : ℝ)
      (ht : t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) :
      -B ≤ S.scalar (T - t ^ 2) (β j t) := by
    have hh := hscalar (inc j) t (hsub j ht)
    have hpj : f (inc j) (β j t) = α (inc j) t := heq j (Ioo_subset_Icc_self ht)
    unfold SolutionOn.scalar SolutionFamily.scalar
    rw [hmet j t ht, metricScalarAt_localPull]
    rwa [hpj]
  have hbar := H.sum_lRegularizedAction_ge_of_stage_curve_separation S g k.property.2 hu huw hμ hr.le hupper hkw β
    (fun j => (hβ j).contMDiffOn) (fun i hi hl => (hmatch i hi hl).symm)
    (fun j t ht => hcompare t ⟨(hb j).1.trans_lt ht.1, ht.2.trans_le ((hb j).2.2.trans hw.2)⟩
      (β j t) (hstay j (Ioo_subset_Icc_self ht)) (lVelocity (β j) t)) hsc hi hsep
  have hsum : (∑ j : H.StageInterval k.val last, lRegularizedAction S T (β j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) =
      ∑ j : H.StageInterval k.val last, H.stageRegularizedAction j.val T (α' j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) := by
    apply Finset.sum_congr rfl
    intro j _
    exact intervalIntegral.integral_congr_uIoo (hlag j)
  rw [hsum] at hbar
  have hbudget := H.sum_stageRegularizedAction_prefix_le_of_sum_le hu huv hupper hlower α hint hscalar le_rfl k hw hkw
  have hratio : μ * r ^ 2 / (2 * (v - u)) ≤ μ * r ^ 2 / (2 * (w - u)) :=
    div_le_div_of_nonneg_left (mul_nonneg hμ (sq_nonneg r)) (by positivity) (by linarith [hw.2])
  dsimp only [α', inc] at hbar
  linarith

theorem mapsTo_common_compact_set_of_sum_stageRegularizedAction_lt
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ x : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j, ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t))
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z) (hpole : α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ x)
    (hnode : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hact : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) <
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K) := by
  intro j
  by_contra hnot
  exact (not_lt_of_ge (H.sum_stageRegularizedAction_ge_of_leaves_common_compact_set first last hle
    f hf hinj K hK hcross hu huv hupper hlower S g hμ hr hmetric hcompare α hα hint hscalar
    x hx hfront hpole hnode ⟨j, hnot⟩)) hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
