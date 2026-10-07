import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceStep_S138
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapExclude_S133
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PrefixTrace_S106
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses

/-!
# CH12-S138, group 1b: the centre trace of a point, pointwise (tower level)

`centreTrace_S138`: on the tower history `H = sliceTowerHistory_CX2 s` of a regular slice, the backward trace `X`
of the endpoint `x0` down to the time `a = s.time - L` exists, and along it the scalar curvature is `≤ 4 C0 / ρ²`.
Template: `hsub86N_trace_S87` (`exists_trace_scalar_bound_S74`); the cap exclusion at the events is the delivered
`exists_regularCrossing_of_nc_S133` (cap clause `hcap` = hCapWin, scale clause `hscale` = `hscale_of_record_S105`,
`hno` = the `hnc` clause for the prefix trace of the partial trace `A`, see `exists_trace_scalar_bound_nc_S138`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem centreTrace_S138 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {Ctime : ℝ≥0}
    (hP2 : P2_O2 Hp Ctime) (s : RegularSlice F.observation) {T₀ θ Dc c₀ ρ L C0 : ℝ}
    (pp : CutoffParameters)
    (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
      T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp)
    (hc₀ : 0 < c₀) (hC0 : 1 ≤ C0) (hρ : 0 < ρ) (hρN : ρ ≤ Hp.parameters.neckRadius s.time)
    (hL0 : 0 ≤ L) (hLs : L ≤ s.time) (hLy : T₀ - θ ≤ s.time - L)
    (hLb : 2 * ((Ctime : ℝ) + 1) * L ≤ ρ ^ 2 / (4 * C0))
    (hLc : L * (4 * C0 / ρ ^ 2) ≤ c₀ * θ)
    (hcap : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dc + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z))
    (hscale : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
        (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dc + 1 →
        c₀ * ((records j hj).static b).neck.scale ≤
          metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
            (((records j hj).static b).window x))
    (x0 : ((sliceTowerHistory_CX2 s).stageAt (sliceTowerTime_CX2 s)).Carrier)
    (hx0 : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s)) (sliceTowerTime_CX2 s)) x0 ≤
        C0 / ρ ^ 2)
    (hnc : ¬ ∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) hl x0)
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius),
      B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
        ‖x.val‖ < Dc + 1 ∧
        s.time - (sliceHistoryR_O3 F s).time j.succ ≤
          θ * (((records j hj).static b).neck.scale)⁻¹) :
    ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (_ : (a : ℝ) = s.time - L)
      (hau : a ≤ sliceTowerTime_CX2 s)
      (X : BackwardPointTrace (sliceTowerHistory_CX2 s) ((sliceTowerHistory_CX2 s).activeStage a)
        ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s))
        ((sliceTowerHistory_CX2 s).activeStage_mono hau) x0),
      ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ sliceTowerTime_CX2 s),
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage w) w)
          (X.point ((sliceTowerHistory_CX2 s).activeStage w)
            ((sliceTowerHistory_CX2 s).activeStage_mono haw)
            ((sliceTowerHistory_CX2 s).activeStage_mono hwu)) ≤ 4 * C0 / ρ ^ 2 := by
  have hr2 : 0 < ρ ^ 2 := by positivity
  have hC0p : 0 < C0 := by linarith
  have hu0 : 0 < s.time := s.positive
  set Cb : ℝ := (Ctime : ℝ) + 1 with hCbdef
  have hCb : 0 < Cb := by positivity
  have hCbC : (Ctime : ℝ) ≤ Cb := by rw [hCbdef]; linarith
  set β : ℝ := ρ ^ 2 / (2 * C0) with hβdef
  have hβ : 0 < β := by positivity
  have hβM : β * (ρ ^ 2)⁻¹ < 1 := by
    rw [hβdef]; field_simp
    linarith
  have hβ2 : β / 2 = ρ ^ 2 / (4 * C0) := by rw [hβdef]; field_simp; ring
  let a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨s.time - L, by linarith, (sub_le_self _ hL0).trans (sliceTowerTime_CX2 s).property.2⟩
  have hau : a ≤ sliceTowerTime_CX2 s := show s.time - L ≤ s.time by linarith
  have hLeq : ((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (a : ℝ) = L := by
    change s.time - (s.time - L) = L; ring
  have hden : 0 < β - 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (a : ℝ)) := by
    rw [hLeq]; nlinarith [hLb, hβ2, hβ]
  have hdenw : ∀ w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon, a ≤ w → w ≤ sliceTowerTime_CX2 s →
      β / 2 ≤ β - 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (w : ℝ)) := by
    intro w haw hwu
    have h1 : ((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (w : ℝ) ≤ L := by
      have : (a : ℝ) ≤ w := haw
      linarith
    have h2 : 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (w : ℝ)) ≤ 2 * Cb * L :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [hLb, hβ2]
  have hS : ∀ w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon, a ≤ w → w ≤ sliceTowerTime_CX2 s →
      (β - 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (w : ℝ)))⁻¹ ≤ 4 * C0 / ρ ^ 2 := by
    intro w haw hwu
    calc (β - 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (w : ℝ)))⁻¹ ≤ (β / 2)⁻¹ :=
          inv_anti₀ (by positivity) (hdenw w haw hwu)
      _ = 4 * C0 / ρ ^ 2 := by rw [hβ2]; field_simp
  have hθfun : ∀ t : ℝ, t ≤ s.time → (Hp.parameters.neckRadius (max t 0) ^ 2)⁻¹ ≤ (ρ ^ 2)⁻¹ := by
    intro t ht
    have h := Hp.radius_antitone (Set.mem_Ici.mpr (le_max_right t 0)) (Set.mem_Ici.mpr hu0.le)
      (max_le ht hu0.le)
    exact inv_anti₀ hr2 (pow_le_pow_left₀ hρ.le (hρN.trans h) 2)
  have hreg : (sliceTowerHistory_CX2 s).time ((sliceTowerHistory_CX2 s).activeStage
      (sliceTowerTime_CX2 s)) < ((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) :=
    slice_precedingR_O3 F s
  have hx0' : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s)) (sliceTowerTime_CX2 s)) x0 <
        β⁻¹ := by
    refine hx0.trans_lt ?_
    rw [hβdef, inv_div, div_lt_div_iff₀ hr2 hr2]
    nlinarith [hr2, mul_pos hr2 hC0p]
  have hcross : ∀ i : Fin (sliceTowerHistory_CX2 s).eventCount,
      (sliceTowerHistory_CX2 s).activeStage a ≤ i.castSucc →
      ∀ hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s),
      ∀ A : BackwardPointTrace (sliceTowerHistory_CX2 s) i.succ
        ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s)) hl x0,
      metricScalarAt ((sliceTowerHistory_CX2 s).event i).outputMetric (A.point i.succ le_rfl hl) ≤
        (β - 2 * Cb * (((sliceTowerTime_CX2 s : Icc (0 : ℝ) _) : ℝ) - (a : ℝ)))⁻¹ →
      ∃ p' : ((sliceTowerHistory_CX2 s).stage i.castSucc).Carrier,
        ((sliceTowerHistory_CX2 s).event i).RegularCrossing p' (A.point i.succ le_rfl hl) := by
    intro i hf hl A hout
    have hij : i.val < (sliceHistoryR_O3 F s).eventCount :=
      Nat.lt_of_succ_le (Fin.le_iff_val_le_val.mp hl)
    let j : Fin (sliceHistoryR_O3 F s).eventCount := ⟨i.val, hij⟩
    have hlast : (sliceTowerHistory_CX2 s).time i.succ ≤ s.time :=
      (((sliceTowerHistory_CX2 s).time_strictMono.monotone hl).trans
        ((sliceTowerHistory_CX2 s).activeStage_time_le (sliceTowerTime_CX2 s)))
    have hlt : (a : ℝ) < (sliceTowerHistory_CX2 s).time i.succ := by
      by_contra hn
      rw [not_lt] at hn
      have h1 : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage a :=
        (sliceTowerHistory_CX2 s).le_activeStage a _ hn
      exact absurd (hf.trans_lt (Fin.castSucc_lt_succ (i := i))) (not_lt.mpr h1)
    have hjt : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ := by
      change T₀ - θ ≤ (sliceTowerHistory_CX2 s).time i.succ
      have : (a : ℝ) = s.time - L := rfl
      linarith
    have hSb : metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (A.point i.succ le_rfl hl) ≤ 4 * C0 / ρ ^ 2 :=
      hout.trans (hS a le_rfl hau)
    have hage0 : 0 ≤ s.time - (sliceHistoryR_O3 F s).time j.succ := by
      change 0 ≤ s.time - (sliceTowerHistory_CX2 s).time i.succ
      linarith
    have hage : (s.time - (sliceHistoryR_O3 F s).time j.succ) * (4 * C0 / ρ ^ 2) ≤ c₀ * θ := by
      refine le_trans ?_ hLc
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      change s.time - (sliceTowerHistory_CX2 s).time i.succ ≤ L
      have : (a : ℝ) = s.time - L := rfl
      linarith
    refine exists_regularCrossing_of_nc_S133 (H := (sliceHistoryR_O3 F s).toHistory) (j := j)
      (records j hjt) (Dc := Dc) (c₀ := c₀) (S := 4 * C0 / ρ ^ 2) (θ := θ) hc₀ hage0
      (hcap j hjt) (hscale j hjt) (A.point i.succ le_rfl hl) hSb hage ?_
    rintro ⟨b, x, hwx, hx, hag⟩
    apply hnc
    exact ⟨j, hjt, Fin.le_last _,
      prefixTrace_S106 (F.tower.history (sliceIndexR_O3 F s)) (sliceStageR_O3 F s) A j
        (Fin.le_iff_val_le_val.mpr le_rfl), b, x, hwx.symm, hx, hag⟩
  obtain ⟨X, hX⟩ := exists_trace_scalar_bound_nc_S138 (sliceTowerHistory_CX2 s) (C := Cb)
    (M := (ρ ^ 2)⁻¹) (β := β) (θ := fun t => (Hp.parameters.neckRadius (max t 0) ^ 2)⁻¹) hCb hβ hβM
    (fun i y t ht hlt => by
      have hmax : max t 0 = t := max_eq_left (((sliceTowerHistory_CX2 s).time_nonneg _).trans ht.1.le)
      simp only [hmax] at hlt
      refine (hP2.1 (sliceTowerIndex_CX2 s) i y t ht hlt).trans ?_
      exact mul_le_mul_of_nonneg_right hCbC (sq_nonneg _))
    (fun h y t ht hlt => by
      have hmax : max t 0 = t := max_eq_left (((sliceTowerHistory_CX2 s).time_nonneg _).trans ht.1.le)
      simp only [hmax] at hlt
      refine (hP2.2 (sliceTowerIndex_CX2 s) h y t ht hlt).trans ?_
      exact mul_le_mul_of_nonneg_right hCbC (sq_nonneg _))
    hau (fun t ht => hθfun t ht) hreg hden x0 hx0' hcross
  exact ⟨a, rfl, hau, X, fun w haw hwu => (hX w haw hwu).trans (hS w haw hwu)⟩

end GC.LongTime.Ch12
