import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem le_two_mul_of_abs_inv_max_sub_le {M R Rt Δ : ℝ} {C : ℝ≥0} (hM : 0 < M)
    (hRt : Rt ≤ M) (hrec : |(max M R)⁻¹ - (max M Rt)⁻¹| ≤ C * Δ)
    (htime : C * M * Δ ≤ 1 / 2) : R ≤ 2 * M := by
  rw [max_eq_left hRt] at hrec
  have hlow := (abs_le.mp hrec).1
  have hhalf : C * Δ ≤ (2 * M)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * M)]
    nlinarith
  have htwo : M⁻¹ = 2 * (2 * M)⁻¹ := by field_simp
  have hinv : (2 * M)⁻¹ ≤ (max M R)⁻¹ := by linarith
  exact (le_max_right M R).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * M) (hM.trans_le (le_max_left M R))).mp hinv)

private theorem lipschitzOnWith_inv_max_scalar_Icc {P : OrientedThreeStage.{u}}
    {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn S) {a b q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hsub : Icc a b ⊆ D.carrier) (x : P.Carrier)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2) :
    LipschitzOnWith C (fun v => (max q (S.scalar v x))⁻¹) (Icc a b) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    (r' := fun v => derivWithin (fun w => S.scalar w x) (Iic v) v) hq
  · intro v hv
    exact (hS.scalarTime hv hsub x).continuousWithinAt
  · intro v hv _
    have hd : DifferentiableAt ℝ (fun w => S.scalar w x) v :=
      (hS.scalarTime (K := Ioo a b) hv (Ioo_subset_Icc_self.trans hsub) x).differentiableAt
        (Ioo_mem_nhds hv.1 hv.2)
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic v)]
    exact hd.hasDerivAt
  · exact hbound

namespace BackwardPointTrace

variable {K : ObservedHistory.{u}}

/-- The first reciprocal piece starts at the actual cut clock; subsequent pieces
are the original trace and use only later derivative data. -/
private theorem inv_max_scalar_sub_endpoint_le_on_time_window
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {v : ℝ} (hv : v ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hbound : ∀ j : Fin H.eventCount, ∀ hfj : i.castSucc ≤ j.castSucc,
      ∀ hjl : j.succ ≤ last, ∀ s ∈ Ioo (H.time j.castSucc) (H.time j.succ), v ≤ s →
      q < (H.event j).incoming.flow.scalar s
        (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl)) →
      |derivWithin (fun w => (H.event j).incoming.flow.scalar w
        (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl))) (Iic s) s| ≤
        C * (H.event j).incoming.flow.scalar s
          (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl)) ^ 2) :
    |(max q ((H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹ -
      (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹| ≤
        C * (H.time last - v) := by
  let B := A.restrictFirst (hf.trans i.castSucc_lt_succ.le) hl
  have htail := inv_max_scalar_sub_endpoint_le last i.succ hl endpoint B hq
    (fun j hj hjl s hs => hbound j (i.castSucc_lt_succ.le.trans hj) hjl s hs
      ((hv.2.le.trans (H.time_strictMono.monotone hj)).trans hs.1.le))
  have hcross := A.crossing i hf hl
  let p : (H.event i).incoming.terminalRegularOpen :=
    ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
      hcross.mem_terminalRegularRegion (H.event i)⟩
  have hstep := (H.event i).terminal.inv_max_scalar_sub_terminal_le_on_time_window
    (H.event i).incoming hq p hv.1 hv.2
    (fun s hs => hbound i le_rfl hl s ⟨hv.1.trans_lt hs.1, hs.2⟩ hs.1.le)
    (show v ∈ Ico v (H.time i.succ) from ⟨le_rfl, hv.2⟩)
  have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) (p := p) hcross
  rw [H.event_output i] at heq
  rw [heq] at hstep
  have htri := abs_sub_le
    ((max q ((H.event i).incoming.flow.scalar v p.val))⁻¹)
    ((max q (metricScalarAt (H.initialMetric i.succ)
      (A.point i.succ (hf.trans i.castSucc_lt_succ.le) hl)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹)
  dsimp only [B, restrictFirst] at htail
  nlinarith

/-- Scalar control along an existing trace from a derivative estimate only on its
actual time interval, with no derivative demanded at surgery births or the horizon. -/
theorem scalar_le_two_mul_of_time_local_derivative_control
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {M : ℝ} (hM : 0 < M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      M < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) ^ 2)
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤ 2 * M := by
  have hstageBound (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
      (hfj : H.activeStage a ≤ j) (hjl : j ≤ H.activeStage t) :
      H.time j < (v : ℝ) → (v : ℝ) < H.horizon →
      M < metricScalarAt (H.stageMetric j v) (A.point j hfj hjl) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric j s) (A.point j hfj hjl))
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric j v) (A.point j hfj hjl) ^ 2 := by
    subst j
    exact hbound v hav hvt
  have hvalue_eq (j k : Fin (H.eventCount + 1)) (hjk : j = k)
      (hfj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t)
      (hfk : H.activeStage a ≤ k) (hkt : k ≤ H.activeStage t) (w : ℝ) :
      metricScalarAt (H.stageMetric j w) (A.point j hfj hjt) =
        metricScalarAt (H.stageMetric k w) (A.point k hfk hkt) := by
    subst k
    rfl
  let c : ℝ := max (a : ℝ) (H.time (H.activeStage t))
  have hac : (a : ℝ) ≤ c := le_max_left _ _
  have hbc : H.time (H.activeStage t) ≤ c := le_max_right _ _
  have hct : c ≤ (t : ℝ) := max_le hat (H.activeStage_time_le t)
  have hlip : LipschitzOnWith Ctime
      (fun w => (max M (metricScalarAt (H.stageMetric (H.activeStage t) w) y))⁻¹)
      (Icc c (t : ℝ)) := by
    by_cases hage : H.time (H.activeStage t) < (t : ℝ)
    · let G := H.closedPrefixAt t hage
      have hfun : (fun w => G.flow.scalar w y) =
          (fun w => metricScalarAt (H.stageMetric (H.activeStage t) w) y) := by
        funext w
        change metricScalarAt (G.flow.base.metric w) y = _
        rw [H.closedPrefixAt_metric]
      have hh := lipschitzOnWith_inv_max_scalar_Icc G.equation hM
        (a := c) (b := (t : ℝ)) (fun w hw => ⟨hbc.trans hw.1, hw.2⟩) y
        (fun w hw hRw => by
          have haw : (a : ℝ) ≤ w := hac.trans hw.1.le
          let wI : Icc (0 : ℝ) H.horizon := ⟨w, a.2.1.trans haw, hw.2.le.trans t.2.2⟩
          have hactive : H.activeStage wI = H.activeStage t :=
            le_antisymm (H.activeStage_mono (show wI ≤ t from hw.2.le))
              (H.le_activeStage wI _ (hbc.trans hw.1.le))
          change M < (fun s => G.flow.scalar s y) w at hRw
          rw [hfun] at hRw
          have hb := hstageBound wI haw hw.2.le (H.activeStage t) hactive
            (H.activeStage_mono hat) le_rfl (hbc.trans_lt hw.1) (hw.2.trans_le t.2.2)
          have hd := hb (by simpa only [A.endpoint_eq] using hRw)
          change |derivWithin (fun s => G.flow.scalar s y) (Iic w) w| ≤
            Ctime * ((fun s => G.flow.scalar s y) w) ^ 2
          rw [hfun]
          simpa only [A.endpoint_eq] using hd)
      change LipschitzOnWith Ctime (fun w => (max M ((fun s => G.flow.scalar s y) w))⁻¹)
        (Icc c (t : ℝ)) at hh
      rw [hfun] at hh
      exact hh
    · have hzero : H.time (H.activeStage t) = (t : ℝ) :=
        le_antisymm (H.activeStage_time_le t) (not_lt.mp hage)
      have hc : c = (t : ℝ) := by dsimp [c]; rw [hzero]; exact max_eq_right hat
      rw [hc, Icc_self]
      intro u hu w hw
      have hu' : u = (t : ℝ) := mem_singleton_iff.mp hu
      have hw' : w = (t : ℝ) := mem_singleton_iff.mp hw
      subst u
      subst w
      simp only [edist_self, mul_zero, le_refl]
  intro v hav hvt
  have hrec :
      |(max M (metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))))⁻¹ -
        (max M (metricScalarAt (H.stageMetric (H.activeStage t) t) y))⁻¹| ≤
        Ctime * ((t : ℝ) - v) := by
    rcases (H.activeStage_mono hvt).lt_or_eq with hlt | heq
    · have hjlast : H.activeStage v ≠ Fin.last H.eventCount :=
        ne_of_lt (hlt.trans_le (Fin.le_last _))
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hjlast
      have hf : H.activeStage a ≤ i.castSucc := by rw [hi]; exact H.activeStage_mono hav
      have hil : i.castSucc < H.activeStage t := by simpa only [hi] using hlt
      have hl : i.succ ≤ H.activeStage t := Fin.castSucc_lt_iff_succ_le.mp hil
      have hvdom : (v : ℝ) ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        have hd := H.activeStage_mem v
        rw [← hi] at hd
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hd
      have hstep := inv_max_scalar_sub_endpoint_le_on_time_window A hM i hf hl hvdom
        (fun j hfj hjl w hw hvw hRw => by
          have haw : (a : ℝ) ≤ w := (show (a : ℝ) ≤ v from hav).trans hvw
          have hwt : w ≤ (t : ℝ) :=
            hw.2.le.trans ((H.time_strictMono.monotone hjl).trans (H.activeStage_time_le t))
          let wI : Icc (0 : ℝ) H.horizon := ⟨w, a.2.1.trans haw, hwt.trans t.2.2⟩
          have hactive : H.activeStage wI = j.castSucc :=
            (H.mem_stageDomain_iff wI j.castSucc).mp (by
              simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
                (show w ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hw.1.le, hw.2⟩))
          have hb := hstageBound wI haw hwt j.castSucc hactive (hf.trans hfj)
            (j.castSucc_lt_succ.le.trans hjl) hw.1
            (hw.2.trans_le (H.time_le_horizon_at j.succ))
          simp only [ObservedHistory.stageMetric_castSucc_apply] at hb
          exact hb hRw)
      have hab : (a : ℝ) ≤ H.time (H.activeStage t) :=
        (show (a : ℝ) ≤ v from hav).trans (hvdom.2.le.trans (H.time_strictMono.monotone hl))
      have hc : c = H.time (H.activeStage t) := max_eq_right hab
      have htop := hlip.dist_le_mul (H.time (H.activeStage t))
        ⟨hc.le, H.activeStage_time_le t⟩ (t : ℝ) ⟨hct, le_rfl⟩
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (H.time (H.activeStage t)) (t : ℝ),
        abs_of_nonneg (sub_nonneg.mpr (H.activeStage_time_le t))] at htop
      simp only [H.stageMetric_initial] at htop
      rw [hvalue_eq _ _ hi.symm (H.activeStage_mono hav) (H.activeStage_mono hvt)
        hf (i.castSucc_lt_succ.le.trans hl) v, ObservedHistory.stageMetric_castSucc_apply]
      have htri := abs_sub_le
        ((max M ((H.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹)
        ((max M (metricScalarAt (H.initialMetric (H.activeStage t)) y))⁻¹)
        ((max M (metricScalarAt (H.stageMetric (H.activeStage t) t) y))⁻¹)
      change |(max M ((H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹ - _| ≤ _
      nlinarith
    · have hvbirth : H.time (H.activeStage t) ≤ (v : ℝ) := by
        rw [← heq]
        exact H.activeStage_time_le v
      have hvc : c ≤ (v : ℝ) := max_le hav hvbirth
      have hh := hlip.dist_le_mul (v : ℝ) ⟨hvc, hvt⟩ (t : ℝ) ⟨hct, le_rfl⟩
      rw [hvalue_eq _ _ heq (H.activeStage_mono hav) (H.activeStage_mono hvt)
        (H.activeStage_mono hat) le_rfl v, A.endpoint_eq]
      simpa only [Real.dist_eq, abs_sub_comm (v : ℝ) (t : ℝ),
        abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ t from hvt))] using hh
  refine le_two_mul_of_abs_inv_max_sub_le hM hscalar hrec ?_
  have hav' : (a : ℝ) ≤ v := hav
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

end BackwardPointTrace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
