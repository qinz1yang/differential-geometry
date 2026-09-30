import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

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

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore (G : P.IncomingSlab a s)
    {Ctime : ℝ≥0} {qcan q t : ℝ} (hq : 0 < q) (hqcan : qcan ≤ q) (hts : t < s)
    (hG : G.DerivativeBoundBefore Ctime qcan t) (y : P.Carrier) :
    LipschitzOnWith Ctime (fun v => (max q (G.flow.scalar v y))⁻¹) (Icc a t) :=
  lipschitzOnWith_inv_max_scalar_Icc G.equation hq (fun _ hv => ⟨hv.1, hv.2.trans_lt hts⟩) y
    (fun v hv hR => hG y v hv (hqcan.trans_lt hR))

theorem scalar_le_two_mul_of_derivativeBoundBefore (G : P.IncomingSlab a s)
    {Ctime : ℝ≥0} {qcan M t u v : ℝ} (y : P.Carrier)
    (hG : G.DerivativeBoundBefore Ctime qcan t) (hts : t < s)
    (hau : a ≤ u) (huv : u ≤ v) (hvt : v ≤ t)
    (hM : 0 < M) (hqcan : qcan ≤ M) (hscalar : G.flow.scalar t y ≤ M)
    (htime : Ctime * M * (t - u) ≤ 1 / 2) : G.flow.scalar v y ≤ 2 * M := by
  have hlip := G.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore hM hqcan hts hG y
  have hd := hlip.dist_le_mul v ⟨hau.trans huv, hvt⟩ t ⟨hau.trans (huv.trans hvt), le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm v t, abs_of_nonneg (sub_nonneg.mpr hvt)] at hd
  refine le_two_mul_of_abs_inv_max_sub_le hM hscalar hd ?_
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

end OrientedThreeStage.IncomingSlab

namespace BackwardPointTrace

variable {K : ObservedHistory.{u}}

private theorem lipschitzOnWith_inv_max_stageMetric_scalar (k : Fin (K.eventCount + 1))
    (x : (K.stage k).Carrier) {Ctime : ℝ≥0} {qcan q t : ℝ} (hq : 0 < q) (hqcan : qcan ≤ q)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hcurrent : ∀ i : Fin K.eventCount, i.castSucc = k →
      (K.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon, k = Fin.last K.eventCount →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t) :
    LipschitzOnWith Ctime (fun v => (max q (metricScalarAt (K.stageMetric k v) x))⁻¹)
      (Icc (K.time k) t) := by
  cases k using Fin.lastCases with
  | last =>
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · simp only [ObservedHistory.stageMetric_last_of_lt (h := h)]
      exact lipschitzOnWith_inv_max_scalar_Icc (K.finalSlab h).equation hq
        (fun _ hv => ⟨hv.1, hv.2.trans ht⟩) x
        (fun v hv hR => hfinal h rfl x v hv (hqcan.trans_lt hR))
    · simp only [ObservedHistory.stageMetric_last_of_le (not_lt.mp h)]
      exact (LipschitzWith.const _).lipschitzOnWith.weaken zero_le
  | cast i =>
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    exact (K.event i).incoming.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore hq hqcan
      (hnext i rfl) (hcurrent i rfl) x

theorem inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore
    {first k : Fin (K.eventCount + 1)} {hle : first ≤ k} {x : (K.stage k).Carrier}
    (A : BackwardPointTrace K first k hle x) {Ctime : ℝ≥0} {qcan q t : ℝ}
    (hq : 0 < q) (hqcan : qcan ≤ q) (htk : K.time k ≤ t)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hslabs : ∀ i : Fin K.eventCount, i.castSucc < k →
      (K.event i).incoming.DerivativeBoundBefore Ctime qcan (K.time i.succ))
    (hcurrent : ∀ i : Fin K.eventCount, i.castSucc = k →
      (K.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon, k = Fin.last K.eventCount →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (j : Fin (K.eventCount + 1)) (hfj : first ≤ j) (hjk : j ≤ k) {v : ℝ}
    (hjv : K.time j ≤ v) (hvnext : ∀ i : Fin K.eventCount, j = i.castSucc → v < K.time i.succ)
    (hvt : v ≤ t) :
    |(max q (metricScalarAt (K.stageMetric j v) (A.point j hfj hjk)))⁻¹ -
      (max q (metricScalarAt (K.stageMetric k t) x))⁻¹| ≤ Ctime * (t - v) := by
  have hlip := lipschitzOnWith_inv_max_stageMetric_scalar k x hq hqcan hnext ht hcurrent hfinal
  rcases hjk.lt_or_eq with hlt | heq
  · have hjl : j ≠ Fin.last K.eventCount := ne_of_lt (hlt.trans_le (Fin.le_last k))
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
    have hsucc : j'.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hlt
    have hstep := A.inv_max_scalar_sub_endpoint_le_at_time hq
      (fun i hf hl w hw hR => hslabs i (i.castSucc_lt_succ.trans_le hl) _ w hw
        (hqcan.trans_lt hR)) j' hfj hsucc ⟨hjv, hvnext j' rfl⟩
    have htop := hlip.dist_le_mul (K.time k) ⟨le_rfl, htk⟩ t ⟨htk, le_rfl⟩
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (K.time k) t,
      abs_of_nonneg (sub_nonneg.mpr htk)] at htop
    simp only [K.stageMetric_initial] at htop
    rw [ObservedHistory.stageMetric_castSucc_apply]
    have htri := abs_sub_le
      ((max q ((K.event j').incoming.flow.scalar v (A.point j'.castSucc hfj hjk)))⁻¹)
      ((max q (metricScalarAt (K.initialMetric k) x))⁻¹)
      ((max q (metricScalarAt (K.stageMetric k t) x))⁻¹)
    change |(max q ((K.event j').incoming.flow.scalar v (A.point j'.castSucc hfj hjk)))⁻¹ -
      (max q (metricScalarAt (K.stageMetric k t) x))⁻¹| ≤ _
    nlinarith
  · subst heq
    have hpt : A.point j hfj hjk = x := A.endpoint_eq
    rw [hpt]
    have hd := hlip.dist_le_mul v ⟨hjv, hvt⟩ t ⟨htk, le_rfl⟩
    rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm v t,
      abs_of_nonneg (sub_nonneg.mpr hvt)] at hd

end BackwardPointTrace

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem lt_time_succ_of_activeStage_eq (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

theorem scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds
    {Ctime : ℝ≥0} {qcan M : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M := by
  intro v huv hvt
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore hM hqcan
    (H.toHistory.activeStage_time_le t)
    (fun i hi => H.lt_time_succ_of_activeStage_eq t i hi) t.2.2 hslabs hcurrent hfinal
    (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
    (H.toHistory.activeStage_mono hvt) (H.toHistory.activeStage_time_le v)
    (fun i hi => H.lt_time_succ_of_activeStage_eq v i hi) hvt
  refine le_two_mul_of_abs_inv_max_sub_le hM hscalar hrec ?_
  have huv' : (u : ℝ) ≤ v := huv
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

theorem extendHorizon_scalar_le_two_mul_of_backwardPointTrace
    {T s : ℝ} (hT : H.horizon ≤ T) (hlT : H.time (Fin.last H.eventCount) < T) (hTs : T < s)
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {Ctime : ℝ≥0} {qcan M : ℝ}
    {u t : Icc (0 : ℝ) (H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.horizon}
    (hut : u ≤ t)
    {p : ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.stage
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace (H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage u)
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage t)
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc =
      (H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hterminal : G.DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt
      ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.stageMetric
        ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) (H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.horizon)
      (huv : u ≤ v) (hvt : v ≤ t),
      metricScalarAt ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.stageMetric
        ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage v) v)
        (A.point ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage v)
          ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage_mono huv)
          ((H.extendHorizon T hT (G.closedPrefix T hlT hTs) hG).toHistory.activeStage_mono hvt)) ≤
        2 * M :=
  scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds _ hut A hslabs hcurrent
    (fun _ _ y v hv hR => hterminal y v hv hR) hM hqcan hscalar htime

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
