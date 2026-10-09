import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingForwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
universe u
variable {H : ObservedHistory.{u}}

theorem scalar_le_two_mul_initial_of_time_sub_le
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (htime : 2 * C * (H.time last - H.time first) * Q ≤ 1) :
    metricScalarAt (H.initialMetric last) endpoint ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := inv_max_scalar_sub_endpoint_le last first hle endpoint A hq hbound
  have hinv : Q⁻¹ ≤ (max q (metricScalarAt (H.initialMetric first)
      (A.point first le_rfl hle)))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * (H.time last - H.time first) ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlow : (2 * Q)⁻¹ ≤ (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹ := by
    have hab := (abs_le.mp hrec).2
    rw [htwo] at hinv
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hq.trans_le (le_max_left _ _))).mp hlow)

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem scalar_incoming_terminal_le_two_mul_initial_of_time_sub_le
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (htime : 2 * C * (s - H.time first) * Q ≤ 1) :
    metricScalarAt L.metric x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := A.inv_max_scalar_initial_sub_incoming_terminal_le G L hinit x hq hderiv hfinal
  have hinv : Q⁻¹ ≤ (max q (metricScalarAt (H.initialMetric first)
      (A.point first le_rfl hle)))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * (s - H.time first) ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlow : (2 * Q)⁻¹ ≤ (max q (metricScalarAt L.metric x))⁻¹ := by
    have hab := (abs_le.mp hrec).2
    rw [htwo] at hinv
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hq.trans_le (le_max_left _ _))).mp hlow)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

end

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}
variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem scalar_incoming_le_two_mul_initial_of_time_sub_le
    (G : (H.stage last).IncomingSlab (H.time last) s)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle x)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    {t : ℝ} (ht : t ∈ Ico (H.time last) s)
    (htime : 2 * C * (t - H.time first) * Q ≤ 1) :
    G.flow.scalar t x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpast := A.inv_max_scalar_sub_endpoint_le last first hle x hq hderiv
  have htail := (G.lipschitzOnWith_inv_max_scalar_at hq x hfinal).dist_le_mul
    (H.time last) ⟨le_rfl, G.lt⟩ t ht
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (H.time last) t,
    abs_of_nonneg (sub_nonneg.mpr ht.1)] at htail
  change |(max q (metricScalarAt (G.flow.base.metric (H.time last)) x))⁻¹ -
    (max q (G.flow.scalar t x))⁻¹| ≤ _ at htail
  rw [hinit] at htail
  have htri := abs_sub_le
    ((max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric last) x))⁻¹)
    ((max q (G.flow.scalar t x))⁻¹)
  have hrec : |(max q (metricScalarAt (H.initialMetric first)
      (A.point first le_rfl hle)))⁻¹ - (max q (G.flow.scalar t x))⁻¹| ≤
      C * (t - H.time first) := by linarith
  have hinv : Q⁻¹ ≤ (max q (metricScalarAt (H.initialMetric first)
      (A.point first le_rfl hle)))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * (t - H.time first) ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlow : (2 * Q)⁻¹ ≤ (max q (G.flow.scalar t x))⁻¹ := by
    have hab := (abs_le.mp hrec).2
    rw [htwo] at hinv
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hq.trans_le (le_max_left _ _))).mp hlow)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

end

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}
variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem mem_incoming_terminalRegularRegion_of_initial_scalar_bound
    (G : (H.stage last).IncomingSlab (H.time last) s)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle x)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    {U : Set (H.stage last).Carrier} (hU : IsOpen U) (hx : x ∈ U)
    (hfinal : ∀ y ∈ U, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (htime : 8 * C * (s - H.time first) * Q ≤ 1) :
    x ∈ G.terminalRegularRegion := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpast : H.time first ≤ H.time last := H.time_strictMono.monotone hle
  have hlength : 0 ≤ s - H.time first := by linarith [G.lt]
  have hstep : 2 * C * (H.time last - H.time first) * Q ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [G.lt] :
        H.time last - H.time first ≤ s - H.time first) (by positivity : 0 ≤ 2 * (C : ℝ))) hQ.le
    nlinarith [mul_nonneg C.coe_nonneg (mul_nonneg hlength hQ.le)]
  have hstart := A.scalar_le_two_mul_initial_of_time_sub_le last first hle x hq hqQ
    hderiv hscalar hstep
  have hstartG : G.flow.scalar (H.time last) x ≤ 2 * Q := by
    change metricScalarAt (G.flow.base.metric (H.time last)) x ≤ 2 * Q
    rw [hinit]
    exact hstart
  apply G.mem_terminalRegularRegion_of_initial_scalar_bound
    (A := 2 * Q) (by positivity) (by linarith : q ≤ 2 * Q) hU hfinal hx hstartG
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hpast s) (by positivity : 0 ≤ 8 * (C : ℝ))) hQ.le
  nlinarith

section

open Filter

variable {endpoint : (H.stage last).Carrier}

theorem scalar_le_two_mul_initial_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (htime : 2 * C * (t - H.time first) * Q ≤ 1) :
    (H.event j).incoming.flow.scalar t
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ≤ 2 * Q := by
  let B := A.restrictLast hf (j.castSucc_lt_succ.le.trans hl)
  exact B.scalar_incoming_le_two_mul_initial_of_time_sub_le
    (H.event j).incoming (H.event_initial j) _ hq hqQ
    (fun k hk hkj => hbound k hk (hkj.trans (j.castSucc_lt_succ.le.trans hl)))
    (hbound j hf hl) hscalar ht htime

theorem extended_riemannNorm_le_of_earlier_scalar_bound_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q a₀ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j ≤ k)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.castSucc ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans hf) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) ^ 2)
    {τ : ℝ} (hτ : τ ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hscalar : (H.event j).incoming.flow.scalar τ
      (A.point j.castSucc hj (Fin.castSucc_le_castSucc_iff.mpr hjk |>.trans hk)) ≤ Q)
    (y : (H.event k).incoming.terminalRegularOpen)
    (hy : y.val = A.point k.castSucc (hj.trans (Fin.castSucc_le_castSucc_iff.mpr hjk)) hk)
    (hpinch : ∀ t ∈ Ico (H.time k.castSucc) (H.time k.succ), τ ≤ t →
      InFixedHamiltonIveyRegion ((H.event k).incoming.flow.base.metric t) a₀ y.val)
    (htime : 2 * C * (H.time k.succ - τ) * Q ≤ 1) :
    ∀ t ∈ Icc (H.time k.castSucc) (H.time k.succ), τ ≤ t →
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((H.event k).terminal.extendedMetric t) y 4
        (metricRm04At ((H.event k).terminal.extendedMetric t) y)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpast (t : ℝ) (ht : t ∈ Ico (H.time k.castSucc) (H.time k.succ)) (hτt : τ ≤ t) :
      (H.event k).incoming.riemannNorm t y.val ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
    have hs := A.scalar_le_two_mul_of_earlier_scalar_le_at_time hq j k hj hjk hk
      hbound hτ ht hτt hqQ hscalar
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le _) (by positivity)) hQ.le).trans htime)
    rw [← hy] at hs
    have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion
      ((H.event k).incoming.flow.base.metric t) y.val ha₀ le_rfl (hpinch t ht hτt) hs
    rw [max_eq_left (by positivity : 0 ≤ 2 * Q), show 2 * Q / 2 = Q by ring] at hr
    exact hr
  intro t ht hτt
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · rw [(H.event k).terminal.extendedMetric_before hlt,
      DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
    exact hpast t ⟨ht.1, hlt⟩ hτt
  · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
    apply le_of_tendsto ((H.event k).terminal.tendsto_riemannNorm y)
    have hτk : τ < H.time k.succ := hτ.2.trans_le
      (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr hjk))
    filter_upwards [Ioo_mem_nhdsLT (H.event k).incoming.lt, Ioo_mem_nhdsLT hτk] with t ht htτ
    exact hpast t ⟨ht.1.le, ht.2⟩ htτ.1.le

theorem extended_riemannNorm_le_of_initial_scalar_bound
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q a₀ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (y : (H.event j).incoming.terminalRegularOpen)
    (hy : y.val = A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))
    (hpinch : ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
      InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ y.val)
    (htime : 2 * C * (H.time j.succ - H.time first) * Q ≤ 1) :
    ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((H.event j).terminal.extendedMetric t) y 4
        (metricRm04At ((H.event j).terminal.extendedMetric t) y)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let j₀ : Fin H.eventCount := ⟨first.val, lt_of_le_of_lt (show first.val ≤ j.val from hf) j.isLt⟩
  have he : j₀.castSucc = first := Fin.ext rfl
  have hj₀ : j₀ ≤ j := by change first.val ≤ j.val; exact hf
  have hbound₀ : ∀ l : Fin H.eventCount, ∀ hf' : j₀.castSucc ≤ l.castSucc,
      ∀ hl' : l.castSucc ≤ j.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t
        (A.point l.castSucc (he.symm.le.trans hf') (hl'.trans (j.castSucc_lt_succ.le.trans hl))) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (he.symm.le.trans hf') (hl'.trans (j.castSucc_lt_succ.le.trans hl)))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t
          (A.point l.castSucc (he.symm.le.trans hf') (hl'.trans (j.castSucc_lt_succ.le.trans hl))) ^ 2 := by
    intro l hf' hl'
    exact hbound l (he.symm.le.trans hf') ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hl')).trans hl)
  have hτ : H.time first ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ) := by
    rw [← he]
    exact ⟨le_rfl, H.time_strictMono j₀.castSucc_lt_succ⟩
  have hscalar₀ : (H.event j₀).incoming.flow.scalar (H.time first)
      (A.point j₀.castSucc he.symm.le (Fin.castSucc_le_castSucc_iff.mpr hj₀ |>.trans
        (j.castSucc_lt_succ.le.trans hl))) ≤ Q := by
    change metricScalarAt ((H.event j₀).incoming.flow.base.metric (H.time first)) _ ≤ Q
    rw [← congrArg H.time he, H.event_initial]
    exact hscalar
  intro t ht
  exact A.extended_riemannNorm_le_of_earlier_scalar_bound_at_time hq hqQ ha₀
    j₀ j he.symm.le hj₀ (j.castSucc_lt_succ.le.trans hl) hbound₀ hτ hscalar₀ y hy
    (fun s hs _ => hpinch s hs) htime t ht ((H.time_strictMono.monotone hf).trans ht.1)


end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace


set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
  {hle : first ≤ last} {s : ℝ}

private theorem half_le_of_inv_max_sub_inv_le
    {q R Q d : ℝ} (hq : 0 < q) (hQ : 2 * q < Q)
    (hrec : |(max q R)⁻¹ - Q⁻¹| ≤ d) (hbudget : d * Q ≤ 1) : Q / 2 ≤ R := by
  have hQpos : 0 < Q := by linarith
  have hd : d ≤ Q⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hQpos).mpr hbudget
  have hinv : (max q R)⁻¹ ≤ (Q / 2)⁻¹ := by
    have h := (abs_le.mp hrec).2
    have heq : (Q / 2)⁻¹ = 2 * Q⁻¹ := by field_simp
    rw [heq]
    linarith
  have hmax : Q / 2 ≤ max q R :=
    (inv_le_inv₀ (hq.trans_le (le_max_left _ _)) (by positivity)).mp hinv
  rcases le_total q R with hqR | hRq
  · rwa [max_eq_right hqR] at hmax
  · rw [max_eq_left hRq] at hmax
    linarith

variable (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
  (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
  {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
  (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
    ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
    q < (H.event j).incoming.flow.scalar t
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
    |derivWithin (fun v => (H.event j).incoming.flow.scalar v
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
      C * (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
  (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
    |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)

include hinit hq hderiv hfinal in
theorem half_terminal_scalar_le_initial_of_time_sub_le
    (hthreshold : 2 * q < metricScalarAt L.metric x)
    (htime : C * (s - H.time first) * metricScalarAt L.metric x ≤ 1) :
    metricScalarAt L.metric x / 2 ≤
      metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) := by
  have hrec := A.inv_max_scalar_initial_sub_incoming_terminal_le G L hinit x hq hderiv hfinal
  rw [max_eq_right (by linarith : q ≤ metricScalarAt L.metric x)] at hrec
  exact half_le_of_inv_max_sub_inv_le hq hthreshold hrec htime

include hinit hq hderiv hfinal in
theorem terminal_scalar_div_le_birth_scale_of_time_sub_le
    {C₀ qcap : ℝ} (hC₀ : 0 < C₀)
    (hbirth : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ C₀ * qcap)
    (hthreshold : 2 * q < metricScalarAt L.metric x)
    (htime : C * (s - H.time first) * metricScalarAt L.metric x ≤ 1) :
    metricScalarAt L.metric x / (2 * C₀) ≤ qcap ∧ q < C₀ * qcap := by
  have hhalf := A.half_terminal_scalar_le_initial_of_time_sub_le G L hinit x hq
    hderiv hfinal hthreshold htime
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * C₀)).mpr
    nlinarith
  · linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
universe u
variable {H : ObservedHistory.{u}}

theorem scalar_incoming_le_two_mul_of_scalar_bound_at_time
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle x)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.succ ≤ last)
    {q Q τ : ℝ} {C : ℝ≥0} (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C*G.flow.scalar t x ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : (H.event j₀).incoming.flow.scalar τ
      (A.point j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀)) ≤ Q)
    {t : ℝ} (ht : t ∈ Ico (H.time last) s) (htime : 2*C*(t-τ)*Q ≤ 1) :
    G.flow.scalar t x ≤ 2*Q := by
  let B := A.restrictFirst hfirst (j₀.castSucc_lt_succ.le.trans hj₀)
  have hpast := B.inv_max_scalar_sub_endpoint_le_at_time hQ
    (fun j hf hl t ht hR => hbound j hf hl t ht (hqQ.trans_lt hR)) j₀ le_rfl hj₀ hτ
  have htail := (G.lipschitzOnWith_inv_max_scalar_at hQ x (fun t ht hR => hfinal t ht (hqQ.trans_lt hR))).dist_le_mul
    (H.time last) ⟨le_rfl,G.lt⟩ t ht
  rw [Real.dist_eq,Real.dist_eq,abs_sub_comm (H.time last) t,
    abs_of_nonneg (sub_nonneg.mpr ht.1)] at htail
  change |(max Q (metricScalarAt (G.flow.base.metric (H.time last)) x))⁻¹-
    (max Q (G.flow.scalar t x))⁻¹| ≤ _ at htail
  rw [hinit] at htail
  have htri := abs_sub_le
    ((max Q ((H.event j₀).incoming.flow.scalar τ
      (A.point j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀))))⁻¹)
    ((max Q (metricScalarAt (H.initialMetric last) x))⁻¹)
    ((max Q (G.flow.scalar t x))⁻¹)
  have hrec : |(max Q ((H.event j₀).incoming.flow.scalar τ
      (A.point j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀))))⁻¹-
      (max Q (G.flow.scalar t x))⁻¹| ≤ C*(t-τ) := by
    dsimp only [B, BackwardPointTrace.restrictFirst] at hpast
    linarith
  have hinv : Q⁻¹ ≤ (max Q ((H.event j₀).incoming.flow.scalar τ
      (A.point j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀))))⁻¹ :=
    inv_anti₀ (hQ.trans_le (le_max_left _ _)) (max_le le_rfl hscalar)
  have hhalf : C*(t-τ) ≤ (2*Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2*Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2*(2*Q)⁻¹ := by field_simp
  have hlow : (2*Q)⁻¹ ≤ (max Q (G.flow.scalar t x))⁻¹ := by
    have hab := (abs_le.mp hrec).2
    rw [htwo] at hinv
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hQ.trans_le (le_max_left _ _))).mp hlow)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
