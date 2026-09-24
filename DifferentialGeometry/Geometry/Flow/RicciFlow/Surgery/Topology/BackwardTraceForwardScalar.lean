import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingForwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
