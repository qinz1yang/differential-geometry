import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# CX-SPINE G6: scalar control on one closed time window at a fixed point

This localizes the proof of the private
`scalar_le_two_mul_of_derivativeBoundBefore_at` in
`Surgery/Topology/SlabGradientScalarControl.lean`, lines 174–204.
Source SHA-256:
`980833eac1fe618e5dcec4e0c4104cc4fffe261e67f5819638e569e1b7bf9119`.

The only derivative input is at the given point on `Ioo v t`, above `qcan`.
Continuity and actual differentiability come from `G.equation.scalarTime`.
The public clipped-reciprocal Lipschitz lemma is applied on `Icc v t` itself.
No global `DerivativeBoundBefore`, spatial Good supply, or footprint is assumed
or produced. Both window endpoints are included in the conclusion.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

/-- A local quadratic time-derivative bound and a short enough window propagate
the terminal scalar upper bound to every point of the closed time interval. -/
theorem scalar_le_two_mul_on_window_CXSP
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {Ctime : ℝ≥0} {qcan K v t : ℝ} (y : P.Carrier)
    (hav : a ≤ v) (hvt : v ≤ t) (hts : t < s)
    (hderiv : ∀ w ∈ Ioo v t, qcan < G.flow.scalar w y →
      |derivWithin (fun z => G.flow.scalar z y) (Iic w) w| ≤
        Ctime * G.flow.scalar w y ^ 2)
    (hK : 0 < K) (hqcan : qcan ≤ K) (hscalar : G.flow.scalar t y ≤ K)
    (htime : Ctime * K * (t - v) ≤ 1 / 2) :
    ∀ w ∈ Icc v t, G.flow.scalar w y ≤ 2 * K := by
  have hsub : Icc v t ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun _ hw => ⟨hav.trans hw.1, hw.2.trans_lt hts⟩
  have hlip : LipschitzOnWith Ctime
      (fun w => (max K (G.flow.scalar w y))⁻¹) (Icc v t) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
      (r' := fun w => derivWithin (fun z => G.flow.scalar z y) (Iic w) w) hK
    · intro w hw
      exact (G.equation.scalarTime hw hsub y).continuousWithinAt
    · intro w hw _
      have hd : DifferentiableAt ℝ (fun z => G.flow.scalar z y) w :=
        (G.equation.scalarTime (K := Ioo v t) hw (Ioo_subset_Icc_self.trans hsub)
          y).differentiableAt (Ioo_mem_nhds hw.1 hw.2)
      rw [hd.derivWithin (uniqueDiffWithinAt_Iic w)]
      exact hd.hasDerivAt
    · exact fun w hw hR => hderiv w hw (hqcan.trans_lt hR)
  intro w hw
  have hd := hlip.dist_le_mul w hw t ⟨hvt, le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm w t,
    abs_of_nonneg (sub_nonneg.mpr hw.2), max_eq_left hscalar] at hd
  have hlow := (abs_le.mp hd).1
  have htimew : (Ctime : ℝ) * K * (t - w) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hw.1 t)
      (mul_nonneg Ctime.coe_nonneg hK.le)).trans htime
  have hhalf : (Ctime : ℝ) * (t - w) ≤ (2 * K)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * K)]
    nlinarith
  have htwo : K⁻¹ = 2 * (2 * K)⁻¹ := by field_simp
  have hinv : (2 * K)⁻¹ ≤ (max K (G.flow.scalar w y))⁻¹ := by linarith
  exact (le_max_right K _).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * K)
      (hK.trans_le (le_max_left K _))).mp hinv)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
