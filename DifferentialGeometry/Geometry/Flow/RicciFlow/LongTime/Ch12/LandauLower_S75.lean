import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Interpolation_S66

set_option autoImplicit false

/-!
# CH12-S75 / G1a: Landau–Kolmogorov with a first-order lower-order term (pure real analysis)

In the chart route for the one-step manifold Landau inequality (`hstep`), the second derivative of a
coordinate component `u(σ) = S(c σ)(e_I)` along a chart line is
`u'' = (∇²S)(…) + Γ * (∇S) + (∂Γ + Γ Γ) * S`, i.e. `‖u''‖ ≤ M2 + c ‖u'‖` with `M2 = β + c' α`.
`landau_1d_S66` does not accept a bound of this shape (its `M2` is a constant), so the `‖u'‖`-term
is absorbed here:  `‖u'‖ ≤ 8 √(M0 M2) + 8 M0 / ℓ + 16 c M0`.
-/

noncomputable section
open Set Metric
namespace GC.LongTime.Ch12

section OneD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Landau with absorbed first-order term.**  If `‖f‖ ≤ M0` and `‖f''‖ ≤ M2 + c ‖f'‖` on
`Icc a b`, then `‖f'‖ ≤ 8 √(M0 M2) + 8 M0 / (b - a) + 16 c M0` on `Icc a b` (all points, endpoints
included). -/
theorem landau_1d_lower_S75 {f f' f'' : ℝ → E} {a b M0 M2 c : ℝ} (hab : a < b) (hM2 : 0 ≤ M2)
    (hc : 0 ≤ c)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivWithinAt f' (f'' x) (Icc a b) x)
    (h0 : ∀ x ∈ Icc a b, ‖f x‖ ≤ M0) (h2 : ∀ x ∈ Icc a b, ‖f'' x‖ ≤ M2 + c * ‖f' x‖) :
    ∀ x ∈ Icc a b, ‖f' x‖ ≤ 8 * √(M0 * M2) + 8 * M0 / (b - a) + 16 * c * M0 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (h0 a ha)
  have hcont : ContinuousOn (fun x => ‖f' x‖) (Icc a b) :=
    (show ContinuousOn f' (Icc a b) from fun x hx => (hf' x hx).continuousWithinAt).norm
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ha⟩ hcont
  set S : ℝ := ‖f' xs‖ with hS
  have hSle : ∀ x ∈ Icc a b, ‖f' x‖ ≤ S := fun x hx => hmax hx
  have hS0 : 0 ≤ S := norm_nonneg _
  have h2' : ∀ x ∈ Icc a b, ‖f'' x‖ ≤ M2 + c * S := fun x hx =>
    (h2 x hx).trans (by nlinarith [hSle x hx])
  have key := landau_1d_S66 hab hf hf' h0 h2' xs hxs
  have hx1 : 0 ≤ M0 * M2 := mul_nonneg hM0 hM2
  have hx2 : 0 ≤ M0 * (c * S) := mul_nonneg hM0 (mul_nonneg hc hS0)
  have hsub : √(M0 * (M2 + c * S)) ≤ √(M0 * M2) + √(M0 * (c * S)) := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 := Real.sq_sqrt hx1
    have e2 := Real.sq_sqrt hx2
    nlinarith [Real.sqrt_nonneg (M0 * M2), Real.sqrt_nonneg (M0 * (c * S)),
      mul_nonneg (Real.sqrt_nonneg (M0 * M2)) (Real.sqrt_nonneg (M0 * (c * S)))]
  set u : ℝ := √(M0 * (c * S)) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = M0 * (c * S) := Real.sq_sqrt hx2
  have hamgm : 4 * u ≤ S / 2 + 8 * (M0 * c) := by
    by_contra hcon
    rw [not_le] at hcon
    have hpos : 0 ≤ S / 2 + 8 * (M0 * c) := by positivity
    nlinarith [sq_nonneg (S / 2 - 8 * (M0 * c)), hcon, hpos, hu2]
  have hdiv : 0 ≤ M0 / (b - a) := div_nonneg hM0 (sub_pos.2 hab).le
  have hS' : S ≤ 4 * (√(M0 * M2) + u + M0 / (b - a)) := by
    have : ‖f' xs‖ ≤ 4 * (√(M0 * (M2 + c * S)) + M0 / (b - a)) := key
    linarith
  have hfin : S ≤ 8 * √(M0 * M2) + 8 * M0 / (b - a) + 16 * c * M0 := by
    have : 8 * M0 / (b - a) = 8 * (M0 / (b - a)) := by ring
    rw [this]
    nlinarith [hamgm, hS']
  intro x hx
  exact (hSle x hx).trans hfin

end OneD

end GC.LongTime.Ch12
