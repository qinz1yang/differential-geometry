import DifferentialGeometry.Geometry.Riemannian.Length.LengthFunctional

set_option linter.unusedSectionVars false

/-!
# Energy functional for curves on a Riemannian manifold

For a smooth Riemannian manifold `(M, g)` and a curve `γ : ℝ → M`, this file
defines the *energy*

```
energy g γ a b = (1/2) ∫_a^b g(γ̇(t), γ̇(t)) dt
```

i.e., half the integral of the squared `g`-speed of `γ`. The principal API
consists of nonnegativity of the energy on `a ≤ b`, the energy of a constant
curve being zero, and the Cauchy–Schwarz inequality relating the length to
the energy:

```
length γ a b ^ 2 ≤ 2 (b - a) · energy g γ a b.
```

The Cauchy–Schwarz step is proved by expanding `0 ≤ ∫_a^b (speed − c)²` for
the optimal real constant `c = (∫ speed) / (b − a)` and rearranging the
non-degenerate case, with the degenerate case `a = b` handled separately.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Length

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Energy functional -/

/-- The energy of a curve segment `γ |_{[a, b]}` with respect to a smooth
Riemannian metric `g`: half the integral of the squared `g`-speed over the
parametrising interval. -/
def energy (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in a..b, g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)

@[simp] lemma energy_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    energy (I := I) g γ a b =
      (1 / 2) *
        ∫ t in a..b, g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := rfl

/-! ### Speed-squared rewrite -/

/-- The energy density is equivalently expressed as the square of the speed.
This is the algebraic identity at the heart of the Cauchy–Schwarz inequality
relating length and energy. -/
lemma energy_eq_half_integral_speed_sq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    energy (I := I) g γ a b = (1 / 2) * ∫ t in a..b, (speed (I := I) g γ t) ^ 2 := by
  unfold energy
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro t _
  exact (speed_sq_eq (I := I) g γ t).symm

/-! ## Continuity / integrability of the squared speed -/

/-- The squared speed of a `C¹` curve is continuous in `t`. -/
theorem speed_sq_continuous
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous (fun t : ℝ => (speed (I := I) g γ t) ^ 2) :=
  (speed_continuous (I := I) g hγ).pow 2

/-- Interval-integrability of the squared speed of a `C¹` curve. -/
theorem speed_sq_intervalIntegrable
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (speed (I := I) g γ t) ^ 2)
      MeasureTheory.volume a b :=
  (speed_sq_continuous (I := I) g hγ).intervalIntegrable a b

/-- Continuity of `t ↦ g.inner (γ t) (γ̇ t) (γ̇ t)` for a `C¹` curve `γ`. This
is the speed-squared expressed in its inner-product form. -/
theorem inner_velocity_velocity_continuous
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous (fun t : ℝ =>
      g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)) := by
  have hsq := speed_sq_continuous (I := I) g hγ
  refine hsq.congr ?_
  intro t
  exact speed_sq_eq (I := I) g γ t

/-- Interval-integrability of `t ↦ g.inner (γ t) (γ̇ t) (γ̇ t)` for a `C¹`
curve `γ`. -/
theorem inner_velocity_velocity_intervalIntegrable
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t))
      MeasureTheory.volume a b :=
  (inner_velocity_velocity_continuous (I := I) g hγ).intervalIntegrable a b

/-! ## Nonneg integrand: the inner product `⟨γ̇, γ̇⟩_g` is pointwise nonneg -/

/-- The squared-velocity inner product is pointwise nonnegative. -/
lemma inner_velocity_velocity_nonneg
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := by
  classical
  by_cases hv : velocity (I := I) γ t = 0
  · rw [hv]
    have hmap : g.inner (γ t) (0 : TangentSpace I (γ t)) =
        (0 : TangentSpace I (γ t) →L[ℝ] ℝ) := map_zero _
    rw [hmap]
    rfl
  · exact le_of_lt (g.pos (γ t) _ hv)

/-! ### Headline: energy is nonneg -/

/-- For `a ≤ b`, the energy of `γ` over `[a, b]` is nonnegative. The proof
uses pointwise nonnegativity of `⟨γ̇, γ̇⟩_g` and
`intervalIntegral.integral_nonneg`; the `ContMDiff` hypothesis on `γ` is
retained for uniformity with the rest of the energy API. -/
theorem energy_nonneg [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ energy (I := I) g γ a b := by
  unfold energy
  have h_int_nonneg :
      0 ≤ ∫ t in a..b,
        g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := by
    refine intervalIntegral.integral_nonneg hab ?_
    intro u _
    exact inner_velocity_velocity_nonneg (I := I) g γ u
  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact mul_nonneg h_half_nonneg h_int_nonneg

/-! ### Trivial endpoint and orientation identities -/

/-- The energy of any curve over a degenerate interval `[a, a]` is zero. -/
theorem energy_self (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    energy (I := I) g γ a a = 0 := by
  unfold energy
  rw [intervalIntegral.integral_same]
  ring

/-- Swapping the bounds of the energy integral flips its sign. -/
theorem energy_swap (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    energy (I := I) g γ a b = - energy (I := I) g γ b a := by
  unfold energy
  rw [intervalIntegral.integral_symm b a]
  ring

/-! ### Headline: energy at a constant curve is zero -/

/-- The energy of a constant curve is zero on every interval. -/
theorem energy_const (g : SmoothRiemannianMetric I M) (p : M) (a b : ℝ) :
    energy (I := I) g (fun _ : ℝ => p) a b = 0 := by
  unfold energy
  have hint :
      ∫ t in a..b, g.inner ((fun _ : ℝ => p) t)
          (velocity (I := I) (fun _ : ℝ => p) t)
          (velocity (I := I) (fun _ : ℝ => p) t) =
        ∫ _ in a..b, (0 : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    change g.inner ((fun _ : ℝ => p) u)
        (velocity (I := I) (fun _ : ℝ => p) u)
        (velocity (I := I) (fun _ : ℝ => p) u) = (0 : ℝ)
    have hvel : velocity (I := I) (fun _ : ℝ => p) u = 0 :=
      Geodesic.velocity_const (I := I) p u
    rw [hvel]
    have hmap : g.inner ((fun _ : ℝ => p) u) (0 : TangentSpace I p) =
        (0 : TangentSpace I p →L[ℝ] ℝ) := map_zero _
    rw [hmap]
    rfl
  rw [hint]
  simp [intervalIntegral.integral_zero]

/-! ## Cauchy–Schwarz: length² ≤ 2(b − a) · energy

The proof rewrites both sides in terms of `f = speed g γ` and reduces to the
elementary inequality

```
(∫_a^b f)^2 ≤ (b - a) · ∫_a^b f^2  (for `a ≤ b` and `f` integrable on `[a, b]`).
```

This is the Cauchy–Schwarz inequality for the inner product on `L²([a, b])`
paired against the constant function `1`. We prove it by expanding the
non-negative integral `∫(f − c)^2` for the optimal `c = (∫f)/(b − a)`.
-/

namespace Internal

/-- Auxiliary expansion: for any interval-integrable `f`, the squared
deviation `(f − c)^2 = f^2 − 2c·f + c^2` integrates by linearity.

The result statement uses `intervalIntegral` with `MeasureTheory.volume`,
which is the canonical convention used by `length` and `energy`. -/
private lemma integral_sub_const_sq_expand
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) MeasureTheory.volume a b)
    (c : ℝ) :
    ∫ t in a..b, (f t - c) ^ 2 =
      (∫ t in a..b, (f t) ^ 2) - 2 * c * (∫ t in a..b, f t) + c ^ 2 * (b - a) := by
  have h_expand : ∀ t : ℝ,
      (f t - c) ^ 2 = (f t) ^ 2 - 2 * c * f t + c ^ 2 := by
    intro t; ring
  -- Rewrite the integrand pointwise.
  have h_rw :
      ∫ t in a..b, (f t - c) ^ 2 =
        ∫ t in a..b, ((f t) ^ 2 - 2 * c * f t + c ^ 2) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    exact h_expand u
  -- Split as a sum of three integrals.
  have h_cf : IntervalIntegrable (fun t => 2 * c * f t) MeasureTheory.volume a b := by
    simpa using hf.const_mul (2 * c)
  have h_sub_int :
      IntervalIntegrable (fun t => (f t) ^ 2 - 2 * c * f t)
        MeasureTheory.volume a b := hf2.sub h_cf
  have h_const_int : IntervalIntegrable (fun _ : ℝ => (c : ℝ) ^ 2)
      MeasureTheory.volume a b := intervalIntegrable_const
  -- First split: ∫(f² − 2c·f + c²) = ∫(f² − 2c·f) + ∫c².
  rw [h_rw,
    intervalIntegral.integral_add h_sub_int h_const_int,
    intervalIntegral.integral_sub hf2 h_cf]
  -- Now compute each piece.
  have h_mul_int :
      ∫ t in a..b, 2 * c * f t = 2 * c * (∫ t in a..b, f t) :=
    intervalIntegral.integral_const_mul (2 * c) f
  have h_const_eval :
      ∫ _ in a..b, (c : ℝ) ^ 2 = (b - a) * c ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [h_mul_int, h_const_eval]
  ring

/-- Cauchy–Schwarz inequality for interval integrals against the constant
function `1`: for any interval-integrable `f` and `a ≤ b`,

```
(∫_a^b f)^2 ≤ (b − a) · ∫_a^b f^2.
```

The proof handles the degenerate case `a = b` separately, and in the
non-degenerate case `a < b` it sets `c = (∫f)/(b − a)` in the trivially
non-negative integral `∫(f − c)^2` and rearranges. -/
private lemma integral_sq_le_diff_mul_integral_sq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) MeasureTheory.volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · -- Degenerate case `a = b`: both sides are zero.
    subst hab_eq
    simp [intervalIntegral.integral_same]
  · -- Non-degenerate case `a < b`.
    have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
    have hba_ne : (b - a) ≠ 0 := ne_of_gt hba_pos
    -- The mean value of `f` over `[a, b]`.
    set μf : ℝ := (∫ t in a..b, f t) / (b - a)
    -- ∫(f − μf)² ≥ 0 pointwise via `sq_nonneg`.
    have h_nonneg : (0 : ℝ) ≤ ∫ t in a..b, (f t - μf) ^ 2 := by
      refine intervalIntegral.integral_nonneg hab ?_
      intro u _
      exact sq_nonneg _
    -- Expand the squared-deviation integral.
    have h_expand :
        ∫ t in a..b, (f t - μf) ^ 2 =
          (∫ t in a..b, (f t) ^ 2) -
            2 * μf * (∫ t in a..b, f t) + μf ^ 2 * (b - a) :=
      integral_sub_const_sq_expand (a := a) (b := b) hf hf2 μf
    -- Substitute `μf = (∫f) / (b − a)` and simplify.
    have h_simp :
        (∫ t in a..b, (f t) ^ 2) -
          2 * μf * (∫ t in a..b, f t) + μf ^ 2 * (b - a) =
          (∫ t in a..b, (f t) ^ 2) - ((∫ t in a..b, f t) ^ 2) / (b - a) := by
      change (∫ t in a..b, (f t) ^ 2) -
          2 * ((∫ t in a..b, f t) / (b - a)) * (∫ t in a..b, f t) +
          ((∫ t in a..b, f t) / (b - a)) ^ 2 * (b - a) =
            (∫ t in a..b, (f t) ^ 2) - ((∫ t in a..b, f t) ^ 2) / (b - a)
      field_simp
      ring
    rw [h_simp] at h_expand
    -- Conclude `(∫f)² / (b − a) ≤ ∫f²`, hence `(∫f)² ≤ (b − a) · ∫f²`.
    have h_div_le :
        (∫ t in a..b, f t) ^ 2 / (b - a) ≤ ∫ t in a..b, (f t) ^ 2 := by
      have h_ineq := h_nonneg
      rw [h_expand] at h_ineq
      linarith
    -- Multiply both sides by `(b - a) > 0`.
    have h_mul := (div_le_iff₀ hba_pos).mp h_div_le
    -- `(∫f)² ≤ (∫f²) * (b - a)`. Rewrite to match goal.
    have : (∫ t in a..b, f t) ^ 2 ≤ (∫ t in a..b, (f t) ^ 2) * (b - a) := h_mul
    linarith

end Internal

/-! ### Headline: length² ≤ 2 (b − a) energy -/

/-- **Cauchy–Schwarz inequality for length and energy.** For any `C¹` curve
`γ : ℝ → M` and any `a ≤ b`, the length and energy of `γ` over `[a, b]`
satisfy

```
(length g γ a b)^2 ≤ 2 (b - a) · energy g γ a b.
```

Equivalently, equality `length^2 = 2 (b - a) · energy` holds iff the speed
of `γ` is essentially constant on `[a, b]`, the parametrisation that
makes `γ` an extremal of the energy. -/
theorem length_sq_le_two_mul_diff_mul_energy [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) :
    (length (I := I) g γ a b) ^ 2 ≤ 2 * (b - a) * energy (I := I) g γ a b := by
  -- Rewrite the energy via the squared speed.
  rw [energy_eq_half_integral_speed_sq (I := I) g γ a b]
  -- Set `f = speed g γ`.
  set f : ℝ → ℝ := speed (I := I) g γ with hf_def
  -- `length = ∫_a^b f`.
  have h_length : length (I := I) g γ a b = ∫ t in a..b, f t := by
    unfold length
    rfl
  rw [h_length]
  -- Integrability hypotheses.
  have hf_int : IntervalIntegrable f MeasureTheory.volume a b :=
    speed_intervalIntegrable (I := I) g hγ a b
  have hf2_int :
      IntervalIntegrable (fun t : ℝ => (f t) ^ 2) MeasureTheory.volume a b :=
    speed_sq_intervalIntegrable (I := I) g hγ a b
  -- Apply the Cauchy–Schwarz step.
  have h_CS :
      (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 :=
    Internal.integral_sq_le_diff_mul_integral_sq hab hf_int hf2_int
  -- The goal is `(∫f)^2 ≤ 2 (b - a) · (1 / 2) ∫f^2 = (b - a) · ∫f^2`.
  -- A direct linear arithmetic step closes the goal.
  have h_eq : 2 * (b - a) * ((1 / 2) * ∫ t in a..b, (f t) ^ 2) =
      (b - a) * ∫ t in a..b, (f t) ^ 2 := by ring
  rw [h_eq]
  exact h_CS

/-! ### Energy of a constant-speed curve

If the speed of `γ` is the constant `c ≥ 0` on every parameter `t`, then the
energy over `[a, b]` (with `a ≤ b`) is `(1/2) · c² · (b - a)`. This is the
energy analogue of `length_eq_speed_mul_of_constSpeed`. -/

/-- For a `C¹` curve with constant speed `c ≥ 0`, the energy over `[a, b]` is
`(1/2) · c² · (b - a)`. -/
theorem energy_of_const_speed [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {c : ℝ} (_hc : 0 ≤ c)
    (hSpeed : ∀ t, speed (I := I) g γ t = c) (a b : ℝ) (_hab : a ≤ b) :
    energy (I := I) g γ a b = (1 / 2) * c ^ 2 * (b - a) := by
  -- Rewrite the energy in terms of the squared speed.
  rw [energy_eq_half_integral_speed_sq (I := I) g γ a b]
  -- Replace the integrand by the constant `c²` and evaluate.
  have hcongr : ∫ t in a..b, (speed (I := I) g γ t) ^ 2 = ∫ _ in a..b, (c ^ 2 : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    change (speed (I := I) g γ u) ^ 2 = c ^ 2
    rw [hSpeed u]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  -- `intervalIntegral.integral_const` gives `(b - a) * c²`; rearrange.
  ring

/-! ### Cauchy–Schwarz equality for constant-speed curves

When `γ` has constant speed `c`, the Cauchy–Schwarz inequality
`length² ≤ 2 (b - a) · energy` saturates: both sides equal `c² (b - a)²`. -/

/-- **Cauchy–Schwarz equality at the constant-speed parametrisation.** For a
`C¹` curve `γ` with constant speed `c ≥ 0` and any `a ≤ b`,

```
length² = 2 (b - a) · energy.
```

This is the equality case of `length_sq_le_two_mul_diff_mul_energy`,
characterising constant-speed parametrisations as energy extremals. -/
theorem length_sq_eq_two_mul_diff_mul_energy_of_const_speed [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {c : ℝ} (hc : 0 ≤ c)
    (hSpeed : ∀ t, speed (I := I) g γ t = c) {a b : ℝ} (hab : a ≤ b) :
    (length (I := I) g γ a b) ^ 2 = 2 * (b - a) * energy (I := I) g γ a b := by
  -- The length and energy each evaluate explicitly at constant speed.
  have h_len :
      length (I := I) g γ a b = c * (b - a) :=
    length_eq_speed_mul_of_constSpeed (I := I) hγ hc hSpeed a b hab
  have h_en :
      energy (I := I) g γ a b = (1 / 2) * c ^ 2 * (b - a) :=
    energy_of_const_speed (I := I) hγ hc hSpeed a b hab
  rw [h_len, h_en]
  ring

/-! ### Sanity check: energy at a constant curve is zero, hence the
Cauchy–Schwarz inequality reduces to `0 ≤ 0` for constant curves. -/

example (g : SmoothRiemannianMetric I M) (p : M) (a b : ℝ) :
    energy (I := I) g (fun _ : ℝ => p) a b = 0 := energy_const (I := I) g p a b

end Length
end Riemannian
end Geometry
end DifferentialGeometry

end
