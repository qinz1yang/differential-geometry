import RicciFlower.GlobalGeometry.IndexForm
import RicciFlower.GlobalGeometry.Myers.SinFieldComputation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers diameter-bound assembly

This file assembles the Myers length bound `L ≤ π/√k` from the pieces produced by
the surrounding `Myers` stack:

* `SinFieldComputation.sum_indexForm_integral_le` — the pure trigonometric
  estimate `∫₀^L [(n-1)(π/L)² cos² − sin² · r] ≤ (n-1)(L/2)((π/L)² − k)` from a
  pointwise Ricci lower bound `r ≥ (n-1)k`;
* the index form `indexForm` of `IndexForm.lean`.

The geometric content that is *not* re-proved here is packaged as two hypotheses
of `geodesic_length_le_of_index_data`:

* `hnonneg` — each test field has nonnegative index form.  This is the
  second-variation consequence of `gamma` being length-minimizing
  (`SecondVariation.secondVar_eq_indexForm` together with
  `SecondVariation.secondDeriv_nonneg_of_isLocalMin`).
* `hsum_eq` — the sum of the test-field index forms equals the trigonometric
  integrand of `sum_indexForm_integral_le`.  This bundles the covariant-derivative
  product rule `D_t(sin(πt/L)·E_i) = (π/L)cos(πt/L)·E_i` for the parallel
  orthonormal frame `E_i` of `ParallelFrame.IsPBParallelONFrame`, curvature
  linearity `R(sin·E_i, T)T = sin·R(E_i,T)T`, and the Ricci trace identity
  `∑_i ⟨R(E_i,T)T, E_i⟩ = Ric(T,T)`.

Once those two producers exist, the diameter bound follows by feeding any
minimizing geodesic through `geodesic_length_le_of_index_data`.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Lecture07 intervalIntegral
open scoped Manifold ContDiff Topology BigOperators

/-- Pure real-analysis core of the Myers bound.

If the summed test-field estimate `0 ≤ (n-1)(L/2)((π/L)² − k)` holds, with
`n ≥ 2`, `L > 0`, and `k > 0`, then `L ≤ π/√k`.  This is exactly the algebraic
inequality obtained by combining `0 ≤ ∑ indexForm` with
`sum_indexForm_integral_le`. -/
theorem length_le_pi_div_sqrt_of_bound
    {L k : ℝ} {n : ℕ} (hn : 1 < n) (hL : 0 < L) (hk : 0 < k)
    (hbound : 0 ≤ ((n : ℝ) - 1) * (L / 2) * ((Real.pi / L) ^ 2 - k)) :
    L ≤ Real.pi / Real.sqrt k := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoef : (0 : ℝ) < ((n : ℝ) - 1) * (L / 2) := mul_pos hn1 (by linarith)
  -- The trigonometric factor `(π/L)² − k` is nonnegative.
  have hB : k ≤ (Real.pi / L) ^ 2 := by
    by_contra hneg
    rw [not_le] at hneg
    have hlt : ((n : ℝ) - 1) * (L / 2) * ((Real.pi / L) ^ 2 - k) < 0 :=
      mul_neg_of_pos_of_neg hcoef (by linarith)
    linarith
  -- Clear the `L`-denominator: `k · L² ≤ π²`.
  have hkL2 : k * L ^ 2 ≤ Real.pi ^ 2 := by
    have hdiv : k ≤ Real.pi ^ 2 / L ^ 2 := by rw [← div_pow]; exact hB
    calc
      k * L ^ 2 ≤ (Real.pi ^ 2 / L ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = Real.pi ^ 2 := by field_simp
  -- Square-root monotonicity.
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  rw [le_div_iff₀ hsk]
  -- Goal: `L * √k ≤ π`; compare squares.
  have hsq : (L * Real.sqrt k) ^ 2 ≤ Real.pi ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk.le, mul_comm (L ^ 2) k]
    exact hkL2
  have hnn : 0 ≤ L * Real.sqrt k := by positivity
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq Real.pi_pos.le] at hfin

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Myers length bound from the assembled index-form data.

Given a finite test-frame index type `ι` (cardinality `n − 1` in the
application) with per-field index forms `indexForm g gamma (V i) (DV i)
(CurvV i) 0 L`, if

* each index form is nonnegative (`hnonneg`, the minimizing-geodesic / second
  variation input), and
* their sum equals the trigonometric integrand of `sum_indexForm_integral_le`
  with pointwise Ricci bound `r ≥ (n-1)k` (`hsum_eq` together with `hr`),

then the geodesic length satisfies `L ≤ π/√k`. -/
theorem geodesic_length_le_of_index_data
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) {gamma : Curve M}
    (V DV CurvV : ι → VectorFieldAlong I gamma)
    {n : ℕ} {k L : ℝ} {r : ℝ → ℝ}
    (hn : 1 < n) (hL : 0 < L) (hk : 0 < k)
    (hr_cont : ContinuousOn r (Set.Icc (0 : ℝ) L))
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) L, ((n : ℝ) - 1) * k ≤ r t)
    (hnonneg : ∀ i, 0 ≤ indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L)
    (hsum_eq :
      (∑ i, indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L)
        = ∫ t in (0 : ℝ)..L,
            ((n : ℝ) - 1) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2
              - Real.sin (Real.pi / L * t) ^ 2 * r t) :
    L ≤ Real.pi / Real.sqrt k := by
  have hsum_nonneg :
      0 ≤ ∑ i, indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L :=
    Finset.sum_nonneg fun i _ => hnonneg i
  rw [hsum_eq] at hsum_nonneg
  have hbound := sum_indexForm_integral_le hL r hr_cont hr
  exact length_le_pi_div_sqrt_of_bound hn hL hk (le_trans hsum_nonneg hbound)

end Assembly

end Myers
end GlobalGeometry
end RicciFlower
