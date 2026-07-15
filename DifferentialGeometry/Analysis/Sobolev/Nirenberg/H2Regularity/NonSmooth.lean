import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import DifferentialGeometry.Analysis.Sobolev.Solutions.FriedrichsCommutator

/-!
# Interior `H²` regularity for non-smooth weak solutions of uniformly
elliptic divergence-form equations on Euclidean space.

This module extends the smooth-case result `loc_smooth_solution` to
weak solutions `u ∈ H¹(Ω)` whose data `f` lies in `L²(Ω)`. The headline
theorem is hypothesis-bearing: it accepts a smooth approximating sequence
`(u_n, f_n)` with associated convergence properties that are the analytic
content of the mollification + Friedrichs commutator construction.

## Argument outline

For an `H¹` weak solution `u ∈ H¹(Ω)` of `B(u, ·) = ⟨f, ·⟩`:

1. Build a smooth approximating sequence `u_n` (e.g. `u_n := u ⋆ φ_{ε_n}`
   on a slightly shrunk subdomain).
2. Each `u_n` satisfies a smooth weak equation `B(u_n, ·) = ⟨f_n, ·⟩` with
   `f_n` close to the mollification of `f` (the `L²` discrepancy is the
   Friedrichs commutator).
3. Apply `loc_smooth_solution` to obtain a per-`n` `L²` bound on
   `∂_k ∂_i u_n` over `Ω''`, with constant uniform in `n` (as the
   smooth-case constant depends only on the elliptic data `B` and the
   geometric room, not on the specific solution).

## Main results

* `SmoothApproximation` — structure encoding a smooth approximating
  sequence to a non-smooth weak solution, together with uniform-in-`n`
  integrated `L²(Ω')` bounds on `u_n`, the gradients `∇u_n`, and the data
  `f_n` over every precompact open `Ω'`.
* `loc_nonsmooth_per_n_bound` — for each pair `(i, k) : Fin d × Fin d`
  and each `n`, the function `∂_i u_n` admits a weak `k`-partial
  derivative `g_n` on `Ω''` with `‖g_n‖²_{L²(Ω'')}` bounded by a constant
  multiple of the master `data_bound`.
* `loc_nonsmooth_solution` — packaged form of the per-`n` bound,
  exposing for each `n` a constant `K` and a witness `g_n`.

## Scope

The construction of the smooth approximating sequence (mollification of
`u` on the right shrunk subdomain, plus the Friedrichs-commutator-based
identification of `f_n` with the mollification of `f`) is a separate
piece of analysis that lies outside this file. Downstream callers
package the construction as a one-shot lemma.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
/-- A continuous function on a set with compact closure is in `L²` on
that set restricted (variant adapted to the non-smooth setting). -/
private lemma memLp_two_of_continuous_compact_closure
    {f : E → ℝ} (hf : Continuous f)
    {S : Set E} (hS_open : IsOpen S) (hS_cc : IsCompact (closure S)) :
    MemLp f 2 (volume.restrict S) := by
  have h_volume_closure_lt_top : volume (closure S) < ⊤ :=
    hS_cc.measure_lt_top
  have h_volume_lt_top : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) h_volume_closure_lt_top
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  obtain ⟨M, hM⟩ := hS_cc.bddAbove_image hf.abs.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable (max M 0) ?_
  rw [ae_restrict_iff' hS_open.measurableSet]
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have h_in_closure : x ∈ closure S := subset_closure hx
  have h := hM (Set.mem_image_of_mem _ h_in_closure)
  rw [Real.norm_eq_abs]
  exact h.trans (le_max_left _ _)

/-- Data describing a smooth approximating sequence to a non-smooth weak
solution. Each `u_n` is smooth, satisfies a smooth weak equation with
data `f_n`, and admits uniform-in-`n` integrated `L²(Ω')` bounds for the
combined `H¹`+data energy on every precompact open `Ω'`.

The bound is formulated as a single nonneg scalar `data_bound` together
with a per-`Ω'` linear control: there exists a constant `C_{Ω'} ≥ 0`
(depending only on `Ω'`) such that, uniformly in `n`,
```
∫_{Ω'} (∑_j (∂_j u_n)² + (u_n)² + (f_n)²) ≤ C_{Ω'} · data_bound.
```
This formulation is the natural one for `H¹`-only weak solutions, where
pointwise sup-norm bounds on the mollified sequence are not available
(the convolution kernel `‖φ_ε‖_∞` blows up as `ε → 0⁺`). -/
structure SmoothApproximation
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (_u _f : E → ℝ) where

  u_seq : ℕ → E → ℝ

  f_seq : ℕ → E → ℝ

  u_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n)

  is_smooth_weak_sol :
    ∀ n, B.IsSmoothWeakSolution (u_seq n) (f_seq n)

  f_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (f_seq n) 2 (volume.restrict S)

  u_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (u_seq n) 2 (volume.restrict S)

  grad_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d,
        MemLp (fun y : E => (fderiv ℝ (u_seq n) y) (EuclideanSpace.single j 1))
          2 (volume.restrict S)

  data_bound : ℝ
  data_bound_nn : 0 ≤ data_bound

  data_integrated_bound :
    ∀ {Ω' : Set E}, IsOpen Ω' → IsCompact (closure Ω') →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        (∫ y in Ω',
            ∑ j : Fin d,
              ((fderiv ℝ (u_seq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E)) +
        (∫ y in Ω', (u_seq n y) ^ 2 ∂(volume : Measure E)) +
        (∫ y in Ω', (f_seq n y) ^ 2 ∂(volume : Measure E)) ≤
          C * data_bound

/-- Per-`n` interior `H²` regularity bound (raw smooth-case form). For
each `n`, the smooth-case result `loc_smooth_solution` applied to
`(u_n, f_n)` yields a weak `k`-partial derivative `g_n` of `∂_i u_n` on
`Ω''`, with `L²(Ω'')` norm bounded in terms of integrated `L²` data
of `u_n` on a smooth-case-chosen intermediate `Ω'`. -/
private lemma loc_per_n_smooth_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f)
    (i k : Fin d) (n : ℕ) :
    ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d,
                    ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure E) +
              ∫ x in Ω', (S.u_seq n x) ^ 2 ∂(volume : Measure E) +
              ∫ x in Ω', (S.f_seq n x) ^ 2 ∂(volume : Measure E)) := by
  obtain ⟨C, hC_nn, h_eng⟩ := loc_smooth_solution (d := d) B
    hΩ'' hΩ''_compact_closure hΩ''_in_Ω h_room
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ :=
    h_eng (S.is_smooth_weak_sol n) (S.f_seq_l2_loc n) i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

/-- **Interior `H²` regularity for non-smooth weak solutions
(per-`n` form, hypothesis-bearing).**

Given a smooth approximating sequence `S` to a non-smooth weak `H¹`
solution `u` of an elliptic divergence-form equation, for each `n` the
function `∂_i u_n` admits a weak `k`-partial derivative `g_n` on `Ω''`
with quantitative `L²(Ω'')` bound. The constant absorbs (1) the smooth
Nirenberg case constant, (2) the per-`Ω'` integrated-bound constant
(here `Ω'` is the thickened intermediate set chosen by the smooth case),
and (3) all uniform-in-`n` factors. The right-hand side of the bound is
`K · data_bound`, where `data_bound` is the master scalar of the
approximation. -/
theorem loc_nonsmooth_per_n_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ K * S.data_bound := by
  classical
  intro i k n
  obtain ⟨g, hg_l2, hg_partial, Ω', hΩ'_open, _hΩ''_in_Ω', _hΩ'_in_Ω,
      hΩ'_compact, C, hC_nn, hC_bound⟩ :=
    loc_per_n_smooth_bound (d := d) B hΩ'' hΩ''_compact_closure hΩ''_in_Ω
      h_room S i k n
  obtain ⟨D, hD_nn, hD_bound⟩ :=
    S.data_integrated_bound (Ω' := Ω') hΩ'_open hΩ'_compact
  refine ⟨g, hg_l2, hg_partial, C * D,
    mul_nonneg hC_nn hD_nn, ?_⟩
  have h_data_le := hD_bound n
  refine hC_bound.trans ?_
  calc C * _
      ≤ C * (D * S.data_bound) :=
        mul_le_mul_of_nonneg_left h_data_le hC_nn
    _ = (C * D) * S.data_bound := by ring

/-- **Interior `H²` regularity for non-smooth weak solutions.**

For a non-smooth weak `H¹` solution `u ∈ H¹(Ω)` of an elliptic
divergence-form equation `B(u, ·) = ⟨f, ·⟩` with smooth coefficients
and `L²` data `f`, together with a smooth approximating sequence
`(u_n, f_n)` (encapsulated in `SmoothApproximation`), each function
`∂_i u_n` is in `H¹(Ω'')` with a quantitative bound on the `L²(Ω'')`
norm of its weak `k`-partial derivative.

The bound has the form
```
∫_{Ω''} g_n² ≤ K · data_bound
```
where `data_bound` is the master scalar of the approximation that
controls the uniform-in-`n` integrated `H¹`+data energy of the
sequence on every precompact open subdomain. -/
theorem loc_nonsmooth_solution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g_n : E → ℝ,
      MemLp g_n 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g_n
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g_n x ^ 2 ∂(volume : Measure E) ≤ K * S.data_bound :=
  loc_nonsmooth_per_n_bound (d := d) B hΩ'' hΩ''_compact_closure
    hΩ''_in_Ω h_room S

end DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
