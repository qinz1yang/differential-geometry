import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.JumpChartHm
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpFour
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2Regularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain

/-!
# Truly unconditional chart-`H^{2k}` regularity for arbitrary `k`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and
any `u_h ∈ laplacianDomainPow g k`, the canonical chart-pushed POU-cut
representative `chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp (2k) 2 (chartTargetEuclid α)` unconditionally, for every `k : ℕ`.
The manifold-level `MemWkpChart g (2k) 2` and the `ChartSideH2kBridge g k`
headlines follow.

## Composition strategy

The chart-`H^{2k}` discharge is by outer recursion on `k`. The base cases
are:

* `k = 0` — chart-`L²` (trivial via `iteratedH2Regularity_zero`).
* `k = 1` — chart-`H²` (via `iteratedH2Regularity_one`).
* `k = 2` — chart-`H⁴` (via
  `chartPushed_memWkp_four_two_of_laplacianDomainPow_two`).

For `k ≥ 2`, the step `k → k + 1` chains two applications of the per-stage
jump `chartPushed_memWkp_succ_jump`. The first call lifts the chart-`H` order
from `2k` to `2k + 1`; the second call lifts from `2k + 1` to `2(k + 1)`.
Each call consumes:

1. `u_h ∈ laplacianDomainPow g 2` (from `u_h ∈ laplacianDomainPow g (k + 1)`
   via downward monotonicity `laplacianDomainPow_le_of_le`).
2. chart-`H^{m + 1}` of `u_h.coeFn` (from the outer IH at level `k`, with
   `m = 2k - 1` for the first call and `m = 2k` for the second call).
3. chart-`H^m` of the canonical function representative of the `Lp`-side
   `(1 - Δ_g)`-preimage of `u_h`.

The chart-`H` regularity of the `(1 - Δ_g)`-preimage at order `2k` is
obtained from the outer IH applied to an `H1Compl` lift of the preimage:
for `u_h ∈ laplacianDomainPow g (k + 1)` with `k ≥ 1`, there exists
`v_h ∈ laplacianDomainPow g k` with
`H1ComplToLp g v_h = laplacianDomain.preimage u_h`. The outer IH then
delivers `MemWkpChart g (2k) 2` of `v_h.coeFn`, which equals
`MemWkpChart g (2k) 2` of the preimage's canonical function representative.

## Main results

* `chartPushed_memWkp_two_k_of_laplacianDomainPow` — the per-chart chart-`H^{2k}`
  regularity of the chart-pushed POU-cut representative on the full chart
  target, for arbitrary `k : ℕ`.
* `memWkpChart_two_k_of_laplacianDomainPow_unconditional` — manifold-level
  `MemWkpChart g (2k) 2` of the canonical function representative, for
  arbitrary `k : ℕ`.
* `chartSideH2kBridge_of_laplacianDomainPow_unconditional` — the
  `ChartSideH2kBridge g k` predicate for the canonical function
  representative, for arbitrary `k : ℕ`.
* `laplacianDomainPow_memWkpChart_two_k_unconditional_arbitrary_k` — the
  combined manifold-level `MemWkpChart g (2k) 2` plus finite chart-based
  norm, for arbitrary `k : ℕ`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartSideH2kBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For `u_h ∈ laplacianDomainPow g (k + 1)` with `k ≥ 1`, there exists a
witness `v_h ∈ laplacianDomainPow g k` whose `Lp` image equals the
canonical `(1 - Δ_g)`-preimage of `u_h`. -/
private theorem laplacianDomainPow_succ_preimage_lift
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk_pos : 1 ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    ∃ v_h : H1Compl (I := I) (M := M) g,
      v_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
      H1ComplToLp (I := I) (M := M) g v_h =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ := by
  classical
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have h_apply :
      iteratedResolventL2 (I := I) (M := M) g (k' + 1) f =
        resolventL2 (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f) :=
    iteratedResolventL2_succ_apply (I := I) (M := M) g k' f
  have h_resolventL2_apply : resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k' f) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f)) := by
    rfl
  refine ⟨resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k' f), ?_, ?_⟩
  · rw [laplacianDomainPow_succ_mem_iff]
    refine ⟨f, rfl⟩
  · apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    rw [← h_resolventL2_apply]
    rw [← h_apply]
    exact hf.symm

/-- The outer-recursion helper: unconditional manifold-level chart-`H^{2k}`
of the canonical function representative of any `u_h ∈ laplacianDomainPow g k`,
for arbitrary `k : ℕ`.

The recursion descends `k` to either a base case (`k ≤ 2`) or the inductive
step (`k ≥ 3`). The step `k → k + 1` (active for `k ≥ 2`, i.e. `k + 1 ≥ 3`)
applies `chartPushed_memWkp_succ_jump` twice: once at `m = 2k - 1` to lift
chart-`H^{2k}` to chart-`H^{2k + 1}`, and once at `m = 2k` to lift
chart-`H^{2k + 1}` to chart-`H^{2(k + 1)}`. -/
private theorem chart_H_at_outer_k
    (g : SmoothRiemannianMetric I M) :
    ∀ (k : ℕ) {u_h : H1Compl (I := I) (M := M) g},
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k →
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * k) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro k
  induction k with
  | zero =>
      intro u_h _hu_h
      have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
      rw [h_eq]
      exact iteratedH2Regularity_zero (I := I) (M := M) g u_h
  | succ k ih =>
      intro u_h hu_h
      match k, hu_h with
      | 0, hu_h =>
          have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
          rw [h_eq]
          exact (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
      | 1, hu_h =>
          have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
          rw [h_eq]
          intro α
          exact chartPushed_memWkp_four_two_of_laplacianDomainPow_two
            (I := I) (M := M) g α hu_h
      | k' + 2, hu_h =>
          set kk : ℕ := k' + 2 with hkk_def
          have hkk_ge_2 : 2 ≤ kk := by omega
          have hu_h_kk : u_h ∈ laplacianDomainPow (I := I) (M := M) g kk :=
            laplacianDomainPow_le_of_le (I := I) (M := M) g
              (Nat.le_succ kk) hu_h
          have hu_h_2 : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2 :=
            laplacianDomainPow_le_of_le (I := I) (M := M) g hkk_ge_2 hu_h_kk
          have h_u_kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) g (2 * kk) 2
              ((H1ComplToLp (I := I) (M := M) g u_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
            ih hu_h_kk
          have hkk_pos : 1 ≤ kk := by omega
          obtain ⟨v_h, hv_h_kk, hv_h_eq⟩ :=
            laplacianDomainPow_succ_preimage_lift (I := I) (M := M) g
              (k := kk) hkk_pos hu_h
          have h_v_kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) g (2 * kk) 2
              ((H1ComplToLp (I := I) (M := M) g v_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
            ih hv_h_kk
          have h_preimage_2kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) g (2 * kk) 2
              ((laplacianDomain.preimage (I := I) (M := M) g
                  ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g kk hu_h⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [show (laplacianDomain.preimage (I := I) (M := M) g
                  ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g kk hu_h⟩) =
                H1ComplToLp (I := I) (M := M) g v_h from hv_h_eq.symm]
            exact h_v_kk
          have h_2kk_pos : 1 ≤ 2 * kk := by omega
          set m₁ : ℕ := 2 * kk - 1 with hm₁_def
          have hm₁_succ_eq : m₁ + 1 = 2 * kk := by omega
          have hm₁_succ_succ_eq : m₁ + 2 = 2 * kk + 1 := by omega
          have h_chart_H_m1_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) g (m₁ + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [hm₁_succ_eq]; exact h_u_kk
          have h_chart_H_m1_RHS :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) g m₁ 2
                ((laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            have h_eq_preimage :
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g kk hu_h⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
              congr 1
            rw [h_eq_preimage]
            exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
              (by omega : m₁ ≤ 2 * kk) h_preimage_2kk
          have h_succ_jump_1 :
              ∀ α : M, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) (m₁ + 2) 2
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
                  (I := I) (M := M) (chartAtlasPOU I M) α
                  ((H1ComplToLp (I := I) (M := M) g u_h :
                    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α) := by
            intro α
            exact chartPushed_memWkp_succ_jump (I := I) (M := M) g α m₁ hu_h_2
              h_chart_H_m1_plus_1_u h_chart_H_m1_RHS
          have h_chart_H_2kk_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) g (2 * kk + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            intro α
            have := h_succ_jump_1 α
            rw [hm₁_succ_succ_eq] at this
            exact this
          set m₂ : ℕ := 2 * kk with hm₂_def
          have hm₂_succ_eq : m₂ + 1 = 2 * kk + 1 := rfl
          have hm₂_succ_succ_eq : m₂ + 2 = 2 * (kk + 1) := by ring
          have h_chart_H_m2_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) g (m₂ + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [hm₂_succ_eq]; exact h_chart_H_2kk_plus_1_u
          have h_chart_H_m2_RHS :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) g m₂ 2
                ((laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            have h_eq_preimage :
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g kk hu_h⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
              congr 1
            rw [h_eq_preimage, hm₂_def]
            exact h_preimage_2kk
          have h_succ_jump_2 :
              ∀ α : M, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) (m₂ + 2) 2
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
                  (I := I) (M := M) (chartAtlasPOU I M) α
                  ((H1ComplToLp (I := I) (M := M) g u_h :
                    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α) := by
            intro α
            exact chartPushed_memWkp_succ_jump (I := I) (M := M) g α m₂ hu_h_2
              h_chart_H_m2_plus_1_u h_chart_H_m2_RHS
          intro α
          have := h_succ_jump_2 α
          rw [hm₂_succ_succ_eq] at this
          change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) (2 * (k' + 2 + 1)) 2 _ _
          have h_arith : 2 * (kk + 1) = 2 * (k' + 2 + 1) := by
            rw [hkk_def]
          rw [← h_arith]
          exact this

/-- **Headline: truly unconditional chart-`H^{2k}` of the chart-pushed
function, for arbitrary `k`.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, an order
`k : ℕ`, and any `u_h ∈ laplacianDomainPow g k`, the canonical chart-pushed
POU-cut representative `chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp (2k) 2 (chartTargetEuclid α)`. -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chart_H_at_outer_k (I := I) (M := M) g k hu_h α

/-- **Headline: truly unconditional manifold-level `MemWkpChart g (2k) 2`,
for arbitrary `k`.**

For `u_h ∈ laplacianDomainPow g k`, the canonical function representative
`(H1ComplToLp g u_h).coeFn` lies in `MemWkpChart g (2k) 2`, unconditionally. -/
theorem memWkpChart_two_k_of_laplacianDomainPow_unconditional
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  chart_H_at_outer_k (I := I) (M := M) g k hu_h

/-- **Headline: truly unconditional `ChartSideH2kBridge g k` for the
canonical function representative, for arbitrary `k`.**

For `u_h ∈ laplacianDomainPow g k`, the chart-side `H^{2k}` bridge for the
canonical function representative holds, unconditionally. -/
theorem chartSideH2kBridge_of_laplacianDomainPow_unconditional
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h

/-- **Headline: truly unconditional combined `MemWkpChart g (2k) 2` with
finite chart-based norm, for arbitrary `k`.**

For `u_h ∈ laplacianDomainPow g k`, the canonical function representative
`(H1ComplToLp g u_h).coeFn` lies in `MemWkpChart g (2k) 2` with a finite
chart-based norm, unconditionally. -/
theorem laplacianDomainPow_memWkpChart_two_k_unconditional_arbitrary_k
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_mem := memWkpChart_two_k_of_laplacianDomainPow_unconditional
    (I := I) (M := M) g k hu_h
  refine ⟨h_mem, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2 * k) (p := 2) (by norm_num) h_mem

end ChartSideH2kBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
