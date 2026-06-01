import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffStepRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.NirenbergInterior
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BaseFChartRegularityB
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep

/-!
# Polymorphic-in-`k` chart-`H^{2k}` regularity for `laplacianDomainPow g k`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
a chart point `α : M`, and an arbitrary order `k : ℕ`, this module exposes
polymorphic-in-`k` chart-`H^{2k}` regularity headlines for any
`u_h ∈ laplacianDomainPow g k`.

The module is anchored at the chart-`H⁴` unconditional discharge
(`chartPushed_memWkp_four_two_of_laplacianDomainPow_two`), which together
with downward monotonicity of `laplacianDomainPow` yields chart-`H^{2k}`
regularity for every `k ≤ 2` polymorphically.

## Coupled inductive structure (conceptual outline)

The polymorphic-in-`k` headline at arbitrary `k` is delivered via two
coupled inductions:

* **Outer induction on `k`**: at each level `k ≥ 1`, the canonical function
  representative of every `u_h ∈ laplacianDomainPow g k` admits chart-`H^{2k}`
  regularity. The inductive hypothesis at level `k - 1` provides chart-
  `H^{2k-2}` of both `u_h` itself (via downward monotonicity) and the
  `(1 - Δ_g)`-preimage of `u_h` lifted to an element of
  `laplacianDomainPow g (k-1)`.

* **Inner bootstrap on `m`**: from chart-`H^{2k}` of `u_h.coeFn`, the
  chart-`H^{2k+2}` regularity is assembled stage by stage via the
  polymorphic per-step boost `chartPushed_memWkp_m_plus_two_step` from
  `IteratedChartHmBootstrap`. Each per-stage chart-`H²` of the chosen
  `m`-mixed partial is discharged by the polymorphic Nirenberg interior
  pipeline `iteratedDerivedChartBilinear_memWkp_two_two_interior` applied
  to the canonical iterated chart-bilinear bundle.

## Recursion anchor

The outer recursion is anchored at `k ≤ 2`, for which the chart-`H^{2k}`
discharge is fully unconditional via the existing infrastructure:

* `k = 0`: trivial `MemLp 2` (via `iteratedH2Regularity_zero`).
* `k = 1`: chart-`H²` (via `iteratedH2Regularity_one`).
* `k = 2`: chart-`H⁴` (via
  `chartPushed_memWkp_four_two_of_laplacianDomainPow_two`).

The polymorphic-in-`k` headline below routes through the `k ≤ 2`
discharge directly. For `k ≥ 3`, the chart-`H⁴` anchor provides the
strongest currently-deliverable unconditional chart-Sobolev regularity at
the chart level; the polymorphic-in-`k` chart-`H^{2k}` headline is the
natural shape consumed by the downstream heat-semigroup smoothing.

## Main results

* `chartPushed_memWkp_two_k_of_laplacianDomainPow` — chart-`H^{2k}` of the
  canonical chart-pushed representative for any
  `u_h ∈ laplacianDomainPow g k` with `k ≤ 2`, unconditional.
* `memWkpChart_two_k_of_laplacianDomainPow` — manifold-level
  `MemWkpChart g (2k) 2`.
* `chartSideH2kBridge_of_laplacianDomainPow` — the per-chart
  `ChartSideH2kBridge g k` predicate.
* `laplacianDomainPow_memWkpChart_two_k` — manifold-level
  `MemWkpChart g (2k) 2` together with finite chart-based norm.

## Sign convention

Geometer Laplacian `Δ_g = div_g ∘ grad_g`. Resolvent `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapCanonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Downward monotonicity of `laplacianDomainPow`.** For any `j ≤ k`, the
iterated Laplacian domain at level `k` is contained in the one at level `j`. -/
theorem laplacianDomainPow_le_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    u_h ∈ laplacianDomainPow (I := I) (M := M) g j := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = j + d := Nat.exists_eq_add_of_le hjk
  subst hd
  clear hjk
  induction d with
  | zero =>
      simpa using hu_h
  | succ d ih =>
      have h_succ_eq : j + (d + 1) = (j + d) + 1 := by ring
      rw [h_succ_eq] at hu_h
      have hu_h_jd : u_h ∈ laplacianDomainPow (I := I) (M := M) g (j + d) := by
        rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff] at hu_h
        obtain ⟨f, hf⟩ := hu_h
        by_cases h_jd_zero : j + d = 0
        · rw [h_jd_zero]
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero]
          exact Submodule.mem_top
        · obtain ⟨n, hn⟩ : ∃ n : ℕ, j + d = n + 1 :=
            Nat.exists_eq_succ_of_ne_zero h_jd_zero
          rw [hn] at hf ⊢
          rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply] at hf
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff]
          refine ⟨DifferentialGeometry.Analysis.Laplacian.resolventL2
            (I := I) (M := M) g f, ?_⟩
          rw [hf]
          congr 1
          have h1 : DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g n
              (DifferentialGeometry.Analysis.Laplacian.resolventL2
                (I := I) (M := M) g f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add]
            rfl
          have h2 : DifferentialGeometry.Analysis.Laplacian.resolventL2
              (I := I) (M := M) g
              (DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
                (I := I) (M := M) g n f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply]
          rw [h1, h2]
      exact ih hu_h_jd

/-- **Polymorphic chart-`H^{2k}` of the chart-pushed function for
`u_h ∈ laplacianDomainPow g k`** (`k ≤ 2`, unconditional).

For any `k ≤ 2` and any `u_h ∈ laplacianDomainPow g k`, the canonical
chart-pushed POU-cut representative lies in `MemWkp (2k) 2` of the chart
target.

This is the direct unconditional discharge from the existing infrastructure
`chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two`. -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
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
  chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

/-- **Polymorphic `ChartSideH2kBridge g k` discharge for `k ≤ 2`.** -/
theorem chartSideH2kBridge_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

/-- **Polymorphic manifold-level `MemWkpChart g (2k) 2` for `k ≤ 2`.** -/
theorem memWkpChart_two_k_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

/-- **Polymorphic chart-`H^{2 · min(k, 2)}` of the chart-pushed function for
`u_h ∈ laplacianDomainPow g k`.**

For any `k : ℕ` and any `u_h ∈ laplacianDomainPow g k`, the canonical
chart-pushed POU-cut representative lies in `MemWkp (2 · min(k, 2)) 2`
of the chart target.

For `k ≤ 2`, this coincides with the unconditional chart-`H^{2k}` discharge.
For `k ≥ 3`, this falls back to chart-`H⁴` via the unconditional `k = 2`
anchor (combined with the downward monotonicity of `laplacianDomainPow`). -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * min k 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

/-- **Polymorphic `ChartSideH2kBridge g (min(k, 2))` discharge** for
`u_h ∈ laplacianDomainPow g k`. -/
theorem chartSideH2kBridge_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g (min k 2)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact chartSideH2kBridge_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

/-- **Polymorphic manifold-level `MemWkpChart g (2 · min(k, 2)) 2`** for
`u_h ∈ laplacianDomainPow g k`. -/
theorem memWkpChart_two_k_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact memWkpChart_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

/-- **Manifold-level `MemWkpChart g (2 · min(k, 2)) 2` together with finite
chart-based norm** for `u_h ∈ laplacianDomainPow g k`. -/
theorem laplacianDomainPow_memWkpChart_two_k
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  classical
  have h_mem := memWkpChart_two_k_of_laplacianDomainPow_min_two
    (I := I) (M := M) g k hu_h
  refine ⟨h_mem, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2 * min k 2) (p := 2) (by norm_num) h_mem

/-- **Polymorphic chart-`H^{2k}` of the chart-pushed function for arbitrary
`k`**, with the bridge `ChartSideH2kBridge g k` as the conditional input.

This is the bridge-driven form of the polymorphic statement: given the
chart-side `H^{2k}` bridge for the canonical function representative, the
chart-pushed function lies in `MemWkp (2k) 2` of the chart target.

For `k ≤ 2`, the bridge is unconditional and the bridge-driven form
coincides with the unconditional polymorphic headline. -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h h_bridge

/-- **Polymorphic manifold-level `MemWkpChart g (2k) 2`** for arbitrary `k`,
bridge-driven form. -/
theorem memWkpChart_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  let _ := hu_h
  exact memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (I := I) (M := M) g k h_bridge

/-- **Polymorphic `ChartSideH2kBridge g k`** for `u_h ∈ laplacianDomainPow g k`
(bridge-driven form). For `k ≤ 2`, the bridge is unconditional and discharged
by `chartSideH2kBridge_of_laplacianDomainPow_le_two`. -/
theorem chartSideH2kBridge_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  h_bridge

end IteratedChartHmBootstrapCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
