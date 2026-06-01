import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedNirenbergWeakened
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorNonSmoothRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSupportPromotion

/-!
# Arbitrary-order interior `W^{k,2}` regularity of the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the eigenvector
chart component `eigenvectorChartComponentFun g r s i α P₀` — the
chart `P₀`-component of a resolvent eigenvector of the connection Laplacian
`Δ_∇`, presented as a function `EuclN → ℝ` — has been shown to lie in
`MemWkp 2 2 … Ω''` on every interior subdomain `Ω''`, and that order-2
regularity globalises to `MemWkp 2 2 … (chartTargetEuclid α)` on the whole chart
target.

This module **closes the coupled interior-regularity induction** and ships the
arbitrary-order conclusion: the eigenvector chart component lies in
`MemWkp k 2 … (chartTargetEuclid α)` for *every* `k : ℕ`.

## The coupled induction

The induction is on the order. Write

```
P_m : ∀ α P₀, MemWkp (m + 2) 2
        (eigenvectorChartComponentFun g r s i α P₀)
        (chartTargetEuclid α).
```

* **Base `P_0`.** The committed order-2 interior engine
  `eigenvector_chartComponent_memWkp` delivers `MemWkp 2 2 … Ω''` on an interior
  subdomain `Ω''`. Taking `Ω''` to be a thickening of the compact
  partition-of-unity kernel `chartPouKernel α` inside the chart target, and
  promoting the interior regularity to the whole chart target via the
  support-aware promotion `MemWkp_of_memWkp_precompact_of_ae_zero_off_compact`
  (the chart component vanishes a.e. off the compact kernel), yields global
  `MemWkp 2 2 … (chartTargetEuclid α)`.

* **Step `P_m → P_{m+1}`.** Given `P_m`, for every `α, P₀` and every direction
  tuple `directions : Fin (m + 1) → Fin n`:
  - the carrier-builder `exists_eigenvectorIteratedCarrier` produces a level-`(m
    + 1)` iterated divergence-form carrier whose direction field is `directions`;
    its `h_pou` regularity input — chart-component regularity at every order
    `j + 2`, `j < m + 1` — is supplied by `P_m` through `MemWkp.le_of_le`;
  - the carrier-to-`W^{2,2}` engine
    `eigenvectorChartIteratedPartial_memWkp_two_two` delivers global `W^{2,2}` of
    every `(m + 1)`-fold mixed weak partial, with parent regularity `P_m`;
  - the polymorphic regularity bridge
    `eigenvectorChartIteratedPartial_memWkp_of_memWkp` at `k = 1` delivers
    `W^{1,2}` of every `j`-fold mixed weak partial for `j ≤ m + 1`, again from
    `P_m`;
  - the structural order-raiser
    `eigenvectorChartComponent_memWkp_m_plus_two_of_iterated` assembles these
    into `MemWkp ((m + 1) + 2) 2 = MemWkp (m + 3) 2` of the chart component.

The arbitrary-`k` headline then specialises `P_m` at `m := k` and drops the
order from `k + 2` to `k` by the downward monotonicity `MemWkp.le_of_le`.

## Main result

* `eigenvector_chartComponent_memWkp_arbitrary` — the eigenvector
  chart component lies in `MemWkp k 2 … (chartTargetEuclid α)` for every
  `k : ℕ`, unconditionally.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `resolventChartComponent_memWkp_of_componentFun`. -/
private lemma resolventChartComponent_memWkp_of_componentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_comp : MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i α P₀
  have h_ae :
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀ y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀)
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    have h_back :
        i.fst.val •
            tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i)
              α P₀ =
          tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            α P₀ := by
      rw [h_chart_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
    rw [h_back] at h_smul
    filter_upwards [h_smul] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    rfl
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_global`. -/
private lemma eigenvector_chartComponent_memWkp_global
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (R_α / 2) K :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_half_in_chart : Metric.cthickening (R_α / 2) K ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (R_α / 2) ≤ R_α := by linarith
    exact (Metric.cthickening_mono hle K).trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_half_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) ⊆
        Metric.cthickening (R₀ + R_α / 2) K := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + R_α / 2) K ⊆
        Metric.cthickening R_α K := by
      have hle : R₀ + R_α / 2 ≤ R_α := by rw [hR₀_def]; linarith
      exact Metric.cthickening_mono hle K
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  have h_interior :
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        Ω'' :=
    eigenvector_chartComponent_memWkp g r s i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_global_Lp :
      MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartComponentFun_memLp_volume
      (I := I) (M := M) g r s i α P₀
  have h_ae_zero :
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀
  exact MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
    h_global_Lp h_ae_zero h_interior

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_pm`. -/
private theorem eigenvector_chartComponent_memWkp_pm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∀ (m : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      intro α P₀
      exact eigenvector_chartComponent_memWkp_global
        (I := I) (M := M) g r s i α P₀
  | succ m ih =>
      intro α P₀
      classical
      have h_pm : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ih α P₀
      have h_pou : ∀ (j : ℕ), j < m + 1 → ∀ (β : M)
          (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro j hj β Q
        have h_pm_βQ : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          ih β Q
        have h_drop : MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : j + 2 ≤ m + 2) h_pm_βQ
        exact resolventChartComponent_memWkp_of_componentFun
          (I := I) (M := M) g r s i (j + 2) β Q h_drop
      have h_top_memWkp_two :
          ∀ (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)),
            MemWkp (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) idx)
              (chartTargetEuclid (I := I) (M := M) α) := by
        intro idx
        obtain ⟨D, hD_dir, _hD_fChartEff⟩ :=
          exists_eigenvectorIteratedCarrier (I := I) (M := M)
            g r s i α P₀ (m + 1) idx h_pou
        exact eigenvectorChartIteratedPartial_memWkp_two_two
          (I := I) (M := M) g r s i α P₀ idx D hD_dir h_pm
      have h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m + 1 →
            ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
              MemWkp (d := Module.finrank ℝ E) 1 2
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ j idx)
                (chartTargetEuclid (I := I) (M := M) α) := by
        intro j hj idx
        have h_parent : MemWkp (d := Module.finrank ℝ E) (1 + j) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : 1 + j ≤ m + 2) h_pm
        exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ j 1 h_parent idx
      have h_raised : MemWkp (d := Module.finrank ℝ E) ((m + 1) + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
          (I := I) (M := M) g r s i α P₀ (m + 1)
          h_intermediate_w1p h_top_memWkp_two
      exact h_raised

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_arbitrary`. -/
theorem eigenvector_chartComponent_memWkp_arbitrary
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_pk : MemWkp (d := Module.finrank ℝ E) (k + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_pm
      (I := I) (M := M) g r s i k α P₀
  exact MemWkp.le_of_le (d := Module.finrank ℝ E)
    (by omega : k ≤ k + 2) h_pk

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
