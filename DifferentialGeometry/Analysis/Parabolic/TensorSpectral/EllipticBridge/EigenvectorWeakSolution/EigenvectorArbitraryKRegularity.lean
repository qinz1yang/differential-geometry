import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedNirenbergWeakened
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorNonSmoothRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSupportPromotion
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# Arbitrary-order interior `W^{k,2}` regularity of the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀` — the chart `P₀`-component
of a resolvent eigenvector of the connection Laplacian `Δ_∇`, presented as a
function `EuclN → ℝ` — has been shown to lie in `MemWkp 2 2 … Ω''` on every
interior subdomain `Ω''`, and that order-2 regularity globalises to
`MemWkp 2 2 … (chartTargetEuclid α)` on the whole chart target.

This module **closes the coupled interior-regularity induction** and ships the
arbitrary-order conclusion: the eigenvector chart component lies in
`MemWkp k 2 … (chartTargetEuclid α)` for *every* `k : ℕ`.

## The coupled induction

The induction is on the order. Write

```
P_m : ∀ α P₀, MemWkp (m + 2) 2
        (eigenvectorChartComponentFun g r s h_atlas i α P₀)
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

* `eigenvector_chartComponent_memWkp_arbitrary` — the eigenvector chart
  component lies in `MemWkp k 2 … (chartTargetEuclid α)` for every `k : ℕ`,
  unconditionally.

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

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The resolvent-coercion chart component from the eigenvector chart component

The carrier-builder `exists_eigenvectorIteratedCarrier` consumes its
chart-component regularity input `h_pou` phrased for the chart component of the
`L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)`. The
coupled induction `P_m` is phrased for the eigenvector chart component
`eigenvectorChartComponentFun`. The two chart components differ by the nonzero
scalar `i.fst.val` (`eigenvector_chartComponent_eq` exhibits the eigenvector
chart component as `i.fst.val⁻¹` times the resolvent-coercion chart component;
hence the resolvent-coercion chart component is `i.fst.val` times the
eigenvector chart component), and `MemWkp` is scalar-invariant, so the
regularity transfers from `eigenvectorChartComponentFun` to the resolvent
coercion. -/

omit [CompleteSpace E] in
/-- **From the eigenvector chart component to the resolvent-coercion chart
component.** Given global chart-`H^N` regularity of the eigenvector chart
component `eigenvectorChartComponentFun g r s h_atlas i α P₀`, the chart
`P₀`-component of the `L²`-coercion `TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent …)` also lies in `MemWkp N 2` on the chart target.

This is the converse of the partition-of-unity bridge
`eigenvectorChartComponentFun_memWkp_of_pou`: the resolvent-coercion chart
component is `i.fst.val •` the eigenvector chart component (the rescaling
`eigenvector_chartComponent_eq` solved for the resolvent coercion), and `MemWkp`
is invariant under scalar multiplication. -/
private lemma resolventChartComponent_memWkp_of_componentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_comp : MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `eigenvector_chartComponent_eq`: the eigenvector chart-component element
  -- equals `i.fst.val⁻¹ •` the resolvent-coercion chart-component element.
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_atlas i α P₀
  -- The resolvent-coercion chart component is `i.fst.val •` the eigenvector
  -- chart component, almost everywhere on `Ω`.
  have h_ae :
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀ y) := by
    -- `Lp.coeFn_smul`: the coercion of `i.fst.val •` the eigenvector
    -- chart-component element is `i.fst.val •` its coercion. The eigenvector
    -- chart-component element is, by `eigenvector_chartComponent_eq`,
    -- `i.fst.val⁻¹ •` the resolvent-coercion element; scaling back by
    -- `i.fst.val` recovers the resolvent-coercion element.
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀)
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    -- `i.fst.val • (eigenvector element) = resolvent-coercion element`.
    have h_back :
        i.fst.val •
            tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
              α P₀ =
          tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            α P₀ := by
      rw [h_chart_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
    rw [h_back] at h_smul
    filter_upwards [h_smul] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    rfl
  -- `MemWkp N 2` is scalar-invariant: scale the eigenvector chart component.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

/-! ## Globalising the order-2 base regularity

The committed order-2 interior engine `eigenvector_chartComponent_memWkp`
delivers `MemWkp 2 2 … Ω''` on an interior subdomain `Ω''`. The lemma below
promotes it to global `MemWkp 2 2 … (chartTargetEuclid α)`: it takes `Ω''` to be
a thickening of the compact partition-of-unity kernel `chartPouKernel α` inside
the chart target, runs the interior engine, and applies the support-aware
promotion `MemWkp_of_memWkp_precompact_of_ae_zero_off_compact` — the eigenvector
chart component vanishes almost everywhere off the compact kernel
(`eigenvectorChartComponentFun_ae_zero_off_chartPouKernel`) and is globally `L²`
(`eigenvectorChartComponentFun_memLp_volume`). This is the same globalisation
recipe as in `eigenvectorChartIteratedPartial_memWkp_two_two`. -/

omit [CompleteSpace E] in
/-- **Global order-2 regularity of the eigenvector chart component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀` lies in
`MemWkp 2 2 … (chartTargetEuclid α)` — it has global `W^{2,2}` regularity on the
whole chart target.

The proof builds an interior subdomain `Ω''` (a thickening of the compact
partition-of-unity kernel `chartPouKernel α` inside the chart target), runs the
order-2 interior engine `eigenvector_chartComponent_memWkp` to obtain
`MemWkp 2 2 … Ω''`, and promotes that interior regularity to the whole chart
target via `MemWkp_of_memWkp_precompact_of_ae_zero_off_compact`, the eigenvector
chart component being globally `L²` and vanishing almost everywhere off the
compact kernel. -/
private lemma eigenvector_chartComponent_memWkp_global
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The compact partition-of-unity kernel and its enclosing open chart target.
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- A closed thickening of `K` of radius `R_α` inside the chart target.
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  -- The precompact interior subdomain `Ω'' := thickening (R_α / 2) K`.
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  -- `closure Ω'' ⊆ cthickening (R_α / 2) K ⊆ cthickening R_α K ⊆ chart target`.
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
  -- The difference-quotient room radius `R₀ := R_α / 4`.
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    -- `cthickening R₀ (closure Ω'') ⊆ cthickening R₀ (cthickening (R_α/2) K)`
    -- `⊆ cthickening (R₀ + R_α/2) K ⊆ cthickening R_α K ⊆ chart target`.
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
  -- The order-2 interior engine on the interior subdomain `Ω''`. Its conclusion
  -- is `MemWkp 2 2` of the coercion `EuclN → ℝ` of the eigenvector chart
  -- component, which is definitionally `eigenvectorChartComponentFun`.
  have h_interior :
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        Ω'' :=
    eigenvector_chartComponent_memWkp g r s h_atlas i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  -- The eigenvector chart component is globally `L²` on the chart target.
  have h_global_Lp :
      MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P₀) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartComponentFun_memLp_volume
      (I := I) (M := M) g r s h_atlas i α P₀
  -- The eigenvector chart component vanishes a.e. off the compact kernel `K`.
  have h_ae_zero :
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀
  -- Promote the interior `W^{2,2}(Ω'')` to global `W^{2,2}` of the chart target.
  exact MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
    h_global_Lp h_ae_zero h_interior

/-! ## The coupled induction `P_m`

The order-`(m + 2)` regularity statement `P_m` for the eigenvector chart
component is proved by induction on `m`. The base `P_0` is the globalised
order-2 regularity; the inductive step assembles the order-raiser
`eigenvectorChartComponent_memWkp_m_plus_two_of_iterated` from a level-`(m + 1)`
iterated carrier and the two per-level regularity hypotheses, all discharged
from `P_m`. -/

omit [CompleteSpace E] in
/-- **The coupled interior-regularity induction for the eigenvector chart
component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, and an eigenbasis index `i`, the eigenvector chart
component lies in `MemWkp (m + 2) 2 … (chartTargetEuclid α)` for every order
`m : ℕ`, every chart center `α : M`, and every component multi-index `P₀`.

The proof is induction on `m`:

* `m = 0`: the globalised order-2 regularity
  `eigenvector_chartComponent_memWkp_global`;
* `m + 1`: from the inductive hypothesis `P_m` (the statement at order `m + 2`,
  for all `α, P₀`), the order-raiser
  `eigenvectorChartComponent_memWkp_m_plus_two_of_iterated` at level `m + 1`
  delivers `MemWkp ((m + 1) + 2) 2 = MemWkp (m + 3) 2`. Its two per-level
  regularity hypotheses — global `W^{2,2}` of every `(m + 1)`-fold mixed weak
  partial and global `W^{1,2}` of every `j`-fold mixed weak partial for
  `j ≤ m + 1` — are discharged from `P_m` via the carrier-builder
  `exists_eigenvectorIteratedCarrier`, the carrier-to-`W^{2,2}` engine
  `eigenvectorChartIteratedPartial_memWkp_two_two`, and the polymorphic
  regularity bridge `eigenvectorChartIteratedPartial_memWkp_of_memWkp`. -/
private theorem eigenvector_chartComponent_memWkp_pm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∀ (m : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      -- Base `P_0`: the globalised order-2 regularity.
      intro α P₀
      exact eigenvector_chartComponent_memWkp_global
        (I := I) (M := M) g r s h_atlas i α P₀
  | succ m ih =>
      -- Step `P_m → P_{m+1}`.
      intro α P₀
      classical
      -- `P_m` for the current `(α, P₀)`, at order `m + 2`.
      have h_pm : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ih α P₀
      -- The `h_pou` regularity input for the carrier-builder: at every order
      -- `j + 2` for `j < m + 1` and every `(β, Q)`, the resolvent-coercion
      -- chart component lies in `MemWkp (j + 2) 2`. From `P_m` (order `m + 2`)
      -- via `MemWkp.le_of_le` (since `j + 2 ≤ m + 2`) and the converse bridge.
      have h_pou : ∀ (j : ℕ), j < m + 1 → ∀ (β : M)
          (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro j hj β Q
        -- `P_m` at `(β, Q)`, order `m + 2`, dropped to order `j + 2`.
        have h_pm_βQ : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          ih β Q
        have h_drop : MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : j + 2 ≤ m + 2) h_pm_βQ
        exact resolventChartComponent_memWkp_of_componentFun
          (I := I) (M := M) g r s h_atlas i (j + 2) β Q h_drop
      -- `h_top_memWkp_two`: global `W^{2,2}` of every `(m + 1)`-fold mixed weak
      -- partial of the chart component. For each direction tuple, build the
      -- level-`(m + 1)` carrier and feed it to the carrier-to-`W^{2,2}` engine.
      have h_top_memWkp_two :
          ∀ (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)),
            MemWkp (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) idx)
              (chartTargetEuclid (I := I) (M := M) α) := by
        intro idx
        -- The level-`(m + 1)` carrier with direction field `idx`.
        obtain ⟨D, hD_dir, _hD_fChartEff⟩ :=
          exists_eigenvectorIteratedCarrier (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) idx h_pou
        -- The carrier-to-`W^{2,2}` engine, with parent regularity `P_m`. The
        -- engine's parent hypothesis is at order `(m + 1) + 1 = m + 2`.
        exact eigenvectorChartIteratedPartial_memWkp_two_two
          (I := I) (M := M) g r s h_atlas i α P₀ idx D hD_dir h_pm
      -- `h_intermediate_w1p`: global `W^{1,2}` of every `j`-fold mixed weak
      -- partial of the chart component for `j ≤ m + 1`. From `P_m` (order
      -- `j + 1 ≤ m + 2`) via the polymorphic regularity bridge at `k = 1`.
      have h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m + 1 →
            ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
              MemWkp (d := Module.finrank ℝ E) 1 2
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ j idx)
                (chartTargetEuclid (I := I) (M := M) α) := by
        intro j hj idx
        -- The polymorphic bridge at `k = 1` needs the chart component at order
        -- `1 + j`. `P_m` (order `m + 2`) dropped to order `1 + j ≤ m + 2`.
        have h_parent : MemWkp (d := Module.finrank ℝ E) (1 + j) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : 1 + j ≤ m + 2) h_pm
        exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s h_atlas i α P₀ j 1 h_parent idx
      -- The structural order-raiser at level `m + 1`: chart-`H^{(m+1)+2}` of
      -- the chart component. `(m + 1) + 2 = m + 3 = (m + 1) + 2`.
      have h_raised : MemWkp (d := Module.finrank ℝ E) ((m + 1) + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          h_intermediate_w1p h_top_memWkp_two
      -- `(m + 1) + 2 = (m + 1) + 2` — the goal order is literally this.
      exact h_raised

/-! ## The arbitrary-order headline

Specialising the coupled induction `P_m` at `m := k` gives `MemWkp (k + 2) 2`
of the eigenvector chart component, from which `MemWkp k 2` follows by the
downward monotonicity `MemWkp.le_of_le` (since `k ≤ k + 2`). -/

omit [CompleteSpace E] in
/-- **Arbitrary-order interior regularity of the eigenvector chart component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, an order `k : ℕ`, a chart
center `α : M`, and a component multi-index `P₀`, the eigenvector chart
component `eigenvectorChartComponentFun g r s h_atlas i α P₀` — the chart
`P₀`-component of a resolvent eigenvector of the connection Laplacian `Δ_∇` —
lies in `MemWkp k 2 … (chartTargetEuclid α)`: it has interior `W^{k,2}`
regularity on the whole chart target, for *every* Sobolev order `k`.

This is the closing node of the interior elliptic-regularity bootstrap. The
proof closes the coupled induction `eigenvector_chartComponent_memWkp_pm`,
which establishes `MemWkp (m + 2) 2` of the chart component for every `m`:
specialising at `m := k` and dropping the order from `k + 2` to `k` by the
downward monotonicity `MemWkp.le_of_le` yields the arbitrary-`k` conclusion. -/
theorem eigenvector_chartComponent_memWkp_arbitrary
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- `P_k`: the chart component lies in `MemWkp (k + 2) 2`.
  have h_pk : MemWkp (d := Module.finrank ℝ E) (k + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_pm
      (I := I) (M := M) g r s h_atlas i k α P₀
  -- Drop the order from `k + 2` to `k` by downward monotonicity.
  exact MemWkp.le_of_le (d := Module.finrank ℝ E)
    (by omega : k ≤ k + 2) h_pk

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The arbitrary-order headline produces `MemWkp k 2` of the eigenvector chart
component on the whole chart target, for every `k`. -/
example (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvector_chartComponent_memWkp_arbitrary g r s h_atlas i k α P₀

/-- At `k = 2` the headline reproduces global `W^{2,2}` regularity. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvector_chartComponent_memWkp_arbitrary g r s h_atlas i 2 α P₀

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations above are keyed on the chart-selection witness
`HasLocallyConstantChartAt`. We now build the chart-locality-free twins, re-keyed
onto the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s)`.
The originals above are kept intact. -/

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `resolventChartComponent_memWkp_of_componentFun`. -/
private lemma resolventChartComponent_memWkp_of_componentFun_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_comp : MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `eigenvector_chartComponent_eq_unconditional`: the eigenvector
  -- chart-component element equals `i.fst.val⁻¹ •` the resolvent-coercion
  -- chart-component element.
  have h_chart_eq := eigenvector_chartComponent_eq_unconditional (I := I) (M := M)
    g r s i α P₀
  -- The resolvent-coercion chart component is `i.fst.val •` the eigenvector
  -- chart component, almost everywhere on `Ω`.
  have h_ae :
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i α P₀ y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i) α P₀)
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    -- `i.fst.val • (eigenvector element) = resolvent-coercion element`.
    have h_back :
        i.fst.val •
            tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i)
              α P₀ =
          tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            α P₀ := by
      rw [h_chart_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
    rw [h_back] at h_smul
    filter_upwards [h_smul] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    rfl
  -- `MemWkp N 2` is scalar-invariant: scale the eigenvector chart component.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_global`. -/
private lemma eigenvector_chartComponent_memWkp_global_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The compact partition-of-unity kernel and its enclosing open chart target.
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- A closed thickening of `K` of radius `R_α` inside the chart target.
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  -- The precompact interior subdomain `Ω'' := thickening (R_α / 2) K`.
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  -- `closure Ω'' ⊆ cthickening (R_α / 2) K ⊆ cthickening R_α K ⊆ chart target`.
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
  -- The difference-quotient room radius `R₀ := R_α / 4`.
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
  -- The order-2 interior engine on the interior subdomain `Ω''`. Its conclusion
  -- is `MemWkp 2 2` of the coercion `EuclN → ℝ` of the eigenvector chart
  -- component, which is definitionally `eigenvectorChartComponentFun_ofCompact`.
  have h_interior :
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        Ω'' :=
    eigenvector_chartComponent_memWkp_unconditional g r s i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  -- The eigenvector chart component is globally `L²` on the chart target.
  have h_global_Lp :
      MemLp (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i α P₀) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartComponentFun_ofCompact_memLp_volume
      (I := I) (M := M) g r s i α P₀
  -- The eigenvector chart component vanishes a.e. off the compact kernel `K`.
  have h_ae_zero :
      eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartComponentFun_ofCompact_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀
  -- Promote the interior `W^{2,2}(Ω'')` to global `W^{2,2}` of the chart target.
  exact MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
    h_global_Lp h_ae_zero h_interior

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_pm`. -/
private theorem eigenvector_chartComponent_memWkp_pm_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∀ (m : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      -- Base `P_0`: the globalised order-2 regularity.
      intro α P₀
      exact eigenvector_chartComponent_memWkp_global_unconditional
        (I := I) (M := M) g r s i α P₀
  | succ m ih =>
      -- Step `P_m → P_{m+1}`.
      intro α P₀
      classical
      -- `P_m` for the current `(α, P₀)`, at order `m + 2`.
      have h_pm : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ih α P₀
      -- The `h_pou` regularity input for the carrier-builder: at every order
      -- `j + 2` for `j < m + 1` and every `(β, Q)`, the resolvent-coercion
      -- chart component lies in `MemWkp (j + 2) 2`.
      have h_pou : ∀ (j : ℕ), j < m + 1 → ∀ (β : M)
          (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro j hj β Q
        -- `P_m` at `(β, Q)`, order `m + 2`, dropped to order `j + 2`.
        have h_pm_βQ : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          ih β Q
        have h_drop : MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i β Q)
            (chartTargetEuclid (I := I) (M := M) β) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : j + 2 ≤ m + 2) h_pm_βQ
        exact resolventChartComponent_memWkp_of_componentFun_unconditional
          (I := I) (M := M) g r s i (j + 2) β Q h_drop
      -- `h_top_memWkp_two`: global `W^{2,2}` of every `(m + 1)`-fold mixed weak
      -- partial of the chart component.
      have h_top_memWkp_two :
          ∀ (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)),
            MemWkp (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) idx)
              (chartTargetEuclid (I := I) (M := M) α) := by
        intro idx
        -- The level-`(m + 1)` carrier with direction field `idx`.
        obtain ⟨D, hD_dir, _hD_fChartEff⟩ :=
          exists_eigenvectorIteratedCarrier_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) idx h_pou
        -- The carrier-to-`W^{2,2}` engine, with parent regularity `P_m`.
        exact eigenvectorChartIteratedPartial_memWkp_two_two_unconditional
          (I := I) (M := M) g r s i α P₀ idx D hD_dir h_pm
      -- `h_intermediate_w1p`: global `W^{1,2}` of every `j`-fold mixed weak
      -- partial of the chart component for `j ≤ m + 1`.
      have h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m + 1 →
            ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
              MemWkp (d := Module.finrank ℝ E) 1 2
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ j idx)
                (chartTargetEuclid (I := I) (M := M) α) := by
        intro j hj idx
        -- The polymorphic bridge at `k = 1` needs the chart component at order
        -- `1 + j`. `P_m` (order `m + 2`) dropped to order `1 + j ≤ m + 2`.
        have h_parent : MemWkp (d := Module.finrank ℝ E) (1 + j) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
          MemWkp.le_of_le (d := Module.finrank ℝ E)
            (by omega : 1 + j ≤ m + 2) h_pm
        exact eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ j 1 h_parent idx
      -- The structural order-raiser at level `m + 1`: chart-`H^{(m+1)+2}` of
      -- the chart component.
      have h_raised : MemWkp (d := Module.finrank ℝ E) ((m + 1) + 2) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponent_memWkp_m_plus_two_of_iterated_unconditional
          (I := I) (M := M) g r s i α P₀ (m + 1)
          h_intermediate_w1p h_top_memWkp_two
      exact h_raised

/-- Chart-locality-free twin of `eigenvector_chartComponent_memWkp_arbitrary`. -/
theorem eigenvector_chartComponent_memWkp_arbitrary_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- `P_k`: the chart component lies in `MemWkp (k + 2) 2`.
  have h_pk : MemWkp (d := Module.finrank ℝ E) (k + 2) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_pm_unconditional
      (I := I) (M := M) g r s i k α P₀
  -- Drop the order from `k + 2` to `k` by downward monotonicity.
  exact MemWkp.le_of_le (d := Module.finrank ℝ E)
    (by omega : k ≤ k + 2) h_pk

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
