import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCutoffWeakPartials
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# Iterated Sobolev regularity of the chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`
and a component multi-index `P₀`, the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s h_atlas i α P₀` of the limiting per-component
variational identity is the `μ⁻¹`-rescaled seven-summand bracket

```
(1) − (2) + (3) − (4) − (5) + (6) − (7).
```

`eigenvectorChartRHS_memLp_weighted` (in `EigenvectorChartRHS.lean`) established
its weighted-`L²` membership — i.e. `MemWkp 0 2` — by splitting the bracket and
proving each summand `MemLp 2`. This module upgrades **all seven summands** to
iterated Euclidean Sobolev regularity `MemWkp K 2` for an arbitrary order `K`,
and assembles the full headline `eigenvectorChartRHS_memWkp`, given the genuine
bootstrap input

* `h_pou` — every partition-of-unity Euclidean chart component of the
  `L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)` of the
  eigenvector resolvent is `W^{K+1,2}` on its chart target, at every chart
  centre and for every component multi-index.

## The seven summands

* **Summand 1** — the canonical eigenvector chart component
  `tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α P₀`.
  It is `μ⁻¹` times the chart component of `TensorH1ComplToTensorL2 g r s
  (eigenvectorResolvent …)` (`eigenvector_chartComponent_eq`); `MemWkp` is
  scalar-invariant, so `h_pou α P₀` and `MemWkp.le_of_le` give `MemWkp K 2`.
* **Summand 2** — the cross-left double sum: a finite `C^∞`-coefficient-weighted
  sum of the cross-left limit object `crossLeftLimitComponent`, which is the
  cutoff Euclidean chart component of the section-level covariant gradient
  `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`. The cutoff ↔
  partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`, fed the
  covariant-gradient chart-component regularity `eigenvectorCovGrad_pou_memWkp`,
  makes it `W^{K,2}`; `MemWkp.smul_smooth_bounded` carries the smooth coefficient.
* **Summand 3** — the cross-right double sum: a finite `C^∞`-coefficient-weighted
  sum of the cross-right limit object `crossRightLimitComponent`, which is the
  cutoff Euclidean chart component of the `L²`-coercion `TensorH1ComplToTensorL2
  g r s (eigenvectorResolvent …)`. The cutoff ↔ partition-of-unity bridge, fed
  `h_pou` directly (after a `MemWkp.le_of_le` from `K + 1` to `K`), makes it
  `W^{K,2}`; `MemWkp.smul_smooth_bounded` carries the smooth coefficient.
* **Summands 4, 5, 6** — the principal rotation coefficient limit, the
  lower-order rotation value coefficient limit, and the chart-density-divided
  lower-order gradient divergence limit. Each unfolds to a finite
  `C^∞`-coefficient-weighted sum — each coefficient indicator-cut to the compact
  partition-of-unity kernel — whose atoms are `componentLpLimit` and
  `partialLpLimit`, the `μ`-rescaled canonical eigenvector chart component and
  its weak chart partial. The chart component is `W^{K,2}` (Summand 1 route);
  its weak partial is `W^{K,2}` because the canonical chart component is
  `W^{K+1,2}` and a weak partial of a `W^{K+1,2}` function lies in `W^{K,2}`.
  The atoms vanish almost everywhere off the compact kernel, so the indicator
  cut is absorbed and `MemWkp.smul_smooth_bounded` carries the smooth
  coefficient.
* **Summand 7** — the cross-right gradient divergence limit, divided by the
  chart density. Its atoms are the cutoff cross-right limit object
  `crossRightLimitComponent` (Summand 3 route) and `μ` times the eigenvector
  cutoff chart partial `eigenvectorCutoffChartPartialLp`. The latter is `W^{K,2}`
  because the eigenvector cutoff chart component is `W^{K+1,2}` (the cutoff ↔
  partition-of-unity bridge at order `K + 1`) and the cutoff chart partial is a
  weak partial of it.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Finite-sum closure of iterated Sobolev membership

`MemWkp k p` is closed under addition and contains the zero function, hence is
closed under arbitrary finite sums. -/

/-- **`MemWkp` is closed under finite sums.** If every member of a family of
functions indexed by a finite set is `W^{k,p}`-regular on an open set, then the
pointwise finite sum is `W^{k,p}`-regular. -/
private lemma memWkp_finsetSum
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

/-! ## `MemWkp` for a chart-target-smooth coefficient times an ae-kernel-vanishing
factor

The workhorse for the cross-left and cross-right double sums. Given a coefficient
`C^∞` on the open chart target and a factor that is `MemWkp K 2` on the chart
target and vanishes almost everywhere off a fixed compact kernel inside the chart
target, the product lies in `MemWkp K 2` on the chart target.

The coefficient is cut off to a globally smooth, compactly supported
representative `χ · coef` by a smooth cutoff `χ` equal to `1` on a closed
thickening of the kernel and supported in the chart target. The product
`χ · coef` is globally smooth and compactly supported, so
`MemWkp.smul_smooth_bounded` keeps `MemWkp K 2`; finally
`(χ · coef) · factor =ᵐ coef · factor` because `χ = 1` on the thickening while
the factor ae-vanishes off the kernel. -/

/-- **`MemWkp` closure for a chart-target-smooth coefficient times an
ae-kernel-vanishing `MemWkp K 2` factor.** For a coefficient `coef` that is `C^∞`
on the open Euclidean chart target, a compact kernel `Kkern` inside the chart
target, and a factor that is `MemWkp K 2` on the chart target and vanishes almost
everywhere off `Kkern`, the pointwise product lies in `MemWkp K 2` on the chart
target. -/
private lemma memWkp_smoothCoef_mul_aeZeroFactor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- A smooth cutoff `χ` equal to `1` on a closed thickening of `Kkern`, supported
  -- in the chart target `Ω`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKkern_compact hΩ_open hKkern_in
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ω`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- A uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- `(χ · coef) · factor ∈ MemWkp K 2` via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  -- `(χ · coef) · factor =ᵐ coef · factor` on `volume.restrict Ω`.
  set Cδ : Set EuclN := Metric.cthickening δ Kkern with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  -- The factor ae-vanishes off `Kkern` against `volume.restrict Ω` (the chart
  -- `L²` measure is, definitionally, `volume.restrict Ω`).
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kkern → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  -- On `Cδ ∩ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
  have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
      (fun y => coef y * factor y) := by
    refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hχy : χ y = 1 := hχ_one y hy.2
    change (χ y * coef y) * factor y = coef y * factor y
    rw [hχy]; ring
  -- On `Ω \ Cδ ⊆ Ω \ Kkern`: the factor ae-vanishes, so both products ae-vanish.
  have hKkern_in_Cδ : Kkern ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kkern → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKkern_in_Cδ hyK))
    filter_upwards [h_factor_diff] with y hy
    show (χ y * coef y) * factor y = coef y * factor y
    rw [hy]; ring
  have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
  have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
    ext y; constructor
    · intro hy
      by_cases h : y ∈ Cδ
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
    Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the almost-everywhere equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

/-! ## The eigenvector chart component as a rescaled resolvent chart component

The regularity input `h_pou` is phrased for the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i)` of the
`H¹`-completion resolvent. The canonical eigenvector chart component, however,
references the eigenvector vector `tensorResolventEigenbasisVec h_atlas i`
itself. The two differ by the nonzero scalar `μ⁻¹` (`eigenvector_chartComponent_eq`),
and `MemWkp` is scalar-invariant. -/

/-- The partition-of-unity Euclidean chart components of the eigenvector vector
`tensorResolventEigenbasisVec h_atlas i` are `MemWkp N 2` on every chart
target, given that those of the `L²`-coercion of the eigenvector resolvent are
`MemWkp N 2`. The two chart components differ by the nonzero scalar `μ⁻¹`, and
`MemWkp` is scalar-invariant; the iteration order is preserved. -/
private lemma eigenvectorVec_pou_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- `MemWkp N 2` of the resolvent-coercion chart component.
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    h_pou β Q
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq`). Pass to `coeFn` and rescale.
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_atlas i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  -- `MemWkp N 2` is scalar-invariant.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-! ## Summand 1 — the canonical eigenvector chart component

The first bracketed summand of `eigenvectorChartRHS` is the canonical eigenvector
chart component. Its `W^{K,2}` regularity is immediate from `eigenvectorVec_pou_memWkp`
(transferring the resolvent-coercion regularity to the eigenvector vector) and the
order-monotonicity `MemWkp.le_of_le`, since `K ≤ K + 1`. -/

/-- **Summand 1 is `W^{K,2}`.** The canonical eigenvector chart component
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α P₀` is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`. -/
theorem eigenvectorChartRHS_summand1_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s h_atlas i (K + 1)
    h_pou α P₀).le_of_le (Nat.le_succ K)

/-! ## Summand 2 — the cross-left limit contribution

The second bracketed summand of `eigenvectorChartRHS` is the finite double sum,
over `(r, s + 1)`-component multi-indices `(P, Q)`, of the `C^∞` coefficient
`covChartMetricGram · crossLeftTestCoeff` times the cross-left limit object
`crossLeftLimitComponent g r s h_atlas i α P`.

`crossLeftLimitComponent` is, by definition, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r (s + 1) (tensorCovGradL2Compl g r s
(eigenvectorResolvent …)) α P`. The cutoff ↔ partition-of-unity bridge
`tensorL2ChartComponentCutoff_memWkp_of_pou`, fed the covariant-gradient
chart-component regularity `eigenvectorCovGrad_pou_memWkp`, makes it `W^{K,2}`;
`MemWkp.smul_smooth_bounded` then carries the smooth coefficient. -/

/-- **The cross-left limit object is `W^{K,2}`.** The cross-left limit object
`crossLeftLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
component of the section-level covariant gradient `tensorCovGradL2Compl g r s
(eigenvectorResolvent …)` — is `MemWkp K 2` on the chart-`α` target, given the
order-`(K + 1)` partition-of-unity regularity input `h_pou`.

The cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`
is fed the order-`K` covariant-gradient chart-component regularity
`eigenvectorCovGrad_pou_memWkp` (which itself consumes `h_pou`). -/
theorem crossLeftLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossLeftLimitComponent` is the cutoff chart component of the section-level
  -- covariant gradient `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`.
  rw [crossLeftLimitComponent]
  -- The bridge: feed it the covariant-gradient chart-component regularity, which
  -- itself consumes `h_pou`.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P K
    (fun β Q => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
      g r s h_atlas i K h_pou β Q)

/-- **Summand 2 is `W^{K,2}`.** The cross-left double sum of `eigenvectorChartRHS`
— a finite `C^∞`-coefficient-weighted sum of the cross-left limit object — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`.

Each summand is the `C^∞` coefficient `covChartMetricGram · crossLeftTestCoeff`
times the `W^{K,2}` cross-left limit object; `MemWkp.smul_smooth_bounded` carries
the coefficient and `memWkp_finsetSum` assembles the double sum. -/
theorem eigenvectorChartRHS_summand2_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossLeftTestCoeff` times the `W^{K,2}` cross-left limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-left limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s h_atlas i α P K h_pou
    -- The coefficient `covChartMetricGram · crossLeftTestCoeff` is `C^∞` on the
    -- chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-left limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

/-! ## Summand 3 — the cross-right limit contribution

The third bracketed summand of `eigenvectorChartRHS` is the finite double sum,
over `(r, s)`-component multi-indices `(P, Q)`, of the `C^∞` coefficient
`covChartMetricGram · crossRightTestValueCoeff` times the cross-right limit
object `crossRightLimitComponent g r s h_atlas i α P`.

`crossRightLimitComponent` is, by definition, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r s (TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent …)) α P`. The cutoff ↔ partition-of-unity bridge
`tensorL2ChartComponentCutoff_memWkp_of_pou`, fed `h_pou` directly (after the
order monotonicity `K + 1 ≥ K`), makes it `W^{K,2}`; `MemWkp.smul_smooth_bounded`
then carries the smooth coefficient. -/

/-- **The cross-right limit object is `W^{K,2}`.** The cross-right limit object
`crossRightLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
component of the `L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent
…)` — is `MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

The cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`
is fed `h_pou` directly, after the order monotonicity `MemWkp.le_of_le` from
`K + 1` to `K`. -/
theorem crossRightLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossRightLimitComponent` is the cutoff chart component of the `L²`-coercion
  -- `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)`.
  rw [crossRightLimitComponent]
  -- The bridge: feed it `h_pou` directly, after the order monotonicity.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P K
    (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K))

/-- **Summand 3 is `W^{K,2}`.** The cross-right double sum of `eigenvectorChartRHS`
— a finite `C^∞`-coefficient-weighted sum of the cross-right limit object — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`.

Each summand is the `C^∞` coefficient `covChartMetricGram · crossRightTestValueCoeff`
times the `W^{K,2}` cross-right limit object; `MemWkp.smul_smooth_bounded` carries
the coefficient and `memWkp_finsetSum` assembles the double sum. -/
theorem eigenvectorChartRHS_summand3_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossRightTestValueCoeff` times the `W^{K,2}` cross-right limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-right limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s h_atlas i α P K h_pou
    -- The coefficient `covChartMetricGram · crossRightTestValueCoeff` is `C^∞` on
    -- the chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-right limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

/-! ## A weak partial of a `W^{K+1,2}` function is `W^{K,2}`

The atoms `partialLpLimit` and the eigenvector cutoff chart partial are weak
chart partials of the canonical chart component, respectively the cutoff chart
component, of the eigenvector. When the differentiated function is `W^{K+1,2}`,
its `chosenWeakPartial'` lies in `W^{K,2}` (`MemWkp.chosenWeakPartial_mem`);
any genuine weak partial agrees with `chosenWeakPartial'` almost everywhere
(weak partials are unique up to a.e. equality), so it too lies in `W^{K,2}`. -/

/-- **A weak chart partial of a `W^{K+1,2}` function is `W^{K,2}`.** For an open
set `Ω`, a weak `k`-th partial `gpart` of a function `u` that is `W^{K+1,2}` on
`Ω`, with `gpart` itself `L²` on `Ω`, lies in `W^{K,2}` on `Ω`.

`u ∈ W^{K+1,2}` is in particular `W^{1,2}`, so `chosenWeakPartial' 2 k u Ω` is a
weak `k`-th partial of `u` and lies in `W^{K,2}` (`MemWkp.chosenWeakPartial_mem`).
Both `gpart` and `chosenWeakPartial' 2 k u Ω` are weak `k`-th partials of `u` and
locally integrable, so they agree almost everywhere; `MemWkp` is invariant under
almost-everywhere equality. -/
private lemma memWkp_of_weakPartial_of_memWkp_succ
    {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {gpart u : EuclN → ℝ}
    (hgpart_memLp : MemLp gpart 2 ((volume : Measure EuclN).restrict Ω))
    (hgpart_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gpart u Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 u Ω) :
    MemWkp (d := Module.finrank ℝ E) K 2 gpart Ω := by
  classical
  -- `u` is `W^{1,2}`, so its chosen weak partial is a genuine weak partial.
  have hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω := hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p k
  -- The chosen weak partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) Ω :=
    hu.chosenWeakPartial_mem k
  -- Both weak partials are locally integrable, so they agree almost everywhere.
  have hgpart_loc : LocallyIntegrable gpart
      ((volume : Measure EuclN).restrict Ω) :=
    hgpart_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae : gpart =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hgpart_weak h_chosen_weak
      hgpart_loc h_chosen_loc
  -- `MemWkp` is invariant under almost-everywhere equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mpr h_chosen_memWkp

/-! ## A weak partial inherits the support of the differentiated function

Weak partial derivatives are local: on the open complement of a closed set, a
weak partial of a function `u` that vanishes almost everywhere off that closed
set is itself almost everywhere zero. The chart-component and cutoff-chart-component
atoms vanish almost everywhere off the compact partition-of-unity kernel, so their
weak chart partials do too. -/

/-- **A weak chart partial inherits the off-kernel vanishing of the
differentiated function.** For an open set `Ω`, a closed set `Kc`, a weak `k`-th
partial `gp` of a `W^{1,2}`-on-`Ω` function `u` that vanishes almost everywhere
off `Kc`, with `gp` itself `L²` on `Ω`, the weak partial `gp` vanishes almost
everywhere off `Kc`.

The open subset `V := Ω \ Kc` carries `u =ᵐ 0`. The chosen weak `k`-th partial
of `u` on `V` is therefore almost everywhere zero on `V`
(`chosenWeakPartial'_ae_zero_of_ae_zero`); it and the restriction of `gp` to `V`
are both weak `k`-th partials of `u` on `V`, so they agree almost everywhere on
`V`, whence `gp =ᵐ 0` on `V`. -/
private lemma hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {Kc : Set EuclN} (hKc_closed : IsClosed Kc)
    {gp u : EuclN → ℝ}
    (hgp_memLp : MemLp gp 2 ((volume : Measure EuclN).restrict Ω))
    (hgp_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u Ω)
    (hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (hu_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → u y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → gp y = 0 := by
  classical
  -- The open subset `V := Ω \ Kc`.
  set V : Set EuclN := Ω \ Kc with hV_def
  have hV_open : IsOpen V := hΩ_open.sdiff hKc_closed
  have hV_sub : V ⊆ Ω := Set.diff_subset
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- `u =ᵐ 0` on `volume.restrict V`.
  have hu_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := by
    have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict V),
        y ∉ Kc → u y = 0 :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono hV_sub le_rfl)).ae_le hu_zero
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict V), y ∈ V :=
      ae_restrict_mem hV_meas
    filter_upwards [h_lift, h_mem] with y hy hy_mem
    exact hy hy_mem.2
  -- `u ∈ W^{1,2}(V)`.
  have hu_w1p_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u V :=
    MemW1p.mono_set hV_open hV_sub hu_w1p
  -- The chosen weak `k`-th partial of `u` on `V` is a.e. zero on `V`.
  have h_chosen_zero : chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      (by norm_num) hV_open hu_zero_V k
  -- It is a genuine weak `k`-th partial of `u` on `V`.
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p_V k
  -- `gp` restricted to `V` is a weak `k`-th partial of `u` on `V`.
  have hgp_weak_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub hgp_weak
  -- Both weak partials are locally integrable on `V`, hence agree a.e. on `V`.
  have hgp_loc_V : LocallyIntegrable gp
      ((volume : Measure EuclN).restrict V) :=
    (hgp_memLp.mono_measure (Measure.restrict_mono hV_sub le_rfl)).locallyIntegrable
      (by norm_num)
  have h_chosen_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V)
      ((volume : Measure EuclN).restrict V) :=
    (chosenWeakPartial'_memLp_of_mem hu_w1p_V k).locallyIntegrable (by norm_num)
  have h_gp_eq : gp =ᵐ[(volume : Measure EuclN).restrict V]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open hgp_weak_V h_chosen_weak
      hgp_loc_V h_chosen_loc_V
  -- Hence `gp =ᵐ 0` on `volume.restrict V`.
  have hgp_zero_V : gp =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := h_gp_eq.trans h_chosen_zero
  -- Lift to `volume.restrict Ω`: off `Kc` and inside `Ω` is exactly `V`.
  have hgp_zero_V' : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ V → gp y = 0 := by
    have h := (ae_restrict_iff' hV_meas).mp hgp_zero_V
    filter_upwards [h] with y hy hy_mem
    exact hy hy_mem
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hgp_zero_V'] with y hy hy_mem hy_notKc
  exact hy ⟨hy_mem, hy_notKc⟩

/-! ## Off-cutoff-kernel vanishing of the cutoff chart-partial atom

The cutoff chart-partial atom `cutoffPartialLpLimit g r s h_atlas i α P k` is a
genuine weak `k`-th partial of the eigenvector cutoff chart component
`tensorL2ChartComponentCutoff g r s (tensorResolventEigenbasisVec h_atlas i) α
P`, which vanishes almost everywhere off the compact cutoff kernel
`cutoffChartKernelEuclid α`. The cutoff chart component is `W^{1,2}` without any
regularity hypothesis — its weak partial in every direction is the corresponding
`L²` cutoff chart-partial limit object — so the locality of weak partials
propagates the off-kernel vanishing to the cutoff chart-partial atom. -/

/-- **The eigenvector cutoff chart component is `W^{1,2}` unconditionally.** Its
weak `k`-th partial in every chart-coordinate direction `k` is the `L²` cutoff
chart-partial limit object `eigenvectorCutoffChartPartialLp g r s h_atlas i α P
k`, so the canonical `W^{1,2}`-membership predicate holds with no
partition-of-unity regularity input. -/
lemma eigenvectorCutoffChartComponent_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨Lp.memLp _, fun k => ?_⟩
  refine ⟨((eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s h_atlas i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ),
    Lp.memLp _, ?_⟩
  exact eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv (I := I) (M := M)
    g r s h_atlas i α P k

/-- **Off-cutoff-kernel vanishing of the cutoff chart-partial atom.** For any
eigenbasis index `i`, the cutoff chart-partial atom `cutoffPartialLpLimit g r s
h_atlas i α P k` vanishes almost everywhere — on the plain Lebesgue volume
restricted to the chart target — off the compact cutoff kernel
`cutoffChartKernelEuclid α`. No partition-of-unity regularity hypothesis is
needed: the cutoff chart component is unconditionally `W^{1,2}`, the cutoff
chart-partial atom is a weak partial of it, and the locality of weak partials
transfers the off-kernel vanishing. -/
lemma cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((cutoffPartialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `cutoffPartialLpLimit = μ • eigenvectorCutoffChartPartialLp`; the bare
  -- cutoff chart partial is a weak `k`-th partial of the cutoff chart component.
  have h_smul : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val •
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [cutoffPartialLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  -- The bare cutoff chart partial is a weak `k`-th partial of the cutoff chart
  -- component, which vanishes a.e. off the compact cutoff kernel.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P k
  have h_comp_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartComponent_memW1p (I := I) (M := M)
      g r s h_atlas i α P
  -- The cutoff chart component vanishes a.e. off the compact cutoff kernel.
  have h_comp_zero := tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P
  -- The locality of weak partials propagates the off-kernel vanishing.
  have h_partial_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α).isClosed
      (Lp.memLp _) h_weak h_comp_memW1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  filter_upwards [h_smul, h_partial_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The eigenvector cutoff chart component is `W^{1,2}` unconditionally
(chart-locality-free).** Chart-locality-free twin of
`eigenvectorCutoffChartComponent_memW1p`, keyed on the unconditional compactness
witness `tensorResolventL2_isCompactOperator_intrinsic` through
`tensorResolventEigenbasisVec_ofCompact`. Its weak `k`-th partial in every
chart-coordinate direction `k` is the chart-locality-free `L²` cutoff
chart-partial limit object `eigenvectorCutoffChartPartialLp_unconditional g r s i
α P k`, so the canonical `W^{1,2}`-membership predicate holds with no
partition-of-unity regularity input and no chart-selection hypothesis. -/
lemma eigenvectorCutoffChartComponent_memW1p_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨Lp.memLp _, fun k => ?_⟩
  refine ⟨((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
      g r s i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ),
    Lp.memLp _, ?_⟩
  exact eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv_unconditional
    (I := I) (M := M) g r s i α P k

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Off-cutoff-kernel vanishing of the cutoff chart-partial atom
(chart-locality-free).** Chart-locality-free twin of
`cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid`, keyed on the
unconditional compactness witness `tensorResolventL2_isCompactOperator_intrinsic`
through `tensorResolventEigenbasisVec_ofCompact`. For any eigenbasis index `i`,
the chart-locality-free cutoff chart-partial atom `cutoffPartialLpLimit_unconditional
g r s i α P k` vanishes almost everywhere — on the plain Lebesgue volume
restricted to the chart target — off the compact cutoff kernel
`cutoffChartKernelEuclid α`. No partition-of-unity regularity hypothesis and no
chart-selection hypothesis are needed: the cutoff chart component is
unconditionally `W^{1,2}`, the cutoff chart-partial atom is a weak partial of it,
and the locality of weak partials transfers the off-kernel vanishing. -/
lemma cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((cutoffPartialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `cutoffPartialLpLimit_unconditional = μ • eigenvectorCutoffChartPartialLp_unconditional`;
  -- the bare cutoff chart partial is a weak `k`-th partial of the cutoff chart
  -- component.
  have h_smul : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val •
        ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [cutoffPartialLpLimit_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  -- The bare cutoff chart partial is a weak `k`-th partial of the cutoff chart
  -- component, which vanishes a.e. off the compact cutoff kernel.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv_unconditional
      (I := I) (M := M) g r s i α P k
  have h_comp_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartComponent_memW1p_unconditional (I := I) (M := M)
      g r s i α P
  -- The cutoff chart component vanishes a.e. off the compact cutoff kernel.
  have h_comp_zero := tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
      i) α P
  -- The locality of weak partials propagates the off-kernel vanishing.
  have h_partial_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α).isClosed
      (Lp.memLp _) h_weak h_comp_memW1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  filter_upwards [h_smul, h_partial_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-! ## `MemWkp` for an indicator-cut chart-target-smooth coefficient times an
ae-kernel-vanishing factor

The lower-order limit summands 4, 5, 6 and 7 are finite sums of products of a
coefficient — a `C^∞` chart-target function indicator-cut to a compact kernel —
with an `L²` chart-component or chart-partial limit object. The limit objects
vanish almost everywhere off the compact kernel, so the indicator cut is
absorbed: the indicator-cut product agrees almost everywhere with the bare
`C^∞`-coefficient product, which is `MemWkp K 2` by the smooth-coefficient
workhorse `memWkp_smoothCoef_mul_aeZeroFactor`. -/

/-- **`MemWkp` closure for an indicator-cut chart-target-smooth coefficient times
an ae-kernel-vanishing `MemWkp K 2` factor.** For a coefficient `coef` that is
`C^∞` on the open Euclidean chart target, a compact kernel `Kkern` inside the
chart target, and a factor that is `MemWkp K 2` on the chart target and vanishes
almost everywhere off `Kkern` (with respect to the chart `L²` measure), the
pointwise product of the `Kkern`-indicator-cut coefficient with the factor lies
in `MemWkp K 2` on the chart target.

Off `Kkern` the indicator-cut coefficient is zero and the factor vanishes almost
everywhere; on `Kkern` the indicator-cut coefficient equals `coef`. Hence the
indicator-cut product agrees almost everywhere with `coef · factor`, which is
`MemWkp K 2` by `memWkp_smoothCoef_mul_aeZeroFactor`. -/
private lemma memWkp_indicatorSmoothCoef_mul_aeZeroFactor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => Set.indicator Kkern coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The bare `C^∞`-coefficient product is `MemWkp K 2`.
  have h_bare : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      hKkern_compact hKkern_in hcoef_chart hfactor_memWkp hfactor_ae_zero
  -- The indicator-cut product agrees almost everywhere with the bare product.
  have h_ae : (fun y => Set.indicator Kkern coef y * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        y ∉ Kkern → factor y = 0 := by
      have h := hfactor_ae_zero
      rw [chartL2Measure] at h
      exact h
    filter_upwards [hfactor_ae_zero'] with y hy
    by_cases hyK : y ∈ Kkern
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr h_bare

/-! ## `MemWkp` for a chart-target-smooth, off-kernel-vanishing coefficient times
an arbitrary `MemWkp K 2` factor

When the coefficient is itself `C^∞` on the chart target *and* vanishes off a
compact kernel inside the chart target, it extends to a globally smooth,
compactly-supported function — no auxiliary cutoff is needed. Its product with
any `MemWkp K 2` factor is then `MemWkp K 2` by `MemWkp.smul_smooth_bounded`,
with no support hypothesis on the factor. This is the workhorse for the
cross-right divergence summand, whose coefficient `crossRightDivFactor` carries
an off-kernel-vanishing partition-of-unity gradient factor. -/

/-- **`MemWkp` closure for a chart-target-smooth, off-kernel-vanishing
coefficient times an arbitrary `MemWkp K 2` factor.** For a coefficient `coef`
that is `C^∞` on the open Euclidean chart target and vanishes pointwise off a
compact kernel `Kkern` inside the chart target, and an arbitrary `MemWkp K 2`
factor, the pointwise product `coef · factor` lies in `MemWkp K 2` on the chart
target.

The off-kernel vanishing makes `coef` globally `C^∞` (smooth on its closed
support inside the chart target, identically zero on the open complement) and
compactly supported; `MemWkp.smul_smooth_bounded` then keeps `MemWkp K 2`. -/
private lemma memWkp_offKernelSmoothCoef_mul
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0)
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The closed support of `coef` sits inside the compact kernel, hence in `Ω`.
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  -- `coef` is globally `C^∞`: smooth on `tsupport coef ⊆ Ω`, zero off it.
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  -- A uniform bound on the iterated derivatives of `coef` up to order `K`.
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hcoef_smooth
    (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp

/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞` and strictly positive
there, so the quotient is `C^∞`. -/
private lemma recipDensityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => 1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div
    (Laplacian.MetricExtension.densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy =>
      (Laplacian.MetricExtension.densityOnEuclid_pos (I := I) g α hy).ne')

/-! ## The chart-component and chart-partial atoms are `W^{K,2}`

The lower-order limit summands are finite sums of indicator-cut `C^∞`
coefficients times the two atoms `componentLpLimit` and `partialLpLimit`. The
component atom is `μ` times the canonical eigenvector chart component, which is
`W^{K,2}` by the Summand-1 route. The partial atom is `μ` times the weak chart
partial of that chart component; the chart component is `W^{K+1,2}`, so its weak
partial is `W^{K,2}`. Both atoms vanish almost everywhere off the compact
partition-of-unity kernel. -/

/-- The component atom `componentLpLimit g r s h_atlas i α P` — `μ` times the
canonical eigenvector chart component — is `MemWkp K 2` on the chart-`α` target,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou`. -/
lemma componentLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{K,2}` (Summand-1 route).
  have h_comp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
      g r s h_atlas i α P K h_pou
  -- `componentLpLimit = μ • tensorL2ChartComponent (eigenvector)`; rescale.
  have h_ae : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P)
    have h_smul' : (fun y => ((componentLpLimit (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [componentLpLimit]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

/-- The component atom `componentLpLimit g r s h_atlas i α P` vanishes almost
everywhere off the compact partition-of-unity kernel `chartPouKernel α`. It is
`μ` times the canonical eigenvector chart component, which is a.e. supported in
`chartPouKernel α` (`tensorL2ChartComponent_ae_zero_off_chartPouKernel`). -/
private lemma componentLpLimit_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  -- `componentLpLimit = μ • tensorL2ChartComponent (eigenvector)`.
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  -- The canonical eigenvector chart component vanishes a.e. off the kernel.
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P
  filter_upwards [h_smul, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-- The chart-partial atom `partialLpLimit g r s h_atlas i α P k` — `μ` times
the weak `k`-th chart partial of the canonical eigenvector chart component — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

The canonical eigenvector chart component is `W^{K+1,2}` (the Summand-1 route at
order `K + 1`), and the eigenvector weak chart partial is a genuine weak partial
of it (`eigenvectorChartWeakPartial_hasWeakPartialDeriv`); a weak partial of a
`W^{K+1,2}` function is `W^{K,2}`. The `μ` rescaling preserves `MemWkp`. -/
lemma partialLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{K+1,2}`.
  have h_comp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorVec_pou_memWkp (I := I) (M := M) g r s h_atlas i (K + 1)
      h_pou α P
  -- The eigenvector weak chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P k
  -- The weak chart partial is `L²` (it is the coercion of an `Lp` class).
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  -- A weak partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k)
      Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_comp_succ
  -- `partialLpLimit = μ • eigenvectorChartPartialLp`; rescale.
  have h_ae : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorChartPartialLp (I := I) (M := M) g r s h_atlas i α P k)
    have h_smul' : (fun y => ((partialLpLimit (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P k y) := by
      rw [partialLpLimit, eigenvectorChartWeakPartial]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

/-- The chart-partial atom `partialLpLimit g r s h_atlas i α P k` vanishes
almost everywhere off the compact partition-of-unity kernel `chartPouKernel α`,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou`.

It is `μ` times the eigenvector weak chart partial. The canonical eigenvector
chart component is `W^{K+1,2}` — in particular `W^{1,2}` — and vanishes almost
everywhere off `chartPouKernel α`; the eigenvector weak chart partial is a
genuine weak partial of it, so by the locality of weak partials
(`hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off`) it too vanishes almost
everywhere off the compact (hence closed) kernel. -/
private lemma partialLpLimit_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{1,2}` (from `W^{K+1,2}`).
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s h_atlas i (K + 1)
      h_pou α P).memW1p
  -- The eigenvector weak chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P k
  -- The eigenvector weak chart partial is `L²`.
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  -- The canonical chart component vanishes a.e. off the kernel.
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P
  -- Locality of weak partials propagates the off-kernel vanishing.
  have h_weak_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      h_weak_memLp h_weak h_comp_w1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  -- `partialLpLimit = μ • eigenvectorChartWeakPartial`; the `μ` scaling is
  -- harmless for the off-kernel vanishing.
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak_zero' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y = 0 := by
    rw [chartL2Measure]; exact h_weak_zero
  filter_upwards [h_smul, h_weak_zero'] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-! ## Summand 4 — the principal rotation coefficient limit

The fourth bracketed summand of `eigenvectorChartRHS` is the principal rotation
coefficient limit `covPrincipalRotationCoeffLimit`, a finite four-fold sum of the
indicator-cut `C^∞` factor `principalRotationFactor` times the chart-partial atom
`partialLpLimit`. Each summand is `W^{K,2}` by
`memWkp_indicatorSmoothCoef_mul_aeZeroFactor`, fed the `W^{K,2}` chart-partial
atom and its almost-everywhere vanishing off the partition-of-unity kernel. -/

/-- **Summand 4 is `W^{K,2}`.** The principal rotation coefficient limit
`covPrincipalRotationCoeffLimit g r s h_atlas i α P₀` is `MemWkp K 2` on the
chart-`α` target, given the order-`(K + 1)` partition-of-unity regularity input
`h_pou`.

It is a finite four-fold sum of the `chartPouKernel`-indicator-cut `C^∞` factor
`principalRotationFactor` times the chart-partial atom `partialLpLimit`; the atom
is `W^{K,2}` and vanishes almost everywhere off the partition-of-unity kernel, so
`memWkp_indicatorSmoothCoef_mul_aeZeroFactor` applies summand-by-summand. -/
theorem eigenvectorChartRHS_summand4_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covPrincipalRotationCoeffLimit
  -- Each `(P, Q, k, l)`-leaf is `W^{K,2}`.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
      (k l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q k l
    exact memWkp_indicatorSmoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (principalRotationFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α P k K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s h_atlas i α P k K h_pou)
  -- Assemble the four-fold finite sum.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k y => ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun l _ => h_leaf P Q k l))))

/-! ## Summand 5 — the lower-order rotation value coefficient limit

The fifth bracketed summand of `eigenvectorChartRHS` is the lower-order rotation
value coefficient limit `covLowerOrderRotationValueCoeffLimit`, the sum of a
four-fold chart-partial-atom sum (`valuePartialFactor` against `partialLpLimit`)
and a five-fold component-atom sum (`valueComponentFactor` against
`componentLpLimit`), each coefficient indicator-cut to the partition-of-unity
kernel. Both atom groups are `W^{K,2}` by
`memWkp_indicatorSmoothCoef_mul_aeZeroFactor`. -/

/-- **Summand 5 is `W^{K,2}`.** The lower-order rotation value coefficient limit
`covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀` is `MemWkp K 2` on
the chart-`α` target, given the order-`(K + 1)` partition-of-unity regularity
input `h_pou`.

It is the sum of a four-fold chart-partial-atom sum and a five-fold
component-atom sum; each leaf is the `chartPouKernel`-indicator-cut `C^∞` factor
(`valuePartialFactor`, `valueComponentFactor`) times an atom (`partialLpLimit`,
`componentLpLimit`) that is `W^{K,2}` and vanishes almost everywhere off the
partition-of-unity kernel, so `memWkp_indicatorSmoothCoef_mul_aeZeroFactor`
applies leaf-by-leaf. -/
theorem eigenvectorChartRHS_summand5_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · -- The chart-partial-atom group.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α P k K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α P k K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => h_leaf P Q k l))))
  · -- The component-atom group.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
            ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valueComponentFactor (I := I) (M := M)
                  g r s α P₀ P Q k l p) y *
              ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
              hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (fun p _ => h_leaf P Q k l p)))))

/-! ## Summand 6 — the lower-order gradient divergence limit

The sixth bracketed summand of `eigenvectorChartRHS` is the finite sum over
chart directions `l` of the chart-density-divided lower-order gradient
divergence limit `weightedGradCoeffDivLimit`. Each `weightedGradCoeffDivLimit` is
the sum of a four-fold component-atom sum (`euclidPartial l weightedGradFactor`
against `componentLpLimit`) and a four-fold chart-partial-atom sum
(`weightedGradFactor` against `partialLpLimit`), each coefficient indicator-cut
to the partition-of-unity kernel; both atom groups are `W^{K,2}` by
`memWkp_indicatorSmoothCoef_mul_aeZeroFactor`. The summand of `eigenvectorChartRHS`
divides the sum by the chart density; the reciprocal `1 / densityOnEuclid g α` is
`C^∞` on the chart target and `memWkp_smoothCoef_mul_aeZeroFactor` carries it. -/

/-- **The lower-order gradient divergence limit `weightedGradCoeffDivLimit` is
`W^{K,2}`.** For a chart direction `l`, `weightedGradCoeffDivLimit g r s h_atlas
i α P₀ l` is `MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

It is the sum of a four-fold component-atom sum and a four-fold chart-partial-atom
sum; each leaf is the `chartPouKernel`-indicator-cut `C^∞` factor
(`euclidPartial l weightedGradFactor`, `weightedGradFactor`) times an atom
(`componentLpLimit`, `partialLpLimit`) that is `W^{K,2}` and vanishes almost
everywhere off the partition-of-unity kernel. -/
theorem weightedGradCoeffDivLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (weightedGradCoeffDivLimit (I := I) (M := M) g r s h_atlas i α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold weightedGradCoeffDivLimit
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · -- The component-atom group: `∂_l weightedGradFactor · componentLpLimit`.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))
  · -- The chart-partial-atom group: `weightedGradFactor · partialLpLimit`.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α p l K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α p l K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))

/-- **Summand 6 is `W^{K,2}`.** The chart-density-divided sum over chart
directions of the lower-order gradient divergence limit — the sixth bracketed
summand of `eigenvectorChartRHS` — is `MemWkp K 2` on the chart-`α` target, given
the order-`(K + 1)` partition-of-unity regularity input `h_pou`.

Each `weightedGradCoeffDivLimit` is `W^{K,2}` (`weightedGradCoeffDivLimit_memWkp`)
and vanishes almost everywhere off the compact partition-of-unity kernel; the
finite sum over chart directions is therefore `W^{K,2}` and so is the product
with the `C^∞` chart-density reciprocal, by
`memWkp_smoothCoef_mul_aeZeroFactor`. -/
theorem eigenvectorChartRHS_summand6_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The finite sum over chart directions is `W^{K,2}`.
  have h_sum : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ l y) Ω :=
    memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l y => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l y)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s h_atlas i α P₀ l K h_pou)
  -- The finite sum vanishes almost everywhere off the partition-of-unity kernel:
  -- every summand of every `weightedGradCoeffDivLimit` carries an
  -- `indicator (chartPouKernel α)` factor.
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => Finset.sum_eq_zero
      (fun l _ => weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ l hy_imp))
  -- The reciprocal chart density is `C^∞` on the chart target.
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_sum h_sum_ae_zero

/-! ## Summand 7 — the cross-right gradient divergence limit

The seventh bracketed summand of `eigenvectorChartRHS` is the chart-density-
divided cross-right gradient divergence limit `crossRightGradCoeffDivLimit`. The
divergence limit is the sum of a three-fold component-atom sum
(`euclidPartial l crossRightDivFactor` against the cutoff cross-right limit
object `crossRightLimitComponent`) and a three-fold chart-partial-atom sum
(`crossRightDivFactor` against the cutoff chart-partial atom `cutoffPartialLpLimit`),
each coefficient indicator-cut to the partition-of-unity kernel. The cutoff
cross-right limit object is `W^{K,2}` by the Summand-3 route; the cutoff
chart-partial atom is `μ` times the eigenvector cutoff chart partial, which is
the weak partial of the `W^{K+1,2}` eigenvector cutoff chart component. -/

/-- The cutoff chart-partial atom `cutoffPartialLpLimit g r s h_atlas i α P k` —
`μ` times the eigenvector cutoff chart partial — is `MemWkp K 2` on the chart-`α`
target, given the order-`(K + 1)` partition-of-unity regularity input `h_pou`.

The eigenvector cutoff chart component is `W^{K+1,2}` (the cutoff ↔
partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou` at order
`K + 1`, fed `h_pou`); the eigenvector cutoff chart partial is a genuine weak
partial of it (`eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv`); a weak
partial of a `W^{K+1,2}` function is `W^{K,2}`. The `μ` rescaling preserves
`MemWkp`. -/
theorem cutoffPartialLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The eigenvector cutoff chart component is `W^{K+1,2}`: feed `h_pou` at
  -- order `K + 1` (after `MemWkp.le_of_le`) to the cutoff ↔ POU bridge applied
  -- to the eigenvector vector.
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp (I := I) (M := M)
      g r s h_atlas i (K + 1) h_pou β Q
  have h_cutoff_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P (K + 1)
      h_pou_eigen
  -- The eigenvector cutoff chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P k
  -- The cutoff chart partial is `L²` (it is the coercion of an `Lp` class).
  have h_weak_memLp : MemLp
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict Ω) := Lp.memLp _
  -- A weak partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_cutoff_succ
  -- `cutoffPartialLpLimit = μ • eigenvectorCutoffChartPartialLp`; rescale.
  have h_ae : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s h_atlas i α P k)
    have h_smul' : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [cutoffPartialLpLimit]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

/-- **Summand 7 is `W^{K,2}`.** The chart-density-divided cross-right gradient
divergence limit — the seventh bracketed summand of `eigenvectorChartRHS` — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

The divergence limit `crossRightGradCoeffDivLimit` is the sum of a three-fold
component-atom sum and a three-fold chart-partial-atom sum; each leaf is the
`chartPouKernel`-indicator-cut `C^∞` factor (`euclidPartial l crossRightDivFactor`,
`crossRightDivFactor`) times an atom (`crossRightLimitComponent`,
`cutoffPartialLpLimit`) that is `W^{K,2}`. The coefficient `crossRightDivFactor`
itself vanishes off the partition-of-unity kernel, so the indicator cut is the
identity and `memWkp_offKernelSmoothCoef_mul` applies — no support hypothesis on
the atom is needed. The divergence limit is therefore `W^{K,2}` and so is the
product with the `C^∞` chart-density reciprocal. -/
theorem eigenvectorChartRHS_summand7_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The cross-right gradient divergence limit is `W^{K,2}`.
  have h_div : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀) Ω := by
    unfold crossRightGradCoeffDivLimit
    refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
    · -- The component-atom group: `∂_l crossRightDivFactor ·
      -- crossRightLimitComponent`. The coefficient `∂_l crossRightDivFactor`
      -- itself vanishes off the partition-of-unity kernel, so the indicator cut
      -- is the identity and `memWkp_offKernelSmoothCoef_mul` applies — no
      -- support hypothesis on the atom is needed.
      have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        -- The indicator cut is the identity: `∂_l crossRightDivFactor`
        -- vanishes off `chartPouKernel`.
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
            g r s α P₀ l P Q)
          (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (crossRightLimitComponent_memWkp (I := I) (M := M)
            g r s h_atlas i α P K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
    · -- The chart-partial-atom group: `crossRightDivFactor · cutoffPartialLpLimit`.
      -- Again the coefficient `crossRightDivFactor` vanishes off the
      -- partition-of-unity kernel, so the indicator cut is the identity.
      have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
            ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
          (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (cutoffPartialLpLimit_memWkp (I := I) (M := M)
            g r s h_atlas i α P l K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
  -- The divergence limit vanishes almost everywhere off the partition-of-unity
  -- kernel.
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ hy_imp)
  -- The reciprocal chart density is `C^∞` on the chart target.
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_div h_div_ae_zero

/-! ## The full chart right-hand side

`eigenvectorChartRHS g r s h_atlas i α P₀` is the `μ⁻¹`-rescaled bracketed
combination `(1) − (2) + (3) − (4) − (5) + (6) − (7)` of the seven summand
objects. All seven summands are `MemWkp K 2`; the `MemWkp` arithmetic closures
(`MemWkp.add`, `MemWkp.sub`, `MemWkp.const_smul`) assemble the bracket and carry
the global `μ⁻¹` factor. -/

/-- **The chart-Euclidean right-hand side is `W^{K,2}`.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the chart-Euclidean
right-hand side `eigenvectorChartRHS g r s h_atlas i α P₀` of the limiting
per-component variational identity is `MemWkp K 2` on the chart-`α` target — i.e.
iterated Euclidean Sobolev regular of order `K` — given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

`eigenvectorChartRHS` is the `μ⁻¹`-rescaled bracketed combination
`(1) − (2) + (3) − (4) − (5) + (6) − (7)` of seven summand objects. Summands 1–3
are `W^{K,2}` by `eigenvectorChartRHS_summand{1,2,3}_memWkp`; summands 4–7 by
`eigenvectorChartRHS_summand{4,5,6,7}_memWkp`. The `MemWkp` arithmetic closures
assemble the bracket and carry the global `μ⁻¹` factor. -/
theorem eigenvectorChartRHS_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  -- Summand 1.
  have h1 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 2.
  have h2 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand2_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 3.
  have h3 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand3_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 4.
  have h4 : MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀) Ω :=
    eigenvectorChartRHS_summand4_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 5.
  have h5 : MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀) Ω :=
    eigenvectorChartRHS_summand5_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 6.
  have h6 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y)) Ω :=
    eigenvectorChartRHS_summand6_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Summand 7.
  have h7 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y) Ω :=
    eigenvectorChartRHS_summand7_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ K h_pou
  -- Assemble the bracket `(1) − (2) + (3) − (4) − (5) + (6) − (7)` and the
  -- global `μ⁻¹` factor by the `MemWkp` arithmetic closures.
  have h12 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1 h2
  have h123 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12 h3
  have h1234 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123 h4
  have h12345 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1234 h5
  have h123456 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12345 h6
  have h1234567 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123456 h7
  have h_assembled : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E) hp hΩ_open h1234567 (i.fst.val)⁻¹
  -- The assembled bracket function is, pointwise, `eigenvectorChartRHS`.
  refine (MemWkp_congr_ae (d := Module.finrank ℝ E) hp hΩ_open
    (Filter.Eventually.of_forall (fun y => ?_))).mp h_assembled
  rw [eigenvectorChartRHS]

/-! ## Chart-locality-free twins of the limit-atom `MemWkp` memberships

The atom `MemWkp K 2` memberships above are keyed, through the eigenvector vector
`tensorResolventEigenbasisVec h_atlas i`, on the chart-selection hypothesis
`h_atlas`. Each one used `h_atlas` only to select the eigenbasis vector and its
resolvent; both have chart-locality-free twins keyed on the unconditional
compactness witness `tensorResolventL2_isCompactOperator_intrinsic` through
`tensorResolventEigenbasisVec_ofCompact`. We re-key the partition-of-unity
regularity input `h_pou` onto `eigenvectorResolvent_unconditional` and assemble
the chart-locality-free atoms from the committed unconditional limit objects and
weak-partial facts. All proof bodies transfer verbatim. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The partition-of-unity Euclidean chart components of the chart-locality-free
eigenvector vector `tensorResolventEigenbasisVec_ofCompact` are `MemWkp N 2` on
every chart target, given that those of the `L²`-coercion of the chart-locality-free
eigenvector resolvent are `MemWkp N 2`. Chart-locality-free twin of
`eigenvectorVec_pou_memWkp`: the two chart components differ by the nonzero scalar
`μ⁻¹` (`eigenvector_chartComponent_eq_unconditional`), and `MemWkp` is
scalar-invariant; the iteration order is preserved. -/
private lemma eigenvectorVec_pou_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- `MemWkp N 2` of the resolvent-coercion chart component.
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    h_pou β Q
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq_unconditional`). Rescale.
  have h_chart_eq := eigenvector_chartComponent_eq_unconditional (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
          i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  -- `MemWkp N 2` is scalar-invariant.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 1 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand1_memWkp`: the canonical chart-locality-free
eigenvector chart component is `MemWkp K 2` on the chart-`α` target, given the
order-`(K + 1)` partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand1_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorVec_pou_memWkp_unconditional (I := I) (M := M) g r s i (K + 1)
    h_pou α P₀).le_of_le (Nat.le_succ K)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The cross-left limit object is `W^{K,2}` (chart-locality-free).**
Chart-locality-free twin of `crossLeftLimitComponent_memWkp`, keyed on the
unconditional compactness witness through `eigenvectorResolvent_unconditional`.
The cross-left limit object `crossLeftLimitComponent_unconditional g r s i α P` is
by definition the cutoff Euclidean chart component of the section-level covariant
gradient `tensorCovGradL2Compl g r s (eigenvectorResolvent_unconditional …)`. The
cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou` is
fed the order-`K` covariant-gradient chart-component regularity
`eigenvectorCovGrad_pou_memWkp_unconditional` (which itself consumes `h_pou`). -/
theorem crossLeftLimitComponent_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossLeftLimitComponent_unconditional` is the cutoff chart component of the
  -- section-level covariant gradient `tensorCovGradL2Compl g r s
  -- (eigenvectorResolvent_unconditional …)`.
  rw [crossLeftLimitComponent_unconditional]
  -- The bridge: feed it the covariant-gradient chart-component regularity, which
  -- itself consumes `h_pou`.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P K
    (fun β Q => eigenvectorCovGrad_pou_memWkp_unconditional (I := I) (M := M)
      g r s i K h_pou β Q)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The cross-right limit object is `W^{K,2}` (chart-locality-free).**
Chart-locality-free twin of `crossRightLimitComponent_memWkp`, keyed on the
unconditional compactness witness through `eigenvectorResolvent_unconditional`.
The cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`
is fed `h_pou` directly, after the order monotonicity `MemWkp.le_of_le`. -/
theorem crossRightLimitComponent_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossRightLimitComponent_unconditional` is the cutoff chart component of the
  -- `L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent_unconditional …)`.
  rw [crossRightLimitComponent_unconditional]
  -- The bridge: feed it `h_pou` directly, after the order monotonicity.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P K
    (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The component atom `componentLpLimit_unconditional g r s i α P` — `μ` times
the canonical chart-locality-free eigenvector chart component — is `MemWkp K 2` on
the chart-`α` target. Chart-locality-free twin of `componentLpLimit_memWkp`. -/
lemma componentLpLimit_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit_unconditional (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{K,2}` (Summand-1 route).
  have h_comp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp_unconditional (I := I) (M := M)
      g r s i α P K h_pou
  -- `componentLpLimit_unconditional = μ • tensorL2ChartComponent (eigenvector)`.
  have h_ae : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
          i) α P)
    have h_smul' : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
              i) α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [componentLpLimit_unconditional]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The component atom `componentLpLimit_unconditional g r s i α P` vanishes
almost everywhere off the compact partition-of-unity kernel `chartPouKernel α`.
Chart-locality-free twin of `componentLpLimit_ae_zero_off_chartPouKernel`. -/
private lemma componentLpLimit_ae_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit_unconditional (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  -- `componentLpLimit_unconditional = μ • tensorL2ChartComponent (eigenvector)`.
  have h_smul : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  -- The canonical eigenvector chart component vanishes a.e. off the kernel.
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)
    α P
  filter_upwards [h_smul, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart-partial atom `partialLpLimit_unconditional g r s i α P k` — `μ`
times the weak `k`-th chart partial of the canonical chart-locality-free
eigenvector chart component — is `MemWkp K 2` on the chart-`α` target.
Chart-locality-free twin of `partialLpLimit_memWkp`. -/
lemma partialLpLimit_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{K+1,2}`.
  have h_comp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorVec_pou_memWkp_unconditional (I := I) (M := M) g r s i (K + 1)
      h_pou α P
  -- The eigenvector weak chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv_unconditional (I := I) (M := M)
      g r s i α P k
  -- The weak chart partial is `L²` (it is the coercion of an `Lp` class).
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial_unconditional]
    exact Lp.memLp _
  -- A weak partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k)
      Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_comp_succ
  -- `partialLpLimit_unconditional = μ • eigenvectorChartPartialLp_unconditional`.
  have h_ae : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorChartPartialLp_unconditional (I := I) (M := M) g r s i α P k)
    have h_smul' : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
            g r s i α P k y) := by
      rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart-partial atom `partialLpLimit_unconditional g r s i α P k` vanishes
almost everywhere off the compact partition-of-unity kernel `chartPouKernel α`,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou`.
Chart-locality-free twin of `partialLpLimit_ae_zero_off_chartPouKernel`. -/
private lemma partialLpLimit_ae_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The canonical eigenvector chart component is `W^{1,2}` (from `W^{K+1,2}`).
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    (eigenvectorVec_pou_memWkp_unconditional (I := I) (M := M) g r s i (K + 1)
      h_pou α P).memW1p
  -- The eigenvector weak chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv_unconditional (I := I) (M := M)
      g r s i α P k
  -- The eigenvector weak chart partial is `L²`.
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial_unconditional]
    exact Lp.memLp _
  -- The canonical chart component vanishes a.e. off the kernel.
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)
    α P
  -- Locality of weak partials propagates the off-kernel vanishing.
  have h_weak_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      h_weak_memLp h_weak h_comp_w1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  -- `partialLpLimit_unconditional = μ • eigenvectorChartWeakPartial_unconditional`.
  have h_smul : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak_zero' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y = 0 := by
    rw [chartL2Measure]; exact h_weak_zero
  filter_upwards [h_smul, h_weak_zero'] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The cutoff chart-partial atom `cutoffPartialLpLimit_unconditional g r s i α P k`
— `μ` times the chart-locality-free eigenvector cutoff chart partial — is
`MemWkp K 2` on the chart-`α` target. Chart-locality-free twin of
`cutoffPartialLpLimit_memWkp`. -/
theorem cutoffPartialLpLimit_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The eigenvector cutoff chart component is `W^{K+1,2}`: feed `h_pou` at
  -- order `K + 1` to the cutoff ↔ POU bridge applied to the eigenvector vector.
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
              i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp_unconditional (I := I) (M := M)
      g r s i (K + 1) h_pou β Q
  have h_cutoff_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)
      α P (K + 1) h_pou_eigen
  -- The eigenvector cutoff chart partial is a genuine weak partial of it.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv_unconditional
      (I := I) (M := M) g r s i α P k
  -- The cutoff chart partial is `L²` (it is the coercion of an `Lp` class).
  have h_weak_memLp : MemLp
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict Ω) := Lp.memLp _
  -- A weak partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_cutoff_succ
  -- `cutoffPartialLpLimit_unconditional = μ • eigenvectorCutoffChartPartialLp_unconditional`.
  have h_ae : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
        g r s i α P k)
    have h_smul' : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [cutoffPartialLpLimit_unconditional]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The lower-order gradient divergence limit `weightedGradCoeffDivLimit_unconditional`
is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`weightedGradCoeffDivLimit_memWkp`: for a chart direction `l`, the
chart-locality-free divergence limit is `MemWkp K 2` on the chart-`α` target,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent_unconditional`. -/
theorem weightedGradCoeffDivLimit_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (weightedGradCoeffDivLimit_unconditional (I := I) (M := M) g r s i α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold weightedGradCoeffDivLimit_unconditional
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · -- The component-atom group: `∂_l weightedGradFactor · componentLpLimit`.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit_memWkp_unconditional (I := I) (M := M)
          g r s i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))
  · -- The chart-partial-atom group: `weightedGradFactor · partialLpLimit`.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit_memWkp_unconditional (I := I) (M := M)
          g r s i α p l K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α p l K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 2 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand2_memWkp`: the cross-left double sum — a finite
`C^∞`-coefficient-weighted sum of the chart-locality-free cross-left limit object
`crossLeftLimitComponent_unconditional` — is `MemWkp K 2` on the chart-`α` target,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand2_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossLeftTestCoeff` times the `W^{K,2}` cross-left limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent_unconditional (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-left limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp_unconditional (I := I) (M := M)
        g r s i α P K h_pou
    -- The coefficient `covChartMetricGram · crossLeftTestCoeff` is `C^∞` on the
    -- chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-left limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent_unconditional (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent_unconditional]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent_unconditional (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent_unconditional (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 3 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand3_memWkp`: the cross-right double sum — a finite
`C^∞`-coefficient-weighted sum of the chart-locality-free cross-right limit object
`crossRightLimitComponent_unconditional` — is `MemWkp K 2` on the chart-`α` target,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand3_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossRightTestValueCoeff` times the `W^{K,2}` cross-right limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent_unconditional (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-right limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp_unconditional (I := I) (M := M)
        g r s i α P K h_pou
    -- The coefficient `covChartMetricGram · crossRightTestValueCoeff` is `C^∞` on
    -- the chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-right limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent_unconditional (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent_unconditional]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent_unconditional (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent_unconditional (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 4 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand4_memWkp`: the chart-locality-free principal rotation
coefficient limit `covPrincipalRotationCoeffLimit_unconditional` is `MemWkp K 2` on
the chart-`α` target, given the order-`(K + 1)` partition-of-unity regularity input
`h_pou` keyed on `eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand4_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covPrincipalRotationCoeffLimit_unconditional
  -- Each `(P, Q, k, l)`-leaf is `W^{K,2}`.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
      (k l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q k l
    exact memWkp_indicatorSmoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (principalRotationFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit_memWkp_unconditional (I := I) (M := M) g r s i α P k K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
        g r s i α P k K h_pou)
  -- Assemble the four-fold finite sum.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k y => ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun l _ => h_leaf P Q k l))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 5 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand5_memWkp`: the chart-locality-free lower-order rotation
value coefficient limit `covLowerOrderRotationValueCoeffLimit_unconditional` is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou` keyed on `eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand5_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covLowerOrderRotationValueCoeffLimit_unconditional
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · -- The chart-partial-atom group.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit_memWkp_unconditional (I := I) (M := M)
          g r s i α P k K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α P k K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => h_leaf P Q k l))))
  · -- The component-atom group.
    have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
            ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit_memWkp_unconditional (I := I) (M := M)
          g r s i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valueComponentFactor (I := I) (M := M)
                  g r s α P₀ P Q k l p) y *
              ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
              hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (fun p _ => h_leaf P Q k l p)))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 6 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand6_memWkp`: the chart-density-divided sum over chart
directions of the chart-locality-free lower-order gradient divergence limit
`weightedGradCoeffDivLimit_unconditional` is `MemWkp K 2` on the chart-`α` target,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand6_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The finite sum over chart directions is `W^{K,2}`.
  have h_sum : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l y => weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
        g r s i α P₀ l y)
      (fun l _ => weightedGradCoeffDivLimit_memWkp_unconditional (I := I) (M := M)
        g r s i α P₀ l K h_pou)
  -- The finite sum vanishes almost everywhere off the partition-of-unity kernel:
  -- every summand of every `weightedGradCoeffDivLimit_unconditional` carries an
  -- `indicator (chartPouKernel α)` factor.
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => Finset.sum_eq_zero
      (fun l _ => weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
        (I := I) (M := M) g r s i α P₀ l hy_imp))
  -- The reciprocal chart density is `C^∞` on the chart target.
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_sum h_sum_ae_zero

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Summand 7 is `W^{K,2}` (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_summand7_memWkp`: the chart-density-divided chart-locality-free
cross-right gradient divergence limit `crossRightGradCoeffDivLimit_unconditional` is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou` keyed on `eigenvectorResolvent_unconditional`. -/
theorem eigenvectorChartRHS_summand7_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
          g r s i α P₀ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The cross-right gradient divergence limit is `W^{K,2}`.
  have h_div : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
        g r s i α P₀) Ω := by
    unfold crossRightGradCoeffDivLimit_unconditional
    refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
    · -- The component-atom group: `∂_l crossRightDivFactor ·
      -- crossRightLimitComponent_unconditional`. The coefficient
      -- `∂_l crossRightDivFactor` itself vanishes off the partition-of-unity
      -- kernel, so the indicator cut is the identity and
      -- `memWkp_offKernelSmoothCoef_mul` applies — no support hypothesis on the
      -- atom is needed.
      have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        -- The indicator cut is the identity: `∂_l crossRightDivFactor`
        -- vanishes off `chartPouKernel`.
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
            ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
            g r s α P₀ l P Q)
          (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (crossRightLimitComponent_memWkp_unconditional (I := I) (M := M)
            g r s i α P K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
    · -- The chart-partial-atom group:
      -- `crossRightDivFactor · cutoffPartialLpLimit_unconditional`.
      -- Again the coefficient `crossRightDivFactor` vanishes off the
      -- partition-of-unity kernel, so the indicator cut is the identity.
      have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
            ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
          (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (cutoffPartialLpLimit_memWkp_unconditional (I := I) (M := M)
            g r s i α P l K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
  -- The divergence limit vanishes almost everywhere off the partition-of-unity
  -- kernel.
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
        (I := I) (M := M) g r s i α P₀ hy_imp)
  -- The reciprocal chart density is `C^∞` on the chart target.
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_div h_div_ae_zero

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-Euclidean right-hand side is `W^{K,2}` (chart-locality-free).**
Chart-locality-free twin of `eigenvectorChartRHS_memWkp`: the chart-locality-free
chart-Euclidean right-hand side `eigenvectorChartRHS_unconditional g r s i α P₀` is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou` keyed on `eigenvectorResolvent_unconditional`.

`eigenvectorChartRHS_unconditional` is the `μ⁻¹`-rescaled bracketed combination
`(1) − (2) + (3) − (4) − (5) + (6) − (7)` of the seven chart-locality-free summand
objects; the seven summand twins `eigenvectorChartRHS_summand{1,…,7}_memWkp_unconditional`
make each summand `W^{K,2}`, and the `MemWkp` arithmetic closures assemble the
bracket and carry the global `μ⁻¹` factor. -/
theorem eigenvectorChartRHS_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  -- Summand 1.
  have h1 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
            i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 2.
  have h2 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand2_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 3.
  have h3 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand3_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 4.
  have h4 : MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit_unconditional (I := I) (M := M)
        g r s i α P₀) Ω :=
    eigenvectorChartRHS_summand4_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 5.
  have h5 : MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit_unconditional (I := I) (M := M)
        g r s i α P₀) Ω :=
    eigenvectorChartRHS_summand5_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 6.
  have h6 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l y)) Ω :=
    eigenvectorChartRHS_summand6_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Summand 7.
  have h7 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
          g r s i α P₀ y) Ω :=
    eigenvectorChartRHS_summand7_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ K h_pou
  -- Assemble the bracket `(1) − (2) + (3) − (4) − (5) + (6) − (7)` and the
  -- global `μ⁻¹` factor by the `MemWkp` arithmetic closures.
  have h12 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1 h2
  have h123 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12 h3
  have h1234 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123 h4
  have h12345 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1234 h5
  have h123456 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12345 h6
  have h1234567 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123456 h7
  have h_assembled : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E) hp hΩ_open h1234567 (i.fst.val)⁻¹
  -- The assembled bracket function is, pointwise, `eigenvectorChartRHS_unconditional`.
  refine (MemWkp_congr_ae (d := Module.finrank ℝ E) hp hΩ_open
    (Filter.Eventually.of_forall (fun y => ?_))).mp h_assembled
  rw [eigenvectorChartRHS_unconditional]

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHS_memWkp (I := I) (M := M) g r s h_atlas i α P₀ K h_pou

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
