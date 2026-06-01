import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.DerivedDataCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.DifferentiatedVariationalIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.ChosenThirdMixedPartial
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.FChartEffTwiceDef
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Twice-differentiated variational identity — IBP infrastructure

For `u_h ∈ laplacianDomainPow g 2` and any chart point `α : M`, the formally
twice-differentiated chart-bilinear variational identity is intended to hold
for every smooth compactly supported test function `ψ` with `tsupport ψ ⊆
chartTargetEuclid α`. This module provides the infrastructure for assembling
that identity.

The schematic form of the headline identity is
```
∫ ∑_{i,j} weightedInvGramOnEuclid · chosenThirdMixedPartialChartPushedU(i, l₁, l₂) · ∂_j ψ
  + ∫ densityOnEuclid · chosenSecondPartialChartPushedU(l₁, l₂) · ψ
  = ∫ densityOnEuclid · fChartEffTwice · ψ.
```

This module establishes five per-pair `l₂`-direction IBP identities, against
each of the weakly-differentiable base scalar fields appearing in the
once-differentiated chart-bilinear identity:

* `per_pair_ibp_chosenSecond` — the second mixed partial
  `chosenSecondPartialChartPushedU g α u_h i l₁` ∈ `MemW1p 2` with weak
  partial `chosenThirdMixedPartialChartPushedU g α u_h i l₁ l₂`.
* `per_pair_ibp_base_weak_partial` — the base first weak partial
  `base.weak_partial i` (a `chartPushedWeakPartialLp` coeFn) ∈ `MemW1p 2`
  (via the chart-target ae-equality bridge to `chartPushedChosenFirstPartial`)
  with weak partial `chosenSecondPartialChartPushedU g α u_h i l₂`.
* `per_pair_ibp_base_u_chart` — the base `u_chart` scalar field with
  weak partials `base.weak_partial l₂`.
* `per_pair_ibp_base_f_chart` — the base `f_chart` scalar field (∈ `MemW1p 2`
  unconditionally via `fChartResidual_memW1p_truly_unconditional` and
  `base_f_chart_memW1p_from_residual_memW1p`) with weak partials
  `chosenFChartDeriv l₂'`.
* `per_pair_ibp_chosenFChartDeriv` — the once-differentiated chart-side
  derivative `chosenFChartDeriv l₁` ∈ `MemW1p 2` (passed as a hypothesis;
  awaiting unconditional chart-`H³` discharge) with weak partial
  `fChartDeriv2 l₁ l₂`.

Two further ergonomic bridges are recorded:

* `base_weak_partial_memW1p` — the base first weak partial lies in `MemW1p 2`
  on the chart target, established via `MemW1p_congr_ae` from the chart-pushed
  chosen first partial `MemW1p 2` regularity.
* `chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond` — the canonical
  chosenWeakPartial' of the base first weak partial in direction `l₂` agrees
  a.e. on the chart target with the canonical mixed second partial
  `chosenSecondPartialChartPushedU g α u_h l₁ l₂`.
* `integral_chosenWeakPartial_base_eq_integral_chosenSecond` — the
  corresponding integral-level identification of the principal `LHS₂` term.

The headline identity is assembled from these helpers by:

1. Applying the once-differentiated explicit-form identity
   (`differentiated_variational_identity_holds`) to the test function
   `∂_{l₂} ψ`.
2. Performing IBP in direction `l₂` against each of the resulting six
   terms via the helpers above, plus an additional Schwarz commutation
   (`fderiv_apply_single_swap`) and a `j`-direction IBP on a residual
   piece via `cross_derivative_term_ibp_second_order_single`.
3. Collecting all 13 resulting RHS contributions and identifying them with
   `fChartEffTwiceNumerator` via the indicator-numerator structure
   (`density_mul_fChartEffTwice_eq_indicator_numerator`).

The auxiliary ae-equality between `chosenWeakPartial' 2 l₂ (base.wp l₁)`
and `chosenSecond(l₁, l₂)` (recorded in
`chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond`) is used to
identify the principal LHS₂ term in the headline form.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDifferentiatedVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For `ψ : EuclN → ℝ` globally smooth, its `l`-direction partial
`y ↦ (fderiv ℝ ψ y) (EuclideanSpace.single l 1)` is also globally smooth. -/
private lemma contDiff_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

/-- The `l`-direction partial of a smooth compactly supported `ψ` is also
compactly supported. -/
private lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

/-- The tsupport of the `l`-direction partial of a smooth `ψ` is contained in
`tsupport ψ`. -/
private lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

/-- The base first weak partial agrees a.e. with the chart-pushed chosen first
weak partial on the volume measure restricted to the chart target. -/
private lemma base_weak_partial_ae_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3.chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3.chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h i

/-- The base first weak partial lies in `MemW1p 2 (chartTargetEuclid α)` for
`u_h ∈ laplacianDomainPow g 2`. -/
private lemma base_weak_partial_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair := laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h
    exact h_pair.1.1 α
  have h_chosen_memWkp_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_memWkp_2.chosenWeakPartial_mem i
  have h_chosen :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp
      h_chosen_memWkp_1
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (MemW1p_congr_ae hΩ_open
    (base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h i)).mpr h_chosen

/-- The chosen weak `l₂`-partial of `base.weak_partial l₁` agrees a.e. with the
canonical second mixed chosen partial `chosenSecondPartialChartPushedU g α u_h
l₁ l₂` on the volume measure restricted to the chart target. -/
private lemma chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
        (chartTargetEuclid (I := I) (M := M) α) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_aeEq :=
    base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h l₁
  have h_congr :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_ae_congr
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_aeEq l₂
  exact h_congr

/-- A smooth coefficient on `chartTargetEuclid α` has a smooth global
extension that agrees with it on a neighborhood of any prescribed compact
subset of the chart target. -/
private lemma exists_smooth_global_extension_chart
    {φ : EuclN → ℝ} {α : M}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) :=
  exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
    hφ_chart hK_compact hK_in

/-- Local-`L²` regularity of `base.u_chart`. -/
private lemma base_u_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.u_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.u_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

/-- Local-`L²` regularity of `base.f_chart`. -/
private lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.f_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

/-- Local-`L²` regularity of `base.weak_partial i`. -/
private lemma base_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i) 2
      ((volume : Measure EuclN).restrict K) :=
  (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
    ).weak_partial_locally_memLp i K hK_compact hK_in

/-- Local-`L²` regularity of `chosenWeakPartial' 2 l₂ (base.weak_partial l₁)`. -/
private lemma chosenWeakPartial_base_wp_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_w1p := base_weak_partial_memW1p (I := I) (M := M) g α hu_h l₁
  have h_global :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_w1p l₂
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

/-- Schwarz symmetry of mixed partials for a smooth function. -/
private lemma fderiv_apply_single_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

/-- The Fréchet derivative of `ψ` vanishes pointwise outside `tsupport ψ`. -/
private lemma fderiv_zero_outside_tsupport
    (ψ : EuclN → ℝ) (x : EuclN) (hx : x ∉ tsupport ψ) :
    fderiv ℝ ψ x = 0 := by
  have h_compl_open : IsOpen ((tsupport ψ)ᶜ) := (isClosed_tsupport _).isOpen_compl
  have h_fderiv_eq : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h_compl_open.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [h_fderiv_eq]; simp

/-- The Fréchet derivative of `fderiv ψ y (single l 1)` vanishes pointwise
outside `tsupport ψ`, for smooth `ψ`. -/
private lemma fderiv_partial_zero_outside_tsupport
    {ψ : EuclN → ℝ} (x : EuclN) (hx : x ∉ tsupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) x = 0 := by
  have h_compl_open : IsOpen ((tsupport ψ)ᶜ) := (isClosed_tsupport _).isOpen_compl
  have h_fderiv_eq : fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) x =
        fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h_compl_open.mem_nhds hx] with y hy
    rw [fderiv_zero_outside_tsupport ψ y hy]; simp
  rw [h_fderiv_eq]; simp

/-- Per-pair IBP: smooth coefficient `φ`, weak base `chosenSecond(i, l₁)` ∈ H¹,
weak `l₂`-partial `chosenThird(i, l₁, l₂)`. Test factor `ψ`. -/
private lemma per_pair_ibp_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l₁ l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y * chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ :=
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenThirdMixedPartialChartPushedU
      (I := I) (M := M) g α u_h i l₁ l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      chosenThirdMixedPartialChartPushedU_isWeakPartial
        (I := I) (M := M) g α hu_h i l₁ l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁ hK'_compact hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁ l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

/-- Per-pair IBP: smooth coefficient `φ`, weak base `base.weak_partial i` ∈ H¹
(via `base_weak_partial_memW1p`), weak `l₂`-partial taken as
`chosenSecondPartialChartPushedU g α u_h i l₂` (which is a weak partial of
`base.weak_partial i` by `hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp`).
Test factor `ψ`. -/
private lemma per_pair_ibp_base_weak_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial i y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω := by
    intro l₂'
    exact hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
      (I := I) (M := M) g α hu_h i l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i hK'_compact hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

/-- Per-pair IBP: smooth coefficient `φ`, weak base `base.u_chart`, weak partials
`base.weak_partial l₂'`. Test factor `ψ`. -/
private lemma per_pair_ibp_base_u_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).u_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  set v : EuclN → ℝ := D.u_chart with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun l₂' => D.weak_partial l₂'
    with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' => D.weak_partial_isWeakPartial l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_u_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact
      hK'_compact.isClosed.measurableSet hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

/-- Per-pair IBP: smooth coefficient `φ`, weak base `base.f_chart` ∈ W^{1,2},
weak partials `chosenFChartDeriv l₂'`. Test factor `ψ`. -/
private lemma per_pair_ibp_base_f_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  set v : EuclN → ℝ := D.f_chart with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenFChartDeriv (I := I) (M := M) g α hu_h l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      chosenFChartDeriv_isWeakPartial (I := I) (M := M) g α hu_h l₂' h_memW1p
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_f_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact
      hK'_compact.isClosed.measurableSet hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_memW1p l₂'
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    have h_unfold :
        w l₂' = DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l₂' D.f_chart Ω := rfl
    rw [h_unfold]
    rw [← h_eq]
    exact h_global.restrict K'
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

/-- Per-pair IBP: smooth coefficient `φ`, weak base `chosenFChartDeriv l₁` ∈
W^{1,2} (under the hypothesis), weak partials `fChartDeriv2 l₁ l₂'`. Test
factor `ψ`. -/
private lemma per_pair_ibp_chosenFChartDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ := chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂' v Ω
    with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_chosenFChartDeriv_memW1p l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  have h_v_global :
      MemLp v 2 ((volume : Measure EuclN).restrict Ω) := by
    change MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) 2
        ((volume : Measure EuclN).restrict Ω)
    unfold chosenFChartDeriv
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p l₁
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_v_global.restrict K'
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_chosenFChartDeriv_memW1p l₂'
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_global.restrict K'
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
      rfl
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

/-- The principal `LHS₂` integral admits two equivalent representations:
the canonical chosenWeakPartial' of `base.wp l₁` and the canonical mixed
second partial `chosenSecond(l₁, l₂)`. -/
private lemma integral_chosenWeakPartial_base_eq_integral_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (ψ : EuclN → ℝ) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l₂
          ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
          (chartTargetEuclid (I := I) (M := M) α)) y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
      ∂(volume : Measure EuclN)) := by
  have h_aeEq := chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond
    (I := I) (M := M) g α hu_h l₁ l₂
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h_aeEq] with y hy
  rw [hy]

private abbrev K_α (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

private lemma K_α_compact (α : M) : IsCompact (K_α (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

private lemma K_α_meas (α : M) : MeasurableSet (K_α (I := I) (M := M) α) :=
  (K_α_compact (I := I) (M := M) α).isClosed.measurableSet

private lemma K_α_subset_target (α : M) :
    K_α (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

private lemma chartTarget_diff_K_α_isOpen (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (K_α_compact (I := I) (M := M) α).isClosed

private lemma chartTarget_diff_K_α_subset_target (α : M) :
    chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1

private lemma chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V) u V :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_ae_zero_of_ae_zero
      (d := Module.finrank ℝ E) hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hu i
  have hg_lp_Ω_V : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_loc_Ω_V : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hu_V i
  have hgV_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_loc_Ω_V hgV_loc
  exact h_unique.trans h_chosen_V_zero

private lemma chartPushed_u_h_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

private lemma chosenWeakPartial_chartPushed_u_h_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  have h_w1p :=
    DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree.chartPushed_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_subset_target (I := I) (M := M) α)
    h_w1p (chartPushed_u_h_ae_zero_off_K_α (I := I) (M := M) g α u_h) i

private lemma chosenSecond_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set g_i : EuclN → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 i
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) with hg_i_def
  have h_pair := laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h
  have h_memWkp_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) := h_pair.1.1 α
  have h_g_i_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_i
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_step := h_memWkp_2.chosenWeakPartial_mem i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_step
    exact h_step
  have h_unfold : chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l g_i
        (chartTargetEuclid (I := I) (M := M) α) := rfl
  rw [h_unfold]
  have h_g_i_ae :=
    chosenWeakPartial_chartPushed_u_h_ae_zero_off_K_α
      (I := I) (M := M) g α hu_h i
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_subset_target (I := I) (M := M) α)
    h_g_i_memW1p h_g_i_ae l

private lemma weakPartial_ae_zero_on_open_subset_of_ae_zero
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_supp
    have hψ_supp_Ω : tsupport ψ ⊆ Ω := hψ_supp.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_supp_Ω
    have h_f_supp_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp h)
        have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_supp] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_supp_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

private lemma locallyIntegrableOn_of_locally_memLp_two_chart
    (_g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ}
    (hf : ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    LocallyIntegrableOn f
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α := by
    intro y hy; apply hr_subset
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
  have hB_subset_Ω : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hB_subset hy).1
  have hf_K : MemLp f 2 ((volume : Measure EuclN).restrict B) :=
    hf B hB_compact hB_subset_Ω
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    hf_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x
    (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

private lemma chosenThird_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l j : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j y = 0 := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak :=
    chosenThirdMixedPartialChartPushedU_isWeakPartial
      (I := I) (M := M) g α hu_h i l j
  have hf_ae := chosenSecond_ae_zero_off_K_α (I := I) (M := M) g α hu_h i l
  have hw_li : LocallyIntegrableOn
      (chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two_chart (I := I) (M := M) g α
      (fun K hK hK_in =>
        chosenThirdMixedPartialChartPushedU_locally_memLp
          (I := I) (M := M) g α hu_h i l j hK hK_in)
  refine weakPartial_ae_zero_on_open_subset_of_ae_zero
    hΩ_open hU_open hU_sub (i := j) h_isWeak hw_li ?_
  exact hf_ae

private lemma vol_restrict_chart_target_absCont_weighted (α : M)
    (g : SmoothRiemannianMetric I M) :
    (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  intro A hA
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chart_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chart_meas))] at hA
  rw [Measure.restrict_apply' h_chart_meas]
  rw [Measure.restrict_apply' h_chart_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

/-- `D.base.u_chart` agrees ae with `chartPushed POU α u_h.coeFn` on
`volume.restrict (chartTargetEuclid α)`. -/
private lemma base_u_chart_ae_eq_chartPushed_on_vol
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  have h_coeFn :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm.chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (H1ComplToLp (I := I) (M := M) g u_h)
  have h_v_abs_w := vol_restrict_chart_target_absCont_weighted (I := I) (M := M)
    (α := α) g
  exact h_v_abs_w.ae_le h_coeFn

private lemma base_u_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart y = 0 := by
  classical
  have h_aeEq := base_u_chart_ae_eq_chartPushed_on_vol (I := I) (M := M) g α hu_h
  have h_abs : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
    MeasureTheory.Measure.absolutelyContinuous_of_le
      (MeasureTheory.Measure.restrict_mono
        (chartTarget_diff_K_α_subset_target (I := I) (M := M) α) le_rfl)
  have h_aeEq_restrict := h_abs.ae_le h_aeEq
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  filter_upwards [(ae_restrict_iff' h_diff_meas).mp h_aeEq_restrict]
    with y hy hy_diff
  rw [hy hy_diff]
  exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy_diff.1 hy_diff.2

private lemma base_weak_partial_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak := D.weak_partial_isWeakPartial i
  have hw_li : LocallyIntegrableOn (D.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two_chart (I := I) (M := M) g α
      (fun K' hK' hK'_in => D.weak_partial_locally_memLp i K' hK' hK'_in)
  have hf_ae := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
  exact weakPartial_ae_zero_on_open_subset_of_ae_zero
    hΩ_open hU_open hU_sub (i := i) h_isWeak hw_li hf_ae

private lemma base_f_chart_locally_memLp_helper
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) :=
  base_f_chart_locally_memLp (I := I) (M := M) g α hu_h hK_compact
    hK_compact.isClosed.measurableSet hK_in

private lemma memLp_top_of_continuousOn_on_compact_chart
    (_g : SmoothRiemannianMetric I M) (α : M)
    {h : EuclN → ℝ}
    (hh_contOn : ContinuousOn h (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp h ∞ ((volume : Measure EuclN).restrict K) := by
  classical
  by_cases hK_empty : K = ∅
  · subst hK_empty
    rw [MeasureTheory.Measure.restrict_empty]
    refine ⟨?_, ?_⟩
    · exact aestronglyMeasurable_zero_measure h
    · simp
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_K_cont : ContinuousOn h K := hh_contOn.mono hK_in
  have h_abs_K : ContinuousOn (fun y => |h y|) K :=
    continuous_abs.comp_continuousOn h_K_cont
  obtain ⟨y_max, _hy_max_K, h_max⟩ :=
    hK_compact.exists_isMaxOn hK_ne h_abs_K
  set C : ℝ := |h y_max|
  have hC_bd : ∀ y ∈ K, |h y| ≤ C := fun y hy => h_max hy
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_meas : AEStronglyMeasurable h ((volume : Measure EuclN).restrict K) :=
    h_K_cont.aestronglyMeasurable hK_meas
  have h_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), |h y| ≤ C := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact hC_bd y hy
  refine ⟨h_meas, ?_⟩
  rw [eLpNorm_exponent_top]
  refine lt_of_le_of_lt ?_
    (show (ENNReal.ofReal (max C 0) : ℝ≥0∞) < ⊤ from
      ENNReal.ofReal_lt_top)
  refine eLpNormEssSup_le_of_ae_enorm_bound (C := ENNReal.ofReal (max C 0)) ?_
  refine h_ae_bd.mono (fun y hy => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  exact hy.trans (le_max_left _ _)

private lemma base_f_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  set U : Set EuclN := Ω \ K_α (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_prod_locInt : LocallyIntegrableOn
      (fun y => densityOnEuclid (I := I) g α y * D.f_chart y) U
      (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
    set B : Set EuclN := Metric.closedBall x (r / 2)
    have hB_compact : IsCompact B := isCompact_closedBall _ _
    have hB_subset_U : B ⊆ U := by
      intro y hy; apply hr_subset
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
    have hB_subset_Ω : B ⊆ Ω := fun y hy => hU_sub (hB_subset_U hy)
    have h_fchart_K_memLp := base_f_chart_locally_memLp_helper
      (I := I) (M := M) g α hu_h hB_compact hB_subset_Ω
    have h_density_memLp_top := memLp_top_of_continuousOn_on_compact_chart
      (I := I) (M := M) g α h_density_contOn hB_compact hB_subset_Ω
    have h_prod_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) 2 ((volume : Measure EuclN).restrict B) :=
      MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fchart_K_memLp h_density_memLp_top
    have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
    haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hB_finite
    have h_int : IntegrableOn (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) B (volume : Measure EuclN) :=
      h_prod_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine ⟨B, ?_, h_int⟩
    refine Filter.mem_inf_of_left ?_
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x
      (by linarith : 0 < r / 2))
    exact Metric.ball_subset_closedBall
  have h_zero_for_test : ∀ ψ : EuclN → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ y, ψ y • (densityOnEuclid (I := I) g α y * D.f_chart y)
        ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_supp_U
    have hψ_supp_chart : tsupport ψ ⊆ Ω := hψ_supp_U.trans hU_sub
    have h_var := D.variational_identity ψ hψ_smooth hψ_cs hψ_supp_chart
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
        ∂(volume : Measure EuclN) at h_var
    have h_principal_zero :
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
              D.weak_partial i y = 0 := fun i =>
          base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α hu_h i
        have h_wp_all_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            ∀ i : Fin (Module.finrank ℝ E),
              y ∈ U → D.weak_partial i y = 0 := by
          rw [ae_all_iff]; intro i
          rw [← ae_restrict_iff' hU_meas]
          exact h_wp_each i
        filter_upwards [h_wp_all_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [hy i hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have h_compl_open : IsOpen (tsupport ψ)ᶜ :=
            (isClosed_tsupport _).isOpen_compl
          have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
            filter_upwards [h_compl_open.mem_nhds h_y_not_in_supp] with z hz
            exact image_eq_zero_of_notMem_tsupport hz
          have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
            have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
            rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [h_fderiv_zero]; simp
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    have h_mass_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => densityOnEuclid (I := I) g α y * D.u_chart y * ψ y) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_uc_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
            D.u_chart y = 0 :=
          base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
        have h_uc_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ U → D.u_chart y = 0 := by
          rw [← ae_restrict_iff' hU_meas]; exact h_uc_ae
        filter_upwards [h_uc_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · rw [hy hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_in_supp
          rw [hψ_y]; ring
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    rw [h_principal_zero, h_mass_zero] at h_var
    have h_fchart_int_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • (densityOnEuclid (I := I) g α x *
        D.f_chart x) = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_chart h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_fchart_int_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  have h_cf_vol : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ U → densityOnEuclid (I := I) g α y * D.f_chart y = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_prod_locInt h_zero_for_test
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_cf_vol] with y hy hy_U
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_U.1
  have h_eq : densityOnEuclid (I := I) g α y * D.f_chart y = 0 := hy hy_U
  have h_ne : densityOnEuclid (I := I) g α y ≠ 0 := ne_of_gt h_pos
  exact (mul_eq_zero.mp h_eq).resolve_left h_ne

private lemma chosenFChartDeriv_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y = 0 := by
  classical
  have hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  have h_base_fc_ae := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hU_open hU_sub
    h_memW1p h_base_fc_ae l

private lemma fChartDeriv2_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y = 0 := by
  classical
  have hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_chosenFC_ae := chosenFChartDeriv_ae_zero_off_K_α
    (I := I) (M := M) g α hu_h l₁
  have h_chosen :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hU_open hU_sub
      h_chosenFChartDeriv_memW1p h_chosenFC_ae l₂
  change ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α) y = 0
  exact h_chosen

private lemma fChartEffTwiceNumerator_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y = 0 := by
  classical
  have h_uc := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_fc := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i y = 0 := fun i =>
    base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i
  have h_sec_each : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 := by
    intro i j
    exact chosenSecond_ae_zero_off_K_α (I := I) (M := M) g α hu_h i j
  have h_third_each : ∀ i l j : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j y = 0 := by
    intro i l j
    exact chosenThird_ae_zero_off_K_α (I := I) (M := M) g α hu_h i l j
  have h_fcDeriv : ∀ l : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y = 0 := fun l =>
    chosenFChartDeriv_ae_zero_off_K_α (I := I) (M := M) g α hu_h l
  have h_fcDeriv2 :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y = 0 :=
    fChartDeriv2_ae_zero_off_K_α (I := I) (M := M) g α hu_h l₁ l₂
      h_chosenFChartDeriv_memW1p
  have hU_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  have h_wp_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i, (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i y = 0 := by
    rw [ae_all_iff]; exact h_wp_each
  have h_sec_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h_sec_each i
  have h_third_l1_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h_third_each i l₁ j
  have h_third_l2_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h_third_each i l₂ j
  filter_upwards [h_uc, h_fc, h_wp_all, h_sec_all, h_third_l1_all, h_third_l2_all,
    h_fcDeriv l₁, h_fcDeriv l₂, h_fcDeriv2]
    with y hy_uc hy_fc hy_wp hy_sec hy_third1 hy_third2 hy_fcD1 hy_fcD2 hy_fcD12
  unfold fChartEffTwiceNumerator
  have h_A1_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_sec i l₁]; ring
  have h_A2_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_third1 i j]; ring
  have h_C1_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_wp i]; ring
  have h_C2_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_sec i j]; ring
  have h_C3_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_sec i l₂]; ring
  have h_C4_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_third2 i j]; ring
  rw [h_A1_zero, h_A2_zero, h_C1_zero, h_C2_zero, h_C3_zero, h_C4_zero,
      hy_wp l₁, hy_wp l₂, hy_fcD1, hy_fcD2, hy_fcD12, hy_uc, hy_fc]
  ring

private lemma integral_fChartEffTwiceNumerator_eq_integral_density_fChartEffTwice
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    (ψ : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hU_meas : MeasurableSet (Ω \ K_α (I := I) (M := M) α) :=
    hΩ_meas.diff (K_α_meas (I := I) (M := M) α)
  have h_ae_eq : (fun y : EuclN =>
      fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y) =ᵐ[
      (volume : Measure EuclN).restrict Ω]
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y) := by
    have h_numer_off := fChartEffTwiceNumerator_ae_zero_off_K_α
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
    refine (ae_restrict_iff' hΩ_meas).mpr ?_
    have h_off_vol : ∀ᵐ y ∂(volume : Measure EuclN),
        y ∈ Ω \ K_α (I := I) (M := M) α →
        fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y = 0 := by
      rw [← ae_restrict_iff' hU_meas]; exact h_numer_off
    filter_upwards [h_off_vol] with y hy hy_Ω
    by_cases hy_K : y ∈ K_α (I := I) (M := M) α
    · have h_pt := density_mul_fChartEffTwice_eq_indicator_numerator
        (I := I) (M := M) g α l₁ l₂ hu_h y hy_Ω
      rw [Set.indicator_of_mem hy_K] at h_pt
      rw [h_pt]
    · have hy_diff : y ∈ Ω \ K_α (I := I) (M := M) α := ⟨hy_Ω, hy_K⟩
      have h_pt := density_mul_fChartEffTwice_eq_indicator_numerator
        (I := I) (M := M) g α l₁ l₂ hu_h y hy_Ω
      rw [Set.indicator_of_notMem hy_K] at h_pt
      rw [hy hy_diff]
      have h_rhs_zero :
          densityOnEuclid (I := I) g α y *
          fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y = 0 := by
        rw [show densityOnEuclid (I := I) g α y *
            fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y =
            (densityOnEuclid (I := I) g α y *
              fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y) * ψ y from rfl]
        rw [h_pt]; ring
      linarith
  exact MeasureTheory.integral_congr_ae h_ae_eq

set_option maxHeartbeats 4000000 in
/-- **Twice-differentiated chart-bilinear variational identity** for
`u_h ∈ laplacianDomainPow g 2`, with the chart-`H³`-equivalent hypothesis
`h_chosenFChartDeriv_memW1p` exposing the once-differentiated chart-side
derivative `chosenFChartDeriv g α hu_h l₁` as `MemW1p 2` on the chart target. -/
theorem twice_differentiated_variational_identity_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN))
    + (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_base_def
  have h_base_f_chart_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  set ψl₂ : EuclN → ℝ := fun y => (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
    with hψl₂_def
  have hψl₂_smooth : ContDiff ℝ (⊤ : ℕ∞) ψl₂ :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l₂
  have hψl₂_cs : HasCompactSupport ψl₂ :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l₂
  have hψl₂_supp : tsupport ψl₂ ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ l₂).trans hψ_supp
  have h_once := differentiated_variational_identity_holds
    (I := I) (M := M) g α hu_h l₁ hψl₂_smooth hψl₂_cs hψl₂_supp
  have h_schwarz_A1 : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1) =
      (fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l₂ 1) := by
    intro y _ j
    change (fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l₂ 1)) y)
        (EuclideanSpace.single j 1) = _
    exact fderiv_apply_single_swap (ψ := ψ) hψ_smooth y j l₂
  set ψj : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hψj_def
  have hψj_smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψj j) := fun j =>
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth j
  have hψj_cs : ∀ j, HasCompactSupport (ψj j) := fun j =>
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs j
  have hψj_supp : ∀ j, tsupport (ψj j) ⊆ Ω := fun j =>
    (tsupport_fderiv_apply_single_subset ψ j).trans hψ_supp
  have h_aij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramOnEuclid (I := I) g α i j) Ω :=
    fun i j => weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  have h_pair_A1 : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψj j y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                ψj j y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₁ l₂
      (h_aij_contDiffOn i j) (hψj_smooth j) (hψj_cs j) (hψj_supp j)
  have h_daij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) Ω :=
    fun i j => weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₂
  have h_pair_A1_inner : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₁ j
      (h_daij_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_density_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_A2 :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
          D_base.weak_partial l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityOnEuclid (I := I) g α) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.weak_partial l₁ y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h l₁ l₂
      h_density_contDiffOn hψ_smooth hψ_cs hψ_supp
  have h_B :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityOnEuclid (I := I) g α) y)
                (EuclideanSpace.single l₂ 1) *
                chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityOnEuclid (I := I) g α y *
                fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ l₂
      h_chosenFChartDeriv_memW1p h_density_contDiffOn
      hψ_smooth hψ_cs hψ_supp
  have h_daij_l₁_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) Ω :=
    fun i j => weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₁
  have h_pair_C : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.weak_partial i y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψ y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i l₂
      (h_daij_l₁_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_dc_l₁_contDiffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l₁) Ω :=
    densityDerivOnEuclid_contDiffOn (I := I) g α l₁
  have h_D :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.u_chart y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.u_chart y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
                D_base.weak_partial l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_u_chart (I := I) (M := M) g α hu_h l₂
      h_dc_l₁_contDiffOn hψ_smooth hψ_cs hψ_supp
  have h_E :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.f_chart y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.f_chart y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
                chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_f_chart (I := I) (M := M) g α hu_h l₂
      h_dc_l₁_contDiffOn hψ_smooth hψ_cs hψ_supp
  have hA1_Schwarz : (∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) =
      (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    rw [h_schwarz_A1 y i j]
  have hC_Schwarz : (∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) =
      (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              D_base.weak_partial i y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    rw [h_schwarz_A1 y i j]
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
    hK_compact.measure_lt_top
  have hvolK_finite' :
      (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  have hψj_fderiv_cont : ∀ j k : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ (ψj j) y) (EuclideanSpace.single k 1)) :=
    fun j k => ((hψj_smooth j).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hψ_fderiv_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_fderiv_zero_outside_K_ψ : ∀ z ∉ K, fderiv ℝ ψ z = 0 :=
    fun z hz => fderiv_zero_outside_tsupport ψ z hz
  have h_fderiv_zero_outside_K_ψj : ∀ j, ∀ z ∉ K, fderiv ℝ (ψj j) z = 0 :=
    fun j z hz => fderiv_partial_zero_outside_tsupport (ψ := ψ) z hz j
  have h_aij_cont_on : ∀ i j, ContinuousOn (weightedInvGramOnEuclid
      (I := I) g α i j) Ω :=
    fun i j => (h_aij_contDiffOn i j).continuousOn
  have h_daij_cont_on : ∀ i j, ContinuousOn (weightedInvGramDerivOnEuclid
      (I := I) g α i j l₂) Ω :=
    fun i j => (h_daij_contDiffOn i j).continuousOn
  have h_daij_l₁_cont_on : ∀ i j, ContinuousOn (weightedInvGramDerivOnEuclid
      (I := I) g α i j l₁) Ω :=
    fun i j => (h_daij_l₁_contDiffOn i j).continuousOn
  have h_aij_fderiv_l₂_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1)) Ω := fun i j => by
    change ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) Ω
    exact h_daij_cont_on i j
  have h_daij_l₂_fderiv_j_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
        (EuclideanSpace.single j 1)) Ω := fun i j =>
    weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₂ j
  have h_daij_l₁_fderiv_l₂_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1)) Ω := fun i j =>
    weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂
  have integrable_triple :
      ∀ {a : EuclN → ℝ} (ha_cont_on : ContinuousOn a Ω)
        {u : EuclN → ℝ} (hu_int : IntegrableOn u K (volume : Measure EuclN))
        {h₁ : EuclN → ℝ} (hh₁_cont : Continuous h₁)
        (hh₁_supp : tsupport h₁ ⊆ K),
        Integrable (fun y => a y * u y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro a ha_cont_on u hu_int h₁ hh₁_cont hh₁_supp
    set h_prod : EuclN → ℝ := fun y => a y * h₁ y with hh_prod_def
    have hh_prod_supp : tsupport h_prod ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hh1y : h₁ y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy_notin (hh₁_supp h))
      exact hy (by change a y * _ = 0; rw [hh1y, mul_zero])
    have hh_prod_cont : Continuous h_prod := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · exact (ha_cont_on.continuousAt
          (hΩ_open.mem_nhds (hK_in hy))).mul hh₁_cont.continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h_prod z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have hh1z : h₁ z = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => hz (hh₁_supp h))
          change a z * h₁ z = 0; rw [hh1z, mul_zero]
        rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
    have hh_prod_contOn_K : ContinuousOn h_prod K := hh_prod_cont.continuousOn
    have hu_h_int_K : IntegrableOn (fun y => u y * h_prod y) K
        (volume : Measure EuclN) :=
      hu_int.mul_continuousOn hh_prod_contOn_K hK_compact
    have h_vanish : ∀ y, y ∉ K → u y * h_prod y = 0 := by
      intro y hy
      have : h_prod y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh_prod_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => u y * h_prod y) = K.indicator (fun y => u y * h_prod y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => u y * h_prod y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr hu_h_int_K
    have full_int : Integrable (fun y => u y * h_prod y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    have h_reassoc : (fun y => u y * h_prod y) =
        (fun y => a y * u y * h₁ y) := by
      funext y; change u y * (a y * h₁ y) = _; ring
    rw [h_reassoc] at full_int
    exact full_int.restrict
  have h_chosenSecond_int : ∀ i l : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
        K (volume : Measure EuclN) :=
    fun i l => (chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_chosenThird_int : ∀ i l j : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenThirdMixedPartialChartPushedU
        (I := I) (M := M) g α u_h i l j) K (volume : Measure EuclN) :=
    fun i l j => (chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l j hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_base_wp_int : ∀ i : Fin (Module.finrank ℝ E),
      IntegrableOn (D_base.weak_partial i) K (volume : Measure EuclN) :=
    fun i => (D_base.weak_partial_locally_memLp i K hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_int_A1_pair : ∀ i j,
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    set h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1) with hh₁_def
    have hh₁_cont : Continuous h₁ := hψj_fderiv_cont j l₂
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψj j y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_aij_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_A1_inner_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    set h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hh₁_def
    have hh₁_cont : Continuous h₁ := hψ_fderiv_cont j
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψ y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_daij_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_C_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          D_base.weak_partial i y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    set h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
    have hh₁_cont : Continuous h₁ := hψj_fderiv_cont j l₂
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψj j y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_daij_l₁_cont_on i j) (h_base_wp_int i)
      hh₁_cont hh₁_supp
  have sum_swap_LHS_A1 :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_A1_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_A1_pair i j)]
  have sum_swap_C :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              D_base.weak_partial i y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C_pair i j)]
  rw [hA1_Schwarz, hC_Schwarz, sum_swap_LHS_A1, sum_swap_C] at h_once
  have h_LHS_A1_after_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  ψj j y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact h_pair_A1 i j
  have h_C_after_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₂ y * ψj j y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i l₂
      (h_daij_l₁_contDiffOn i j) (hψj_smooth j) (hψj_cs j) (hψj_supp j)
  rw [h_LHS_A1_after_IBP, h_C_after_IBP, h_A2, h_B, h_D, h_E] at h_once
  have h_fderiv_aij_eq : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1) =
      weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y :=
    fun _ _ _ => rfl
  have h_fderiv_daij_l₁_eq : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1) =
      weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y :=
    fun _ _ _ => rfl
  have h_fderiv_c_eq : ∀ y : EuclN,
      (fderiv ℝ (densityOnEuclid (I := I) g α) y)
        (EuclideanSpace.single l₂ 1) =
      densityDerivOnEuclid (I := I) g α l₂ y :=
    fun _ => rfl
  have h_fderiv_dc_l₁_eq : ∀ y : EuclN,
      (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
        (EuclideanSpace.single l₂ 1) =
      densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y :=
    fun _ => rfl
  have h_ψj_eq : ∀ j : Fin (Module.finrank ℝ E), ∀ y : EuclN,
      ψj j y = (fderiv ℝ ψ y) (EuclideanSpace.single j 1) := fun _ _ => rfl
  set h_pair_A1_inner_ext : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) := h_pair_A1_inner with hh_ext
  have h_int_X1_ij : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
            (EuclideanSpace.single l₂ 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_aij_fderiv_l₂_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_Y1_ij : ∀ i j,
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          chosenThirdMixedPartialChartPushedU
            (I := I) (M := M) g α u_h i l₁ l₂ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_aij_cont_on i j) (h_chosenThird_int i l₁ l₂)
      hh₁_cont hh₁_supp
  have h_int_X2_ij : ∀ i j,
      Integrable (fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single l₂ 1) *
          D_base.weak_partial i y * ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_daij_l₁_fderiv_l₂_cont_on i j) (h_base_wp_int i)
      hh₁_cont hh₁_supp
  have h_int_Y2_ij : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_daij_l₁_cont_on i j) (h_chosenSecond_int i l₂)
      hh₁_cont hh₁_supp
  have h_sum_distrib_LHS_A1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  ψj j y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                ψj j y
              ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ y * ψj j y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω,
                weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y * ψj j y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ y * ψj j y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  have h_sum_distrib_C :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₂ y * ψj j y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
              D_base.weak_partial i y * ψj j y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
              D_base.weak_partial i y * ψj j y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  rw [h_sum_distrib_LHS_A1, h_sum_distrib_C] at h_once
  set α1_sub1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
      ψj j y
      ∂(volume : Measure EuclN) with hα1_sub1_def
  set α1_sub2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
      ψj j y
      ∂(volume : Measure EuclN) with hα1_sub2_def
  set γ_sub1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1) *
      D_base.weak_partial i y * ψj j y
      ∂(volume : Measure EuclN) with hγ_sub1_def
  set γ_sub2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
      ψj j y
      ∂(volume : Measure EuclN) with hγ_sub2_def
  have hα1_sub1_inner_IBP_form : ∀ i j : Fin (Module.finrank ℝ E),
      α1_sub1 i j = -((∫ y in Ω,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
            ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
            ∂(volume : Measure EuclN))) := by
    intro i j
    have : α1_sub1 i j =
        ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
            (EuclideanSpace.single l₂ 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          ψj j y
          ∂(volume : Measure EuclN)) = _
      refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
      have := h_fderiv_aij_eq y i j
      rw [show ψj j y = (fderiv ℝ ψ y) (EuclideanSpace.single j 1) from rfl]
      rw [this]
    rw [this]
    exact h_pair_A1_inner i j
  have h_sum_α1_sub1_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub1 i j =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact hα1_sub1_inner_IBP_form i j
  have h_sum_α1_sub1_split :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  have hSum_α1_sub1_final :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub1 i j =
      - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))) := by
    rw [h_sum_α1_sub1_IBP, h_sum_α1_sub1_split]
  have hSwap_LHS1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            ψj j y
            ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y)
        ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_Y1_ij i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_Y1_ij i j)]
  have hψj_consolidate_LHS1 :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y)
        ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) := rfl
  have h_LHS1_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub2 i j) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        α1_sub2 i j) = (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y
              ∂(volume : Measure EuclN)) from rfl]
    rw [hSwap_LHS1]
  set I_lhs1_target : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) with hI_lhs1_def
  set I_lhs2_target : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
      ∂(volume : Measure EuclN) with hI_lhs2_def
  set I_rhs_target : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN) with hI_rhs_def
  set X1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
      ψ y
      ∂(volume : Measure EuclN) with hX1_def
  set X2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
      ψ y
      ∂(volume : Measure EuclN) with hX2_def
  set C1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
        (EuclideanSpace.single j 1) *
      D_base.weak_partial i y * ψ y
      ∂(volume : Measure EuclN) with hC1_def
  set C2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y
      ∂(volume : Measure EuclN) with hC2_def
  set C3 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y
      ∂(volume : Measure EuclN) with hC3_def
  set C4 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y
      ∂(volume : Measure EuclN) with hC4_def
  have h_d2aij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) Ω :=
    fun i j => weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂
  have h_γ_sub1_IBP : ∀ i j : Fin (Module.finrank ℝ E),
      γ_sub1 i j = -(C1 i j + C2 i j) := by
    intro i j
    have h_rewrite : γ_sub1 i j =
        ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single l₂ 1) *
          D_base.weak_partial i y * ψj j y
          ∂(volume : Measure EuclN)) = _
      rfl
    rw [h_rewrite]
    exact per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i j
      (h_d2aij_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_γ_sub2_IBP : ∀ i j : Fin (Module.finrank ℝ E),
      γ_sub2 i j = -(C3 i j + C4 i j) := by
    intro i j
    have h_rewrite : γ_sub2 i j =
        ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          ψj j y
          ∂(volume : Measure EuclN)) = _
      rfl
    rw [h_rewrite]
    exact per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₂ j
      (h_daij_l₁_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_sumγ_sub1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub1 i j =
      - (∑ i, ∑ j, C1 i j) - (∑ i, ∑ j, C2 i j) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub1 i j
        = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), -(C1 i j + C2 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_γ_sub1_IBP i j
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), (-C1 i j + -C2 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j, -C1 i j) + (∑ j, -C2 i j)) := by
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, -C1 i j) + (∑ i, ∑ j, -C2 i j) := Finset.sum_add_distrib
      _ = - (∑ i, ∑ j, C1 i j) - (∑ i, ∑ j, C2 i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  have h_sumγ_sub2 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub2 i j =
      - (∑ i, ∑ j, C3 i j) - (∑ i, ∑ j, C4 i j) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub2 i j
        = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), -(C3 i j + C4 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_γ_sub2_IBP i j
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), (-C3 i j + -C4 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j, -C3 i j) + (∑ j, -C4 i j)) := by
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, -C3 i j) + (∑ i, ∑ j, -C4 i j) := Finset.sum_add_distrib
      _ = - (∑ i, ∑ j, C3 i j) - (∑ i, ∑ j, C4 i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  have h_α1_sub2_eq : α1_sub2 = fun i j =>
    ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN) := by
    funext i j; rfl
  have h_lhs1_swap_to_sum :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN)) =
      I_lhs1_target := by
    change (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
          chosenThirdMixedPartialChartPushedU
            (I := I) (M := M) g α u_h i l₁ l₂ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) =
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_Y1_ij i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_Y1_ij i j)]
  have h_α1_sub2_to_lhs1 :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub2 i j) = I_lhs1_target := by
    rw [h_α1_sub2_eq]; exact h_lhs1_swap_to_sum
  set N_A3 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    D_base.weak_partial l₁ y * ψ y ∂(volume : Measure EuclN) with hN_A3_def
  set N_B1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
    ∂(volume : Measure EuclN) with hN_B1_def
  set N_B2 : ℝ := ∫ y in Ω, densityOnEuclid (I := I) g α y *
    fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
    ∂(volume : Measure EuclN) with hN_B2_def
  set N_D1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.u_chart y * ψ y ∂(volume : Measure EuclN) with hN_D1_def
  set N_D2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    D_base.weak_partial l₂ y * ψ y ∂(volume : Measure EuclN) with hN_D2_def
  set N_E1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.f_chart y * ψ y ∂(volume : Measure EuclN) with hN_E1_def
  set N_E2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
    ∂(volume : Measure EuclN) with hN_E2_def
  have h_A2_named :
      (∫ y in Ω, densityOnEuclid (I := I) g α y * D_base.weak_partial l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_A3 + I_lhs2_target) := h_A2
  have h_B_named :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_B1 + N_B2) := h_B
  have h_D_named :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y * D_base.u_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_D1 + N_D2) := h_D
  have h_E_named :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y * D_base.f_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_E1 + N_E2) := h_E
  set I_num : ℝ := ∫ y in Ω,
    fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
    ∂(volume : Measure EuclN) with hI_num_def
  have h_psi_cont : Continuous ψ := hψ_smooth.continuous
  have h_psi_supp : tsupport ψ ⊆ K := le_refl _
  have h_base_uc_int : IntegrableOn D_base.u_chart K (volume : Measure EuclN) :=
    (base_u_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
      hK_compact hK_meas hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_base_fc_int : IntegrableOn D_base.f_chart K (volume : Measure EuclN) :=
    (base_f_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
      hK_compact hK_meas hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_chosenFChartDeriv_int : ∀ l : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenFChartDeriv (I := I) (M := M) g α hu_h l)
        K (volume : Measure EuclN) := fun l => by
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_base_f_chart_memW1p l
    have h_K_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1; exact Set.inter_eq_self_of_subset_left hK_in
    have h_memLp_K : MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
        ((volume : Measure EuclN).restrict K) := by
      change MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l D_base.f_chart Ω) 2 _
      rw [← h_K_eq]; exact h_global.restrict K
    exact h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_fChartDeriv2_int :
      IntegrableOn (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂)
        K (volume : Measure EuclN) := by
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_chosenFChartDeriv_memW1p l₂
    have h_K_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1; exact Set.inter_eq_self_of_subset_left hK_in
    have h_memLp_K : MemLp (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) 2
        ((volume : Measure EuclN).restrict K) := by
      change MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) Ω) 2 _
      rw [← h_K_eq]; exact h_global.restrict K
    exact h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_c_cont_on : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    h_density_contDiffOn.continuousOn
  have h_dc_l₁_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₁) Ω :=
    h_dc_l₁_contDiffOn.continuousOn
  have h_dc_l₂_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₂) Ω :=
    (densityDerivOnEuclid_contDiffOn (I := I) g α l₂).continuousOn
  have h_d2c_cont_on : ContinuousOn
      (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) Ω :=
    densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂
  have h_d2aij_cont_on : ∀ i j, ContinuousOn
      (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) Ω :=
    fun i j => weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂
  have integrable_triple_psi :
      ∀ {a : EuclN → ℝ}, ContinuousOn a Ω →
        ∀ {u : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Integrable (fun y => a y * u y * ψ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro a ha u hu_int
    exact integrable_triple ha hu_int h_psi_cont h_psi_supp
  have integrable_double_psi :
      ∀ {a : EuclN → ℝ}, ContinuousOn a Ω →
        ∀ {u : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Integrable (fun y => a y * u y * ψ y)
          ((volume : Measure EuclN).restrict Ω) :=
    @integrable_triple_psi
  have h_int_C1_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
            (I := I) g α i j l₁ l₂) y) (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on : ContinuousOn (fun y =>
        (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
          (EuclideanSpace.single j 1)) Ω := by
      have h_smooth := h_d2aij_contDiffOn i j
      have h_open : IsOpen Ω := hΩ_open
      have h_fderiv : ContDiffOn ℝ ∞ (fun y => fderiv ℝ
          (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y) Ω :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
      have h_eval : ContDiff ℝ ∞ (fun (L : EuclN →L[ℝ] ℝ) =>
          L (EuclideanSpace.single j 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
      exact (h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)).continuousOn
    exact integrable_triple_psi h_ai_cont_on (h_base_wp_int i)
  have h_int_C2_pair : ∀ i j,
      Integrable (fun y => weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_d2aij_cont_on i j) (h_chosenSecond_int i j)
  have h_int_C3_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₁) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on : ContinuousOn (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
          (EuclideanSpace.single j 1)) Ω :=
      weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ j
    exact integrable_triple_psi h_ai_cont_on (h_chosenSecond_int i l₂)
  have h_int_C4_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_daij_l₁_cont_on i j) (h_chosenThird_int i l₂ j)
  have h_int_X1_named : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₂) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on : ContinuousOn (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
          (EuclideanSpace.single j 1)) Ω :=
      weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₂ j
    exact integrable_triple_psi h_ai_cont_on (h_chosenSecond_int i l₁)
  have h_int_X2_named : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_daij_cont_on i j) (h_chosenThird_int i l₁ j)
  have h_I_num_decomp : I_num =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X1 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X2 i j) +
      (- N_A3) + N_B1 + N_B2 +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C1 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C2 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C3 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C4 i j) +
      (- N_D1) + (- N_D2) + N_E1 + N_E2 := by
    classical
    change (∫ y in Ω,
        fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN)) = _
    have h_integrand_eq : ∀ y : EuclN,
        fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y) +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y) +
        (- (densityDerivOnEuclid (I := I) g α l₂ y *
              D_base.weak_partial l₁ y * ψ y)) +
        densityDerivOnEuclid (I := I) g α l₂ y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y +
        densityOnEuclid (I := I) g α y *
          fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
                (EuclideanSpace.single j 1) *
              D_base.weak_partial i y * ψ y) +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
              ψ y) +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
              ψ y) +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₂ j y *
              ψ y) +
        (- (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
              D_base.u_chart y * ψ y)) +
        (- (densityDerivOnEuclid (I := I) g α l₁ y *
              D_base.weak_partial l₂ y * ψ y)) +
        densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y * D_base.f_chart y * ψ y +
        densityDerivOnEuclid (I := I) g α l₁ y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y := by
      intro y
      unfold fChartEffTwiceNumerator
      simp only [add_mul, sub_mul, Finset.sum_mul]
      ring
    rw [setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => h_integrand_eq y)]
    set int_A1 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
            (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          ψ y with hint_A1_def
    set int_A2 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
          ψ y with hint_A2_def
    set int_A3 : EuclN → ℝ := fun y =>
      - (densityDerivOnEuclid (I := I) g α l₂ y *
          D_base.weak_partial l₁ y * ψ y) with hint_A3_def
    set int_B1 : EuclN → ℝ := fun y =>
      densityDerivOnEuclid (I := I) g α l₂ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y with hint_B1_def
    set int_B2 : EuclN → ℝ := fun y =>
      densityOnEuclid (I := I) g α y *
        fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y with hint_B2_def
    set int_C1 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
            (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y with hint_C1_def
    set int_C2 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
          ψ y with hint_C2_def
    set int_C3 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          ψ y with hint_C3_def
    set int_C4 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y *
          ψ y with hint_C4_def
    set int_D1 : EuclN → ℝ := fun y =>
      - (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
          D_base.u_chart y * ψ y) with hint_D1_def
    set int_D2 : EuclN → ℝ := fun y =>
      - (densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.weak_partial l₂ y * ψ y) with hint_D2_def
    set int_E1 : EuclN → ℝ := fun y =>
      densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
        D_base.f_chart y * ψ y with hint_E1_def
    set int_E2 : EuclN → ℝ := fun y =>
      densityDerivOnEuclid (I := I) g α l₁ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y with hint_E2_def
    have hint_A1 : Integrable int_A1 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_X1_named i j))
    have hint_A2 : Integrable int_A2 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_X2_named i j))
    have hint_A3 : Integrable int_A3 ((volume : Measure EuclN).restrict Ω) :=
      (integrable_triple_psi h_dc_l₂_cont_on (h_base_wp_int l₁)).neg
    have hint_B1 : Integrable int_B1 ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple_psi h_dc_l₂_cont_on (h_chosenFChartDeriv_int l₁)
    have hint_B2 : Integrable int_B2 ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple_psi h_c_cont_on h_fChartDeriv2_int
    have hint_C1 : Integrable int_C1 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_C1_pair i j))
    have hint_C2 : Integrable int_C2 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_C2_pair i j))
    have hint_C3 : Integrable int_C3 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_C3_pair i j))
    have hint_C4 : Integrable int_C4 ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_C4_pair i j))
    have hint_D1 : Integrable int_D1 ((volume : Measure EuclN).restrict Ω) :=
      (integrable_triple_psi h_d2c_cont_on h_base_uc_int).neg
    have hint_D2 : Integrable int_D2 ((volume : Measure EuclN).restrict Ω) :=
      (integrable_triple_psi h_dc_l₁_cont_on (h_base_wp_int l₂)).neg
    have hint_E1 : Integrable int_E1 ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple_psi h_d2c_cont_on h_base_fc_int
    have hint_E2 : Integrable int_E2 ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple_psi h_dc_l₁_cont_on (h_chosenFChartDeriv_int l₂)
    have hint_sum_A1A2 :
        Integrable (fun y => int_A1 y + int_A2 y)
          ((volume : Measure EuclN).restrict Ω) := hint_A1.add hint_A2
    have hint_sum_through_A3 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_A1A2.add hint_A3
    have hint_sum_through_B1 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_A3.add hint_B1
    have hint_sum_through_B2 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_B1.add hint_B2
    have hint_sum_through_C1 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y) ((volume : Measure EuclN).restrict Ω) :=
      hint_sum_through_B2.add hint_C1
    have hint_sum_through_C2 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y) ((volume : Measure EuclN).restrict Ω) :=
      hint_sum_through_C1.add hint_C2
    have hint_sum_through_C3 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y + int_C3 y) ((volume : Measure EuclN).restrict Ω) :=
      hint_sum_through_C2.add hint_C3
    have hint_sum_through_C4 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y + int_C3 y + int_C4 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_C3.add hint_C4
    have hint_sum_through_D1 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y + int_C3 y + int_C4 y + int_D1 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_C4.add hint_D1
    have hint_sum_through_D2 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y + int_C3 y + int_C4 y + int_D1 y + int_D2 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_D1.add hint_D2
    have hint_sum_through_E1 :
        Integrable (fun y => int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
          int_C1 y + int_C2 y + int_C3 y + int_C4 y + int_D1 y + int_D2 y + int_E1 y)
          ((volume : Measure EuclN).restrict Ω) := hint_sum_through_D2.add hint_E1
    have h_int_split :
        (∫ y in Ω, int_A1 y + int_A2 y + int_A3 y + int_B1 y + int_B2 y +
            int_C1 y + int_C2 y + int_C3 y + int_C4 y + int_D1 y + int_D2 y +
            int_E1 y + int_E2 y ∂(volume : Measure EuclN)) =
        (∫ y in Ω, int_A1 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_A2 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_A3 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_B1 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_B2 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_C1 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_C2 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_C3 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_C4 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_D1 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_D2 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_E1 y ∂(volume : Measure EuclN)) +
        (∫ y in Ω, int_E2 y ∂(volume : Measure EuclN)) := by
      rw [MeasureTheory.integral_add hint_sum_through_E1 hint_E2]
      rw [MeasureTheory.integral_add hint_sum_through_D2 hint_E1]
      rw [MeasureTheory.integral_add hint_sum_through_D1 hint_D2]
      rw [MeasureTheory.integral_add hint_sum_through_C4 hint_D1]
      rw [MeasureTheory.integral_add hint_sum_through_C3 hint_C4]
      rw [MeasureTheory.integral_add hint_sum_through_C2 hint_C3]
      rw [MeasureTheory.integral_add hint_sum_through_C1 hint_C2]
      rw [MeasureTheory.integral_add hint_sum_through_B2 hint_C1]
      rw [MeasureTheory.integral_add hint_sum_through_B1 hint_B2]
      rw [MeasureTheory.integral_add hint_sum_through_A3 hint_B1]
      rw [MeasureTheory.integral_add hint_sum_A1A2 hint_A3]
      rw [MeasureTheory.integral_add hint_A1 hint_A2]
    have eq_intA1 : (∫ y in Ω, int_A1 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X1 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X1 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_X1_named i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_X1_named i j)]

    have eq_intA2 : (∫ y in Ω, int_A2 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X2 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X2 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_X2_named i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_X2_named i j)]

    have eq_intA3 : (∫ y in Ω, int_A3 y ∂(volume : Measure EuclN)) = - N_A3 := by
      change (∫ y in Ω,
          - (densityDerivOnEuclid (I := I) g α l₂ y *
            D_base.weak_partial l₁ y * ψ y)
          ∂(volume : Measure EuclN)) = - N_A3
      rw [MeasureTheory.integral_neg]
      rfl

    have eq_intB1 : (∫ y in Ω, int_B1 y ∂(volume : Measure EuclN)) = N_B1 := rfl
    have eq_intB2 : (∫ y in Ω, int_B2 y ∂(volume : Measure EuclN)) = N_B2 := rfl
    have eq_intC1 : (∫ y in Ω, int_C1 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C1 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
                (I := I) g α i j l₁ l₂) y)
                (EuclideanSpace.single j 1) *
                D_base.weak_partial i y * ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C1 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_C1_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_C1_pair i j)]

    have eq_intC2 : (∫ y in Ω, int_C2 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C2 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
                ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C2 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_C2_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_C2_pair i j)]

    have eq_intC3 : (∫ y in Ω, int_C3 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C3 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
                ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C3 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_C3_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_C3_pair i j)]

    have eq_intC4 : (∫ y in Ω, int_C4 y ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C4 i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ j y * ψ y
          ∂(volume : Measure EuclN)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), C4 i j
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_C4_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_C4_pair i j)]

    have eq_intD1 : (∫ y in Ω, int_D1 y ∂(volume : Measure EuclN)) = - N_D1 := by
      change (∫ y in Ω,
          - (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
            D_base.u_chart y * ψ y)
          ∂(volume : Measure EuclN)) = - N_D1
      rw [MeasureTheory.integral_neg]
      rfl

    have eq_intD2 : (∫ y in Ω, int_D2 y ∂(volume : Measure EuclN)) = - N_D2 := by
      change (∫ y in Ω,
          - (densityDerivOnEuclid (I := I) g α l₁ y *
            D_base.weak_partial l₂ y * ψ y)
          ∂(volume : Measure EuclN)) = - N_D2
      rw [MeasureTheory.integral_neg]

    have eq_intE1 : (∫ y in Ω, int_E1 y ∂(volume : Measure EuclN)) = N_E1 := rfl
    have eq_intE2 : (∫ y in Ω, int_E2 y ∂(volume : Measure EuclN)) = N_E2 := rfl
    rw [h_int_split, eq_intA1, eq_intA2, eq_intA3, eq_intB1, eq_intB2,
      eq_intC1, eq_intC2, eq_intC3, eq_intC4, eq_intD1, eq_intD2, eq_intE1, eq_intE2]
  have h_I_num_eq_rhs :=
    integral_fChartEffTwiceNumerator_eq_integral_density_fChartEffTwice
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p ψ
  rw [show I_num = ∫ y in chartTargetEuclid (I := I) (M := M) α,
        fChartEffTwiceNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) from rfl] at h_I_num_decomp
  change I_lhs1_target + I_lhs2_target = I_rhs_target
  rw [hSum_α1_sub1_final, h_sumγ_sub1, h_sumγ_sub2, h_α1_sub2_to_lhs1] at h_once
  change I_lhs1_target + I_lhs2_target =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN)
  rw [← h_I_num_eq_rhs]
  rw [h_I_num_decomp]
  linarith

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
