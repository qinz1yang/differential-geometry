import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffNumeratorWkpNormSharp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffWkpNormEnergyBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffStepWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorArbitraryKRegularity

/-!
# Sharp chain-length-aware `wkpNorm`-graded bound for the differentiated chart-RHS

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis chart
center `α : M`, a component multi-index `P₀`, a level `m`, a regularity order
`K`, and a direction multi-index `l : Fin m → Fin n`, the level-`m`
differentiated chart-RHS `eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` is
the chart-Euclidean source of the level-`m` carrier; level `0` is the
seven-summand chart RHS, while each successive level is an indicator of the
partition-of-unity kernel applied to the chart-density-divided differentiated
numerator (`eigenvectorChartRHSDiff_succ`).

This file records the chain-length-aware **sharp** order-`K` `wkpNorm` bound:
given seven *per-`K`-family* quantitative `wkpNorm K'`-bounds — one per source
atom of the level-`0` chart RHS, indexed by `K' ∈ ℕ` so the recursion can
invoke the same hypotheses at chains `K, K+1, …` as it deepens — together with
the structural `MemWkp` regularity of the resolvent chart components on every
order (the partition-of-unity input threaded through `eigenvectorChartRHSDiff_memWkp`),
there is a single nonnegative constant `C : ℝ` and exponent `e : ℕ` such that,
for *every* eigenbasis index `i`,

```
wkpNorm K 2 (eigenvectorChartRHSDiff … m l) (chartTargetEuclid α)
  ≤ ENNReal.ofReal (C · (i.fst.val)⁻¹^e) ·
      ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖.
```

## Proof strategy

We prove the bound by `Nat.rec` on `m` with `K` *generalised*: each step
invokes the inductive hypothesis at *both* chain `K` (Layer D of the
numerator) *and* chain `K + 1` (Layer E, which peels a chosen weak partial of
the previous-level data). The five-layer sharp numerator
`eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_sharp` and the sharp
polymorphic bridge
`eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp` package the per-layer
atoms; the indicator-stripping ae-equality and the smooth reciprocal-density
coefficient bound transport the bound across the recursion step.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`.
The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Eigenvalue / exponent helpers -/

omit [CompleteSpace E] in
/-- The resolvent eigenvalue's reciprocal `(i.fst.val)⁻¹` is at least `1`. -/
lemma sharpDiff_eigen_inv_one_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    1 ≤ (i.fst.val)⁻¹ := by
  have h_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s) h_atlas).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  exact (one_le_inv₀ hμ_unit.1).mpr hμ_unit.2

omit [CompleteSpace E] in
/-- `(i.fst.val)⁻¹ ≥ 0`. -/
lemma sharpDiff_eigen_inv_nn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
  le_trans zero_le_one
    (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s h_atlas i)

omit [CompleteSpace E] in
/-- For `1 ≤ x`, `x^a ≤ x^b` whenever `a ≤ b`. -/
lemma sharpDiff_pow_eigen_inv_mono
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {a b : ℕ} (hab : a ≤ b) :
    (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ b :=
  pow_le_pow_right₀
    (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s h_atlas i) hab

omit [CompleteSpace E] in
/-- For nonnegative `C` and `k ≤ e`, `ofReal (C · μ⁻¹^k) ≤ ofReal (C · μ⁻¹^e)`. -/
lemma sharpDiff_ofReal_const_pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {C : ℝ} (hC_nn : 0 ≤ C) {k e : ℕ} (hke : k ≤ e) :
    ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ k) ≤
      ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) := by
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ hC_nn
  exact sharpDiff_pow_eigen_inv_mono (I := I) (M := M) g r s h_atlas i hke

/-! ## File-local smooth-coefficient `wkpNorm` Leibniz bound

A local copy of the factor-uniform `wkpNorm` smooth-coefficient bound — for a
`C^∞` coefficient on the chart target and a factor that lies in `W^{K, 2}` on
the chart target and ae-vanishes off the compact partition-of-unity kernel, the
product `coef · factor` is in `W^{K, 2}` and has `wkpNorm K 2 ≤ ofReal C ·
wkpNorm K 2 factor`. -/

omit [CompleteSpace E] in
/-- A factor-uniform smooth-coefficient `wkpNorm K 2` Leibniz bound for any
smooth coefficient on the chart target and a factor that ae-vanishes off the
compact partition-of-unity kernel. Mirrors the `sharp_wkpNorm_coef_mul_factor_le_uniform`
helper of `EigenvectorChartRHSDiffNumeratorWkpNormSharp` but is local to this
file. -/
lemma sharpDiff_wkpNorm_coef_mul_factor_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => coef y * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨δ, χ, _hδ_pos, _hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ (chartPouKernel (I := I) (M := M) α)
    with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hΩ_open.measurableSet
  refine ⟨Kc, le_of_lt hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : chartPouKernel (I := I) (M := M) α ⊆ Cδ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : chartTargetEuclid (I := I) (M := M) α \ Cδ ⊆
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ Cδ) ≪
          (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \ Cδ) :=
      hΩ_meas.diff hCδ_meas
    have h_cover : chartTargetEuclid (I := I) (M := M) α =
        (chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ∪
          (chartTargetEuclid (I := I) (M := M) α \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint
        (chartTargetEuclid (I := I) (M := M) α ∩ Cδ)
        (chartTargetEuclid (I := I) (M := M) α \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        (volume : Measure EuclN).restrict
          ((chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ∪
            (chartTargetEuclid (I := I) (M := M) α \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

/-! ## The per-`K'`-family hypothesis structure

The seven per-`K'`-family input hypotheses needed by the recursion, plus a
structural `MemWkp` companion for the resolvent chart component (the
partition-of-unity input threaded through `eigenvectorChartRHSDiff_memWkp` at
every order). The seven `wkpNorm`-bounds all take the standard shape
`atom ≤ ENNReal.ofReal (CX K' · μ⁻¹^eX K') · ‖vec‖`. -/

/-- The per-`K'`-family hypothesis bundle for the level-`0` chart RHS atoms,
plus a per-`K'`-family chart-component bound, plus a `MemWkp K'`
companion for the resolvent chart component (the structural regularity input
threaded through `eigenvectorChartRHSDiff_memWkp`). The seven `wkpNorm`-bounds
take the standard shape
`wkpNorm K' atom ≤ ENNReal.ofReal (CX K' · μ⁻¹^eX K') · ‖vec‖`. -/
structure sharpDiffPerK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) where
  /-- The structural `MemWkp K'` regularity of the resolvent chart component,
  needed to apply `eigenvectorChartRHSDiff_memWkp` at every order. -/
  h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
          EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)
  /-- Chart-component bound at order `K'`. -/
  Ceig : ℕ → ℝ
  eEig : ℕ → ℕ
  hCeig_nn : ∀ K', 0 ≤ Ceig K'
  hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- High-order resolvent chart-component atom at order `K' + 1`. -/
  CresH : ℕ → ℝ
  eResH : ℕ → ℕ
  hCresH_nn : ∀ K', 0 ≤ CresH K'
  hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- Low-order resolvent chart-component atom at order `K'`. -/
  CresL : ℕ → ℝ
  eResL : ℕ → ℕ
  hCresL_nn : ∀ K', 0 ≤ CresL K'
  hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- Partial-`Lp`-limit atom at order `K'`. -/
  Cpar : ℕ → ℝ
  ePar : ℕ → ℕ
  hCpar_nn : ∀ K', 0 ≤ Cpar K'
  hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((partialLpLimit (I := I) (M := M)
            g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- Component-`Lp`-limit atom at order `K'`. -/
  Ccom : ℕ → ℝ
  eCom : ℕ → ℕ
  hCcom_nn : ∀ K', 0 ≤ Ccom K'
  hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (p : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((componentLpLimit (I := I) (M := M)
            g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- Cross-right limit-component atom at order `K'`. -/
  CcR : ℕ → ℝ
  eCcR : ℕ → ℕ
  hCcR_nn : ∀ K', 0 ≤ CcR K'
  hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
  /-- Cutoff-partial-`Lp`-limit atom at order `K'`. -/
  Ccut : ℕ → ℝ
  eCcut : ℕ → ℕ
  hCcut_nn : ∀ K', 0 ≤ Ccut K'
  hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
            g r s h_atlas i α P l :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖

/-! ## Derived `MemWkp` from the per-`K'`-family bundle -/

omit [CompleteSpace E] in
/-- The level-`m` differentiated chart RHS is `MemWkp K' 2` for any chain `K'`,
derived via `eigenvectorChartRHSDiff_memWkp` from the structural resolvent
chart-component regularity input in the bundle. -/
private lemma sharpDiff_diff_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (H : sharpDiffPerK (I := I) (M := M) g r s h_atlas α P₀)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (m K' : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp (I := I) (M := M) g r s h_atlas i α P₀ m K' l
    (fun β Q => H.h_pou_resolv i (m + 1 + K') β Q)

/-! ## Helper: `wkpNorm` of an indicator of `chartPouKernel` of a function -/

omit [CompleteSpace E] in
/-- `wkpNorm K of indicator_{chartPouKernel α} Q = wkpNorm K of Q` on the open
chart target, when `Q` ae-vanishes off the kernel. -/
lemma sharpDiff_wkpNorm_indicator_eq
    (α : M) (K : ℕ) {Q : EuclN → ℝ}
    (hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (Set.indicator (chartPouKernel (I := I) (M := M) α) Q)
        (chartTargetEuclid (I := I) (M := M) α)
      = wkpNorm (d := Module.finrank ℝ E) K 2 Q
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hKα_meas : MeasurableSet Kα :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  -- On `Ω ∩ Kα`: `indicator Kα Q = Q`.
  have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
  have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
      (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
    refine (ae_restrict_iff' h_inter_meas).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact Set.indicator_of_mem hy.2 _
  -- On `Ω \ Kα`: `indicator Kα Q = 0` and `Q =ᵐ 0`.
  have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
  have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
      (volume : Measure EuclN).restrict (Ω \ Kα)]
      (fun _ : EuclN => (0 : ℝ)) := by
    refine (ae_restrict_iff' h_diff_meas).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact Set.indicator_of_notMem hy.2 _
  have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
      (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
    filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
    rw [h0, hQ0]
  have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
    ext y; constructor
    · intro hy
      by_cases h : y ∈ Kα
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
    Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
  have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
      (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
    rw [← h_cover]
  have h_indicator_ae_eq_Q :
      Set.indicator Kα Q =ᵐ[(volume : Measure EuclN).restrict Ω] Q := by
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q

/-! ## The level-`0` sharp `wkpNorm K` bound -/

omit [CompleteSpace E] in
/-- **The level-`0` sharp `wkpNorm K` bound for the chart RHS.**

The chart RHS is `μ⁻¹ • (a seven-term bracket)`. The seven per-`K'`-family
atom bounds collapse the bracket via `rhsZeroAggregate_le_energy_perK`; the
combination with the scaling factor `μ⁻¹` (a single power of `μ⁻¹` from the
chart-RHS smul identity) produces a single `wkpNorm K`-bound for the
chart RHS at level `0`. -/
private lemma sharpDiff_level_zero_wkpNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (H : sharpDiffPerK (I := I) (M := M) g r s h_atlas α P₀) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The aggregate bound, sharp in `μ⁻¹^e`.
  obtain ⟨Cagg, eAgg, hCagg_nn, hCagg_bd⟩ :=
    rhsZeroAggregate_le_energy_perK (I := I) (M := M) g r s h_atlas α P₀ K
      H.Ceig H.eEig H.hCeig_nn H.hCeig_bd
      H.CresH H.eResH H.hCresH_nn H.hCresH_bd
      H.CresL H.eResL H.hCresL_nn H.hCresL_bd
      H.Cpar H.ePar H.hCpar_nn H.hCpar_bd
      H.Ccom H.eCom H.hCcom_nn H.hCcom_bd
      H.CcR H.eCcR H.hCcR_nn H.hCcR_bd
      H.Ccut H.eCcut H.hCcut_nn H.hCcut_bd
  -- The `μ⁻¹`-prefactor bound by the seven-summand source aggregate, derived
  -- from the resolvent chart-cpt regularity input in the bundle.
  have h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun i β Q =>
    H.h_pou_resolv i (K + 1) β Q
  obtain ⟨Cmu, hCmu_nn, hCmu_bd⟩ :=
    eigenvectorChartRHS_wkpNorm_le_uniform (I := I) (M := M) g r s h_atlas α P₀
      K h_pou
  refine ⟨Cmu * Cagg, eAgg + 1, mul_nonneg hCmu_nn hCagg_nn, fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_nn (I := I) (M := M) g r s h_atlas i
  have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eAgg :=
    pow_nonneg hμ_inv_nn _
  have hCmu_aux := hCmu_bd i
  have hCagg_aux := hCagg_bd i
  -- The aggregate on the RHS of `hCmu_aux` is, definitionally,
  -- `rhsZeroAggregate g r s h_atlas i α P₀ K`. Use `change` to rephrase.
  change wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) *
        rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K at hCmu_aux
  -- Compose: `wkpNorm RHS ≤ ofReal(μ⁻¹·Cmu) · rhsZeroAggregate ≤
  --   ofReal(μ⁻¹·Cmu) · ofReal(Cagg·μ⁻¹^eAgg) · ‖vec‖ =
  --   ofReal((Cmu·Cagg)·μ⁻¹^(eAgg+1)) · ‖vec‖`.
  refine le_trans hCmu_aux ?_
  refine le_trans (mul_le_mul' (le_refl _) hCagg_aux) ?_
  rw [show ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) =
      ENNReal.ofReal (i.fst.val)⁻¹ * ENNReal.ofReal Cmu from
    ENNReal.ofReal_mul hμ_inv_nn]
  rw [show ENNReal.ofReal (Cagg * (i.fst.val)⁻¹ ^ eAgg) =
      ENNReal.ofReal Cagg * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) from
    ENNReal.ofReal_mul hCagg_nn]
  rw [show ENNReal.ofReal (Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1)) =
      ENNReal.ofReal Cmu * ENNReal.ofReal Cagg *
        ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) * ENNReal.ofReal (i.fst.val)⁻¹ by
    rw [show Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1) =
        Cmu * Cagg * (i.fst.val)⁻¹ ^ eAgg * (i.fst.val)⁻¹ from by ring,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCmu_nn hCagg_nn) hμ_inv_pow_nn),
      ENNReal.ofReal_mul (mul_nonneg hCmu_nn hCagg_nn),
      ENNReal.ofReal_mul hCmu_nn]]
  -- Both sides are products with `‖vec‖`; reassociate the constants on the LHS
  -- and the eigenvalue factor on the RHS.
  ring_nf
  exact le_refl _

/-! ## The main chain-length-aware sharp `wkpNorm K` recursion -/

set_option maxHeartbeats 32000000 in
omit [CompleteSpace E] in
/-- **The chain-length-aware sharp `wkpNorm K` recursion for the differentiated
chart RHS.**

Given the per-`K'`-family hypothesis bundle `H`, for every level `m` and chain
`K`, there is a single nonnegative constant `C` and an exponent `e` such that,
for every eigenbasis index `i`, the order-`K` `wkpNorm` of the level-`m`
differentiated chart RHS is bounded by `ofReal(C · μ⁻¹^e) · ‖vec‖`.

The proof is by `Nat.rec` on `m` with `K` generalised; at each step the
recursion invokes the inductive hypothesis at chains `K` (Layer D of the
numerator) and `K + 1` (Layer E, which peels a chosen weak partial). -/
private lemma sharpDiff_recursion
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (H : sharpDiffPerK (I := I) (M := M) g r s h_atlas α P₀) :
    ∀ (m : ℕ) (K : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)),
      ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s h_atlas i α P₀ m l)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro m
  induction m with
  | zero =>
      intro K _l
      -- Level `0`: `eigenvectorChartRHSDiff … 0 _ = eigenvectorChartRHS`.
      obtain ⟨C, e, hC_nn, hC_bd⟩ :=
        sharpDiff_level_zero_wkpNorm (I := I) (M := M) g r s h_atlas α P₀ K H
      refine ⟨C, e, hC_nn, fun i => ?_⟩
      have h_eq : eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀
          0 _l = eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀ :=
        eigenvectorChartRHSDiff_zero (I := I) (M := M) g r s h_atlas i α P₀ _l
      rw [h_eq]
      exact hC_bd i
  | succ m ih =>
      intro K l
      -- The IH at chain `K` and chain `K + 1`, at level `m`, direction
      -- `Fin.init l`. The chain `K + 1` is needed for Layer E.
      obtain ⟨C_K, e_K, hC_K_nn, hC_K_bd⟩ := ih K (Fin.init l)
      obtain ⟨C_K1, e_K1, hC_K1_nn, hC_K1_bd⟩ := ih (K + 1) (Fin.init l)
      -- The structural prerequisites for the numerator sharp bound:
      -- `f_chart_m` is in `MemWkp (K+1) 2` (via `sharpDiff_diff_memWkp`),
      -- and `f_chart_m` ae-vanishes off `chartPouKernel α`.
      have h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
        sharpDiff_diff_memWkp (I := I) (M := M) g r s h_atlas α P₀ H i m
          (K + 1) (Fin.init l)
      have h_prev_ae_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m
              (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
        fun i =>
          eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
            (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)
      -- The five layer-atom bounds for the numerator sharp bound.
      -- Layer A: `wkpNorm K 2 (m+1)-iter ≤ ofReal (Ceig (K+m+1) · μ⁻¹^eEig) · ‖vec‖`,
      -- using the sharp bridge with `j = m + 1` and chart-cpt at `K + (m + 1)`.
      have hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 1) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := by
        intro i a
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s h_atlas i (K + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) K
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i (K + (m + 1))
        have h_arith : K + m + 1 = K + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      -- Layer B: `wkpNorm K 2 (chosenWeakPartial b (m+1)-iter) ≤
      --            wkpNorm (K+1) 2 (m+1)-iter ≤ wkpNorm (K+m+2) of chart cpt`.
      have hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a b : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 2) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m + 2))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := by
        intro i a b
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) b
        refine le_trans h_chosen ?_
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s h_atlas i ((K + 1) + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) (K + 1)
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i ((K + 1) + (m + 1))
        have h_arith : K + m + 2 = (K + 1) + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      -- Layer C: `wkpNorm K 2 (m-iter) ≤ wkpNorm (K + m) of chart cpt`.
      have hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := by
        intro i
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s h_atlas i (K + m) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s h_atlas i α P₀ m K
            h_chart_cpt_mem
            (Fin.init l)).2
        refine le_trans h_bridge ?_
        exact H.hCeig_bd i (K + m)
      -- Layer D: `wkpNorm K (f_chart_m)` — from IH at chain `K`.
      have hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K * (i.fst.val)⁻¹ ^ e_K) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := hC_K_bd
      -- Layer E: `wkpNorm K (chosenWeakPartial l_last (f_chart_m)) ≤
      --            wkpNorm (K+1) (f_chart_m)`, from IH at chain `K+1`.
      have hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (eigenvectorChartRHSDiff (I := I) (M := M)
                  g r s h_atlas i α P₀ m (Fin.init l))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K1 * (i.fst.val)⁻¹ ^ e_K1) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := by
        intro i
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l)) (l (Fin.last m))
        exact le_trans h_chosen (hC_K1_bd i)
      -- Now apply the P3.1 sharp numerator bound.
      obtain ⟨Cnum, eNum, hCnum_nn, hCnum_bd⟩ :=
        eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_sharp
          (I := I) (M := M) g r s h_atlas α P₀ m K l
          (fun i => eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (H.Ceig (K + m + 1)) (H.eEig (K + m + 1)) (H.hCeig_nn _) hAtomA_bd
          (H.Ceig (K + m + 2)) (H.eEig (K + m + 2)) (H.hCeig_nn _) hAtomB_bd
          (H.Ceig (K + m)) (H.eEig (K + m)) (H.hCeig_nn _) hAtomC_bd
          C_K e_K hC_K_nn hAtomD_bd
          C_K1 e_K1 hC_K1_nn hAtomE_bd
          h_prev_mem_succ h_prev_ae_zero
      -- Reduce the level-`(m+1)` `wkpNorm` to the numerator/density `wkpNorm`
      -- via indicator stripping + reciprocal-density smooth-coefficient bound.
      obtain ⟨Cden, hCden_nn, hCden_bd⟩ :=
        sharpDiff_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
          (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid
            (I := I) (M := M) g α)
      refine ⟨Cden * Cnum, eNum, mul_nonneg hCden_nn hCnum_nn, fun i => ?_⟩
      -- The numerator function (at `i`).
      set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m l
        (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l)) with hnumFun_def
      -- The quotient function `numFun / density`, written as `(1/density) · numFun`.
      set Q : EuclN → ℝ := fun y =>
        (1 / densityOnEuclid (I := I) g α y) * numFun y with hQ_def
      -- Numerator is `MemWkp K 2` and ae-vanishes off `chartPouKernel`.
      have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hnumFun_def]
        refine eigenvectorChartRHSDiffNumerator_memWkp_of_iter
          (I := I) (M := M) g r s h_atlas i α P₀ m K l ?_ ?_ ?_
        · intro j idx
          have h_chart_cpt_mem :
              MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
                (eigenvectorChartComponentFun (I := I) (M := M)
                  g r s h_atlas i α P₀)
                (chartTargetEuclid (I := I) (M := M) α) :=
            eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
              g r s h_atlas i ((2 + K) + j) α P₀
          exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s h_atlas i α P₀ j (2 + K)
            h_chart_cpt_mem idx).1
        · exact h_prev_mem_succ i
        · exact h_prev_ae_zero i
      have h_num_ae_zero :
          numFun =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        rw [hnumFun_def]
        exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ m l (h_prev_ae_zero i)
      -- `Q = (1/density) · numFun` is `MemWkp K 2` and ae-vanishes off
      -- `chartPouKernel`.
      have h_Q_props := hCden_bd numFun h_num_memWkp h_num_ae_zero
      have h_Q_bd : wkpNorm (d := Module.finrank ℝ E) K 2 Q
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal Cden *
            wkpNorm (d := Module.finrank ℝ E) K 2 numFun
              (chartTargetEuclid (I := I) (M := M) α) := h_Q_props.2
      -- `Q` ae-vanishes off `chartPouKernel`: `Q y = (1/density) · numFun y`,
      -- and `numFun` ae-vanishes off the kernel.
      have h_Q_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_num_ae_zero] with y hy
        rw [hQ_def]
        simp [hy]
      -- The level-`(m+1)` diff RHS is the indicator of `chartPouKernel` applied
      -- to `numFun / density = Q`.
      have h_diff_eq : eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) l =
          Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
        rw [eigenvectorChartRHSDiff_succ]
        funext y
        rw [hQ_def, hnumFun_def]
        rcases Classical.em (y ∈ chartPouKernel (I := I) (M := M) α) with
          h_mem | h_mem
        · rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_mem,
            one_div, mul_comm, ← div_eq_mul_inv]
        · rw [Set.indicator_of_notMem h_mem, Set.indicator_of_notMem h_mem]
      rw [h_diff_eq]
      -- Strip the indicator via ae-equality on `Ω`.
      have h_strip := sharpDiff_wkpNorm_indicator_eq (I := I) (M := M) α K
        (Q := Q) h_Q_ae_zero
      rw [h_strip]
      -- Now bound `wkpNorm K Q ≤ ofReal Cden · wkpNorm K numFun ≤
      --     ofReal Cden · ofReal (Cnum · μ⁻¹^eNum) · ‖vec‖ =
      --     ofReal ((Cden · Cnum) · μ⁻¹^eNum) · ‖vec‖`.
      have hCnum_bd_i : wkpNorm (d := Module.finrank ℝ E) K 2 numFun
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
        rw [hnumFun_def]
        exact hCnum_bd i
      refine le_trans h_Q_bd ?_
      refine le_trans (mul_le_mul' (le_refl _) hCnum_bd_i) ?_
      have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eNum := by
        exact pow_nonneg (sharpDiff_eigen_inv_nn
          (I := I) (M := M) g r s h_atlas i) _
      rw [show ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cnum * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) from
        ENNReal.ofReal_mul hCnum_nn]
      rw [show ENNReal.ofReal (Cden * Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cden * ENNReal.ofReal Cnum *
            ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) by
        rw [ENNReal.ofReal_mul (mul_nonneg hCden_nn hCnum_nn),
          ENNReal.ofReal_mul hCden_nn]]
      ring_nf
      exact le_refl _

/-! ## The public headline -/

/-- **Sharp chain-length-aware order-`K` `wkpNorm` bound on the differentiated
chart RHS.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis chart
center `α : M`, a component multi-index `P₀`, a level `m`, a regularity order
`K`, a direction multi-index `l : Fin m → Fin n`, and a *per-`K'`-family*
hypothesis bundle `H : sharpDiffPerK g r s h_atlas α P₀`, there is a
nonnegative constant `C : ℝ` and an exponent `e : ℕ` such that, for *every*
eigenbasis index `i`, the order-`K` `wkpNorm` of the level-`m` differentiated
chart RHS is bounded by `ofReal(C · μ⁻¹^e) · ‖vec‖`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (H : sharpDiffPerK (I := I) (M := M) g r s h_atlas α P₀) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
  sharpDiff_recursion (I := I) (M := M) g r s h_atlas α P₀ H m K l

/-! ## Chart-locality-free twins -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `sharpDiff_eigen_inv_one_le`. -/
lemma sharpDiff_eigen_inv_one_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    1 ≤ (i.fst.val)⁻¹ := by
  have h_norm :
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ = 1 :=
    (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s)).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  exact (one_le_inv₀ hμ_unit.1).mpr hμ_unit.2

/-- Chart-locality-free twin of `sharpDiff_eigen_inv_nn`. -/
lemma sharpDiff_eigen_inv_nn_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
  le_trans zero_le_one
    (sharpDiff_eigen_inv_one_le_unconditional (I := I) (M := M) g r s i)

/-- Chart-locality-free twin of `sharpDiff_pow_eigen_inv_mono`. -/
lemma sharpDiff_pow_eigen_inv_mono_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {a b : ℕ} (hab : a ≤ b) :
    (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ b :=
  pow_le_pow_right₀
    (sharpDiff_eigen_inv_one_le_unconditional (I := I) (M := M) g r s i) hab

/-- Chart-locality-free twin of `sharpDiff_ofReal_const_pow_eigen_inv_le`. -/
lemma sharpDiff_ofReal_const_pow_eigen_inv_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {C : ℝ} (hC_nn : 0 ≤ C) {k e : ℕ} (hke : k ≤ e) :
    ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ k) ≤
      ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) := by
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ hC_nn
  exact sharpDiff_pow_eigen_inv_mono_unconditional (I := I) (M := M) g r s i hke

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `sharpDiffPerK`. -/
structure sharpDiffPerK_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) where
  /-- The structural `MemWkp K'` regularity of the resolvent chart component,
  needed to apply `eigenvectorChartRHSDiff_memWkp_unconditional` at every order. -/
  h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
          EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)
  /-- Chart-component bound at order `K'`. -/
  Ceig : ℕ → ℝ
  eEig : ℕ → ℕ
  hCeig_nn : ∀ K', 0 ≤ Ceig K'
  hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- High-order resolvent chart-component atom at order `K' + 1`. -/
  CresH : ℕ → ℝ
  eResH : ℕ → ℕ
  hCresH_nn : ∀ K', 0 ≤ CresH K'
  hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- Low-order resolvent chart-component atom at order `K'`. -/
  CresL : ℕ → ℝ
  eResL : ℕ → ℕ
  hCresL_nn : ∀ K', 0 ≤ CresL K'
  hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- Partial-`Lp`-limit atom at order `K'`. -/
  Cpar : ℕ → ℝ
  ePar : ℕ → ℕ
  hCpar_nn : ∀ K', 0 ≤ Cpar K'
  hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- Component-`Lp`-limit atom at order `K'`. -/
  Ccom : ℕ → ℝ
  eCom : ℕ → ℕ
  hCcom_nn : ∀ K', 0 ≤ Ccom K'
  hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (p : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
            g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- Cross-right limit-component atom at order `K'`. -/
  CcR : ℕ → ℝ
  eCcR : ℕ → ℕ
  hCcR_nn : ∀ K', 0 ≤ CcR K'
  hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
  /-- Cutoff-partial-`Lp`-limit atom at order `K'`. -/
  Ccut : ℕ → ℝ
  eCcut : ℕ → ℕ
  hCcut_nn : ∀ K', 0 ≤ Ccut K'
  hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
    wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
            g r s i α P l :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `sharpDiff_diff_memWkp`. -/
private lemma sharpDiff_diff_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (H : sharpDiffPerK_unconditional (I := I) (M := M) g r s α P₀)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (m K' : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp_unconditional (I := I) (M := M)
    g r s i α P₀ m K' l
    (fun β Q => H.h_pou_resolv i (m + 1 + K') β Q)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `sharpDiff_level_zero_wkpNorm`. -/
private lemma sharpDiff_level_zero_wkpNorm_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (H : sharpDiffPerK_unconditional (I := I) (M := M) g r s α P₀) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- The aggregate bound, sharp in `μ⁻¹^e`.
  obtain ⟨Cagg, eAgg, hCagg_nn, hCagg_bd⟩ :=
    rhsZeroAggregate_le_energy_perK_unconditional (I := I) (M := M) g r s α P₀ K
      H.Ceig H.eEig H.hCeig_nn H.hCeig_bd
      H.CresH H.eResH H.hCresH_nn H.hCresH_bd
      H.CresL H.eResL H.hCresL_nn H.hCresL_bd
      H.Cpar H.ePar H.hCpar_nn H.hCpar_bd
      H.Ccom H.eCom H.hCcom_nn H.hCcom_bd
      H.CcR H.eCcR H.hCcR_nn H.hCcR_bd
      H.Ccut H.eCcut H.hCcut_nn H.hCcut_bd
  -- The `μ⁻¹`-prefactor bound by the seven-summand source aggregate, derived
  -- from the resolvent chart-cpt regularity input in the bundle.
  have h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun i β Q =>
    H.h_pou_resolv i (K + 1) β Q
  obtain ⟨Cmu, hCmu_nn, hCmu_bd⟩ :=
    eigenvectorChartRHS_wkpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀ K h_pou
  refine ⟨Cmu * Cagg, eAgg + 1, mul_nonneg hCmu_nn hCagg_nn, fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_nn_unconditional (I := I) (M := M) g r s i
  have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eAgg :=
    pow_nonneg hμ_inv_nn _
  have hCmu_aux := hCmu_bd i
  have hCagg_aux := hCagg_bd i
  -- The aggregate on the RHS of `hCmu_aux` is, definitionally,
  -- `rhsZeroAggregate_unconditional g r s i α P₀ K`. Use `change` to rephrase.
  change wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) *
        rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K at hCmu_aux
  -- Compose: `wkpNorm RHS ≤ ofReal(μ⁻¹·Cmu) · rhsZeroAggregate ≤
  --   ofReal(μ⁻¹·Cmu) · ofReal(Cagg·μ⁻¹^eAgg) · ‖vec‖ =
  --   ofReal((Cmu·Cagg)·μ⁻¹^(eAgg+1)) · ‖vec‖`.
  refine le_trans hCmu_aux ?_
  refine le_trans (mul_le_mul' (le_refl _) hCagg_aux) ?_
  rw [show ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) =
      ENNReal.ofReal (i.fst.val)⁻¹ * ENNReal.ofReal Cmu from
    ENNReal.ofReal_mul hμ_inv_nn]
  rw [show ENNReal.ofReal (Cagg * (i.fst.val)⁻¹ ^ eAgg) =
      ENNReal.ofReal Cagg * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) from
    ENNReal.ofReal_mul hCagg_nn]
  rw [show ENNReal.ofReal (Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1)) =
      ENNReal.ofReal Cmu * ENNReal.ofReal Cagg *
        ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) * ENNReal.ofReal (i.fst.val)⁻¹ by
    rw [show Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1) =
        Cmu * Cagg * (i.fst.val)⁻¹ ^ eAgg * (i.fst.val)⁻¹ from by ring,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCmu_nn hCagg_nn) hμ_inv_pow_nn),
      ENNReal.ofReal_mul (mul_nonneg hCmu_nn hCagg_nn),
      ENNReal.ofReal_mul hCmu_nn]]
  -- Both sides are products with `‖vec‖`; reassociate the constants on the LHS
  -- and the eigenvalue factor on the RHS.
  ring_nf
  exact le_refl _

set_option maxHeartbeats 32000000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `sharpDiff_recursion`. -/
private lemma sharpDiff_recursion_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (H : sharpDiffPerK_unconditional (I := I) (M := M) g r s α P₀) :
    ∀ (m : ℕ) (K : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)),
      ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
                g r s i α P₀ m l)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖ := by
  classical
  intro m
  induction m with
  | zero =>
      intro K _l
      -- Level `0`: `eigenvectorChartRHSDiff_unconditional … 0 _ =
      -- eigenvectorChartRHS_unconditional`.
      obtain ⟨C, e, hC_nn, hC_bd⟩ :=
        sharpDiff_level_zero_wkpNorm_unconditional (I := I) (M := M)
          g r s α P₀ K H
      refine ⟨C, e, hC_nn, fun i => ?_⟩
      have h_eq : eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ 0 _l =
          eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀ :=
        eigenvectorChartRHSDiff_unconditional_zero (I := I) (M := M)
          g r s i α P₀ _l
      rw [h_eq]
      exact hC_bd i
  | succ m ih =>
      intro K l
      -- The IH at chain `K` and chain `K + 1`, at level `m`, direction
      -- `Fin.init l`. The chain `K + 1` is needed for Layer E.
      obtain ⟨C_K, e_K, hC_K_nn, hC_K_bd⟩ := ih K (Fin.init l)
      obtain ⟨C_K1, e_K1, hC_K1_nn, hC_K1_bd⟩ := ih (K + 1) (Fin.init l)
      -- The structural prerequisites for the numerator sharp bound:
      -- `f_chart_m` is in `MemWkp (K+1) 2` (via `sharpDiff_diff_memWkp_unconditional`),
      -- and `f_chart_m` ae-vanishes off `chartPouKernel α`.
      have h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
        sharpDiff_diff_memWkp_unconditional (I := I) (M := M) g r s α P₀ H i m
          (K + 1) (Fin.init l)
      have h_prev_ae_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
        fun i =>
          eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel_unconditional
            (I := I) (M := M) g r s i α P₀ m (Fin.init l)
      -- The five layer-atom bounds for the numerator sharp bound.
      -- Layer A: `wkpNorm K 2 (m+1)-iter ≤ ofReal (Ceig (K+m+1) · μ⁻¹^eEig) · ‖vec‖`,
      -- using the sharp bridge with `j = m + 1` and chart-cpt at `K + (m + 1)`.
      have hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 1) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖ := by
        intro i a
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
              (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
            g r s i (K + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
            (I := I) (M := M) g r s i α P₀ (m + 1) K
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i (K + (m + 1))
        have h_arith : K + m + 1 = K + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      -- Layer B: `wkpNorm K 2 (chosenWeakPartial b (m+1)-iter) ≤
      --            wkpNorm (K+1) 2 (m+1)-iter ≤ wkpNorm (K+m+2) of chart cpt`.
      have hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a b : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 2) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m + 2))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖ := by
        intro i a b
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) b
        refine le_trans h_chosen ?_
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
              (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
            g r s i ((K + 1) + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
            (I := I) (M := M) g r s i α P₀ (m + 1) (K + 1)
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i ((K + 1) + (m + 1))
        have h_arith : K + m + 2 = (K + 1) + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      -- Layer C: `wkpNorm K 2 (m-iter) ≤ wkpNorm (K + m) of chart cpt`.
      have hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m) *
              (i.fst.val)⁻¹ ^ (H.eEig (K + m))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + m) 2
              (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
            g r s i (K + m) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
            (I := I) (M := M) g r s i α P₀ m K
            h_chart_cpt_mem
            (Fin.init l)).2
        refine le_trans h_bridge ?_
        exact H.hCeig_bd i (K + m)
      -- Layer D: `wkpNorm K (f_chart_m)` — from IH at chain `K`.
      have hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K * (i.fst.val)⁻¹ ^ e_K) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖ := hC_K_bd
      -- Layer E: `wkpNorm K (chosenWeakPartial l_last (f_chart_m)) ≤
      --            wkpNorm (K+1) (f_chart_m)`, from IH at chain `K+1`.
      have hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K1 * (i.fst.val)⁻¹ ^ e_K1) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) (l (Fin.last m))
        exact le_trans h_chosen (hC_K1_bd i)
      -- Now apply the sharp numerator bound twin.
      obtain ⟨Cnum, eNum, hCnum_nn, hCnum_bd⟩ :=
        eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_sharp_unconditional
          (I := I) (M := M) g r s α P₀ m K l
          (fun i => eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (H.Ceig (K + m + 1)) (H.eEig (K + m + 1)) (H.hCeig_nn _) hAtomA_bd
          (H.Ceig (K + m + 2)) (H.eEig (K + m + 2)) (H.hCeig_nn _) hAtomB_bd
          (H.Ceig (K + m)) (H.eEig (K + m)) (H.hCeig_nn _) hAtomC_bd
          C_K e_K hC_K_nn hAtomD_bd
          C_K1 e_K1 hC_K1_nn hAtomE_bd
          h_prev_mem_succ h_prev_ae_zero
      -- Reduce the level-`(m+1)` `wkpNorm` to the numerator/density `wkpNorm`
      -- via indicator stripping + reciprocal-density smooth-coefficient bound.
      obtain ⟨Cden, hCden_nn, hCden_bd⟩ :=
        sharpDiff_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
          (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid
            (I := I) (M := M) g α)
      refine ⟨Cden * Cnum, eNum, mul_nonneg hCden_nn hCnum_nn, fun i => ?_⟩
      -- The numerator function (at `i`).
      set numFun : EuclN → ℝ :=
        eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
          g r s i α P₀ m l
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) with hnumFun_def
      -- The quotient function `numFun / density`, written as `(1/density) · numFun`.
      set Q : EuclN → ℝ := fun y =>
        (1 / densityOnEuclid (I := I) g α y) * numFun y with hQ_def
      -- Numerator is `MemWkp K 2` and ae-vanishes off `chartPouKernel`.
      have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hnumFun_def]
        refine eigenvectorChartRHSDiffNumerator_memWkp_of_iter_unconditional
          (I := I) (M := M) g r s i α P₀ m K l ?_ ?_ ?_
        · intro j idx
          have h_chart_cpt_mem :
              MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
                (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
                  g r s i α P₀)
                (chartTargetEuclid (I := I) (M := M) α) :=
            eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
              g r s i ((2 + K) + j) α P₀
          exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
            (I := I) (M := M) g r s i α P₀ j (2 + K)
            h_chart_cpt_mem idx).1
        · exact h_prev_mem_succ i
        · exact h_prev_ae_zero i
      have h_num_ae_zero :
          numFun =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        rw [hnumFun_def]
        exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ m l (h_prev_ae_zero i)
      -- `Q = (1/density) · numFun` is `MemWkp K 2` and ae-vanishes off
      -- `chartPouKernel`.
      have h_Q_props := hCden_bd numFun h_num_memWkp h_num_ae_zero
      have h_Q_bd : wkpNorm (d := Module.finrank ℝ E) K 2 Q
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal Cden *
            wkpNorm (d := Module.finrank ℝ E) K 2 numFun
              (chartTargetEuclid (I := I) (M := M) α) := h_Q_props.2
      -- `Q` ae-vanishes off `chartPouKernel`: `Q y = (1/density) · numFun y`,
      -- and `numFun` ae-vanishes off the kernel.
      have h_Q_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_num_ae_zero] with y hy
        rw [hQ_def]
        simp [hy]
      -- The level-`(m+1)` diff RHS is the indicator of `chartPouKernel` applied
      -- to `numFun / density = Q`.
      have h_diff_eq : eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) l =
          Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
        rw [eigenvectorChartRHSDiff_unconditional_succ]
        funext y
        rw [hQ_def, hnumFun_def]
        rcases Classical.em (y ∈ chartPouKernel (I := I) (M := M) α) with
          h_mem | h_mem
        · rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_mem,
            one_div, mul_comm, ← div_eq_mul_inv]
        · rw [Set.indicator_of_notMem h_mem, Set.indicator_of_notMem h_mem]
      rw [h_diff_eq]
      -- Strip the indicator via ae-equality on `Ω`.
      have h_strip := sharpDiff_wkpNorm_indicator_eq (I := I) (M := M) α K
        (Q := Q) h_Q_ae_zero
      rw [h_strip]
      -- Now bound `wkpNorm K Q ≤ ofReal Cden · wkpNorm K numFun ≤
      --     ofReal Cden · ofReal (Cnum · μ⁻¹^eNum) · ‖vec‖ =
      --     ofReal ((Cden · Cnum) · μ⁻¹^eNum) · ‖vec‖`.
      have hCnum_bd_i : wkpNorm (d := Module.finrank ℝ E) K 2 numFun
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
        rw [hnumFun_def]
        exact hCnum_bd i
      refine le_trans h_Q_bd ?_
      refine le_trans (mul_le_mul' (le_refl _) hCnum_bd_i) ?_
      have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eNum := by
        exact pow_nonneg (sharpDiff_eigen_inv_nn_unconditional
          (I := I) (M := M) g r s i) _
      rw [show ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cnum * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) from
        ENNReal.ofReal_mul hCnum_nn]
      rw [show ENNReal.ofReal (Cden * Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cden * ENNReal.ofReal Cnum *
            ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) by
        rw [ENNReal.ofReal_mul (mul_nonneg hCden_nn hCnum_nn),
          ENNReal.ofReal_mul hCden_nn]]
      ring_nf
      exact le_refl _

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (H : sharpDiffPerK_unconditional (I := I) (M := M) g r s α P₀) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ :=
  sharpDiff_recursion_unconditional (I := I) (M := M) g r s α P₀ H m K l

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
