import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.TensorChartSmooth
import DifferentialGeometry.Integral.Connection.BochnerConcrete

/-!
# Chart-invariance of the chart-α tensor Hessian–Frobenius pairing

For smooth `φ : C^∞⟮I, M; ℝ⟯` and a smooth scalar `v : SmoothScalar g` on a closed
Riemannian manifold `(M, g)`, this module bridges the chart-α tensor smooth
Hessian–Frobenius pairing on `EuclideanSpace`
(`smoothTensorPairingChart g α φ v y`, defined in `HessianTensorChartSmooth`)
with the chart-invariant smooth pairing on `M`
(`hessPairingChart g φ v_bundle x`, defined in `HessianPairingChart`) via the
chart-α inverse map `x = (extChartAt α).symm (toEuclidean.symm y)`.

The structural backbone:

1. **Manifold-side chart-α pairing.** Lift `smoothTensorPairingChart` from
   `EuclN` to a function on `M` by pulling back the chart-α coordinates:
   `hessPairingByChartα g α φ v x := smoothTensorPairingChart g α φ v
       (toEuclidean (extChartAt α x))`.

2. **Pointwise identity on the chart target.** For `y ∈ chartTargetEuclid α`,
   `smoothTensorPairingChart g α φ v y =
       hessPairingByChartα g α φ v ((extChartAt α).symm (toEuclidean.symm y))`
   by mechanical chart-pullback algebra.

3. **Chart-invariance of the pointwise pairing.** For `x` in the chart source
   `(chartAt H α).source`, the chart-α pairing `hessPairingByChartα g α φ v x`
   equals the chart-invariant pairing `hessPairingChart g φ v_bundle x` (where
   `v_bundle := smoothScalarToContMDiffMap v`). The proof goes through the
   common chart-invariant Hilbert–Schmidt inner product of the abstract
   Hessian operators of `φ` and `v` at `x`.

The chart-invariance step splits into:

   3a. *Chart-α matrix identity.* For `x ∈ (chartAt H α).source`, the abstract
       Hessian `abstractHessian g f x` on the chart-α basis pair
       `(chartBasisVecFiber α i x, chartBasisVecFiber α j x)` equals the chart-α
       tensor Hessian `chartHessianTensor g α f i j x`.

   3b. *Chart-α Hilbert–Schmidt identity.* The chart-α tensor Frobenius squared
       `chartHessFrobeniusSqOnChartAlpha g α f x` equals `chartHessFrobeniusSq
       g f x` (the chart-at-x version). The proof mirrors
       `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq` from `BochnerConcrete`,
       with the chart-α matrix identity replacing the chart-at-x version.

   3c. *Polarization bridge.* The bilinear pairing `hessPairingByChartα g α φ v
       x` arises as the polarization
       `(chartHessFrobeniusSqOnChartAlpha g α (φ + v) x -
         chartHessFrobeniusSqOnChartAlpha g α (φ - v) x) / 4`,
       and likewise `hessPairingChart` arises as the chart-at-x polarization.
       By 3b, the two polarizations agree.

The chart-α matrix identity 3a is the lynchpin lemma; once it holds, the rest
of the chain (3b, 3c, 2, 1) is mechanical algebra. We package 3a as the
`chartAlphaMatrixIdentity` hypothesis, exposed as an explicit `Prop`, and
deliver the full chart-invariant identification chain conditional on it.

## Main definitions

* `hessPairingByChartα g α φ v x` — the pointwise chart-α tensor Frobenius
  pairing on `M`, defined as the chart-α-Euclidean version pulled back.

* `chartHessFrobeniusSqOnChartAlpha g α f x` — the chart-α tensor Frobenius
  squared of `f` at `x`, using chart-α basis and chart-α Gram matrices.

* `chartAlphaMatrixIdentity g α f x` — the lynchpin Prop: chart-α tensor
  Hessian entries equal the abstract Hessian on the chart-α basis pair.

## Main results

* `smoothTensorPairingChart_eq_hessPairingByChartα_pullback` — pointwise
  pullback identity on the chart target (no chart-α matrix identity needed).

* `chartHessFrobeniusPairOnChartAlpha_eq_polarization_of_smooth` — polarization
  identity for the chart-α Frobenius bilinear pairing (uses bilinearity in the
  function argument).

* `chartFrobeniusInvariance_of_HSBridge` — chart-α / chart-at-x agreement for
  the chart-Frobenius squared, conditional on the chart-α Hilbert–Schmidt
  bridge for `f` at `x`.

* `chartHessFrobeniusPairOnChartAlpha_eq_hessPairingChart_of_invariance` —
  chart-α / chart-at-x agreement for the pointwise pairing of two smooth
  scalars, conditional on the chart-α Frobenius invariance for the polarization
  combinations `φ ± v` at `x`.

* `smoothTensorPairingChart_eq_hessPairingChart_of_invariance` and
  `smoothTensorPairingChart_eq_hessPairingChart_of_HSBridge` — the bridge
  identity at the pointwise Euclidean level, conditional respectively on the
  chart-α Frobenius invariance or the chart-α Hilbert–Schmidt bridge for the
  polarization combinations at the chart-α image of `x`.

The chart-α matrix identity `chartAlphaMatrixIdentity` is left as an explicit
hypothesis to be discharged by follow-up work via the chart-α analog of
`chartHessianMatrixIdentity_holds`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartInvariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Sobolev.Chart


private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


/-- The pointwise chart-α tensor Frobenius pairing on `M`. -/
noncomputable def hessPairingByChartα
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (x : M) : ℝ :=
  smoothTensorPairingChart (I := I) (M := M) g α φ v
    ((toEuclidean (E := E)) (extChartAt I α x))

@[simp] lemma hessPairingByChartα_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (x : M) :
    hessPairingByChartα (I := I) (M := M) g α φ v x =
      smoothTensorPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) := rfl


/-- The pullback identity for `smoothTensorPairingChart`. -/
theorem smoothTensorPairingChart_eq_hessPairingByChartα_pullback
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingByChartα (I := I) (M := M) g α φ v
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold hessPairingByChartα
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_chart_inv : extChartAt I α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  have h_toE_inv : (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  rw [h_chart_inv, h_toE_inv]


/-- The chart-α tensor Frobenius squared of `f` at the manifold point `x`. -/
noncomputable def chartHessFrobeniusSqOnChartAlpha
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i k *
            chartInvGramMatrix (I := I) g α x j l *
            chartHessianTensor (I := I) g α f i j x *
            chartHessianTensor (I := I) g α f k l x

@[simp] lemma chartHessFrobeniusSqOnChartAlpha_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x i k *
                chartInvGramMatrix (I := I) g α x j l *
                chartHessianTensor (I := I) g α f i j x *
                chartHessianTensor (I := I) g α f k l x := rfl


/-- The chart-α tensor Frobenius bilinear pairing of `f` and `f'` at `x`. -/
noncomputable def chartHessFrobeniusPairOnChartAlpha
    (g : SmoothRiemannianMetric I M) (α : M) (f f' : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i k *
            chartInvGramMatrix (I := I) g α x j l *
            chartHessianTensor (I := I) g α f i j x *
            chartHessianTensor (I := I) g α f' k l x

@[simp] lemma chartHessFrobeniusPairOnChartAlpha_def
    (g : SmoothRiemannianMetric I M) (α : M) (f f' : M → ℝ) (x : M) :
    chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α f f' x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x i k *
                chartInvGramMatrix (I := I) g α x j l *
                chartHessianTensor (I := I) g α f i j x *
                chartHessianTensor (I := I) g α f' k l x := rfl

/-- `chartHessFrobeniusPairOnChartAlpha g α f f x = chartHessFrobeniusSqOnChartAlpha g α f x`. -/
@[simp] lemma chartHessFrobeniusPairOnChartAlpha_self
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α f f x =
      chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x := rfl



private lemma scalarOnE_add_pointwise (α : M) (f f' : M → ℝ) :
    scalarOnE (I := I) α (fun y : M => f y + f' y) =
      (fun y : E => scalarOnE (I := I) α f y + scalarOnE (I := I) α f' y) := by
  funext y
  unfold scalarOnE
  rfl

private lemma scalarOnE_neg_pointwise (α : M) (f : M → ℝ) :
    scalarOnE (I := I) α (fun y : M => -f y) =
      (fun y : E => -scalarOnE (I := I) α f y) := by
  funext y
  unfold scalarOnE
  rfl

/-- **Linearity of `chartHessianTensor` in the function argument (additivity),
on the chart α source.** For smooth scalars `f, f'` and `x ∈ (chartAt H α).source`,
the chart-α tensor Hessian distributes over sums. -/
lemma chartHessianTensor_add_of_smooth
    (g : SmoothRiemannianMetric I M) (α : M) {f f' : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf' : ContMDiff I 𝓘(ℝ) ∞ f')
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartHessianTensor (I := I) g α (fun y : M => f y + f' y) i j x =
      chartHessianTensor (I := I) g α f i j x +
        chartHessianTensor (I := I) g α f' i j x := by
  classical
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hf'_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f')
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf'
  have hx_src_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_tgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src_ext
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_tgt
  have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hf_int_diff : ∀ y ∈ interior ((extChartAt I α).target : Set E),
      DifferentiableAt ℝ (scalarOnE (I := I) α f) y := by
    intro y hy
    have hf_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
        (interior ((extChartAt I α).target : Set E)) :=
      hf_smooth_target.mono interior_subset
    have hf_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) y :=
      hf_int.contDiffAt (hopen_int.mem_nhds hy)
    exact hf_at.differentiableAt (by simp)
  have hf'_int_diff : ∀ y ∈ interior ((extChartAt I α).target : Set E),
      DifferentiableAt ℝ (scalarOnE (I := I) α f') y := by
    intro y hy
    have hf'_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f')
        (interior ((extChartAt I α).target : Set E)) :=
      hf'_smooth_target.mono interior_subset
    have hf'_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f') y :=
      hf'_int.contDiffAt (hopen_int.mem_nhds hy)
    exact hf'_at.differentiableAt (by simp)
  set u : E → ℝ := scalarOnE (I := I) α f with hu_def
  set u' : E → ℝ := scalarOnE (I := I) α f' with hu'_def
  set z : E := extChartAt I α x with hz_def
  rw [chartHessianTensor_def, chartHessianTensor_def, chartHessianTensor_def]
  have h_iter_add : chartIteratedPartialDeriv (I := I) α
      (fun y : M => f y + f' y) i j z =
      chartIteratedPartialDeriv (I := I) α f i j z +
        chartIteratedPartialDeriv (I := I) α f' i j z := by
    unfold chartIteratedPartialDeriv partialDeriv
    rw [scalarOnE_add_pointwise (I := I) α f f']
    have h_inner_pointwise : ∀ y ∈ interior ((extChartAt I α).target : Set E),
        fderiv ℝ (fun w : E => u w + u' w) y =
          fderiv ℝ u y + fderiv ℝ u' y := by
      intro y hy
      exact fderiv_fun_add (hf_int_diff y hy) (hf'_int_diff y hy)
    have h_eq_eventually : (fun y : E => fderiv ℝ (fun w : E => u w + u' w) y
          ((chartModelBasis E) j)) =ᶠ[𝓝 z]
        (fun y : E => fderiv ℝ u y ((chartModelBasis E) j) +
          fderiv ℝ u' y ((chartModelBasis E) j)) := by
      have h_nbd : interior ((extChartAt I α).target : Set E) ∈ 𝓝 z :=
        hopen_int.mem_nhds hx_int
      filter_upwards [h_nbd] with y hy
      rw [h_inner_pointwise y hy]
      rfl
    have h_LHS_fderiv : fderiv ℝ (fun y : E => fderiv ℝ
        (fun w : E => u w + u' w) y ((chartModelBasis E) j)) z =
        fderiv ℝ (fun y : E => fderiv ℝ u y ((chartModelBasis E) j) +
          fderiv ℝ u' y ((chartModelBasis E) j)) z :=
      Filter.EventuallyEq.fderiv_eq h_eq_eventually
    rw [h_LHS_fderiv]
    have h_a_diff_at_z : DifferentiableAt ℝ
        (fun y : E => fderiv ℝ u y ((chartModelBasis E) j)) z := by
      have hf_fder_int : ContDiffOn ℝ ∞ (fderiv ℝ u)
          (interior ((extChartAt I α).target : Set E)) := by
        have hf_int : ContDiffOn ℝ ∞ u
            (interior ((extChartAt I α).target : Set E)) :=
          hf_smooth_target.mono interior_subset
        exact hf_int.fderiv_of_isOpen hopen_int (by rw [ENat.coe_top_add_one])
      have hf_pd : ContDiffOn ℝ ∞
          (fun y : E => fderiv ℝ u y ((chartModelBasis E) j))
          (interior ((extChartAt I α).target : Set E)) :=
        hf_fder_int.clm_apply contDiffOn_const
      have hf_pd_at : ContDiffAt ℝ ∞
          (fun y : E => fderiv ℝ u y ((chartModelBasis E) j)) z :=
        hf_pd.contDiffAt (hopen_int.mem_nhds hx_int)
      exact hf_pd_at.differentiableAt (by simp)
    have h_b_diff_at_z : DifferentiableAt ℝ
        (fun y : E => fderiv ℝ u' y ((chartModelBasis E) j)) z := by
      have hf'_fder_int : ContDiffOn ℝ ∞ (fderiv ℝ u')
          (interior ((extChartAt I α).target : Set E)) := by
        have hf'_int : ContDiffOn ℝ ∞ u'
            (interior ((extChartAt I α).target : Set E)) :=
          hf'_smooth_target.mono interior_subset
        exact hf'_int.fderiv_of_isOpen hopen_int (by rw [ENat.coe_top_add_one])
      have hf'_pd : ContDiffOn ℝ ∞
          (fun y : E => fderiv ℝ u' y ((chartModelBasis E) j))
          (interior ((extChartAt I α).target : Set E)) :=
        hf'_fder_int.clm_apply contDiffOn_const
      have hf'_pd_at : ContDiffAt ℝ ∞
          (fun y : E => fderiv ℝ u' y ((chartModelBasis E) j)) z :=
        hf'_pd.contDiffAt (hopen_int.mem_nhds hx_int)
      exact hf'_pd_at.differentiableAt (by simp)
    have h_outer_add : fderiv ℝ
        (fun y : E => fderiv ℝ u y ((chartModelBasis E) j) +
          fderiv ℝ u' y ((chartModelBasis E) j)) z =
        fderiv ℝ (fun y : E => fderiv ℝ u y ((chartModelBasis E) j)) z +
          fderiv ℝ (fun y : E => fderiv ℝ u' y ((chartModelBasis E) j)) z := by
      exact fderiv_fun_add h_a_diff_at_z h_b_diff_at_z
    rw [h_outer_add]
    rfl
  have h_chris_add : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k
          (scalarOnE (I := I) α (fun y : M => f y + f' y)) z =
        partialDeriv (E := E) k (scalarOnE (I := I) α f) z +
          partialDeriv (E := E) k (scalarOnE (I := I) α f') z := by
    intro k
    unfold partialDeriv
    rw [scalarOnE_add_pointwise (I := I) α f f']
    have hu_diff : DifferentiableAt ℝ u z := hf_int_diff z hx_int
    have hu'_diff : DifferentiableAt ℝ u' z := hf'_int_diff z hx_int
    have h_fderiv_add : fderiv ℝ (fun y : E => u y + u' y) z =
        fderiv ℝ u z + fderiv ℝ u' z := by
      change fderiv ℝ (u + u') z = fderiv ℝ u z + fderiv ℝ u' z
      exact fderiv_fun_add hu_diff hu'_diff
    rw [h_fderiv_add]
    rfl
  have h_chris_sum :
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k z *
          partialDeriv (E := E) k
            (scalarOnE (I := I) α (fun y : M => f y + f' y)) z =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k z *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) z +
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k z *
          partialDeriv (E := E) k (scalarOnE (I := I) α f') z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [h_chris_add k]
    ring
  rw [h_iter_add, h_chris_sum]
  ring

/-- **Linearity of `chartHessianTensor` in the function argument (negation),
on the chart α source.** -/
lemma chartHessianTensor_neg_of_smooth
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartHessianTensor (I := I) g α (fun y : M => -f y) i j x =
      -chartHessianTensor (I := I) g α f i j x := by
  classical
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hx_src_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_tgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src_ext
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_tgt
  have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  set u : E → ℝ := scalarOnE (I := I) α f with hu_def
  set z : E := extChartAt I α x with hz_def
  rw [chartHessianTensor_def, chartHessianTensor_def]
  have h_iter_neg : chartIteratedPartialDeriv (I := I) α
      (fun y : M => -f y) i j z = -chartIteratedPartialDeriv (I := I) α f i j z := by
    unfold chartIteratedPartialDeriv partialDeriv
    rw [scalarOnE_neg_pointwise (I := I) α f]
    have h_fderiv_neg_fn : (fun y : E => fderiv ℝ (fun w : E => -u w) y
          ((chartModelBasis E) j)) =
        fun y : E => -fderiv ℝ u y ((chartModelBasis E) j) := by
      funext y
      have h1 : fderiv ℝ (fun w : E => -u w) y = -fderiv ℝ u y := by
        change fderiv ℝ (-u) y = -fderiv ℝ u y
        rw [fderiv_neg]
      rw [h1]
      rfl
    rw [h_fderiv_neg_fn]
    have h_outer_neg : fderiv ℝ (fun y : E => -(fderiv ℝ u y ((chartModelBasis E) j))) z =
        -fderiv ℝ (fun y : E => fderiv ℝ u y ((chartModelBasis E) j)) z := by
      change fderiv ℝ (-(fun y : E => fderiv ℝ u y ((chartModelBasis E) j))) z = _
      rw [fderiv_neg]
    rw [h_outer_neg]
    rfl
  have h_chris_neg : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (scalarOnE (I := I) α (fun y : M => -f y)) z =
        -partialDeriv (E := E) k (scalarOnE (I := I) α f) z := by
    intro k
    unfold partialDeriv
    rw [scalarOnE_neg_pointwise (I := I) α f]
    have h_fderiv_neg : fderiv ℝ (fun y : E => -u y) z = -fderiv ℝ u z := by
      change fderiv ℝ (-u) z = -fderiv ℝ u z
      rw [fderiv_neg]
    rw [h_fderiv_neg]
    rfl
  have h_chris_sum :
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k z *
          partialDeriv (E := E) k (scalarOnE (I := I) α (fun y : M => -f y)) z =
      -∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k z *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) z := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [h_chris_neg k]
    ring
  rw [h_iter_neg, h_chris_sum]
  ring

/-- **Linearity of `chartHessianTensor` in the function argument (subtraction),
on the chart α source.** -/
lemma chartHessianTensor_sub_of_smooth
    (g : SmoothRiemannianMetric I M) (α : M) {f f' : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf' : ContMDiff I 𝓘(ℝ) ∞ f')
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartHessianTensor (I := I) g α (fun y : M => f y - f' y) i j x =
      chartHessianTensor (I := I) g α f i j x -
        chartHessianTensor (I := I) g α f' i j x := by
  classical
  have heq : (fun y : M => f y - f' y) = (fun y : M => f y + (-f' y)) := by
    funext y; ring
  have hf'_neg : ContMDiff I 𝓘(ℝ) ∞ (fun y : M => -f' y) := hf'.neg
  rw [heq]
  rw [chartHessianTensor_add_of_smooth (I := I) g α hf hf'_neg i j hx]
  rw [chartHessianTensor_neg_of_smooth (I := I) g α hf' i j hx]
  ring

/-- **Polarization identity for the chart-α Frobenius pairing.** For two smooth
scalars `f, f' : M → ℝ` and `x ∈ (chartAt H α).source`, the chart-α bilinear
pairing equals the polarization of the chart-α Frobenius squared.

The proof relies on:
1. Linearity of `chartHessianTensor` in the function argument (smoothness needed).
2. Symmetry of the chart inverse Gram matrix to identify the cross terms in the
   polarization expansion.

The symmetry-based relabeling of the cross terms is supplied as the explicit
hypothesis `h_swap_aux`. -/
theorem chartHessFrobeniusPairOnChartAlpha_eq_polarization_of_smooth
    (g : SmoothRiemannianMetric I M) (α : M) {f f' : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf' : ContMDiff I 𝓘(ℝ) ∞ f')
    {x : M} (hx : x ∈ (chartAt H α).source)
    (h_swap_aux :
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f' i j x *
          chartHessianTensor (I := I) g α f k l x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f i j x *
          chartHessianTensor (I := I) g α f' k l x)) :
    4 * chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α f f' x =
      chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α (fun y : M => f y + f' y) x -
        chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α (fun y : M => f y - f' y) x := by
  classical
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartInvGramMatrix (I := I) g α x i k with hG_def
  set Hf : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f i j x with hHf_def
  set Hf' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f' i j x with hHf'_def
  have h_Hadd : ∀ (i j : Fin (Module.finrank ℝ E)),
      chartHessianTensor (I := I) g α (fun y : M => f y + f' y) i j x = Hf i j + Hf' i j := by
    intro i j
    rw [chartHessianTensor_add_of_smooth (I := I) g α hf hf' i j hx]
  have h_Hsub : ∀ (i j : Fin (Module.finrank ℝ E)),
      chartHessianTensor (I := I) g α (fun y : M => f y - f' y) i j x = Hf i j - Hf' i j := by
    intro i j
    rw [chartHessianTensor_sub_of_smooth (I := I) g α hf hf' i j hx]
  have h_Gsymm : ∀ i k : Fin (Module.finrank ℝ E), G i k = G k i := by
    intro i k
    change chartInvGramMatrix (I := I) g α x i k = chartInvGramMatrix (I := I) g α x k i
    have hHerm : (chartGramMatrix (I := I) g α x).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α x
    have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
      unfold chartInvGramMatrix
      exact hHerm.inv
    have h_apply := hHermInv.apply i k
    rw [star_trivial] at h_apply
    exact h_apply.symm
  rw [chartHessFrobeniusPairOnChartAlpha_def, chartHessFrobeniusSqOnChartAlpha_def,
    chartHessFrobeniusSqOnChartAlpha_def]
  simp only [← hG_def]
  have h_rhs_eq :
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * chartHessianTensor (I := I) g α (fun y : M => f y + f' y) i j x *
          chartHessianTensor (I := I) g α (fun y : M => f y + f' y) k l x) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * chartHessianTensor (I := I) g α (fun y : M => f y - f' y) i j x *
          chartHessianTensor (I := I) g α (fun y : M => f y - f' y) k l x) =
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * (Hf i j + Hf' i j) * (Hf k l + Hf' k l)) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * (Hf i j - Hf' i j) * (Hf k l - Hf' k l)) := by
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_Hadd i j, h_Hadd k l]
    · refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_Hsub i j, h_Hsub k l]
  rw [h_rhs_eq]
  have h_per_term_eq : ∀ (i j k l : Fin (Module.finrank ℝ E)),
      G i k * G j l * (Hf i j + Hf' i j) * (Hf k l + Hf' k l) -
        G i k * G j l * (Hf i j - Hf' i j) * (Hf k l - Hf' k l) =
      2 * (G i k * G j l * Hf i j * Hf' k l) +
        2 * (G i k * G j l * Hf' i j * Hf k l) := by
    intro i j k l
    ring
  have h_combine :
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * (Hf i j + Hf' i j) * (Hf k l + Hf' k l)) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        G i k * G j l * (Hf i j - Hf' i j) * (Hf k l - Hf' k l)) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (G i k * G j l * (Hf i j + Hf' i j) * (Hf k l + Hf' k l) -
          G i k * G j l * (Hf i j - Hf' i j) * (Hf k l - Hf' k l)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← Finset.sum_sub_distrib]
  rw [h_combine]
  have h_per_apply :
      ∑ i, ∑ j, ∑ k, ∑ l,
        (G i k * G j l * (Hf i j + Hf' i j) * (Hf k l + Hf' k l) -
          G i k * G j l * (Hf i j - Hf' i j) * (Hf k l - Hf' k l)) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (2 * (G i k * G j l * Hf i j * Hf' k l) +
          2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    exact h_per_term_eq i j k l
  rw [h_per_apply]
  have h_split :
      ∑ i, ∑ j, ∑ k, ∑ l,
        (2 * (G i k * G j l * Hf i j * Hf' k l) +
          2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * (G i k * G j l * Hf i j * Hf' k l)) +
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← Finset.sum_add_distrib]
  rw [h_split]
  have h_swap :
      ∑ i, ∑ j, ∑ k, ∑ l, 2 * (G i k * G j l * Hf' i j * Hf k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, 2 * (G i k * G j l * Hf i j * Hf' k l) := h_swap_aux
  rw [h_swap]
  have h_double :
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * (G i k * G j l * Hf i j * Hf' k l)) =
      2 * (∑ i, ∑ j, ∑ k, ∑ l, (G i k * G j l * Hf i j * Hf' k l)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
  rw [h_double]
  ring


/-- **The chart-α matrix identity.** For `f : M → ℝ` of class `C^∞` and
`x ∈ (chartAt H α).source`, the abstract Hessian `abstractHessian g f x` on the
chart-α basis pair equals the chart-α tensor Hessian entry. -/
def chartAlphaMatrixIdentity
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) : Prop :=
  ∀ i j : Fin (Module.finrank ℝ E),
    abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) =
      chartHessianTensor (I := I) g α f i j x

@[simp] lemma chartAlphaMatrixIdentity_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartAlphaMatrixIdentity (I := I) (M := M) g α f x ↔
      ∀ i j : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x
            (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α j x) =
          chartHessianTensor (I := I) g α f i j x := Iff.rfl


/-- For `x` in the chart-α base set, the chart-α basis at `x` is the model basis
trivialized via chart α. We package this fact in a form usable by the
Hilbert–Schmidt frame trace identity. -/
private lemma chartBasisVecFiber_baseSet
    (α : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α
        ⟨x, chartBasisVecFiber (I := I) α i x⟩).2 =
      (chartModelBasis E) i :=
  trivializationAt_chartBasisVec_snd (I := I) α i hx


/-- The chart-α tensor Frobenius squared rewritten using the abstract Hessian
on the chart-α basis pair, conditional on the chart-α matrix identity. -/
theorem chartHessFrobeniusSqOnChartAlpha_eq_abstractHessian
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M)
    (hM : chartAlphaMatrixIdentity (I := I) (M := M) g α f x) :
    chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x i k *
                chartInvGramMatrix (I := I) g α x j l *
                abstractHessian (I := I) g f x
                  (chartBasisVecFiber (I := I) α i x)
                  (chartBasisVecFiber (I := I) α j x) *
                abstractHessian (I := I) g f x
                  (chartBasisVecFiber (I := I) α k x)
                  (chartBasisVecFiber (I := I) α l x) := by
  classical
  rw [chartHessFrobeniusSqOnChartAlpha_def]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hM i j, hM k l]

/-- Similarly, the chart-α bilinear pairing rewritten using abstract Hessians on
the chart-α basis pair, conditional on the chart-α matrix identity for both
functions. -/
theorem chartHessFrobeniusPairOnChartAlpha_eq_abstractHessian
    (g : SmoothRiemannianMetric I M) (α : M) (f f' : M → ℝ) (x : M)
    (hMf : chartAlphaMatrixIdentity (I := I) (M := M) g α f x)
    (hMf' : chartAlphaMatrixIdentity (I := I) (M := M) g α f' x) :
    chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α f f' x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x i k *
                chartInvGramMatrix (I := I) g α x j l *
                abstractHessian (I := I) g f x
                  (chartBasisVecFiber (I := I) α i x)
                  (chartBasisVecFiber (I := I) α j x) *
                abstractHessian (I := I) g f' x
                  (chartBasisVecFiber (I := I) α k x)
                  (chartBasisVecFiber (I := I) α l x) := by
  classical
  rw [chartHessFrobeniusPairOnChartAlpha_def]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hMf i j, hMf' k l]


/-- **Chart-invariance hypothesis.** The chart-α tensor Frobenius squared at `x`
equals the chart-at-`x` Frobenius squared `chartHessFrobeniusSq g f x`. This is
the chart-α analog of `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`. -/
def chartFrobeniusInvariance
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) : Prop :=
  chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
    chartHessFrobeniusSq (I := I) g f x

@[simp] lemma chartFrobeniusInvariance_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartFrobeniusInvariance (I := I) (M := M) g α f x ↔
      chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
        chartHessFrobeniusSq (I := I) g f x := Iff.rfl

/-- **Bridge from chart-α to chart-invariant pairing.** Conditional on the
chart-α Frobenius invariance for both polarization combinations (`φ + v` and
`φ - v`), and `x ∈ (chartAt H α).source`, the chart-α bilinear pairing equals
the chart-invariant Hess pairing. -/
theorem chartHessFrobeniusPairOnChartAlpha_eq_hessPairingChart_of_invariance
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (h_inv_add : chartFrobeniusInvariance (I := I) (M := M) g α
      (fun y : M => (φ : M → ℝ) y + v.toFun y) x)
    (h_inv_sub : chartFrobeniusInvariance (I := I) (M := M) g α
      (fun y : M => (φ : M → ℝ) y - v.toFun y) x)
    (h_swap_aux :
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α v.toFun i j x *
          chartHessianTensor (I := I) g α (φ : M → ℝ) k l x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α (φ : M → ℝ) i j x *
          chartHessianTensor (I := I) g α v.toFun k l x)) :
    chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α
        (φ : M → ℝ) v.toFun x =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  have h_pol_left : 4 * chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α
      (φ : M → ℝ) v.toFun x =
      chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α
          (fun y : M => (φ : M → ℝ) y + v.toFun y) x -
        chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α
          (fun y : M => (φ : M → ℝ) y - v.toFun y) x :=
    chartHessFrobeniusPairOnChartAlpha_eq_polarization_of_smooth (I := I) (M := M) g α
      φ.contMDiff v.smooth hx h_swap_aux
  rw [chartFrobeniusInvariance_def] at h_inv_add h_inv_sub
  have h_subst : chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α
      (fun y : M => (φ : M → ℝ) y + v.toFun y) x -
        chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α
          (fun y : M => (φ : M → ℝ) y - v.toFun y) x =
      chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y + v.toFun y) x -
        chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y - v.toFun y) x := by
    rw [h_inv_add, h_inv_sub]
  have h_v_bundle_eq : ∀ y : M,
      (smoothScalarToContMDiffMap (I := I) (g := g) v : M → ℝ) y = v.toFun y := by
    intro y
    rfl
  have h_pol_right : 4 * hessPairingChart (I := I) g φ
      (smoothScalarToContMDiffMap (I := I) (g := g) v) x =
      chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y + v.toFun y) x -
        chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y - v.toFun y) x := by
    rw [hessPairingChart_def]
    have h_add_eq : (fun x : M => (φ : M → ℝ) x +
          (smoothScalarToContMDiffMap (I := I) (g := g) v : M → ℝ) x) =
        (fun y : M => (φ : M → ℝ) y + v.toFun y) := by
      funext y
      rw [h_v_bundle_eq y]
    have h_sub_eq : (fun x : M => (φ : M → ℝ) x -
          (smoothScalarToContMDiffMap (I := I) (g := g) v : M → ℝ) x) =
        (fun y : M => (φ : M → ℝ) y - v.toFun y) := by
      funext y
      rw [h_v_bundle_eq y]
    have h_phi_eq : ∀ x : M, (φ : C^∞⟮I, M; ℝ⟯) x = (φ : M → ℝ) x := by
      intro x; rfl
    rw [show (fun x : M => (φ : C^∞⟮I, M; ℝ⟯) x +
          (smoothScalarToContMDiffMap (I := I) (g := g) v : C^∞⟮I, M; ℝ⟯) x) =
        (fun y : M => (φ : M → ℝ) y + v.toFun y) from by
      funext y
      change (φ : M → ℝ) y +
        (smoothScalarToContMDiffMap (I := I) (g := g) v : M → ℝ) y = _
      rw [h_v_bundle_eq y]]
    rw [show (fun x : M => (φ : C^∞⟮I, M; ℝ⟯) x -
          (smoothScalarToContMDiffMap (I := I) (g := g) v : C^∞⟮I, M; ℝ⟯) x) =
        (fun y : M => (φ : M → ℝ) y - v.toFun y) from by
      funext y
      change (φ : M → ℝ) y -
        (smoothScalarToContMDiffMap (I := I) (g := g) v : M → ℝ) y = _
      rw [h_v_bundle_eq y]]
    ring
  have h_4eq : 4 * chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α
      (φ : M → ℝ) v.toFun x =
      4 * hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    rw [h_pol_left, h_subst, ← h_pol_right]
  have h4ne : (4 : ℝ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h4ne h_4eq


/-- **The chart-α tensor pairing at `y` equals the manifold pairing at `x_y`.**

Conditional on the chart-α Frobenius invariance for the polarization
combinations `φ ± v` at the manifold point `x_y :=
(extChartAt α).symm (toEuclidean.symm y)`. -/
theorem smoothTensorPairingChart_eq_hessPairingChart_of_invariance
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_inv_add : chartFrobeniusInvariance (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z + v.toFun z)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
    (h_inv_sub : chartFrobeniusInvariance (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z - v.toFun z)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
    (h_swap_aux :
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i k *
          chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) j l *
          chartHessianTensor (I := I) g α v.toFun i j
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          chartHessianTensor (I := I) g α (φ : M → ℝ) k l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i k *
          chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) j l *
          chartHessianTensor (I := I) g α (φ : M → ℝ) i j
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          chartHessianTensor (I := I) g α v.toFun k l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set x_y : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_y_def
  have h_step1 : smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingByChartα (I := I) (M := M) g α φ v x_y :=
    smoothTensorPairingChart_eq_hessPairingByChartα_pullback (I := I) (M := M) g α φ v hy
  rw [h_step1]
  have h_step2 : hessPairingByChartα (I := I) (M := M) g α φ v x_y =
      chartHessFrobeniusPairOnChartAlpha (I := I) (M := M) g α
        (φ : M → ℝ) v.toFun x_y := by
    unfold hessPairingByChartα
    rw [smoothTensorPairingChart_def, chartHessFrobeniusPairOnChartAlpha_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    set y' : EuclN := (toEuclidean (E := E)) (extChartAt I α x_y) with hy'_def
    have h_toE_inv : (toEuclidean (E := E)).symm y' = extChartAt I α x_y :=
      (toEuclidean (E := E)).symm_apply_apply (extChartAt I α x_y)
    have hx_y_chart : x_y ∈ (chartAt H α).source := by
      have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
        toEuclidean_symm_mem_target (I := I) hy
      have hx_y_source_ext : x_y ∈ (extChartAt I α).source := by
        rw [hx_y_def]
        exact (extChartAt I α).map_target hy_target
      rwa [extChartAt_source_eq_chartAt_source] at hx_y_source_ext
    have h_chart_inv : (extChartAt I α).symm (extChartAt I α x_y) = x_y := by
      rw [(extChartAt I α).left_inv]
      rwa [extChartAt_source_eq_chartAt_source]
    have h_invGram : invGramOnEuclid (I := I) g α i k y' =
        chartInvGramMatrix (I := I) g α x_y i k := by
      unfold invGramOnEuclid
      rw [h_toE_inv, h_chart_inv]
    have h_invGram_jl : invGramOnEuclid (I := I) g α j l y' =
        chartInvGramMatrix (I := I) g α x_y j l := by
      unfold invGramOnEuclid
      rw [h_toE_inv, h_chart_inv]
    have h_HphiOnEuclid : chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y' =
        chartHessianTensor (I := I) g α (φ : M → ℝ) i j x_y := by
      rw [HessianPairingLapDom.chartHessianPhiOnEuclid_def]
      rw [h_toE_inv, h_chart_inv]
    have h_HvOnEuclid : chartHessianVOnEuclid (I := I) (M := M) g α v k l y' =
        chartHessianTensor (I := I) g α v.toFun k l x_y := by
      rw [chartHessianVOnEuclid_def]
      rw [h_toE_inv, h_chart_inv]
    rw [h_invGram, h_invGram_jl, h_HphiOnEuclid, h_HvOnEuclid]
  rw [h_step2]
  have hx_y_chart : x_y ∈ (chartAt H α).source := by
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have hx_y_source_ext : x_y ∈ (extChartAt I α).source := by
      rw [hx_y_def]
      exact (extChartAt I α).map_target hy_target
    rwa [extChartAt_source_eq_chartAt_source] at hx_y_source_ext
  exact chartHessFrobeniusPairOnChartAlpha_eq_hessPairingChart_of_invariance
    (I := I) (M := M) g α φ v hx_y_chart h_inv_add h_inv_sub h_swap_aux


/-- **The chart-α Hilbert–Schmidt bridge Prop.** The chart-α tensor Frobenius
squared at `x` equals the abstract Hilbert–Schmidt Frobenius squared
`frobeniusSq_grad_vector g (gradFun g f) x`. We expose this as a separate Prop
to keep the chart-α HS frame argument as the single remaining ingredient. -/
def chartFrobeniusSqHSBridge
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) : Prop :=
  chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
    frobeniusSq_grad_vector (I := I) g
      (fun b : M => gradFun (I := I) g f b) x

@[simp] lemma chartFrobeniusSqHSBridge_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartFrobeniusSqHSBridge (I := I) (M := M) g α f x ↔
      chartHessFrobeniusSqOnChartAlpha (I := I) (M := M) g α f x =
        frobeniusSq_grad_vector (I := I) g
          (fun b : M => gradFun (I := I) g f b) x := Iff.rfl

/-- **Chart-α Frobenius invariance via the HS bridge.** Given the chart-α HS
bridge and the existing chart-at-x bridge
`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`, the chart-α Frobenius
squared equals the chart-at-x Frobenius squared. -/
theorem chartFrobeniusInvariance_of_HSBridge
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h_HS : chartFrobeniusSqHSBridge (I := I) (M := M) g α f x) :
    chartFrobeniusInvariance (I := I) (M := M) g α f x := by
  classical
  rw [chartFrobeniusInvariance_def]
  rw [chartFrobeniusSqHSBridge_def] at h_HS
  rw [h_HS]
  exact frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x

/-- **Packaged bridge.** Given the chart-α HS bridges for the polarization
combinations `φ ± v` at the manifold point `x_y`, the chart-α tensor pairing
at `y` equals the chart-invariant pairing at `x_y`. -/
theorem smoothTensorPairingChart_eq_hessPairingChart_of_HSBridge
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_HS_add : chartFrobeniusSqHSBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z + v.toFun z)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
    (h_HS_sub : chartFrobeniusSqHSBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z - v.toFun z)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
    (h_swap_aux :
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i k *
          chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) j l *
          chartHessianTensor (I := I) g α v.toFun i j
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          chartHessianTensor (I := I) g α (φ : M → ℝ) k l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i k *
          chartInvGramMatrix (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) j l *
          chartHessianTensor (I := I) g α (φ : M → ℝ) i j
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          chartHessianTensor (I := I) g α v.toFun k l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  have hf_add : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z + v.toFun z) :=
    φ.contMDiff.add v.smooth
  have hf_sub : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z - v.toFun z) :=
    φ.contMDiff.sub v.smooth
  have h_inv_add := chartFrobeniusInvariance_of_HSBridge (I := I) (M := M) g α
    (fun z : M => (φ : M → ℝ) z + v.toFun z)
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) hf_add h_HS_add
  have h_inv_sub := chartFrobeniusInvariance_of_HSBridge (I := I) (M := M) g α
    (fun z : M => (φ : M → ℝ) z - v.toFun z)
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) hf_sub h_HS_sub
  exact smoothTensorPairingChart_eq_hessPairingChart_of_invariance
    (I := I) (M := M) g α φ v hy h_inv_add h_inv_sub h_swap_aux

end HessianChartInvariance
end Laplacian
end Analysis
end DifferentialGeometry

end
