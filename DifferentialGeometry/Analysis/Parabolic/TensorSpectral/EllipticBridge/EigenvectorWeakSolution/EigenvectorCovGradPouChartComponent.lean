import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradChartIdentity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradChristoffelLimit
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorWeakPartials
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossLimits

/-!
# The non-smooth covariant-gradient partition-of-unity chart-component identity

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and an eigenbasis
index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, let
`φ := tensorResolventEigenbasisVec … i` be the eigenvector and
`R := eigenvectorResolvent g r s i` its `H¹`-completion resolvent.
The abstract `L²` covariant gradient of `R` is `tensorCovGradL2Compl g r s R`, an
`(r, s + 1)`-tensor.

This file proves the **partition-of-unity covariant-gradient chart-component
almost-everywhere identity**: the canonical Euclidean chart component of
`tensorCovGradL2Compl g r s R`, rescaled by `μ⁻¹`, equals — almost everywhere on
the Euclidean chart target — a principal term (the established weak chart
partial of `φ`'s chart component) minus a partition-of-unity Leibniz cross-term
limit plus a Christoffel-correction limit.

## The rescaling convention

`R` lies in the `H¹` completion; its `L²` shadow is `μ • φ`
(`eigenvector_eq_resolvent_smul`). The completion-extended covariant gradient
`tensorCovGradL2Compl g r s` is `ℝ`-linear, so `tensorCovGradL2Compl g r s R`
represents the covariant gradient of `μ • φ`, i.e. `μ` times the covariant
gradient of `φ`. Each of the three named limit objects on the right —
`eigenvectorChartWeakPartial`, the cross-term limit
`covGradPouLeibnizCrossLimit` constructed here, and
`covGradChristoffelLimit` (companion file) — is a chart
object of the eigenvector `φ` itself, i.e. `μ`-clean. Consequently the headline
carries a `μ⁻¹`-rescaling on its left-hand side: with it, the `μ`-factors of the
intermediate smooth-approximant terms cancel exactly.

## Proof route

The approximating sequence `wₙ := eigenvectorSmoothApprox g r s i n`
has completion embeddings converging to `R`
(`eigenvectorSmoothApprox_tendsto`).
Both `tensorCovGradL2Compl g r s` and `tensorL2ChartComponentCLM g r (s + 1) β
Q'` are continuous linear maps; applying their composition to that convergence
exhibits the chart component of `tensorCovGradL2Compl g r s R` as the `L²`-limit
of the chart components of the section-level covariant gradients
`covGrad g r s wₙ.toCcTensor`.

For each `n`, the `n`-th term is rewritten almost everywhere on the chart
target, by the raw chart-component formula `tensorChartComponentRaw_covGrad`
together with the partition-of-unity Leibniz identity
`chartPushedRaw_pou_mul_euclidPartial_eq`, into the difference of a principal
chart-partial term and a Leibniz cross term, plus the Christoffel correction at
the partition-of-unity-weighted approximant. Taking the three `L²`-limits
termwise — via `eigenvectorChartPartialLp_tendsto`,
`covGradPouLeibnizCrossLimit_tendsto`, and
`covGradChristoffel_tendsto` — and appealing to uniqueness of
`L²`-limits yields the headline.

## Main definitions

* `covGradPouLeibnizCrossLimit g r s i β P₀ k` — the explicit
  `L²`-limit function of the partition-of-unity Leibniz cross term: the `C^∞`
  derivative of the chart-pushed partition-of-unity weight times the cutoff
  Euclidean chart component of the eigenvector.

## Main results

* `covGradPouLeibnizCrossLimit_memLp` — the cross-term limit
  function is `L²`.
* `covGradPouLeibnizCrossLimit_tendsto` — its `n → ∞`
  `L²`-convergence.
* `eigenvectorCovGrad_pou_chartComponent_ae_eq` — **the headline**:
  the `μ⁻¹`-rescaled canonical chart component of the section-level covariant
  gradient of the eigenvector resolvent equals, almost everywhere, the principal
  weak chart partial minus the cross-term limit plus the Christoffel-correction
  limit.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The chart-pushed partition-of-unity weight vanishes outside the
partition-of-unity kernel of the chart. -/
private lemma chartPushedRaw_chartAtlasPOU_eq_zero_off_chartPouKernel
    (β : M) {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) β) :
    chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) β
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ htar]
    refine image_eq_zero_of_notMem_tsupport (fun hb => hy ?_)
    have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I β).target :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) htar
    refine ⟨(toEuclidean (E := E)).symm y,
      ⟨(extChartAt I β).symm ((toEuclidean (E := E)).symm y), hb, ?_⟩, ?_⟩
    · exact (extChartAt I β).right_inv hmem
    · exact toEuclidean.apply_symm_apply y
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ htar

/-- The chart-Euclidean partial of the chart-pushed partition-of-unity weight
vanishes outside the partition-of-unity kernel of the chart. -/
private lemma euclidPartial_chartPushedRaw_chartAtlasPOU_eq_zero_off_chartPouKernel
    (β : M) (k : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) β) :
    euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y =
      0 := by
  classical
  have hsupp : Function.support
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartPouKernel (I := I) (M := M) β := by
    intro z hz
    by_contra hzk
    exact hz (chartPushedRaw_chartAtlasPOU_eq_zero_off_chartPouKernel
      (I := I) (M := M) β hzk)
  have htsupp : tsupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartPouKernel (I := I) (M := M) β :=
    closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) β).isClosed
  have hy_compl : y ∈ (tsupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt :
      chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hy_compl)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

/-- The Leibniz cross-term multiplier `euclidPartial k (chartPushedRaw I β
chartAtlasPOU)` is `C^∞` on the open chart target. -/
private lemma contDiffOn_euclidPartial_chartPushedRaw_chartAtlasPOU
    (β : M) (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_isOpen (I := I) (M := M) β
  have hbase : ContDiffOn ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) β) :=
    chartPushedRaw_chartAtlasPOU_contDiffOn (I := I) (M := M) β
  intro y hy
  have hcontDiffAt : ContDiffAt ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y :=
    (hbase y hy).contDiffAt (hopen.mem_nhds hy)
  have hfderiv : ContDiffAt ℝ ∞
      (fderiv ℝ (chartPushedRaw I β
        ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) y :=
    hcontDiffAt.fderiv_right (m := ∞) le_rfl
  have heval : ContDiffAt ℝ ∞
      (fun z : EuclN => fderiv ℝ (chartPushedRaw I β
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) z
        (EuclideanSpace.single k 1)) y := by
    have h := (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single k 1)).contDiff.comp_contDiffAt y hfderiv
    simpa only [Function.comp_def] using h
  refine (heval.contDiffWithinAt).congr ?_ ?_
  · intro z _; rw [euclidPartial_def]
  · rw [euclidPartial_def]

/-- The Leibniz cross-term multiplier is bounded on the partition-of-unity
kernel of the chart: a `C^∞`-on-the-chart-target function on a compact set. -/
private lemma exists_bound_euclidPartial_chartPushedRaw_chartAtlasPOU
    (β : M) (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ chartPouKernel (I := I) (M := M) β,
      ‖euclidPartial (E := E) k
        (chartPushedRaw I β
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y‖ ≤ C :=
  exists_bound_on_chartPouKernel (I := I) (M := M) β
    (contDiffOn_euclidPartial_chartPushedRaw_chartAtlasPOU (I := I) (M := M) β k)

/-- The indicator-restricted Leibniz cross-term multiplier: the multiplier cut
to the compact partition-of-unity kernel. It is globally bounded and agrees with
the un-restricted multiplier everywhere. -/
private def crossMultiplier
    (β : M) (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartPouKernel (I := I) (M := M) β)
    (euclidPartial (E := E) k
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

/-- The indicator-restricted cross-term multiplier agrees with the un-restricted
multiplier at every Euclidean point: outside the kernel both vanish. -/
private lemma crossMultiplier_eq
    (β : M) (k : Fin (Module.finrank ℝ E)) (y : EuclN) :
    crossMultiplier (I := I) (M := M) β k y =
      euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  classical
  unfold crossMultiplier
  by_cases hy : y ∈ chartPouKernel (I := I) (M := M) β
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    exact (euclidPartial_chartPushedRaw_chartAtlasPOU_eq_zero_off_chartPouKernel
      (I := I) (M := M) β k hy).symm

/-- The indicator-restricted cross-term multiplier is globally bounded. -/
private lemma exists_bound_crossMultiplier
    (β : M) (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      ‖crossMultiplier (I := I) (M := M) β k y‖ ≤ C := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_euclidPartial_chartPushedRaw_chartAtlasPOU (I := I) (M := M) β k
  refine ⟨C, hC0, fun y => ?_⟩
  unfold crossMultiplier
  by_cases hy : y ∈ chartPouKernel (I := I) (M := M) β
  · rw [Set.indicator_of_mem hy]; exact hC y hy
  · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC0

/-- The indicator-restricted cross-term multiplier is `AEStronglyMeasurable`
with respect to the chart `L²` measure. -/
private lemma aestronglyMeasurable_crossMultiplier
    (β : M) (k : Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable (crossMultiplier (I := I) (M := M) β k)
      (chartL2Measure (I := I) (M := M) β) :=
  aestronglyMeasurable_indicator_mul (I := I) (M := M) β
    (contDiffOn_euclidPartial_chartPushedRaw_chartAtlasPOU (I := I) (M := M) β k)

/-- On the chart target, the cross-term multiplier times the chart-pushed raw
chart component of a smooth section equals the cross-term multiplier times the
cutoff Euclidean chart component of that section. The multiplier vanishes off
the partition-of-unity kernel; on it, the chart-kernel cutoff equals `1`, so the
two chart components coincide. -/
private lemma crossMultiplier_mul_chartPushedRaw_eq_cutoffComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      chartPushedRaw I β
        (tensorChartComponentRaw (I := I) (M := M) g r s S β Idx Jdx) y =
    euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      cutoffComponentEuclid (I := I) (M := M) g r s S β Idx Jdx y := by
  classical
  set b : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y) with hb_def
  by_cases hker : y ∈ chartPouKernel (I := I) (M := M) β
  · have hb_supp : b ∈ tsupport
        (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
      obtain ⟨e, ⟨z, hz_supp, hz_eq⟩, he_eq⟩ := hker
      have hz_src : z ∈ (extChartAt I β).source := by
        rw [extChartAt_source]
        exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
          I M) β hz_supp
      have hb_z : b = z := by
        rw [hb_def, ← he_eq, toEuclidean.symm_apply_apply, ← hz_eq,
          (extChartAt I β).left_inv hz_src]
      rw [hb_z]; exact hz_supp
    have hcut_one :
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) β hb_supp
    have hcomp_eq :
        chartPushedRaw I β
            (tensorChartComponentRaw (I := I) (M := M) g r s S β Idx Jdx) y =
          cutoffComponentEuclid (I := I) (M := M) g r s S β Idx Jdx y := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy,
        cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S β Idx Jdx hy]
      unfold cutoffComponentScalar
      rw [← hb_def, hcut_one, one_mul]
    rw [hcomp_eq]
  · rw [euclidPartial_chartPushedRaw_chartAtlasPOU_eq_zero_off_chartPouKernel
      (I := I) (M := M) β k hker, zero_mul, zero_mul]

/-- On the chart target, the chart-pushed partition-of-unity weight times the
zeroth-order Christoffel correction of a smooth section equals the Christoffel
correction of the partition-of-unity-weighted section. -/
private lemma chartPushedRaw_pou_mul_covDerivLowerOrderTerm_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (β : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
        covDerivLowerOrderTerm (I := I) (M := M) g r s S β m Idx Jdx y =
      covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s β S) β m Idx Jdx y := by
  classical
  rw [covDerivLowerOrderTerm_def, covDerivLowerOrderTerm_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_smul_pou (I := I) (M := M) g r s β S p.1 p.2]
  ring

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGradPouLeibnizCrossLimit`. -/
noncomputable def covGradPouLeibnizCrossLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) β P₀ :
        EuclN → ℝ) y

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGradPouLeibnizCrossLimit_memLp`. -/
theorem covGradPouLeibnizCrossLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P₀ k) 2
      (chartL2Measure (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_bound_crossMultiplier (I := I) (M := M) β k
  refine (memLp_bdd_mul (I := I) (M := M) β hC0 hC
    (aestronglyMeasurable_crossMultiplier (I := I) (M := M) β k)
    (Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) β P₀))).ae_eq ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  change crossMultiplier (I := I) (M := M) β k y *
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) β P₀ :
        EuclN → ℝ) y =
    covGradPouLeibnizCrossLimit (I := I) (M := M) g r s i β P₀ k y
  unfold covGradPouLeibnizCrossLimit
  rw [crossMultiplier_eq (I := I) (M := M) β k y]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `cutoffComponent_smoothApprox_tendsto`. -/
private lemma cutoffComponent_smoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) β P₀)
      atTop
      (𝓝 (i.fst.val •
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β P₀)) := by
  classical
  have h_l2 :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s β P₀).continuous.tendsto
      _).comp h_l2
  have h_term : ∀ n : ℕ,
      tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s β P₀
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))) =
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g) β P₀ := by
    intro n
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M) g r s i n),
      tensorL2ChartComponentCutoffCLM_apply]
  have h_lim :
      tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s β P₀
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) =
        i.fst.val •
          tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P₀ := by
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    have h_shadow :
        TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i) =
          i.fst.val •
            tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i := by
      have h_eq :=
        eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i
      rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
    rw [h_shadow, map_smul, tensorL2ChartComponentCutoffCLM_apply]
  simp only [Function.comp_def] at h_clm
  rw [h_lim] at h_clm
  exact h_clm.congr (fun n => h_term n)

/-- Chart-locality-free twin of `crossTermApprox`. -/
private def crossTermApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) : EuclN → ℝ :=
  fun y =>
    euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      chartPushedRaw I β
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor β P₀.1 P₀.2) y

/-- Chart-locality-free twin of `crossTermCutoff`. -/
private def crossTermCutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) : EuclN → ℝ :=
  fun y =>
    crossMultiplier (I := I) (M := M) β k y *
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) β P₀ :
        EuclN → ℝ) y

/-- Chart-locality-free twin of `crossTermCutoff_memLp`. -/
private lemma crossTermCutoff_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp (crossTermCutoff (I := I) (M := M) g r s i β P₀ k n) 2
      (chartL2Measure (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_bound_crossMultiplier (I := I) (M := M) β k
  exact memLp_bdd_mul (I := I) (M := M) β hC0 hC
    (aestronglyMeasurable_crossMultiplier (I := I) (M := M) β k)
    (Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) β P₀))

/-- Chart-locality-free twin of `crossTermApprox_ae_eq_crossTermCutoff`. -/
private lemma crossTermApprox_ae_eq_crossTermCutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    crossTermApprox (I := I) (M := M) g r s i β P₀ k n
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      crossTermCutoff (I := I) (M := M) g r s i β P₀ k n := by
  classical
  have h_coeFn :=
    tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor β P₀
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) β)
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  unfold crossTermApprox crossTermCutoff
  rw [crossMultiplier_mul_chartPushedRaw_eq_cutoffComponent
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    β P₀.1 P₀.2 k hy, crossMultiplier_eq (I := I) (M := M) β k y, hy_coe]

/-- Chart-locality-free twin of `crossTermApprox_memLp`. -/
private lemma crossTermApprox_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp (crossTermApprox (I := I) (M := M) g r s i β P₀ k n) 2
      (chartL2Measure (I := I) (M := M) β) :=
  (crossTermCutoff_memLp (I := I) (M := M) g r s i β P₀ k n).ae_eq
    (crossTermApprox_ae_eq_crossTermCutoff (I := I) (M := M)
      g r s i β P₀ k n).symm

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGradPouLeibnizCrossLimit_tendsto`. -/
theorem covGradPouLeibnizCrossLimit_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        ((crossTermApprox_memLp (I := I) (M := M)
          g r s i β P₀ k n).toLp
          (crossTermApprox (I := I) (M := M)
            g r s i β P₀ k n) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)))
      atTop
      (𝓝 ((covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
        g r s i β P₀ k).toLp
        (covGradPouLeibnizCrossLimit (I := I) (M := M)
          g r s i β P₀ k))) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_bound_crossMultiplier (I := I) (M := M) β k
  have h_smul :=
    (tendsto_bdd_mul (I := I) (M := M) β hC0 hC
      (aestronglyMeasurable_crossMultiplier (I := I) (M := M) β k)
      (cutoffComponent_smoothApprox_tendsto (I := I) (M := M)
        g r s i β P₀)).const_smul (i.fst.val)⁻¹
  have h_lim :
      (i.fst.val)⁻¹ •
          (memLp_bdd_mul (I := I) (M := M) β hC0 hC
            (aestronglyMeasurable_crossMultiplier (I := I) (M := M) β k)
            (Lp.memLp (i.fst.val •
              tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β P₀))).toLp
            (fun y => crossMultiplier (I := I) (M := M) β k y *
              ((i.fst.val •
                tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i) β P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y) =
        (covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
          g r s i β P₀ k).toLp
          (covGradPouLeibnizCrossLimit (I := I) (M := M)
            g r s i β P₀ k) := by
    apply Lp.ext
    refine (Lp.coeFn_smul (i.fst.val)⁻¹ _).trans ?_
    refine Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp (covGradPouLeibnizCrossLimit_memLp
        (I := I) (M := M) g r s i β P₀ k)).symm
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) β hC0 hC
      (aestronglyMeasurable_crossMultiplier (I := I) (M := M) β k)
      (Lp.memLp (i.fst.val •
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β P₀))),
      Lp.coeFn_smul (i.fst.val)
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β P₀)] with y hy_toLp hy_smul
    rw [Pi.smul_apply, hy_toLp, crossMultiplier_eq (I := I) (M := M) β k y,
      hy_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    unfold covGradPouLeibnizCrossLimit
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    field_simp
  rw [h_lim] at h_smul
  refine h_smul.congr' (Filter.Eventually.of_forall (fun n => ?_))
  congr 1
  exact (MemLp.toLp_congr _ _
    (crossTermApprox_ae_eq_crossTermCutoff (I := I) (M := M)
      g r s i β P₀ k n)).symm

/-- Chart-locality-free twin of `covGrad_chartComponent_ae_decompose`. -/
private lemma covGrad_chartComponent_ae_decompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) (n : ℕ) :
    tensorChartComponent (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) β Q'.1 Q'.2
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      fun y =>
        euclidPartial (E := E) (Q'.2 0)
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor β Q'.1
              (Matrix.vecTail Q'.2)) y
          - crossTermApprox (I := I) (M := M) g r s i β
              (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n y
          + covDerivLowerOrderTerm (I := I) (M := M) g r s
              (pouSmul (I := I) (M := M) g r s β
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) β (Q'.2 0) Q'.1
              (Matrix.vecTail Q'.2) y := by
  classical
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) β)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  set S : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    with hS_def
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S) β
    Q'.1 Q'.2 hy]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S) β Q'.1 Q'.2) hy,
    tensorChartComponentRaw_covGrad (I := I) (M := M) g r s S β
      Q'.1 Q'.2 hy, mul_add]
  rw [chartPushedRaw_pou_mul_euclidPartial_eq (I := I) (M := M) g r s S β
    Q'.1 (Matrix.vecTail Q'.2) (Q'.2 0) hy]
  rw [chartPushedRaw_pou_mul_covDerivLowerOrderTerm_eq (I := I) (M := M)
    g r s S β (Q'.2 0) Q'.1 (Matrix.vecTail Q'.2) hy]
  simp only [crossTermApprox]
  ring

/-- Chart-locality-free twin of `principalTerm_tendsto`. -/
private lemma principalTerm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1))
    (hf : ∀ n : ℕ, MemLp
      (euclidPartial (E := E) (Q'.2 0)
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor β Q'.1
          (Matrix.vecTail Q'.2))) 2
      (chartL2Measure (I := I) (M := M) β)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ • (hf n).toLp _)
      atTop
      (𝓝 (eigenvectorChartPartialLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0))) := by
  classical
  refine (eigenvectorChartPartialLp_tendsto (I := I) (M := M)
    g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).congr'
    (Filter.Eventually.of_forall (fun n => ?_))
  rw [eigenvectorChartPartialLp_approx_eq (I := I) (M := M)
    g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n]
  congr 1
  exact MemLp.toLp_congr _ _
    (chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor β Q'.1 (Matrix.vecTail Q'.2)
      (Q'.2 0))

/-- Chart-locality-free twin of `christoffelTerm_tendsto`. -/
private lemma christoffelTerm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1))
    (hf : ∀ n : ℕ, MemLp
      (covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s β
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) β (Q'.2 0) Q'.1
        (Matrix.vecTail Q'.2)) 2
      (chartL2Measure (I := I) (M := M) β)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ • (hf n).toLp _)
      atTop
      (𝓝 ((covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp
        (covGradChristoffelLimit (I := I) (M := M)
          g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)))) := by
  classical
  refine (covGradChristoffel_tendsto (I := I) (M := M)
    g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).congr'
    (Filter.Eventually.of_forall (fun n => ?_))
  congr 1

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGrad_chartComponent_tendsto`. -/
private lemma covGrad_chartComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          ((covGrad (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) β Q')
      atTop
      (𝓝 ((i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M)
              g r s i)) β Q')) := by
  classical
  have h1 :=
    ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h2 :=
    ((tensorL2ChartComponentCLM (I := I) (M := M) g r (s + 1) β Q').continuous.tendsto
      _).comp h1
  have h_smul := h2.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  refine h_smul.congr (fun n => ?_)
  rw [tensorL2ChartComponentCLM_apply,
    tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Chart-locality-free twin of `eigenvectorCovGrad_pou_chartComponent_ae_eq`.**
The `μ⁻¹`-rescaled canonical Euclidean chart component of the section-level
covariant gradient `tensorCovGradL2Compl g r s` of the chart-locality-free
eigenvector resolvent `eigenvectorResolvent g r s i` equals, almost
everywhere on the Euclidean chart target, the established weak `(Q'.2 0)`-th chart
partial of the eigenvector chart component, minus the partition-of-unity Leibniz
cross-term limit `covGradPouLeibnizCrossLimit`, plus the
Christoffel-correction limit `covGradChristoffelLimit`. -/
theorem eigenvectorCovGrad_pou_chartComponent_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    (((i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M)
              g r s i)) β Q' :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M) g r s i β
            (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M) g r s i β
              (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M) g r s i β
              (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) y) := by
  classical
  have hf1 : ∀ n : ℕ, MemLp
      (euclidPartial (E := E) (Q'.2 0)
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor β Q'.1
          (Matrix.vecTail Q'.2))) 2
      (chartL2Measure (I := I) (M := M) β) := fun n =>
    (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      β Q'.1 (Matrix.vecTail Q'.2) (Q'.2 0)).ae_eq
      (chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor β Q'.1 (Matrix.vecTail Q'.2)
        (Q'.2 0))
  have hf2 : ∀ n : ℕ, MemLp
      (crossTermApprox (I := I) (M := M) g r s i β
        (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n) 2
      (chartL2Measure (I := I) (M := M) β) := fun n =>
    crossTermApprox_memLp (I := I) (M := M) g r s i β
      (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n
  have hf3 : ∀ n : ℕ, MemLp
      (covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s β
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) β (Q'.2 0) Q'.1
        (Matrix.vecTail Q'.2)) 2
      (chartL2Measure (I := I) (M := M) β) := fun n =>
    covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M) g r s i β
      (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n
  have hfA : ∀ n : ℕ, MemLp
      (tensorChartComponent (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) β Q'.1 Q'.2) 2
      (chartL2Measure (I := I) (M := M) β) := fun n =>
    tensorChartComponent_memLp (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) β Q'.1 Q'.2
  have h_tendsto_A :=
    covGrad_chartComponent_tendsto (I := I) (M := M) g r s i β Q'
  have h_term : ∀ n : ℕ,
      (i.fst.val)⁻¹ •
          tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            ((covGrad (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor :
              SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) β Q' =
        ((i.fst.val)⁻¹ • (hf1 n).toLp _ -
            (i.fst.val)⁻¹ • (hf2 n).toLp _) +
          (i.fst.val)⁻¹ • (hf3 n).toLp _ := by
    intro n
    apply Lp.ext
    have h_decomp := covGrad_chartComponent_ae_decompose (I := I) (M := M)
      g r s i β Q' n
    have h_lhs :
        (((i.fst.val)⁻¹ •
            tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
              ((covGrad (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor :
                SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) β Q' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) β]
          fun y => (i.fst.val)⁻¹ •
            tensorChartComponent (I := I) (M := M) g r (s + 1)
              (covGrad (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) β Q'.1 Q'.2 y := by
      filter_upwards [Lp.coeFn_smul (i.fst.val)⁻¹
          (tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            ((covGrad (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor :
              SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) β Q'),
        tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M)
          g r (s + 1) (covGrad (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) β Q'] with y hy_smul hy_comp
      rw [hy_smul, Pi.smul_apply, hy_comp]
    have h_rhs :
        ((((i.fst.val)⁻¹ • (hf1 n).toLp _ -
              (i.fst.val)⁻¹ • (hf2 n).toLp _) +
            (i.fst.val)⁻¹ • (hf3 n).toLp _ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) β]
          fun y => (i.fst.val)⁻¹ •
            ((euclidPartial (E := E) (Q'.2 0)
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor β Q'.1
                    (Matrix.vecTail Q'.2)) y -
                crossTermApprox (I := I) (M := M) g r s i β
                  (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) n y) +
              covDerivLowerOrderTerm (I := I) (M := M) g r s
                (pouSmul (I := I) (M := M) g r s β
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) β (Q'.2 0) Q'.1
                (Matrix.vecTail Q'.2) y) := by
      filter_upwards [Lp.coeFn_add ((i.fst.val)⁻¹ • (hf1 n).toLp _ -
          (i.fst.val)⁻¹ • (hf2 n).toLp _) ((i.fst.val)⁻¹ • (hf3 n).toLp _),
        Lp.coeFn_sub ((i.fst.val)⁻¹ • (hf1 n).toLp _)
          ((i.fst.val)⁻¹ • (hf2 n).toLp _),
        Lp.coeFn_smul (i.fst.val)⁻¹ ((hf1 n).toLp _),
        Lp.coeFn_smul (i.fst.val)⁻¹ ((hf2 n).toLp _),
        Lp.coeFn_smul (i.fst.val)⁻¹ ((hf3 n).toLp _),
        MemLp.coeFn_toLp (hf1 n), MemLp.coeFn_toLp (hf2 n),
        MemLp.coeFn_toLp (hf3 n)]
        with y ha hs hm1 hm2 hm3 ht1 ht2 ht3
      rw [ha, Pi.add_apply, hs, Pi.sub_apply, hm1, hm2, hm3, Pi.smul_apply,
        Pi.smul_apply, Pi.smul_apply, ht1, ht2, ht3]
      simp only [smul_eq_mul]
      ring
    refine h_lhs.trans (Filter.EventuallyEq.trans ?_ h_rhs.symm)
    filter_upwards [h_decomp] with y hy_decomp
    rw [hy_decomp]
  rw [show (fun n => (i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          ((covGrad (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) β Q') =
      (fun n => ((i.fst.val)⁻¹ • (hf1 n).toLp _ -
          (i.fst.val)⁻¹ • (hf2 n).toLp _) +
        (i.fst.val)⁻¹ • (hf3 n).toLp _) from funext h_term] at h_tendsto_A
  have h_lim1 := principalTerm_tendsto (I := I) (M := M)
    g r s i β Q' hf1
  have h_lim2 := covGradPouLeibnizCrossLimit_tendsto (I := I) (M := M)
    g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)
  have h_lim3 := christoffelTerm_tendsto (I := I) (M := M)
    g r s i β Q' hf3
  have h_lim2' : Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ • (hf2 n).toLp _) atTop
      (𝓝 ((covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp
        (covGradPouLeibnizCrossLimit (I := I) (M := M)
          g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)))) := by
    refine h_lim2.congr (fun n => ?_)
    congr 1
  have h_lim_sum :
      Filter.Tendsto
        (fun n => ((i.fst.val)⁻¹ • (hf1 n).toLp _ -
            (i.fst.val)⁻¹ • (hf2 n).toLp _) +
          (i.fst.val)⁻¹ • (hf3 n).toLp _) atTop
        (𝓝 ((eigenvectorChartPartialLp (I := I) (M := M)
              g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) -
            (covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
              g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp
              (covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β (Q'.1, Matrix.vecTail Q'.2)
                (Q'.2 0))) +
          (covGradChristoffelLimit_memLp (I := I) (M := M)
            g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)))) :=
    (h_lim1.sub h_lim2').add h_lim3
  have h_eq := tendsto_nhds_unique h_tendsto_A h_lim_sum
  apply Lp.ext_iff.mp at h_eq
  refine h_eq.trans ?_
  have h_w := MemLp.coeFn_toLp (covGradPouLeibnizCrossLimit_memLp
    (I := I) (M := M) g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0))
  have h_c := MemLp.coeFn_toLp (covGradChristoffelLimit_memLp
    (I := I) (M := M) g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0))
  filter_upwards [Lp.coeFn_add
      (eigenvectorChartPartialLp (I := I) (M := M) g r s i β
        (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0) -
      (covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp _)
      ((covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp _),
    Lp.coeFn_sub
      (eigenvectorChartPartialLp (I := I) (M := M) g r s i β
        (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0))
      ((covGradPouLeibnizCrossLimit_memLp (I := I) (M := M)
        g r s i β (Q'.1, Matrix.vecTail Q'.2) (Q'.2 0)).toLp _),
    h_w, h_c] with y hy_add hy_sub hy_w hy_c
  rw [hy_add, Pi.add_apply, hy_sub, Pi.sub_apply, hy_w, hy_c]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
