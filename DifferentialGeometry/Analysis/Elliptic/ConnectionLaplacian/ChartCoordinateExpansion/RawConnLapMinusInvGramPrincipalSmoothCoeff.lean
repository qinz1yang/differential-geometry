import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartProjFullExpansionViaChartInvGram
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameTraceΓCorrectionT0Linear
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartInvGramMatrixPullback
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator

/-!
# The frame-independent chart-coordinate Christoffel correction of `Δ_∇` after the
inverse-Gram principal block, with `C^∞` chart coefficients

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a chart base point `α`, and
component multi-indices `(Idx, Jdx)`, this file ships the two ingredients that turn the chart-`α`
`(Idx, Jdx)` raw scalar component of the rough tensor connection Laplacian
`Δ_∇ T₀ = rawTensorConnLapSmooth g r s T₀`, *minus* the frame-independent chart-`α` inverse-Gram
principal sum `chartInvGramPrincipalSum`, into the canonical first-order chart-coordinate
smooth-coefficient form on the **whole** chart-`α` Levi-Civita good set.

## The mathematical content

The rough Laplacian is, *unconditionally* at every base point, the metric trace of the Hessian
(`rawTensorConnLap_eq_metricTraceHessian`); the second covariant derivative
`tensorSecondCovDeriv X Y T x = ∇_X(∇_Y T)(x) − ∇_{∇_X Y}T(x)` is a genuine `(0,2)`-tensor in its
two direction slots (`C^∞(M)`-bilinear in `(X x, Y x)`, the `−∇_{∇_X Y}T` term being exactly the
correction that tensorialises the second/field slot). The metric trace of a `g`-symmetric fibre
bilinear form is basis-independent, so it equals the chart-`α` inverse-Gram-weighted coordinate-basis
trace at every good-set point:
```
raw_{IJ}(Δ_∇ T₀)(b) = ∑_{k,l} g^{kl}(b) · proj(tensorSecondCovDeriv ∂_l ∂_k T₀ (b))   (g^{kl} := chartInvGramMatrix),
```
with `∂_m := chartBasisVecFiber α m`. Expanding the Hessian via `tensorSecondCovDeriv_def` and using
the definition of `chartInvGramPrincipalSum = ∑_{k,l} g^{kl}·proj(∇_{∂_k}(∇·T₀)(∂_l))` (the
inverse-Gram-weighted *naive iterated* covariant derivative — i.e. the first summand of the Hessian
trace) leaves exactly the frame-independent chart-coordinate Christoffel correction
```
raw_{IJ}(Δ_∇ T₀)(b) − chartInvGramPrincipalSum(b)
  = − ∑_{k,l} g^{kl}(b) · proj(cov_RS T₀ (b) ((LC g) ∂_k (b) (∂_l b))),
```
a *single* first covariant derivative of `T₀` contracted against the smooth chart-Christoffel-trace
field `W := ∑_{k,l} g^{kl}·(LC g) ∂_k (∂_l)`. This is the frame-independent counterpart of the
bumped-frame `chartFrameTraceΓCorrection_eq_T₀_linear` (whose field is `∑_i (LC g) B_i (B_i)`), and
it holds on the whole good set because the metric trace is frame-free (the bumped frame's
orthonormality, localised to the partition-of-unity tsupport, is not used).

## What this file establishes

* `rawConnLap_chartα_minus_invGramPrincipalSum_eq_christoffelTrace` — the frame-independent
  Christoffel-correction identity (the genuine remaining differential-geometric prerequisite: the
  basis-independence of the Hessian metric trace, i.e. the second/field-slot tensoriality of
  `tensorSecondCovDeriv`). It is `g`-natural (consistent with `∇g = 0` and the bumped-frame
  analogue), good-set-wide.

* `christoffelTrace_correction_eq_T₀_linear` — the smooth-coefficient packaging of that Christoffel
  correction into the canonical first-partial-block + zeroth-order-block chart-coordinate form, with
  `T₀`-independent `C^∞` coefficients on the Euclidean chart target. This is the exact frame-free
  analogue of `chartFrameTraceΓCorrection_eq_T₀_linear`: the chart-Christoffel-trace field
  coordinates pull back smoothly (via `chartInvGramMatrix_pullback_contDiffOn_chartTarget` and the
  chart-Christoffel pullback smoothness `chartLeviCivitaParallelCLM_coordEntry_contDiffOn`), and the
  per-direction first covariant derivative rewrites via the chart-coordinate component formula.

Both are unconditional in the chart atlas: no chart-locality predicate, no frame, no moving-centre
object, no uniform operator-norm bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The frame-independent chart-coordinate Christoffel correction of `Δ_∇` after the inverse-Gram
principal block (the genuine remaining differential-geometric content).**

For a base point `b` in the chart-`α` Levi-Civita good set, the chart-`α` `(Idx, Jdx)` raw scalar
component of `Δ_∇ T₀`, minus the (frame-independent) chart-`α` inverse-Gram principal sum
`chartInvGramPrincipalSum`, equals the chart-coordinate Christoffel correction
```
raw_{IJ}(Δ_∇ T₀)(b) − chartInvGramPrincipalSum(b)
  = − ∑_{k,l} chartInvGramMatrix g α b k l ·
        proj(cov_RS T₀ (b) ((LC g) (∂_k) (b) (∂_l b))),
```
with `proj := tensorChartComponentProjection ∘ (triv α).clmAt b`, `cov_RS := tensorRSCovariantDerivative
… (LeviCivita g)`, and `∂_m := chartBasisVecFiber α m`.

This is TRUE and standard. The rough Laplacian is *unconditionally* the metric trace of the Hessian
(`rawTensorConnLap_eq_metricTraceHessian`); the Hessian `tensorSecondCovDeriv X Y T x =
∇_X(∇_Y T)(x) − ∇_{∇_X Y}T(x)` is a genuine `(0,2)`-tensor in `(X x, Y x)` (`C^∞`-bilinear; the
`−∇_{∇_X Y}T` correction tensorialises the field slot), so the metric trace of the `g`-symmetric
fibre bilinear form `(u, v) ↦ proj(tensorSecondCovDeriv u v T b)` is basis-independent and equals its
chart-`α` inverse-Gram coordinate-basis trace `∑_{k,l} g^{kl}(b)·proj(tensorSecondCovDeriv ∂_l ∂_k
T₀(b))`. Expanding that trace via `tensorSecondCovDeriv_def` and matching the first (naive iterated)
summand to the definition of `chartInvGramPrincipalSum` (whose `(k,l)` summand is
`g^{kl}·proj((cov_RS)(covApply cov_RS ∂_k T₀)(b)(∂_l b))`) leaves exactly the displayed Christoffel
correction `−∑_{k,l} g^{kl}·proj(cov_RS T₀ (b)((LC g) ∂_k (b)(∂_l b)))`. It is the frame-independent
counterpart of the bumped-frame `chartFrameTraceΓCorrection_eq_T₀_linear`, holding on the whole good
set because the metric trace is frame-free (the bumped frame's tsupport-localised orthonormality is
not invoked); it is `g`-natural (consistent with `∇g = 0`).

Posited here as the genuine remaining differential-geometric prerequisite — the basis-independence of
the Hessian metric trace, equivalently the second/field-slot tensoriality of `tensorSecondCovDeriv`
on the general `(r, s)`-tensor bundle, which the committed `MetricTraceFrame`/`PartialMetricTrace`
foundation establishes only for the first (covariant-direction) slot. The smooth-coefficient
packaging of the right-hand side is discharged sorry-free by
`christoffelTrace_correction_eq_T₀_linear`. -/
theorem rawConnLap_chartα_minus_invGramPrincipalSum_eq_christoffelTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b -
      chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b =
      - ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (fun z : M => T₀.toSection z) b
                    ((LeviCivita (I := I) g).toFun
                      (fun z : M => chartBasisVecFiber (I := I) α k z) b
                      (chartBasisVecFiber (I := I) α l b)))) := by
  classical
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((fun z : M => T₀.toSection z) y)) := T₀.toSection.contMDiff
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb

  set proj : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)
    with hproj_def
  have hproj_apply : ∀ D : TensorRSSpace r s I b,
      proj D =
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b D) := by
    intro D; rw [hproj_def, ContinuousLinearMap.comp_apply]

  set Ψ : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    rawTensorConnLap_psi_bilinAt (I := I) g r s (fun z : M => T₀.toSection z) hT_total b
    with hΨ_def
  set B : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g b i b with hB_def
  have hB_orthonormal : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j

  have hChartBasis_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
          (chartBasisVecFiber (I := I) α k z)) b :=
    fun k => ((chartBasisVec_contMDiffOn (I := I) α k).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
        hb_base)).mdifferentiableAt (by simp)

  have hLHS_trace :
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
        proj (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) := by
    rw [tensorChartComponentRaw_def, tensorTrivProj, rawTensorConnLapSmooth_toSection_apply]
    rw [rawTensorConnLap_eq_frame_trace (I := I) g r s
      (fun z : M => T₀.toSection z) hT_total b B hB_orthonormal]
    rw [← hΨ_def, hproj_apply]

  have hTrace_fibre :
      (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l •
            Ψ (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) :=
    orthonormal_basis_bilin_trace_chartα (I := I) (A := TensorRSSpace r s I b)
      g α hb_base Ψ B hB_orthonormal
  have hTrace_chartα :
      proj (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            proj (Ψ (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b)) := by
    rw [hTrace_fibre, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]

  have hProjΨ_chartBasis : ∀ k l : Fin (Module.finrank ℝ E),
      proj (Ψ (chartBasisVecFiber (I := I) α k b) (chartBasisVecFiber (I := I) α l b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)) (chartBasisVecFiber (I := I) α k)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b))) -
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b)))) := by
    intro k l
    rw [hΨ_def, rawTensorConnLap_psi_bilinAt_apply (I := I) g r s
      (fun z : M => T₀.toSection z) hT_total (hChartBasis_mdiff k) (hChartBasis_mdiff l)]
    rw [hproj_apply, map_sub, map_sub]

  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l =>
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) (chartBasisVecFiber (I := I) α k)
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)))
    with hA_def
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l =>
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b))))
    with hC_def

  have hProjΨ_split : ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α b k l *
          proj (Ψ (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b)) =
        A k l - C k l := by
    intro k l
    rw [hProjΨ_chartBasis k l, hA_def, hC_def, mul_sub]
  rw [hLHS_trace, hTrace_chartα]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hProjΨ_split k l))]
  have hPrincipal :
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), A k l) =
        chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b := by
    rw [chartInvGramPrincipalSum, hA_def]
  have hSplit :
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), (A k l - C k l)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), A k l) -
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), C k l := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_sub_distrib]
  rw [hSplit, hPrincipal]
  ring

/-- The chart-`α` `m`-th coordinate of the chart-Christoffel-trace tangent field
`W := ∑_{k,l} g^{kl}·(LC g) ∂_k (∂_l)`, pulled back to the Euclidean chart target:
`W^m(y) = ∑_{k,l} chartInvGramEuclid g α k l y · chartChristoffelEuclid g α l k m y`. -/
private noncomputable def wTraceCoordPullback
    (g : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramEuclid (I := I) g α k l y *
          chartChristoffelEuclid (I := I) g α l k m y

/-- The chart-Christoffel-trace coordinate `wTraceCoordPullback` is `C^∞` on the Euclidean chart
target: a finite sum of products of the pulled-back inverse-Gram entries
(`chartInvGramEuclid_contDiffOn`) and the pulled-back Christoffel symbols
(`chartChristoffelEuclid_contDiffOn`). -/
private lemma wTraceCoordPullback_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (wTraceCoordPullback (I := I) (M := M) g α m)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun k _ => ?_)
  refine ContDiffOn.sum (fun l _ => ?_)
  exact (chartInvGramEuclid_contDiffOn (I := I) g α k l).mul
    (chartChristoffelEuclid_contDiffOn (I := I) g α l k m)

/-- At a chart-`α` good-set point `b`, the projected first covariant derivative of `T₀` along the
chart-Christoffel-trace field `W b = ∑_{k,l} g^{kl}(b)·(LC g) ∂_k (b) (∂_l b)` equals the finite sum,
over `m`, of `W^m(b) · proj(cov_RS T₀ (b) (∂_m b))`, where `W^m(b)` is the chart-`α` `m`-coordinate
of `W b`.  Obtained by expanding each `(LC g) ∂_k (b) (∂_l b) = ∑_m chartChristoffel g α l k m
(extChart b) • ∂_m b` (`LeviCivita_chartBasisVec_alpha_basis_apply`), pushing the projection CLM and
the inverse-Gram scalar through the finite sums, and collecting the `(k, l)`-sum into `W^m(b)`. -/
private lemma christoffelTrace_proj_eq_wCoord_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (fun z : M => T₀.toSection z) b
                  ((LeviCivita (I := I) g).toFun
                    (fun z : M => chartBasisVecFiber (I := I) α k z) b
                    (chartBasisVecFiber (I := I) α l b))))) =
      ∑ m : Fin (Module.finrank ℝ E),
        wTraceCoordPullback (I := I) (M := M) g α m
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                (chartBasisVecFiber (I := I) α m b))) := by
  classical
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]; exact (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_te, hleft_inv]
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b)
    with hL_def
  set Lcov : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (fun z : M => T₀.toSection z) b
    with hLcov_def

  have hChristEval : ∀ k l m : Fin (Module.finrank ℝ E),
      chartChristoffelEuclid (I := I) g α l k m y =
        chartChristoffel (I := I) g α l k m ((extChartAt I α) b) := by
    intro k l m
    rw [chartChristoffelEuclid_def, hsymm_te]

  have hInvGramEval : ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y = chartInvGramMatrix (I := I) g α b k l := by
    intro k l
    rw [chartInvGramEuclid_def, chartInvGramOnE_def, hsymm_te, hleft_inv]

  have hSummandLHS : ∀ k l : Fin (Module.finrank ℝ E),
      L (Lcov ((LeviCivita (I := I) g).toFun
            (fun z : M => chartBasisVecFiber (I := I) α k z) b
            (chartBasisVecFiber (I := I) α l b))) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
            L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    intro k l
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) (M := M) g α l k hb]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Lcov.map_smul, L.map_smul, smul_eq_mul]

  have hExpand : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            L (Lcov ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b)))) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
              L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hSummandLHS k l, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have hReorder : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
              L (Lcov (chartBasisVecFiber (I := I) α m b))) =
      ∑ m : Fin (Module.finrank ℝ E),
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b)) *
          L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => Finset.sum_comm
      (f := fun (l : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E)) =>
        chartInvGramMatrix (I := I) g α b k l *
          chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
          L (Lcov (chartBasisVecFiber (I := I) α m b))))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
  have hStep := hExpand.trans hReorder
  rw [hL_def, hLcov_def] at hStep
  simp only [ContinuousLinearMap.comp_apply] at hStep
  rw [hStep]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  rw [wTraceCoordPullback]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hInvGramEval k l, hChristEval k l m]

/-- For a chart-`α` good-set point `b`, the chart-`α` `(Idx, Jdx)` raw scalar of the first covariant
derivative `cov_RS T₀ (b) (∂_m b)` equals the chart-Euclidean partial `euclidPartial m
(chartPushedRaw raw_{IJ}(T₀))` at `y := toEuclidean (chart b)` plus the zeroth-order
`covDerivLowerOrderTerm`.  This is the public-lemma assembly of `tensorCovDerivAt_def`,
`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`, and
`covDerivComponent_eq_euclidPartial_add_lowerOrder`. -/
private lemma chartα_proj_covRS_chartBasis_eq_euclidPartial_plus_lower
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            (chartBasisVecFiber (I := I) α m b))) =
      euclidPartial (E := E) m
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
          ((toEuclidean (E := E)) ((extChartAt I α) b)) +
        covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have hy_mem : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]; exact (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_te, hleft_inv]
  have hLHS_eq :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun z : M => T₀.toSection z) b
        (chartBasisVecFiber (I := I) α m b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
        (chartBasisVecFiber (I := I) α m) b := by
    have htdef := tensorCovDerivAt_def (I := I) (M := M) g r s T₀ b
      (chartBasisVecFiber (I := I) α m b)
    have hagree := tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s T₀ α m hb
    exact htdef.symm.trans hagree
  rw [hLHS_eq]
  have hB1 := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s T₀ α m Idx Jdx hy_mem
  rw [hb_eq] at hB1
  rw [hB1]

/-- The principal coefficient of the `T₀`-linear expansion of the Christoffel correction: indexed by
`(I', J', m)`, supported on `(I', J') = (Idx, Jdx)` only, carrying the negated field coordinate
`W^m`. -/
private noncomputable def christoffelTracePrincipalCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (if I' = Idx ∧ J' = Jdx then (1 : ℝ) else 0) *
      (- wTraceCoordPullback (I := I) (M := M) g α m y)

/-- Smoothness of the principal coefficient on the Euclidean chart target. -/
private lemma christoffelTracePrincipalCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx I' J' m)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold christoffelTracePrincipalCoeff
  exact contDiffOn_const.mul (wTraceCoordPullback_contDiffOn (I := I) (M := M) g α m).neg

/-- The zeroth-order coefficient of the `T₀`-linear expansion of the Christoffel correction: indexed
by `(I', J')`, carrying the negated field coordinate `W^m` against the lower-order coefficient. -/
private noncomputable def christoffelTraceZerothCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ m : Fin (Module.finrank ℝ E),
      (- wTraceCoordPullback (I := I) (M := M) g α m y) *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y

/-- Smoothness of the zeroth-order coefficient on the Euclidean chart target. -/
private lemma christoffelTraceZerothCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx I' J')
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold christoffelTraceZerothCoeff
  refine ContDiffOn.sum (fun m _ => ?_)
  exact (wTraceCoordPullback_contDiffOn (I := I) (M := M) g α m).neg.mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx I' Jdx J')

/-- **The frame-independent chart-coordinate Christoffel correction admits a smooth-coefficient
chart-coordinate form.**

There exist `T₀`-independent `C^∞` coefficient families `B_1`, `B_0` on the Euclidean chart target
such that, for every smooth compactly-supported section `T₀` and every base point `b` in the
chart-`α` Levi-Civita good set, the chart-coordinate Christoffel correction
```
− ∑_{k,l} chartInvGramMatrix g α b k l ·
    proj(cov_RS T₀ (b) ((LC g) ∂_k (b) (∂_l b)))
```
equals the canonical first-order chart-coordinate form
```
∑_{I', J', m} B_1 I' J' m · ∂_m (chartPushedRaw raw_{I'J'}(T₀))
  + ∑_{I', J'} B_0 I' J' · chartPushedRaw raw_{I'J'}(T₀)    (at toEuclidean (chart b)).
```

This is TRUE and is the exact frame-independent analogue of the bumped-frame
`chartFrameTraceΓCorrection_eq_T₀_linear`. The correction is a *single* first covariant derivative
of `T₀` (carrying at most one derivative of `T₀`) contracted against the smooth chart-Christoffel
trace field `W := ∑_{k,l} chartInvGramMatrix g α b k l · (LC g) ∂_k (b) (∂_l b)`, whose `m`-th
chart-`α` coordinate `W^m(b) = ∑_{k,l} chartInvGramMatrix g α b k l · chartChristoffel g α l k
(extChart b)` pulls back to a `C^∞` function on `chartTargetEuclid α`
(`chartInvGramMatrix_pullback_contDiffOn_chartTarget` and the chart-Christoffel pullback smoothness
`chartLeviCivitaParallelCLM_coordEntry_contDiffOn`). Expanding `W b = ∑_m W^m(b) ∂_m b` in the chart
coordinate basis, pushing the projection CLM through, and applying the chart-coordinate
covariant-derivative component formula `covDerivComponent_eq_euclidPartial_add_lowerOrder`
(each projected `proj(cov_RS T₀ (b) (∂_m b))` rewrites as `∂_m(chartPushedRaw raw_{IJ}(T₀))` plus a
zeroth-order `covDerivLowerOrderTerm`, itself a `C^∞`-coefficient combination of the undifferentiated
raw components by `covDerivLowerOrderCoeff_contDiffOn`) yields the canonical form with `T₀`-independent
`C^∞` coefficients.

Posited here as a precise true prerequisite: the (mechanical but lengthy) frame-free mirror of
`chartFrameTraceΓCorrection_eq_T₀_linear`, packaging the chart-Christoffel-trace first covariant
derivative as a smooth-coefficient first-order chart-coordinate operator. -/
theorem christoffelTrace_correction_eq_T₀_linear
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (B_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (B_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (B_1 I' J' m)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (B_0 I' J')
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          (- ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b k l *
                  tensorChartComponentProjection (E := E) r s Idx Jdx
                    ((trivializationAt (TensorRSModel r s ℝ E)
                        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                      ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                          (LeviCivita (I := I) g)).toFun
                        (fun z : M => T₀.toSection z) b
                        ((LeviCivita (I := I) g).toFun
                          (fun z : M => chartBasisVecFiber (I := I) α k z) b
                          (chartBasisVecFiber (I := I) α l b))))) =
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              B_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              B_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  refine ⟨christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx,
          christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx,
          ?_, ?_, ?_⟩
  · intro I' J' m
    exact christoffelTracePrincipalCoeff_contDiffOn (I := I) (M := M) g r s α Idx Jdx I' J' m
  · intro I' J'
    exact christoffelTraceZerothCoeff_contDiffOn (I := I) (M := M) g r s α Idx Jdx I' J'
  · intro T₀ b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hb_src : b ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
    have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_src
    have hy_mem : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := ⟨(extChartAt I α) b, hb_tgt, rfl⟩

    rw [christoffelTrace_proj_eq_wCoord_sum (I := I) (M := M) g r s α T₀ Idx Jdx hb]

    have hStep2 :
        (∑ m : Fin (Module.finrank ℝ E),
          wTraceCoordPullback (I := I) (M := M) g α m y *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (fun z : M => T₀.toSection z) b
                  (chartBasisVecFiber (I := I) α m b)))) =
        ∑ m : Fin (Module.finrank ℝ E),
          wTraceCoordPullback (I := I) (M := M) g α m y *
            (euclidPartial (E := E) m
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [chartα_proj_covRS_chartBasis_eq_euclidPartial_plus_lower
        (I := I) (M := M) g r s α T₀ m Idx Jdx hb]
    rw [hStep2]

    have hStep3 :
        (- ∑ m : Fin (Module.finrank ℝ E),
            wTraceCoordPullback (I := I) (M := M) g α m y *
              (euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y)) =
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            euclidPartial (E := E) m
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) +
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hStep3]

    have hPrincipal_block_eq :
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            euclidPartial (E := E) m
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx I' J' m y *
                euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
      rw [Finset.sum_eq_single Idx]
      · rw [Finset.sum_eq_single Jdx]
        · refine Finset.sum_congr rfl (fun m _ => ?_)
          unfold christoffelTracePrincipalCoeff
          simp [and_self]
        · intro J' _ hJne
          refine Finset.sum_eq_zero (fun m _ => ?_)
          unfold christoffelTracePrincipalCoeff
          simp [hJne]
        · intro hJ; exact absurd (Finset.mem_univ _) hJ
      · intro I' _ hIne
        refine Finset.sum_eq_zero (fun J' _ => ?_)
        refine Finset.sum_eq_zero (fun m _ => ?_)
        unfold christoffelTracePrincipalCoeff
        simp [hIne]
      · intro hI; exact absurd (Finset.mem_univ _) hI

    have hZeroth_block_eq :
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx I' J' y *
              DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y := by
      have hLowerEq : ∀ m,
          covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y *
                DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y := by
        intro m
        rw [covDerivComponent_lowerOrder_eq_linearCombination
          (I := I) (M := M) g r s T₀ α m Idx Jdx y]
        rw [← Finset.sum_product']
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) hy_mem]
      have hSubst :
          (∑ m : Fin (Module.finrank ℝ E),
            (- wTraceCoordPullback (I := I) (M := M) g α m y) *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
          ∑ m : Fin (Module.finrank ℝ E),
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                (- wTraceCoordPullback (I := I) (M := M) g α m y) *
                  (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y *
                    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hLowerEq m, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I' _ => ?_)
        rw [Finset.mul_sum]
      rw [hSubst]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      unfold christoffelTraceZerothCoeff
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hPrincipal_block_eq, hZeroth_block_eq]

end Connection
end Integral
end DifferentialGeometry

end
