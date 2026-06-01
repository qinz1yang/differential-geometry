import DifferentialGeometry.Integral.Connection.TensorConnLapGreenAssembly
import DifferentialGeometry.Integral.Connection.TensorConnLapGreenIdentity
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# Per-chart weighted Dirichlet–second-order identity for the `(0, 2)` connection Laplacian

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file assembles, on a single chart base point
`α : M`, the partition-of-unity-weighted form of the integrated Green identity
for the rough (connection) Laplacian acting on `(0, 2)`-tensor fields.

The headline per-chart identity expresses the `ρ_α`-weighted integral of the
inverse-Gram-weighted covariant-gradient (Dirichlet) pairing
`tensorCovDerivPointwiseInner g 0 2 T v` as minus the `ρ_α`-weighted integral of
the full second-order frame sum (the second covariant derivative
`∇_{Bᵢ}(∇_{Bᵢ}T)` of `T` paired against `v`), minus the frame
divergence-correction sum, minus the partition-of-unity Leibniz weight terms,
where `Bᵢ = chartFrameNormGlobalSmooth g α i` is the globally smooth chart-`α`
orthonormal frame:

```
∫ ρ_α · tensorCovDerivPointwiseInner g 0 2 T v
  = − ∑ᵢ ∫ ρ_α · ⟨∇_{Bᵢ}(∇_{Bᵢ}T), v⟩
    − ∑ᵢ ∫ ρ_α · ⟨∇_{Bᵢ}T, v⟩ · divᵍ Bᵢ
    − ∑ᵢ ∫ ⟨∇_{Bᵢ}T, v⟩ · Bᵢ(ρ_α).
```

All inner products are the mixed `(0, 2)`-tensor pointwise inner product
`tensorInnerScalar g 0 2`, written through the smooth directional covariant
derivative sections `covDerivAlongVFSection g · Bᵢ` of `TensorConnLapSecondOrderIBP`.
This form keeps every integrand a *mixed* tensor inner-product scalar, whose
smoothness (hence integrability on a closed manifold) is the committed
`tensorInnerScalar_contMDiff`.

It is obtained by combining three committed ingredients:

* the **diagonal-frame reduction** of the Dirichlet integrand
  `tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two`, valid at a
  base point where the chart-`α` frame is `g`-orthonormal — which holds on the
  intersection of the chart-`α` partition-of-unity tsupport with the chart-`α`
  Levi-Civita good set
  (`chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet`), and is killed
  off-support by `ρ_α = 0` through the support case-split;

* the **partition-of-unity-weighted second-order integration by parts**
  `integral_weighted_secondOrder_combined_eq_neg_weightDeriv`, applied per frame
  direction `Bᵢ`;

* finite-sum / integrability bookkeeping over the frame index `i`.

The diagonal-frame middle term `tensorInnerPointwise_0s (0 + 2) g b (∇_{Bᵢ}T)ᵇ (∇_{Bᵢ}v)ᵇ`
and the weighted-IBP lowered cross term are both identified with the mixed
inner product `tensorInnerScalar g 0 2 (∇_{Bᵢ}T) (∇_{Bᵢ}v)` through the
metric-lowering / lifting-section identities
`tensorInnerPointwise_eq_liftedTensorSection_inner`,
`toModel_liftedTensorSection_covDerivAlongVFSection`, and the definitional
unfolding of `loweredCovDerivAlongVF`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The chart-`α` frame direction `i` as a smooth tangent vector field. -/
def frameVF
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  chartFrameNormGlobalSmooth (I := I) (M := M) g α i

/-- The per-direction *cross (Dirichlet)* integrand `⟨∇_{Bᵢ}T, ∇_{Bᵢ}v⟩`, as a
mixed `(0, 2)`-tensor inner-product scalar. -/
def perDirCross
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  tensorInnerScalar (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
    (covDerivAlongVFSection (I := I) (M := M) g v.toSection (frameVF (I := I) (M := M) g α i))

/-- The per-direction *second-order* integrand `⟨∇_{Bᵢ}(∇_{Bᵢ}T), v⟩`, as a
mixed `(0, 2)`-tensor inner-product scalar. -/
def perDirSecond
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  tensorInnerScalar (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
      (frameVF (I := I) (M := M) g α i))
    v.toSection

/-- The per-direction *divergence-correction* integrand `⟨∇_{Bᵢ}T, v⟩ · divᵍ Bᵢ`. -/
def perDirDiv
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun b =>
    tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
        v.toSection b
      * divergence_g (I := I) g (frameVF (I := I) (M := M) g α i) b

/-- The per-direction *weight (Leibniz)* integrand `⟨∇_{Bᵢ}T, v⟩ · Bᵢ(ρ_α)`. -/
def perDirWeight
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun b =>
    tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
        v.toSection b
      * tangentSectionAction (I := I) (frameVF (I := I) (M := M) g α i)
          ((chartAtlasPOU I M α : M → ℝ)) b

private lemma perDirCross_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (perDirCross (I := I) (M := M) g T v α i) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

private lemma perDirSecond_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (perDirSecond (I := I) (M := M) g T v α i) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

private lemma perDirInner_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (tensorInnerScalar (I := I) (M := M) g 0 2
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
      v.toSection) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

private lemma perDirDiv_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (perDirDiv (I := I) (M := M) g T v α i) :=
  (perDirInner_continuous (I := I) (M := M) g T v α i).mul
    (divergence_g_contMDiff (I := I) g (frameVF (I := I) (M := M) g α i)).continuous

private lemma perDirWeight_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (perDirWeight (I := I) (M := M) g T v α i) :=
  (perDirInner_continuous (I := I) (M := M) g T v α i).mul
    (tangentSectionAction_contMDiff (I := I) (frameVF (I := I) (M := M) g α i)
      (chartAtlasPOU I M α).contMDiff).continuous

private lemma perDir_integrable_of_continuous
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    (I := I) g hf (HasCompactSupport.of_compactSpace _)

/-- **Diagonal-frame reduction at orthonormality points.** On the intersection
of the chart-`α` partition-of-unity tsupport with the chart-`α` Levi-Civita good
set, the inverse-Gram-weighted Dirichlet integrand
`tensorCovDerivPointwiseInner g 0 2 T v b` equals the plain frame sum of the
per-direction mixed cross integrands `perDirCross g T v α i b`.

The proof instantiates `tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two`
with the frame `Bᵢ = chartFrameNormGlobalSmooth g α i`, whose orthonormality at
`b` on this intersection is supplied by
`chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet`, then identifies
each lowered diagonal summand with the mixed inner product `perDirCross` via the
lifting-section / lowering identities. -/
private theorem tensorCovDerivPointwiseInner_eq_perDirCross_sum_on_support
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        perDirCross (I := I) (M := M) g T v α i b := by
  classical
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j =>
      chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
        (I := I) (M := M) g α hb i j
  rw [tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two
    (I := I) (M := M) g T v b
    (fun i : Fin (Module.finrank ℝ E) =>
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
    hB_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold perDirCross frameVF
  rw [tensorInnerScalar_apply,
    tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
      (covDerivAlongVFSection (I := I) (M := M) g v.toSection
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i)) b]
  rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g T.toSection
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b,
    toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g v.toSection
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
  rfl

/-- **Per-direction weighted Dirichlet integration-by-parts rearrangement.**
For each chart-`α` frame direction `i`,

```
∫ ρ_α · perDirCross g T v α i
  = − ∫ ρ_α · perDirSecond g T v α i
    − ∫ ρ_α · perDirDiv g T v α i
    − ∫ perDirWeight g T v α i.
```

This is the committed weighted second-order combined integration by parts
`integral_weighted_secondOrder_combined_eq_neg_weightDeriv` (with `B = Bᵢ`,
`ρ = ρ_α`), after recasting the lowered `tensorInnerPointwise_0s` summands as the
mixed inner-product scalars `perDirSecond`, `perDirCross`, then rearranging using
additivity of the integral and integrability of the three smooth,
compactly-supported summands. -/
private theorem integral_pou_perDirCross_eq
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirCross (I := I) (M := M) g T v α i b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -(∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirSecond (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirDiv (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ b, perDirWeight (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hB_def
  set ρ : M → ℝ := (chartAtlasPOU I M α : M → ℝ) with hρ_def
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := (chartAtlasPOU I M α).contMDiff
  have hIBP := integral_weighted_secondOrder_combined_eq_neg_weightDeriv
    (I := I) (M := M) g T.toSection v.toSection B ρ hρ
  have hLHS_pt : ∀ b : M,
      ρ b * (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v.toSection b))
            + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) b))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v.toSection B b))
            + tensorInnerScalar (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
              * divergence_g (I := I) g B b) =
        ρ b * perDirSecond (I := I) (M := M) g T v α i b
          + ρ b * perDirCross (I := I) (M := M) g T v α i b
          + ρ b * perDirDiv (I := I) (M := M) g T v α i b := by
    intro b
    have hA : tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v.toSection b)) =
        perDirSecond (I := I) (M := M) g T v α i b := by
      unfold perDirSecond frameVF
      rw [tensorInnerScalar_apply,
        tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
          v.toSection b]
      rw [hB_def]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
      rfl
    have hC : tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) b))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v.toSection B b)) =
        perDirCross (I := I) (M := M) g T v α i b := by
      unfold perDirCross frameVF
      rw [tensorInnerScalar_apply,
        tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
          (covDerivAlongVFSection (I := I) (M := M) g v.toSection
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i)) b]
      rw [hB_def]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g T.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b,
        toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g v.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
      rfl
    have hD : tensorInnerScalar (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
              * divergence_g (I := I) g B b =
        perDirDiv (I := I) (M := M) g T v α i b := by
      unfold perDirDiv frameVF; rw [hB_def]
    rw [hA, hC, hD]; ring
  have hRHS_pt : ∀ b : M,
      tensorInnerScalar (I := I) (M := M) g 0 2
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
          * tangentSectionAction (I := I) B ρ b =
        perDirWeight (I := I) (M := M) g T v α i b := by
    intro b; unfold perDirWeight frameVF; rw [hB_def, hρ_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hLHS_pt)] at hIBP
  rw [integral_congr_ae (Filter.Eventually.of_forall hRHS_pt)] at hIBP
  have hρ_cont : Continuous ρ := hρ.continuous
  have h_int_second : Integrable
      (fun b : M => ρ b * perDirSecond (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirSecond_continuous (I := I) (M := M) g T v α i))
  have h_int_cross : Integrable
      (fun b : M => ρ b * perDirCross (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirCross_continuous (I := I) (M := M) g T v α i))
  have h_int_div : Integrable
      (fun b : M => ρ b * perDirDiv (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirDiv_continuous (I := I) (M := M) g T v α i))
  have hadd1 :
      ∫ b, ((ρ b * perDirSecond (I := I) (M := M) g T v α i b
              + ρ b * perDirCross (I := I) (M := M) g T v α i b)
            + ρ b * perDirDiv (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, (ρ b * perDirSecond (I := I) (M := M) g T v α i b
              + ρ b * perDirCross (I := I) (M := M) g T v α i b) ∂μ)
          + (∫ b, ρ b * perDirDiv (I := I) (M := M) g T v α i b ∂μ) :=
    integral_add (μ := μ)
      (f := fun b : M => ρ b * perDirSecond (I := I) (M := M) g T v α i b
              + ρ b * perDirCross (I := I) (M := M) g T v α i b)
      (g := fun b : M => ρ b * perDirDiv (I := I) (M := M) g T v α i b)
      (h_int_second.add h_int_cross) h_int_div
  have hadd2 :
      ∫ b, (ρ b * perDirSecond (I := I) (M := M) g T v α i b
              + ρ b * perDirCross (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, ρ b * perDirSecond (I := I) (M := M) g T v α i b ∂μ)
          + (∫ b, ρ b * perDirCross (I := I) (M := M) g T v α i b ∂μ) :=
    integral_add (μ := μ)
      (f := fun b : M => ρ b * perDirSecond (I := I) (M := M) g T v α i b)
      (g := fun b : M => ρ b * perDirCross (I := I) (M := M) g T v α i b)
      h_int_second h_int_cross
  have h3 :
      ∫ b, ((ρ b * perDirSecond (I := I) (M := M) g T v α i b
            + ρ b * perDirCross (I := I) (M := M) g T v α i b)
            + ρ b * perDirDiv (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, ρ b * perDirSecond (I := I) (M := M) g T v α i b ∂μ)
        + (∫ b, ρ b * perDirCross (I := I) (M := M) g T v α i b ∂μ)
        + (∫ b, ρ b * perDirDiv (I := I) (M := M) g T v α i b ∂μ) := by
    rw [hadd1, hadd2]
  rw [h3] at hIBP
  linarith [hIBP]

/-- **`ρ_α`-weighted Dirichlet integrand equals the `ρ_α`-weighted frame
cross-sum pointwise.** For every base point `b`,

```
ρ_α b · tensorCovDerivPointwiseInner g 0 2 T v b
  = ρ_α b · ∑ᵢ perDirCross g T v α i b.
```

On the chart-`α` partition-of-unity tsupport the chart-source / good-set
identification supplies the orthonormality needed by the diagonal-frame
reduction; off the tsupport `ρ_α b = 0` kills both sides. -/
private theorem pou_tensorCovDerivPointwiseInner_eq_perDirCross_sum
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) (b : M) :
    (chartAtlasPOU I M α : M → ℝ) b
        * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      (chartAtlasPOU I M α : M → ℝ) b
        * ∑ i : Fin (Module.finrank ℝ E), perDirCross (I := I) (M := M) g T v α i b := by
  classical
  by_cases hb_supp : b ∈ tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hb_chartSrc : b ∈ (chartAt H α).source :=
      (chartAtlasPOU_isSubordinate (I := I) (M := M) α) hb_supp
    have hb_extSrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source]; exact hb_chartSrc
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]; exact hb_extSrc
    have hb_inter : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α := ⟨hb_supp, hb_good⟩
    rw [tensorCovDerivPointwiseInner_eq_perDirCross_sum_on_support
      (I := I) (M := M) g T v α hb_inter]
  · have hp0 : (chartAtlasPOU I M α : M → ℝ) b = 0 :=
      image_eq_zero_of_notMem_tsupport hb_supp
    rw [hp0, zero_mul, zero_mul]

/-- **Integrated `ρ_α`-weighted Dirichlet reduction.** Integrating the
`ρ_α`-weighted Dirichlet integrand equals the frame sum of the integrated
`ρ_α`-weighted per-direction cross integrands. -/
private theorem integral_pou_tensorCovDerivPointwiseInner_eq_frame_sum
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b
          * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirCross (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (pou_tensorCovDerivPointwiseInner_eq_perDirCross_sum (I := I) (M := M) g T v α))]
  have hdist : ∀ b : M,
      (chartAtlasPOU I M α : M → ℝ) b
          * ∑ i : Fin (Module.finrank ℝ E), perDirCross (I := I) (M := M) g T v α i b =
        ∑ i : Fin (Module.finrank ℝ E),
          (chartAtlasPOU I M α : M → ℝ) b * perDirCross (I := I) (M := M) g T v α i b := by
    intro b; rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdist)]
  have hρ_cont : Continuous ((chartAtlasPOU I M α : M → ℝ)) :=
    (chartAtlasPOU I M α).contMDiff.continuous
  refine MeasureTheory.integral_finset_sum (Finset.univ) (fun i _ => ?_)
  exact perDir_integrable_of_continuous (I := I) g
    (hρ_cont.mul (perDirCross_continuous (I := I) (M := M) g T v α i))

/-- **Per-chart weighted Green identity for the `(0, 2)` connection Laplacian.**
For a single chart base point `α`, the `ρ_α`-weighted integral of the Dirichlet
pairing equals minus the frame sums of the integrated `ρ_α`-weighted
second-order pairings, divergence-correction terms, and partition-of-unity
Leibniz weight terms:

```
∫ ρ_α · tensorCovDerivPointwiseInner g 0 2 T v
  = − ∑ᵢ ∫ ρ_α · perDirSecond g T v α i
    − ∑ᵢ ∫ ρ_α · perDirDiv g T v α i
    − ∑ᵢ ∫ perDirWeight g T v α i,
```

where, with `Bᵢ = chartFrameNormGlobalSmooth g α i`,

* `perDirSecond g T v α i = ⟨∇_{Bᵢ}(∇_{Bᵢ}T), v⟩` is the full second-order
  covariant-derivative pairing;
* `perDirDiv g T v α i = ⟨∇_{Bᵢ}T, v⟩ · divᵍ Bᵢ` is the frame divergence
  correction;
* `perDirWeight g T v α i = ⟨∇_{Bᵢ}T, v⟩ · Bᵢ(ρ_α)` is the partition-of-unity
  Leibniz weight term.

It combines the integrated weighted Dirichlet reduction
`integral_pou_tensorCovDerivPointwiseInner_eq_frame_sum` (diagonal-frame
reduction with the support case-split) with the per-direction weighted
integration by parts `integral_pou_perDirCross_eq`, summed over the chart-`α`
frame index. -/
theorem integral_pou_tensorCovDerivPointwiseInner_eq_neg_second_div_weight
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b
          * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -(∑ i : Fin (Module.finrank ℝ E),
          ∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirSecond (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∑ i : Fin (Module.finrank ℝ E),
          ∫ b, (chartAtlasPOU I M α : M → ℝ) b * perDirDiv (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∑ i : Fin (Module.finrank ℝ E),
          ∫ b, perDirWeight (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  rw [integral_pou_tensorCovDerivPointwiseInner_eq_frame_sum (I := I) (M := M) g T v α]
  rw [Finset.sum_congr rfl (fun i _ =>
    integral_pou_perDirCross_eq (I := I) (M := M) g T v α i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end Connection
end Integral
end DifferentialGeometry

end
