import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.HeatOutputRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Tensor.RSTensor.RankZero
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma real_inner_eq_mul' (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  change RCLike.re ⟪a, b⟫_ℝ = a * b
  have h := RCLike.inner_apply a b
  have hrw : RCLike.re ⟪a, b⟫_ℝ = RCLike.re (b * (starRingEnd ℝ) a) := congrArg RCLike.re h
  rw [hrw]
  simp
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothToLp_inner_eq_integral_mul
    (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ⟪smoothToLp (I := I) (M := M) g f, smoothToLp (I := I) (M := M) g h⟫_ℝ =
      ∫ x, f.toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) f.memLp_two,
    MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) h.memLp_two] with x hx₁ hx₂
  rw [smoothToLp_apply, smoothToLp_apply]
  rw [hx₁, hx₂]
  exact real_inner_eq_mul' (f.toFun x) (h.toFun x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensorEval_zero_zero_scalar0
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
      (1 : ℝ))) Fin.elim0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x := by
  unfold TensorRSField.scalar0 TensorRSField.rs0
  simp only [SmoothCcTensor.toFun_apply, Tensor0SField.toScalarField]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma separableForm_zero_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v : Fin 0 → E) (w : Fin 0 → E) :
    (separableFormAt (I := I) (M := M) g x 0) v w = 1 := by
  rw [separableFormAt_apply]
  simp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensorInnerPointwise_smooth_zero_zero
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x (S.toFun x) (T.toFun x) =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x := by
  unfold tensorInnerPointwise
  rw [tensorInnerPointwise_0s_zero_arity]
  rw [lowerAllUpperIndices_apply]
  rw [lowerAllUpperIndices_apply]
  have hS : (separableFormAt (I := I) (M := M) g x 0
        (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro w
    exact separableForm_zero_apply (I := I) (M := M) g x
      (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i)) w
  rw [hS]
  change ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
    (1 : ℝ))) Fin.elim0 *
      ((T.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
        (1 : ℝ))) Fin.elim0 =
    TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g S x]
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g T x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem tensorL2Inner_zero_zero_eq_integral_scalar0_mul
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    tensorL2Inner (I := I) (M := M) g 0 0 S.toFun T.toFun =
      ∫ x,
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  apply integral_congr_ae
  filter_upwards with x
  exact tensorInnerPointwise_smooth_zero_zero (I := I) (M := M) g S T x

abbrev TensorEigenIdx00 (g : SmoothRiemannianMetric I M) :=
  Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 0

theorem eigenvectorSmooth00_eq_basis
    (g : SmoothRiemannianMetric I M) (j : TensorEigenIdx00 g) :
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) =
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j := by
  calc
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
        = tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
    _ = tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j).symm

theorem tensorL2Coeff_eigenvectorSmooth00
    (g : SmoothRiemannianMetric I M) [DecidableEq (TensorEigenIdx00 g)]
    (i j : TensorEigenIdx00 g) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        ((eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)) i =
      (if i = j then (1 : ℝ) else 0) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  change (b.repr (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) i) =
    if i = j then (1 : ℝ) else 0
  have hbj : (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) = b j := by
    calc
      (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
          = tensorResolventEigenbasisVec (I := I) (M := M) hc j :=
        eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
      _ = b j := by
        rw [hb_def]
        exact (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M) hc j).symm
  rw [hbj]
  rw [HilbertBasis.repr_apply_apply]
  rw [real_inner_comm]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    simpa using horth j j
  · have hne : i ≠ j := fun hij => hji hij.symm
    rw [if_neg hne]
    exact Orthonormal.inner_eq_zero b.orthonormal hji

theorem tensorEigen00_rawLap_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i)) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  apply b.repr.injective
  ext j
  change tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i))) j =
    tensorL2Coeff (I := I) (M := M) hc
      ((- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j
  rw [rawLap_coeff (I := I) (M := M) g 0 hc (eigenvectorSmooth g 0 0 i) j]
  rw [tensorL2Coeff_smul (I := I) (M := M) hc
    (- TensorEigenIdx.lambda (I := I) (M := M) i)
    (SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j]
  haveI : DecidableEq (TensorEigenIdx00 g) := Classical.decEq _
  have hcoeff := tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
  rw [← SmoothCcTensor.toL2_apply] at hcoeff
  rw [hcoeff]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

omit [SigmaCompactSpace M] [CompactSpace M] in
private lemma rawLapSection_eq_toRS0 (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (x : M) :
    rawTensorConnLap g 0 0 (fun y : M => S.toSection y) x =
      ((Tensor0SNabla.tensor0Iso I M x).symm (laplacian (LeviCivita g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) x)).toRS0 := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  have hraw := rawLap_scalar (I := I) (M := M) g hf x
  have hlift := TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  rw [hlift] at hraw
  exact hraw

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] in
private lemma laplacian_scalar0_smooth (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (I := I) (LeviCivita (I := I) g) g
      (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection)) := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  refine (Δ_g_contMDiff (I := I) g ⟨_, hf⟩).congr ?_
  intro x
  exact laplacian_levi_eq (I := I) g hf x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensor0Iso_fromScalarField
    (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    Tensor0SNabla.tensor0Iso I M y (Tensor0SField.fromScalarField ∞ f hf y) = f y := by
  unfold Tensor0SField.fromScalarField Tensor0SNabla.tensor0Iso
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      (Tensor0SSpace.toModel (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I y) (f y))) = f y
  rfl

omit [SigmaCompactSpace M] [CompactSpace M] in
theorem scalar0_rawLap_eq_scalarLap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection x =
      laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) x := by
  change Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
    laplacian (I := I) (LeviCivita (I := I) g) g
      (Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞)) S.toSection)) x
  have hpt : (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
      Tensor0SField.fromScalarField ∞
        (laplacian (I := I) (LeviCivita (I := I) g) g
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
        (laplacian_scalar0_smooth (I := I) (M := M) g S) x := by
    rw [TensorRSField.rs0_apply]
    rw [rawTensorConnLapSmooth_toSection_apply]
    rw [rawLapSection_eq_toRS0 (I := I) (M := M) g S x]
    rw [Tensor0SSpace.toRS0_apply]
    have hone : tensor0SSpace_evalScalar x
        (Tensor0SField.one0 (n := (∞ : WithTop ℕ∞))
          (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) x) = 1 := by
      change Tensor0SSpace.toModel (Tensor0SField.one0 (n := (∞ : WithTop ℕ∞))
        (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) x) Fin.elim0 = 1
      rw [Tensor0SField.one0_apply]
    rw [hone, one_smul]
    symm
    apply (Tensor0SNabla.tensor0Iso I M x).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact tensor0Iso_fromScalarField
      (laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
      (laplacian_scalar0_smooth (I := I) (M := M) g S) x
  rw [show Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
      Tensor0SField.toScalarField ∞ (Tensor0SField.fromScalarField ∞
        (laplacian (I := I) (LeviCivita (I := I) g) g
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
        (laplacian_scalar0_smooth (I := I) (M := M) g S)) x by
    unfold Tensor0SField.toScalarField
    rw [hpt]]
  rw [Tensor0SField.toScalarField_fromScalarField]
  rfl

theorem scalarEigen00_laplacian_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection) x =
      - TensorEigenIdx.lambda (I := I) (M := M) i *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection x := by
  rw [← scalar0_rawLap_eq_scalarLap g (eigenvectorSmooth g 0 0 i) x]
  have hcc : rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        eigenvectorSmooth g 0 0 i := by
    exact Integral.L2.SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq
      (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i))
      ((- TensorEigenIdx.lambda (I := I) (M := M) i) • eigenvectorSmooth g 0 0 i)
      (by
        rw [map_smul]
        exact tensorEigen00_rawLap_eq (I := I) (M := M) g i)
  calc
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i)).toSection x
        = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
            ((- TensorEigenIdx.lambda (I := I) (M := M) i) •
              eigenvectorSmooth g 0 0 i).toSection x := by
          rw [hcc]
    _ = - TensorEigenIdx.lambda (I := I) (M := M) i *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection x := by
          simp

end HeatEquation
end Analysis
end DifferentialGeometry

end
