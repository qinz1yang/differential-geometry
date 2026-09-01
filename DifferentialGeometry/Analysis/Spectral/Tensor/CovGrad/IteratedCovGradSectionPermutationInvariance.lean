import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.PassZero
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Norm

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (sigma : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (rsDomDomCongrSection (I := I) (M := M) g r s sigma R)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s sigma R
    (rsDomDomCongrSection (I := I) (M := M) g r s sigma R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
        ((iteratedCovGrad (I := I) g 0 2 k
          (ccTensor02Symm (I := I) (M := M) g P)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
        ((iteratedCovGrad (I := I) g 0 2 k P).toSection x) := by
  rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g P k]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P +
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P).toSection x +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_add]
    rfl]
  refine (riemannianFiberNormSq_add_le_sq_sqrt
    (I := I) (M := M) g 0 (2 + k) x _ _).trans ?_
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 k P).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul,
    DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) P k x]
  set A := riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
    ((iteratedCovGrad (I := I) g 0 2 k P).toSection x) with hA_def
  have hA0 : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + k) x _
  have hs : Real.sqrt ((1 / 2 : ℝ) ^ 2 * A) =
      (1 / 2 : ℝ) * Real.sqrt A := by
    rw [Real.sqrt_mul (by positivity) A, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hs]
  nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg A]

end Spectral
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Integral.Connection

alias riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq :=
  DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq

end DifferentialGeometry.Integral.Connection

end
