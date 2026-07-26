import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.FiniteReprLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapLinear
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Retag
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The finite spectral core of the moving scalar Laplacian

This file realizes the genuine scalar Laplacian difference on the dense
finite-support spectral core, with values in the fixed reference `L²` space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The dense finite-support scalar spectral `H²` core. -/
abbrev ScalarH2Core (g : SmoothRiemannianMetric I M) :=
  tensorHs.finiteSupportSubmodule
    (I := I) (M := M) (g := g) (r := 0) (s := 0) 2

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toRS0_sub {x : M} (A B : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 (A - B) =
      Tensor0SSpace.toRS0 A - Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  change tensor0SSpace_evalScalar x c • (A - B) =
    tensor0SSpace_evalScalar x c • A - tensor0SSpace_evalScalar x c • B
  exact smul_sub _ _ _

/-- The true moving-minus-reference rough Laplacian on the smooth finite core. -/
noncomputable def lapDiffSec
    (g h : SmoothRiemannianMetric I M) :
    ScalarH2Core (I := I) (M := M) g →ₗ[Real] SmoothCcTensor g 0 0 :=
  ((SmoothCcTensor.retagEquiv h g 0 0).toLinearMap.comp
      ((rawConnLapLin (I := I) h 0 0).comp
        ((SmoothCcTensor.retagEquiv g h 0 0).toLinearMap.comp
          (finiteReprLin (I := I) (M := M) g 0 0 2)))) -
    (rawConnLapLin (I := I) g 0 0).comp
      (finiteReprLin (I := I) (M := M) g 0 0 2)

/-- Pointwise, `lapDiffSec` is the canonical rank-zero lift of the actual
scalar Laplacian difference. -/
theorem lapDiffSec_apply
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g) (x : M) :
    (lapDiffSec (I := I) (M := M) g h v).toSection x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (Δ_g (I := I) h
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
            Δ_g (I := I) g
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x)) := by
  simp only [lapDiffSec, LinearMap.sub_apply, LinearMap.comp_apply,
    finiteReprLin_apply, rawConnLapLin_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  change rawTensorConnLap (I := I) h 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x -
      rawTensorConnLap (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x = _
  rw [← repr_eq_lift (I := I) (M := M) v.1 v.2]
  rw [rawLap_scalar (I := I) (M := M) h
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x,
    rawLap_scalar (I := I) (M := M) g
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x]
  rw [laplacian_levi_eq (I := I) h
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x,
    laplacian_levi_eq (I := I) g
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x]
  rw [← toRS0_sub]
  rw [map_sub]

/-- The genuine fixed-reference `L²` realization of the finite-core
Laplacian difference. -/
noncomputable def lapDiffCore
    (g h : SmoothRiemannianMetric I M) :
    ScalarH2Core (I := I) (M := M) g →ₗ[Real] TensorL2 0 0 g :=
  (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 0)).toLinearMap.comp
    (lapDiffSec (I := I) (M := M) g h)

/-- Pairing a finite-core moving-Laplacian difference with a finite spectral
test vector is the fixed-volume integral of the genuine scalar difference. -/
theorem lapDiffCore_pair
    (q h : SmoothRiemannianMetric I M)
    (v w : ScalarH2Core (I := I) (M := M) q) :
    inner Real (lapDiffCore (I := I) (M := M) q h v)
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)) =
      ∫ x, (Δ_g (I := I) h
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
            Δ_g (I := I) q
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x) *
          reprScalar0 (I := I) (M := M) w.1 w.2 x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  change inner Real
      (SmoothCcTensor.toL2 (lapDiffSec (I := I) (M := M) q h v))
      (SmoothCcTensor.toL2
        (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)) = _
  rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply]
  rw [lapDiffSec_apply (I := I) (M := M) q h v x]
  have hrepr_x :
      (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2).toSection x =
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) w.1 w.2)
          (reprScalar0_smooth (I := I) (M := M) w.1 w.2)).toTensorRSField ∞ x := by
    exact congrArg (fun T => T x)
      (repr_eq_lift (I := I) (M := M) w.1 w.2).symm
  rw [hrepr_x, Tensor0SField.toRS0_eq,
    inner_toRS0_zero (I := I) (M := M) q x]
  have hlap :
      tensor0SSpace_evalScalar x
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (Δ_g (I := I) h
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
            Δ_g (I := I) q
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x)) =
        Δ_g (I := I) h
            (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
          Δ_g (I := I) q
            (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x := by
    change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hrepr :
      tensor0SSpace_evalScalar x
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) w.1 w.2)
          (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x) =
        reprScalar0 (I := I) (M := M) w.1 w.2 x := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SSpace.toModel
      (Tensor0SField.fromScalarField ∞
        (reprScalar0 (I := I) (M := M) w.1 w.2)
        (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x) Fin.elim0 = _
    exact Tensor0SField.fromScalarField_apply ∞
      (reprScalar0 (I := I) (M := M) w.1 w.2)
      (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x Fin.elim0
  rw [hlap, hrepr]

/-- The squared fixed-reference `L²` norm of `lapDiffCore` is the scalar
Laplacian-difference energy. -/
theorem lapDiffCore_sq
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g) :
    ‖lapDiffCore (I := I) (M := M) g h v‖ ^ 2 =
      ∫ x, (Δ_g (I := I) h
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
            Δ_g (I := I) g
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  change ‖SmoothCcTensor.toL2
      (lapDiffSec (I := I) (M := M) g h v)‖ ^ 2 = _
  rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun (I := I) (M := M) g 0 0
      (lapDiffSec (I := I) (M := M) g h v)]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply]
  rw [lapDiffSec_apply (I := I) (M := M) g h v x]
  rw [inner_toRS0_scalar (I := I) (M := M) g x]
  ring

/-- The finite-core `L²` norm is bounded by the metric `C¹` modulus, with a
constant independent of the spectral support. -/
theorem lapDiffCore_norm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : ScalarH2Core (I := I) (M := M) g),
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g <= (1 / 2 : Real) →
          ‖lapDiffCore (I := I) (M := M) g h v‖ <=
            Real.sqrt C *
              |HCGCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h g g| * ‖v‖ := by
  obtain ⟨C, hC, henergy⟩ := lapDiff_energy_le (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro h v hsmall
  let rho : Real :=
    HCGCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g
  have hsq :
      ‖lapDiffCore (I := I) (M := M) g h v‖ ^ 2 <=
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [lapDiffCore_sq (I := I) (M := M) g h v]
    simpa only [rho] using henergy h v.1 v.2 hsmall
  have hrhs :
      (Real.sqrt C * |rho| * ‖v‖) ^ 2 =
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC, sq_abs]
  have hrhs0 : 0 <= Real.sqrt C * |rho| * ‖v‖ := by positivity
  rw [← hrhs] at hsq
  nlinarith [norm_nonneg
    (lapDiffCore (I := I) (M := M) g h v)]

/-- The genuine moving-minus-reference scalar Laplacian, extended uniquely
from the dense finite spectral core to a bounded map `H²(g) → L²(g)`. -/
noncomputable def lapDiffOp
    (g h : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g 0 0 2 →L[Real] TensorL2 0 0 g :=
  (lapDiffCore (I := I) (M := M) g h).extendOfNorm
    (ScalarH2Core (I := I) (M := M) g).subtype

/-- On the finite spectral core, `lapDiffOp` evaluates to the genuine
Laplacian-difference realization whenever the local metric bound applies. -/
theorem lapDiffOp_core
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g)
    (hsmall : (Module.finrank Real E : Real) *
        HCGCompactness.metricDerivNormSupOn
          (I := I) Set.univ 1 h g g <= (1 / 2 : Real)) :
    lapDiffOp (I := I) (M := M) g h v.1 =
      lapDiffCore (I := I) (M := M) g h v := by
  obtain ⟨C, hC, hbound⟩ := lapDiffCore_norm (I := I) (M := M) g
  let B : Real := Real.sqrt C *
    |HCGCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g|
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) g).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := g) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨B, ?_⟩
  intro w
  simpa only [B, Submodule.coe_subtype] using hbound h w hsmall

/-- The operator norm of `lapDiffOp` is controlled by the same support-free
metric `C¹` modulus. -/
theorem lapDiffOp_norm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M),
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g <= (1 / 2 : Real) →
          ‖lapDiffOp (I := I) (M := M) g h‖ <=
            Real.sqrt C *
              |HCGCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h g g| := by
  obtain ⟨C, hC, hbound⟩ := lapDiffCore_norm (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro h hsmall
  let B : Real := Real.sqrt C *
    |HCGCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g|
  have hB : 0 <= B := by positivity
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) g).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := g) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply LinearMap.opNorm_extendOfNorm_le hdense hB
  intro w
  simpa only [B, Submodule.coe_subtype] using hbound h w hsmall

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
