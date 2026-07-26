import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Operator.PointwiseMixed
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentCovDerivIdentification

/-!
# Musical naturality of the connection Laplacian

This file supplies the two rank-one bridges needed to run a vector-valued
parabolic equation through the existing mixed-tensor maximal-regularity
theory.

* `mixed01_connLap` identifies the mixed `(0, 1)` connection Laplacian,
  evaluated on the unit `(0, 0)` tensor, with the cotangent connection
  Laplacian.
* `sharp_connLap` states that the Levi-Civita connection Laplacian commutes
  with the metric musical sharp.

Both statements are pointwise consequences of metric compatibility.  No
coordinate frame is introduced: the proof uses the canonical smooth
orthonormal frame already used by all three connection-Laplacian definitions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma cotCLM_apply {x : M} (α : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToCLM (I := I) α w = α (fun _ : Fin 1 => w) := by
  have h := cotangentToDual_apply (I := I) α w
  rw [show cotangentToDual (I := I) α w = cotangentToCLM (I := I) α w from rfl] at h
  exact h

/-- A smooth abstract `(0, 1)` section has a smooth realization as a
cotangent continuous-linear-map section. -/
private lemma cotCLM_smooth
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun x : M => Tensor0SSpace 1 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) b
        (cotangentToCLM (I := I) (w b))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := ℝ) (V₂ := fun _ : M => ℝ)
    (φ := fun b : M => cotangentToCLM (I := I) (w b))
  intro Z
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (w b) (fun _ : Fin 1 => Z b)) :=
    TensorMultilinear.contMDiff_section_apply (n := 1)
      (fun b : M => w b) w.contMDiff
      (fun _ : Fin 1 => fun b : M => Z b) (fun _ => Z.contMDiff)
  have hmk : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) b
        (Tensor0SSpace.toModel (w b) (fun _ : Fin 1 => Z b))) := by
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr (hscalar x)
  refine hmk.congr (fun b => ?_)
  change (⟨b, Tensor0SSpace.toModel (w b) (fun _ : Fin 1 => Z b)⟩ :
      TotalSpace ℝ (Bundle.Trivial M ℝ)) =
    TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (cotangentToCLM (I := I) (w b) (Z b))
  rw [cotCLM_apply]
  rfl

/-- First-order agreement between the abstract `(0, 1)` tensor connection
and the cotangent extension of the Levi-Civita connection. -/
private lemma covDeriv01_eq
    (g : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y))
    (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
        (fun y : M => w y) x v =
      dualToCotangent (I := I)
        ((cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M => cotangentToCLM (I := I) (w b)) x v) := by
  classical
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro u
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent]
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  have hwmd : TensorSectionMDiffAt (I := I) 1 (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hbridge := tensor0SCovariantDerivative_one_cotangentToCLM
    (I := I) g (fun y : M => w y) hwmd Y v
  have hθmd : MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (w b)) x :=
    ((cotCLM_smooth (I := I) w) x).mdifferentiableAt (by norm_num)
  have hYmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g)
    (θ := fun b : M => cotangentToCLM (I := I) (w b)) hθmd
    (Y := fun b : M => Y b) hYmd v
  rw [show cotangentToDual (I := I)
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun y : M => w y) x v) u =
      cotangentToCLM (I := I)
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun y : M => w y) x v) u from rfl]
  rw [← hYx]
  rw [hbridge, hpair]
  simp only [add_sub_cancel_right, ContinuousLinearMap.coe_coe]

private lemma cotCLM_sub {x : M} (α β : Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (α - β) =
      cotangentToCLM (I := I) α - cotangentToCLM (I := I) β := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.sub_apply, cotCLM_apply, cotCLM_apply, cotCLM_apply,
    ContinuousMultilinearMap.sub_apply]

private lemma cotCLM_dual {x : M} (α : TangentSpace I x →L[ℝ] ℝ) :
    cotangentToCLM (I := I) (dualToCotangent (I := I) α.toLinearMap) = α := by
  apply ContinuousLinearMap.ext
  intro w
  change cotangentToDual (I := I)
      (dualToCotangent (I := I) α.toLinearMap) w = α.toLinearMap w
  rw [cotangentToDual_dualToCotangent]

private lemma cotCLM_sum {ι : Type*} [Fintype ι] {x : M}
    (A : ι → Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (∑ i, A i) =
      ∑ i, cotangentToCLM (I := I) (A i) := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.sum_apply]
  simp only [cotCLM_apply]
  rw [← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]

/-- Per-direction second-order agreement between the abstract one-covariant
connection and the cotangent connection. -/
private lemma second01_eq
    (g : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y))
    {B : Π y : M, TangentSpace I y}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    cotangentToCLM (I := I)
        ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (covApply (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)) B
              (fun y : M => w y)) x (B x) -
          (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => w y) x
            ((LeviCivita (I := I) g).toFun B x (B x))) =
      (cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M =>
            (cotangentCov (LeviCivita (I := I) g)).toFun
              (fun y : M => cotangentToCLM (I := I) (w y)) b (B b)) x (B x) -
        (cotangentCov (LeviCivita (I := I) g)).toFun
          (fun y : M => cotangentToCLM (I := I) (w y)) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  let wB : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y) :=
    ContMDiffSection.mk
      (covApply (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)) B
        (fun y : M => w y))
      (covApply_contMDiff
        (cov := tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g))
        hB w.contMDiff)
  have hwB : (fun b : M => cotangentToCLM (I := I) (wB b)) =
      (fun b : M =>
        (cotangentCov (LeviCivita (I := I) g)).toFun
          (fun y : M => cotangentToCLM (I := I) (w y)) b (B b)) := by
    funext b
    have hb := covDeriv01_eq (I := I) g w b (B b)
    change cotangentToCLM (I := I)
        ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
          (fun y : M => w y) b (B b)) = _
    rw [hb, cotCLM_dual]
  have houter := covDeriv01_eq (I := I) g wB x (B x)
  have hcorr := covDeriv01_eq (I := I) g w x
    ((LeviCivita (I := I) g).toFun B x (B x))
  change cotangentToCLM (I := I)
      ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
          (fun y : M => wB y) x (B x) -
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
          (fun y : M => w y) x
          ((LeviCivita (I := I) g).toFun B x (B x))) = _
  rw [cotCLM_sub, houter, hcorr, cotCLM_dual, cotCLM_dual, hwB]

/-- Covariant differentiation commutes once with the metric sharp. -/
private lemma sharp_covDeriv
    (g : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y))
    (x : M) (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun y : M => inverseMetricSharpFib (I := I) g y (w y)) x v =
      inverseMetricSharpFib (I := I) g x
        ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
          (fun y : M => w y) x v) := by
  have hsharp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (inverseMetricSharpFib (I := I) g y (w y))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g) w.contMDiff
  rw [inverseMetricSharpField_covGrad_eq_zero (I := I) g
    (fun y : M => w y)
    (hsharp.contMDiffAt.mdifferentiableAt (by simp)) v]
  rw [covDeriv01_eq (I := I) g w x v]

/-- Per-direction second covariant derivatives commute with the metric
sharp. -/
private lemma sharp_second_eq
    (g : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y))
    {B : Π y : M, TangentSpace I y}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (LeviCivita (I := I) g).toFun
          (covApply (LeviCivita (I := I) g) B
            (fun y : M => inverseMetricSharpFib (I := I) g y (w y))) x (B x) -
        (LeviCivita (I := I) g).toFun
          (fun y : M => inverseMetricSharpFib (I := I) g y (w y)) x
          ((LeviCivita (I := I) g).toFun B x (B x)) =
      inverseMetricSharpFib (I := I) g x
        ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (covApply (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)) B
              (fun y : M => w y)) x (B x) -
          (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => w y) x
            ((LeviCivita (I := I) g).toFun B x (B x))) := by
  let wB : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y) :=
    ContMDiffSection.mk
      (covApply (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)) B
        (fun y : M => w y))
      (covApply_contMDiff
        (cov := tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g))
        hB w.contMDiff)
  have hfield :
      covApply (LeviCivita (I := I) g) B
          (fun y : M => inverseMetricSharpFib (I := I) g y (w y)) =
        (fun y : M => inverseMetricSharpFib (I := I) g y (wB y)) := by
    funext y
    exact sharp_covDeriv (I := I) g w y (B y)
  calc
    (LeviCivita (I := I) g).toFun
          (covApply (LeviCivita (I := I) g) B
            (fun y : M => inverseMetricSharpFib (I := I) g y (w y))) x (B x) -
        (LeviCivita (I := I) g).toFun
          (fun y : M => inverseMetricSharpFib (I := I) g y (w y)) x
          ((LeviCivita (I := I) g).toFun B x (B x)) =
      inverseMetricSharpFib (I := I) g x
          ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => wB y) x (B x)) -
        inverseMetricSharpFib (I := I) g x
          ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => w y) x
            ((LeviCivita (I := I) g).toFun B x (B x))) := by
        rw [hfield, sharp_covDeriv (I := I) g wB x (B x),
          sharp_covDeriv (I := I) g w x
            ((LeviCivita (I := I) g).toFun B x (B x))]
    _ = inverseMetricSharpFib (I := I) g x
        ((tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => wB y) x (B x) -
          (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)).toFun
            (fun y : M => w y) x
            ((LeviCivita (I := I) g).toFun B x (B x))) := by
      rw [map_sub]
    _ = _ := rfl

/-- The pointwise mixed `(0, 1)` connection Laplacian, evaluated on the
unit `(0, 0)` tensor, is the cotangent connection Laplacian of the realized
one-form. -/
theorem mixed01_connLap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 1) (x : M) :
    cotangentToCLM (I := I)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          connLaplacianMixed (I := I) g 0 1 S.toSection x)
          (unitZeroSec (I := I) (M := M) x)) =
      connLaplacian_oneForm (I := I) g (ccTensor01Covec (I := I) g S) x := by
  classical
  let w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y) :=
    ContMDiffSection.mk
      (unitEvalSection (I := I) (M := M) g 1 S)
      (contMDiff_unitEvalSection (I := I) (M := M) g 1 S)
  rw [connLaplacianMixed_def,
    rawTensorConnLap_eq_frame_trace_secondCovDeriv,
    connLaplacian_oneForm_def]
  rw [ContinuousLinearMap.sum_apply, cotCLM_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_unit_eval_genVal (I := I) (M := M) g 1 S
    (smoothOrthoFrame_smooth (I := I) g x i) x]
  simpa only [w, ccTensor01Covec, unitEvalSection] using
    second01_eq (I := I) g w (smoothOrthoFrame_smooth (I := I) g x i) x

/-- The Levi-Civita connection Laplacian commutes with the metric musical
sharp on a smooth one-covariant tensor section. -/
theorem sharp_connLap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 1) (x : M) :
    connLaplacian_vector (I := I) g
        (fun y : M => inverseMetricSharpFib (I := I) g y
          (unitEvalSection (I := I) (M := M) g 1 S y)) x =
      inverseMetricSharpFib (I := I) g x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          connLaplacianMixed (I := I) g 0 1 S.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  let w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞
      (fun y : M => Tensor0SSpace 1 I y) :=
    ContMDiffSection.mk
      (unitEvalSection (I := I) (M := M) g 1 S)
      (contMDiff_unitEvalSection (I := I) (M := M) g 1 S)
  rw [connLaplacian_vector_def, localConnLap_vector_def,
    connLaplacianMixed_def,
    rawTensorConnLap_eq_frame_trace_secondCovDeriv]
  rw [ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_unit_eval_genVal (I := I) (M := M) g 1 S
    (smoothOrthoFrame_smooth (I := I) g x i) x]
  simpa only [w, unitEvalSection] using
    sharp_second_eq (I := I) g w (smoothOrthoFrame_smooth (I := I) g x i) x

end Connection
end Integral
end DifferentialGeometry

end
