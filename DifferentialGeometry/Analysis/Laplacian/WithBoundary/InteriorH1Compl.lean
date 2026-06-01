import DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalarPreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# H¹ Hilbert space and L² inclusion for interior-supported smooth scalars
(with-boundary, half-space model)

The Hausdorff completion of `InteriorSmoothScalar g` (the pre-Hilbert space of
interior-supported smooth real-valued functions on a closed Riemannian
manifold-with-boundary `(M, g)` modelled on `EuclideanHalfSpace n`) carries
the canonical Hilbert-space structure. We package:

* `H1ComplInterior g`: the completion, a real Hilbert space.
* `smoothToH1ComplInterior`: the canonical embedding `InteriorSmoothScalar g
  →L[ℝ] H1ComplInterior g`.
* `smoothToLpInterior`: the L² inclusion `InteriorSmoothScalar g →L[ℝ]
  Lp ℝ 2 μ_g`.
* `H1ComplInteriorToLp`: the unique continuous linear extension of
  `smoothToLpInterior` along `smoothToH1ComplInterior`, i.e. the H¹ → L²
  inclusion.

This shared infrastructure is then used to build the with-boundary Neumann
and Dirichlet variants of the variational Laplacian. Both variants restrict
the test-function space to the interior-supported smooth functions; under
this restriction, the boundary terms in Green's identities vanish, and the
smooth bridge reduces to the boundaryless case.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Local abbreviation for the canonical Euclidean half-space model. -/
private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The H¹ Hilbert space for interior-supported smooth functions on `(M, g)`,
defined as the Hausdorff completion of the pre-Hilbert space
`InteriorSmoothScalar g`. -/
abbrev H1ComplInterior (g : SmoothRiemannianMetric (I_half n) M) : Type _ :=
  UniformSpace.Completion (InteriorSmoothScalar g)

/-- The canonical embedding `InteriorSmoothScalar g →L[ℝ] H1ComplInterior g`. -/
noncomputable def smoothToH1ComplInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →L[ℝ] H1ComplInterior g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToH1ComplInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToH1ComplInterior g f = (f : H1ComplInterior g) := rfl

/-- An interior-supported smooth scalar function on a closed
manifold-with-boundary lies in `MemLp 2`: it is continuous and supported in
a compact set (since `M` itself is compact). -/
lemma InteriorSmoothScalar.memLp_two
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The linear map from interior-supported smooth scalars to `Lp ℝ 2 μ_g`. -/
noncomputable def smoothToLpLinInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) where
  toFun f := f.memLp_two.toLp f.toFun
  map_add' f h := by
    have h_lhs_rfl : (f + h).memLp_two.toLp (f + h).toFun =
        (f.memLp_two.add h.memLp_two).toLp (f.toFun + h.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_add]
  map_smul' c f := by
    have h_lhs_rfl : (c • f).memLp_two.toLp (c • f).toFun =
        (f.memLp_two.const_smul c).toLp (c • f.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_const_smul]
    rfl

@[simp] lemma smoothToLpLinInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToLpLinInterior g f = f.memLp_two.toLp f.toFun := rfl

lemma InteriorSmoothScalar.norm_smoothToLp_sq
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLinInterior g f)
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((smoothToLpLinInterior g f : Lp ℝ 2 _) a)
          ((smoothToLpLinInterior g f : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLinInterior g f : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

/-- The squared seminorm of an interior-supported smooth scalar in pre-H¹
equals the H¹ self-pairing. -/
lemma InteriorSmoothScalar.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖f‖ ^ 2 = interiorSmoothScalarH1Inner f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [InteriorSmoothScalar.inner_def] at h
  exact h.symm

/-- Squared L² norm is bounded by the squared pre-H¹ norm. -/
lemma InteriorSmoothScalar.norm_smoothToLp_sq_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold interiorSmoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x ((grad_g_with_boundary_section
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((grad_g_with_boundary_section
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

/-- L²-norm of the smooth-inclusion is bounded by the pre-H¹ norm. -/
lemma InteriorSmoothScalar.norm_smoothToLp_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLinInterior g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

lemma InteriorSmoothScalar.norm_smoothToLp_le_one_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

/-- The continuous linear map from interior-supported smooth scalars to
`Lp ℝ 2 μ_g`. -/
noncomputable def smoothToLpInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (smoothToLpLinInterior g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

@[simp] lemma smoothToLpInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToLpInterior g f = f.memLp_two.toLp f.toFun := rfl

private lemma denseRange_toComplL_interiorSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g →L[ℝ] H1ComplInterior g) := by
  rw [show (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g → H1ComplInterior g) =
      ((↑) : InteriorSmoothScalar g →
        UniformSpace.Completion (InteriorSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_toComplL_interiorSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        InteriorSmoothScalar g →L[ℝ] H1ComplInterior g) := by
  rw [show (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g → H1ComplInterior g) =
      ((↑) : InteriorSmoothScalar g →
        UniformSpace.Completion (InteriorSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (InteriorSmoothScalar g)

/-- The continuous linear extension of `smoothToLpInterior` along the dense
embedding `smoothToH1ComplInterior`. -/
noncomputable def H1ComplInteriorToLp
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLpInterior g)
    (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g →L[ℝ] H1ComplInterior g)

@[simp] lemma H1ComplInteriorToLp_smoothToH1ComplInterior
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    H1ComplInteriorToLp g (smoothToH1ComplInterior g f) =
      smoothToLpInterior g f := by
  unfold H1ComplInteriorToLp
  exact ContinuousLinearMap.extend_eq (smoothToLpInterior g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_interiorSmoothScalar g)
    (isUniformInducing_toComplL_interiorSmoothScalar g) f

example (g : SmoothRiemannianMetric (I_half n) M) : Type _ := H1ComplInterior g

example (g : SmoothRiemannianMetric (I_half n) M) :
    NormedAddCommGroup (H1ComplInterior g) := inferInstance

example (g : SmoothRiemannianMetric (I_half n) M) :
    InnerProductSpace ℝ (H1ComplInterior g) := inferInstance

example (g : SmoothRiemannianMetric (I_half n) M) :
    CompleteSpace (H1ComplInterior g) := inferInstance

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
