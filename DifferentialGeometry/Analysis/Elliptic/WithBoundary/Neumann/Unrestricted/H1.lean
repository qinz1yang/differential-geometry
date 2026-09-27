import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.Unrestricted.SmoothScalar
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

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

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

abbrev UnrestrictedH1Compl (g : SmoothRiemannianMetric (I_half n) M) : Type _ :=
  UniformSpace.Completion (UnrestrictedSmoothScalar g)

noncomputable def smoothToUnrestrictedH1Compl
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedSmoothScalar g →L[ℝ] UnrestrictedH1Compl g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToUnrestrictedH1Compl_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : UnrestrictedSmoothScalar g) :
    smoothToUnrestrictedH1Compl g f = (f : UnrestrictedH1Compl g) := rfl

lemma UnrestrictedSmoothScalar.memLp_two
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def smoothToLpLinUnrestricted
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedSmoothScalar g →ₗ[ℝ]
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

@[simp] lemma smoothToLpLinUnrestricted_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : UnrestrictedSmoothScalar g) :
    smoothToLpLinUnrestricted g f = f.memLp_two.toLp f.toFun := rfl

lemma UnrestrictedSmoothScalar.norm_smoothToLp_sq
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    ‖smoothToLpLinUnrestricted g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLinUnrestricted g f)
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((smoothToLpLinUnrestricted g f : Lp ℝ 2 _) a)
          ((smoothToLpLinUnrestricted g f : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLinUnrestricted g f : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

lemma UnrestrictedSmoothScalar.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    ‖f‖ ^ 2 = unrestrictedSmoothScalarH1Inner f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [UnrestrictedSmoothScalar.inner_def] at h
  exact h.symm

lemma UnrestrictedSmoothScalar.norm_smoothToLp_sq_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    ‖smoothToLpLinUnrestricted g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold unrestrictedSmoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g f.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

lemma UnrestrictedSmoothScalar.norm_smoothToLp_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    ‖smoothToLpLinUnrestricted g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLinUnrestricted g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

lemma UnrestrictedSmoothScalar.norm_smoothToLp_le_one_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    ‖smoothToLpLinUnrestricted g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

noncomputable def smoothToLpUnrestricted
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedSmoothScalar g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (smoothToLpLinUnrestricted g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

@[simp] lemma smoothToLpUnrestricted_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : UnrestrictedSmoothScalar g) :
    smoothToLpUnrestricted g f = f.memLp_two.toLp f.toFun := rfl

private lemma denseRange_toComplL_fullSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (UniformSpace.Completion.toComplL :
      UnrestrictedSmoothScalar g →L[ℝ] UnrestrictedH1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL :
      UnrestrictedSmoothScalar g → UnrestrictedH1Compl g) =
      ((↑) : UnrestrictedSmoothScalar g →
        UniformSpace.Completion (UnrestrictedSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_toComplL_fullSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        UnrestrictedSmoothScalar g →L[ℝ] UnrestrictedH1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL :
      UnrestrictedSmoothScalar g → UnrestrictedH1Compl g) =
      ((↑) : UnrestrictedSmoothScalar g →
        UniformSpace.Completion (UnrestrictedSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (UnrestrictedSmoothScalar g)

noncomputable def unrestrictedH1ComplToLp
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedH1Compl g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLpUnrestricted g)
    (UniformSpace.Completion.toComplL :
      UnrestrictedSmoothScalar g →L[ℝ] UnrestrictedH1Compl g)

lemma unrestrictedH1ComplToLp_smoothToUnrestrictedH1Compl
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : UnrestrictedSmoothScalar g) :
    unrestrictedH1ComplToLp g (smoothToUnrestrictedH1Compl g f) =
      smoothToLpUnrestricted g f := by
  unfold unrestrictedH1ComplToLp
  exact ContinuousLinearMap.extend_eq (smoothToLpUnrestricted g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_fullSmoothScalar g)
    (isUniformInducing_toComplL_fullSmoothScalar g) f

noncomputable def unrestrictedH1ComplBilin
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedH1Compl g →L[ℝ] UnrestrictedH1Compl g →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma unrestrictedH1ComplBilin_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : UnrestrictedH1Compl g) :
    unrestrictedH1ComplBilin g u v = ⟪u, v⟫_ℝ := rfl

lemma unrestrictedH1ComplBilin_isCoercive
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCoercive (unrestrictedH1ComplBilin g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show unrestrictedH1ComplBilin g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

noncomputable def lpFunctionalCLMUnrestricted
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      (UnrestrictedH1Compl g →L[ℝ] ℝ) :=
  let applyL :
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (UnrestrictedH1Compl g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) →L[ℝ]
        (UnrestrictedH1Compl g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (UnrestrictedH1Compl g)
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) ℝ
  ((applyL.flip) (unrestrictedH1ComplToLp g)).comp
    (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ)

@[simp] lemma lpFunctionalCLMUnrestricted_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : UnrestrictedH1Compl g) :
    lpFunctionalCLMUnrestricted g f v =
      ⟪unrestrictedH1ComplToLp g v, f⟫_ℝ := by
  change (innerSL ℝ f) (unrestrictedH1ComplToLp g v) =
    ⟪unrestrictedH1ComplToLp g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (unrestrictedH1ComplToLp g v) f

noncomputable def unrestrictedH1ComplLaxMilgramEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    UnrestrictedH1Compl g ≃L[ℝ] UnrestrictedH1Compl g :=
  IsCoercive.continuousLinearEquivOfBilin
    (unrestrictedH1ComplBilin_isCoercive g)

@[simp] lemma unrestrictedH1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u w : UnrestrictedH1Compl g) :
    ⟪unrestrictedH1ComplLaxMilgramEquiv g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

noncomputable def unrestrictedH1ComplRieszRepr
    (g : SmoothRiemannianMetric (I_half n) M) :
    (UnrestrictedH1Compl g →L[ℝ] ℝ) →L[ℝ] UnrestrictedH1Compl g :=
  LinearMap.mkContinuous
    { toFun := fun φ =>
        (InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm φ
      map_add' := fun φ ψ =>
        (InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm φ‖
        ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm.norm_map φ))

lemma unrestrictedH1ComplRieszRepr_inner
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : UnrestrictedH1Compl g →L[ℝ] ℝ) (w : UnrestrictedH1Compl g) :
    ⟪unrestrictedH1ComplRieszRepr g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (UnrestrictedH1Compl g)).symm φ, w⟫_ℝ
    = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (E := UnrestrictedH1Compl g) (x := w) (y := φ)

noncomputable def unrestrictedNeumannResolvent
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      UnrestrictedH1Compl g :=
  (unrestrictedH1ComplRieszRepr g).comp (lpFunctionalCLMUnrestricted g)

theorem unrestrictedNeumannResolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : UnrestrictedH1Compl g) :
    ⟪unrestrictedNeumannResolvent g f, v⟫_ℝ =
      ⟪unrestrictedH1ComplToLp g v, f⟫_ℝ := by
  unfold unrestrictedNeumannResolvent
  rw [ContinuousLinearMap.comp_apply, unrestrictedH1ComplRieszRepr_inner,
    lpFunctionalCLMUnrestricted_apply]

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
