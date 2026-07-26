import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Pushforward of a vector field along a diffeomorphism

Defines `Diffeomorph.pushforward`, the pushforward of a tangent vector field through a
diffeomorphism, used throughout the pullback-naturality development.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff

noncomputable def Diffeomorph.pushforward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (W : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x :=
  fun x => Φ.apply_symm_apply x ▸ (mfderiv I I Φ (Φ.symm x)) (W (Φ.symm x))

/-- The pushforward of a vector field at the image of `x` is the manifold
derivative of the diffeomorphism applied to the field at `x`.  This is the
transport-free form used by time-dependent gauge equations. -/
theorem Diffeomorph.pushforward_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M) (W : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward Φ W (Φ x) =
      mfderiv I I (Φ : M → M) x (W x) := by
  change (Φ.apply_symm_apply (Φ x)) ▸
    (mfderiv I I (Φ : M → M) (Φ.symm (Φ x))) (W (Φ.symm (Φ x))) =
      mfderiv I I (Φ : M → M) x (W x)
  have hbase : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  refine eq_of_heq ?_
  refine (eqRec_heq (φ := fun z => TangentSpace I z)
    (Φ.apply_symm_apply (Φ x))
    ((mfderiv I I (Φ : M → M) (Φ.symm (Φ x)))
      (W (Φ.symm (Φ x))))).trans ?_
  rw [hbase]

/-- The derivative of a diffeomorphism followed by the derivative of its
inverse is the identity, in the order acting on a source tangent vector. -/
theorem Diffeomorph.mfderiv_symm_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (Φ.symm : M → M) (Φ x)
        (mfderiv I I (Φ : M → M) x v) = v := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hΦ : MDifferentiableAt I I (Φ : M → M) x :=
    Φ.mdifferentiable hn x
  have hΦsymm : MDifferentiableAt I I (Φ.symm : M → M) (Φ x) :=
    Φ.symm.mdifferentiable hn (Φ x)
  have hcomp : (Φ.symm : M → M) ∘ (Φ : M → M) = id := by
    funext z
    exact Φ.symm_apply_apply z
  have hchain := mfderiv_comp x hΦsymm hΦ
  rw [hcomp, mfderiv_id] at hchain
  have happ := congrArg
    (fun A : TangentSpace I x →L[ℝ] TangentSpace I x => A v) hchain.symm
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using happ

/-- The derivative of an inverse diffeomorphism followed by the derivative of
the original diffeomorphism is the identity, in the order acting on a target
tangent vector. -/
theorem Diffeomorph.mfderiv_self_symm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (w : TangentSpace I (Φ x)) :
    mfderiv I I (Φ : M → M) x
        (mfderiv I I (Φ.symm : M → M) (Φ x) w) = w := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hΦsymm : MDifferentiableAt I I (Φ.symm : M → M) (Φ x) :=
    Φ.symm.mdifferentiable hn (Φ x)
  have hΦ : MDifferentiableAt I I (Φ : M → M) (Φ.symm (Φ x)) := by
    rw [Φ.symm_apply_apply]
    exact Φ.mdifferentiable hn x
  have hcomp : (Φ : M → M) ∘ (Φ.symm : M → M) = id := by
    funext z
    exact Φ.apply_symm_apply z
  have hchain := mfderiv_comp (Φ x) hΦ hΦsymm
  rw [hcomp, mfderiv_id] at hchain
  have hbase : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  have hΦatx : mfderiv I I (Φ : M → M) (Φ.symm (Φ x)) =
      mfderiv I I (Φ : M → M) x := by
    rw [hbase]
  rw [hΦatx] at hchain
  have happ := congrArg
    (fun A : TangentSpace I (Φ x) →L[ℝ] TangentSpace I (Φ x) => A w)
    hchain.symm
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using happ

/-- Pushforward by the identity diffeomorphism fixes every vector field. -/
@[simp] theorem Diffeomorph.pushforward_refl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (W : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward (Diffeomorph.refl I M ∞) W x = W x := by
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply] using
    (Diffeomorph.pushforward_image (I := I)
      (Diffeomorph.refl I M ∞) W x)

end DifferentialGeometry.PDE.RicciFlow.Pullback
