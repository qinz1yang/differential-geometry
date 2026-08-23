import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.Pullback

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

noncomputable def Diffeomorph.pushforward
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (W : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x :=
  fun x => Φ.apply_symm_apply x ▸ (mfderiv I I Φ (Φ.symm x)) (W (Φ.symm x))

theorem Diffeomorph.pushforward_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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

theorem Diffeomorph.mfderiv_symm_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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

theorem Diffeomorph.mfderiv_self_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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

@[simp] theorem Diffeomorph.pushforward_refl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (W : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward (Diffeomorph.refl I M ∞) W x = W x := by
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply] using
    (Diffeomorph.pushforward_image (I := I)
      (Diffeomorph.refl I M ∞) W x)

theorem Diffeomorph.pushforward_eq_mpullback_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x) =
      (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  have hinv :
      (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable (by simp) _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        rw [Φ.apply_symm_apply]
        exact Φ.symm.mdifferentiable (by simp) z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w
        exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      rw [Φ.apply_symm_apply] at hchain
      exact hchain.symm
    · have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable (by simp) z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable (by simp) _
      have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
        funext w
        exact Φ.apply_symm_apply w
      have hchain := mfderiv_comp z hΦ hΦsymm
      rw [hcomp, mfderiv_id] at hchain
      exact hchain.symm
  change (Φ.apply_symm_apply z) ▸
      (mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z)) =
    (mfderiv I I (⇑Φ.symm) z).inverse (Y (Φ.symm z))
  rw [hinv]
  refine eq_of_heq ?_
  exact eqRec_heq (φ := fun w => TangentSpace I w) (Φ.apply_symm_apply z)
    ((mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z)))

theorem Diffeomorph.pushforward_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M) {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (Diffeomorph.pushforward Φ Y)) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [Diffeomorph.pushforward_eq_mpullback_symm (I := I) Φ Y]
  have hinv : ∀ x, (mfderiv I I (⇑Φ.symm) x).IsInvertible := by
    intro x
    refine ⟨Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm (by simp) x, ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (Φ := Φ.symm) (x := x) (by simp)
  exact ContMDiff.mpullback_vectorField (I := I) (I' := I) (V := Y)
    (f := ⇑Φ.symm) (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
    hY Φ.symm.contMDiff hinv (by simp)

end DifferentialGeometry
