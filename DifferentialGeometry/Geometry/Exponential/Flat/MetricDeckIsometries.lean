import DifferentialGeometry.Geometry.Exponential.Flat.DeckTranslation

/-!
# Actual deck isometries of a metric local diffeomorphism

The pullback metric identity and the exact deck square force each actual deck differential to
preserve the Euclidean norm. The mean value theorem for a deck map and its inverse then gives
its global isometry property. This converts geometric differential data into the metric input
of the actual affine deck-action construction.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V]
  {E : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  {H : Type*} [instH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [instM : TopologicalSpace M] [instCM : ChartedSpace H M]
  [instMF : IsManifold I ∞ M]

private theorem metric_deck_derivative_norm (g : SmoothRiemannianMetric I M) (p : V → M)
    (hp : IsLocalDiffeomorph 𝓘(ℝ, V) I ∞ p)
    (hmetric : ∀ (x v w : V), g.inner (p x) (mfderiv 𝓘(ℝ, V) I p x v)
      (mfderiv 𝓘(ℝ, V) I p x w) = inner ℝ v w)
    (γ : coveringDeckGroup p) (x v : V) :
    ‖fderiv ℝ (γ.1 : V → V) x v‖ = ‖v‖ := by
  have hγ := coveringDeckGroup_contMDiff hp γ
  have hcomp : p ∘ (fun y : V => γ • y) = p := funext (coveringDeckGroup_map γ)
  have hchain : mfderiv 𝓘(ℝ, V) I p (γ • x)
      (fderiv ℝ (γ.1 : V → V) x v) = mfderiv 𝓘(ℝ, V) I p x v := by
    have h := mfderiv_comp x ((hp.contMDiff (γ • x)).mdifferentiableAt (by simp))
      ((hγ x).mdifferentiableAt (by simp))
    rw [hcomp] at h
    rw [h]
    have hdf : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (fun y : V => γ • y) x v =
        fderiv ℝ (γ.1 : V → V) x v := by
      have hd := congrArg
        (fun D : TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, V) (γ • x) => D v)
        (mfderiv_eq_fderiv (f := fun y : V => γ • y) (x := x))
      exact hd
    exact congrArg (mfderiv 𝓘(ℝ, V) I p (γ • x)) hdf.symm
  have hkey : ∀ (a b : M) (u v w z : E), a = b → u = w → v = z →
      g.inner a u v = g.inner b w z := by
    rintro a b u v w z rfl rfl rfl
    rfl
  have hinner : inner ℝ (fderiv ℝ (γ.1 : V → V) x v)
      (fderiv ℝ (γ.1 : V → V) x v) = inner ℝ v v := by
    calc
      inner ℝ (fderiv ℝ (γ.1 : V → V) x v) (fderiv ℝ (γ.1 : V → V) x v) =
          g.inner (p (γ • x))
            (mfderiv 𝓘(ℝ, V) I p (γ • x) (fderiv ℝ (γ.1 : V → V) x v))
            (mfderiv 𝓘(ℝ, V) I p (γ • x) (fderiv ℝ (γ.1 : V → V) x v)) :=
        (hmetric (γ • x) _ _).symm
      _ = g.inner (p x) (mfderiv 𝓘(ℝ, V) I p x v) (mfderiv 𝓘(ℝ, V) I p x v) := by
        exact hkey _ _ _ _ _ _ (coveringDeckGroup_map γ x) hchain hchain
      _ = inner ℝ v v := hmetric x v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hinner

theorem deck_isometry_of_metric_derivative (g : SmoothRiemannianMetric I M) (p : V → M)
    (hp : IsLocalDiffeomorph 𝓘(ℝ, V) I ∞ p)
    (hmetric : ∀ (x v w : V), g.inner (p x) (mfderiv 𝓘(ℝ, V) I p x v)
      (mfderiv 𝓘(ℝ, V) I p x w) = inner ℝ v w)
    (γ : coveringDeckGroup p) : Isometry (γ.1 : V → V) := by
  have hd (δ : coveringDeckGroup p) : Differentiable ℝ (δ.1 : V → V) :=
    (contMDiff_iff_contDiff.mp (coveringDeckGroup_contMDiff hp δ)).differentiable (by simp)
  apply isometry_of_fderiv_norm_le γ.1 (hd γ)
    (fun x v => (metric_deck_derivative_norm g p hp hmetric γ x v).le) (hd γ⁻¹)
  intro x v
  exact (metric_deck_derivative_norm g p hp hmetric γ⁻¹ x v).le

end DifferentialGeometry.Geometry.FlatSurface
