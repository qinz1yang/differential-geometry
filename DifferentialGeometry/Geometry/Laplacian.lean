import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction

/-!
# The Laplace–Beltrami operator on a Riemannian manifold

For a smooth Riemannian metric `g` on a smooth manifold `M` (without boundary)
and a smooth scalar function `f : M → ℝ`, the Laplace–Beltrami operator is
defined as the metric divergence of the gradient,
$$\Delta_g f := \operatorname{div}_g(\nabla_g f).$$

This file defines `Δ_g g hf` (where `hf` is a smoothness witness for `f`) as a
smooth real-valued function on `M`, and establishes basic algebraic properties
(linearity, behaviour on constants).

## Main definitions

* `Δ_g g hf` : the Laplacian of a smooth scalar function as a smooth scalar
  function.

## Main results

* `Δ_g_contMDiff` : smoothness of the Laplacian.
* `Δ_g_add` : linearity of the Laplacian on the sum of smooth functions.

## Sign convention

The geometer convention `Δ = div ∘ grad` is used throughout. With this
convention the Laplacian is a non-positive operator on a closed manifold, so the
spectrum lies in `(-∞, 0]`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The Laplace–Beltrami operator of a smooth scalar function `f` (with
smoothness proof `hf`), defined as the metric divergence of the gradient. -/
def Δ_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  divergence_g (I := I) g (grad_g (I := I) g hf)

@[simp] lemma Δ_g_def [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g hf x =
      divergence_g (I := I) g (grad_g (I := I) g hf) x := rfl

/-- The Laplacian is `C^∞`. -/
theorem Δ_g_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
  divergence_g_contMDiff (I := I) g (grad_g (I := I) g hf)

/-- The pointwise gradient of a sum of differentiable functions is the sum of the
gradients. -/
lemma gradFun_add
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (f + h) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradFun (I := I) g (f + h) x) v =
    g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v
  rw [inner_gradFun (I := I) g (f + h) x v]
  set d : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (f + h) x with hd_def
  set d_f : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hd_f_def
  set d_h : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) h x with hd_h_def
  have hsum : d = d_f + d_h := by
    have hAddDeriv : HasMFDerivAt I 𝓘(ℝ, ℝ) (f + h) x (d_f + d_h) := by
      have hHaf : HasMFDerivAt I 𝓘(ℝ, ℝ) f x d_f := by
        rw [hd_f_def]; exact hf.hasMFDerivAt
      have hHah : HasMFDerivAt I 𝓘(ℝ, ℝ) h x d_h := by
        rw [hd_h_def]; exact hh.hasMFDerivAt
      exact hHaf.add hHah
    rw [hd_def]
    exact hAddDeriv.mfderiv
  change d v = g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v
  rw [hsum, ContinuousLinearMap.add_apply]
  rw [map_add, ContinuousLinearMap.add_apply]
  congr 1
  · rw [hd_f_def]; exact (inner_gradFun (I := I) g f x v).symm
  · rw [hd_h_def]; exact (inner_gradFun (I := I) g h x v).symm

/-- For smooth `f` and `h`, the gradient section of `f + h` agrees pointwise with
the sum of the gradient sections. -/
lemma grad_g_add_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    ((grad_g (I := I) g (hf.add hh) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply, grad_g_apply, grad_g_apply]
  exact gradFun_add (I := I) g (hf.mdifferentiable (by simp) x)
    (hh.mdifferentiable (by simp) x)

/-- The Laplacian of a sum of smooth functions equals the sum of the Laplacians. -/
theorem Δ_g_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    Δ_g (I := I) g (hf.add hh) x = Δ_g (I := I) g hf x + Δ_g (I := I) g hh x := by
  classical
  have hsection_eq : (grad_g (I := I) g (hf.add hh) :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        (grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    ext y
    rw [ContMDiffSection.coe_add]
    change ((grad_g (I := I) g (hf.add hh) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y) =
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y) +
          ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y)
    exact grad_g_add_apply (I := I) g hf hh y
  rw [Δ_g_def, Δ_g_def, Δ_g_def]
  rw [hsection_eq]
  exact divergence_g_add (I := I) g _ _ x

/-- The gradient of a constant function vanishes. -/
@[simp] lemma gradFun_const
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    gradFun (I := I) g (fun _ : M => c) x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero
  exact mfderiv_const

/-- The Laplacian of a constant function vanishes. -/
@[simp] theorem Δ_g_const [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    Δ_g (I := I) g (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) x = 0 := by
  classical
  have hsection_eq : (grad_g (I := I) g
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    ext y
    rw [grad_g_apply]
    change gradFun (I := I) g (fun _ : M => c) y = (0 : TangentSpace I y)
    exact gradFun_const (I := I) g c y
  rw [Δ_g_def, hsection_eq]
  exact divergence_g_zero (I := I) g x

end DivergenceTheorem
end Integral
end DifferentialGeometry
