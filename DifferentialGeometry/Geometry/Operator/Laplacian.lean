import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.POUReduction


noncomputable section

open DifferentialGeometry.Integral.DivergenceTheorem
open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def Δ_g [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) : M → ℝ :=
  divergence_g (I := I) g (grad_g (I := I) g f)

@[simp] lemma Δ_g_def [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    Δ_g (I := I) g f x =
      divergence_g (I := I) g (grad_g (I := I) g f) x := rfl

theorem Δ_g_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g f) :=
  divergence_g_contMDiff (I := I) g (grad_g (I := I) g f)

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

lemma grad_g_add_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (f h : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    ((grad_g (I := I) g (f + h) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      ((grad_g (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      ((grad_g (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply, grad_g_apply, grad_g_apply]
  exact gradFun_add (I := I) g (f.contMDiff.mdifferentiable (by simp) x)
    (h.contMDiff.mdifferentiable (by simp) x)

theorem Δ_g_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (f h : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    Δ_g (I := I) g (f + h) x = Δ_g (I := I) g f x + Δ_g (I := I) g h x := by
  classical
  have hsection_eq : (grad_g (I := I) g (f + h) :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        (grad_g (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    ext y
    rw [ContMDiffSection.coe_add]
    change ((grad_g (I := I) g (f + h) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y) =
        ((grad_g (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y) +
          ((grad_g (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y)
    exact grad_g_add_apply (I := I) g f h y
  rw [Δ_g_def, Δ_g_def, Δ_g_def]
  rw [hsection_eq]
  exact divergence_g_add (I := I) g _ _ x

@[simp] lemma gradFun_const
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    gradFun (I := I) g (fun _ : M => c) x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero
  exact mfderiv_const

@[simp] theorem Δ_g_const [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    Δ_g (I := I) g (⟨fun _ : M => c, contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) x = 0 := by
  classical
  have hsection_eq : (grad_g (I := I) g
      (⟨fun _ : M => c, contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    ext y
    rw [grad_g_apply]
    change gradFun (I := I) g (fun _ : M => c) y = (0 : TangentSpace I y)
    exact gradFun_const (I := I) g c y
  rw [Δ_g_def, hsection_eq]
  exact divergence_g_zero (I := I) g x

end Operator
end Geometry
end DifferentialGeometry
