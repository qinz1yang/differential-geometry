import DifferentialGeometry.Geometry.Metric.CurveUnitTangent
import DifferentialGeometry.Geometry.Connection.SectionAlongRegularity
import DifferentialGeometry.Geometry.Connection.SectionAlongSmooth
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def riemannianCurveCurvature (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  (riemannianCurveSpeed g γ t)⁻¹ •
    covDerivAlong g γ (riemannianCurveUnitTangent g γ) t



theorem contMDiff_riemannianCurveCurvature (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (γ t) (riemannianCurveCurvature g γ t)) := by
  have hD := contMDiff_covDerivAlong g (contMDiff_riemannianCurveUnitTangent g hγ hi)
  have hs := (contDiff_riemannianCurveSpeed g hγ hi).inv
    (fun t => ne_of_gt (riemannianCurveSpeed_pos g (hi t)))
  intro t
  exact contMDiffAt_tangent_smul hs.contMDiff.contMDiffAt hD.contMDiffAt



theorem riemannianCurveCurvature_orthogonal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) (t : ℝ) :
    g.inner (γ t) (riemannianCurveCurvature g γ t) (riemannianCurveUnitTangent g γ t) = 0 := by
  have hT := contMDiff_riemannianCurveUnitTangent g hγ hi
  have hr := (contDiffAt_chartRepAt_of_section (hT.contMDiffAt (x := t))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hd := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g γ
    (riemannianCurveUnitTangent g γ) (riemannianCurveUnitTangent g γ) t hγ.contMDiffAt hr hr
  have heq : (fun s => g.inner (γ s) (riemannianCurveUnitTangent g γ s)
      (riemannianCurveUnitTangent g γ s)) = fun _ => (1 : ℝ) :=
    funext (fun s => riemannianCurveUnitTangent_inner_self g (hi s))
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : ℝ))
  rw [g.symm (γ t) (riemannianCurveUnitTangent g γ t)] at hz
  have hzero : g.inner (γ t)
      (covDerivAlong g γ (riemannianCurveUnitTangent g γ) t)
      (riemannianCurveUnitTangent g γ t) = 0 := by linarith
  simp only [riemannianCurveCurvature, map_smul, smul_apply, smul_eq_mul, hzero, mul_zero]




theorem riemannianCurveCurvature_inner_normal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    {t : ℝ} (ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0)
    (N : TangentSpace 𝓘(ℝ, E) (γ t))
    (hN : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) N = 0) :
    g.inner (γ t) (riemannianCurveCurvature g γ t) N =
      g.inner (γ t) (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t) N /
        riemannianCurveSpeed g γ t ^ 2 := by
  have hV := contMDiffOn_univ.mp
    (contMDiffOn_source_partial isOpen_univ hγ.contMDiffOn (m := ∞) (by simp) 1)
  have hr := (contDiffAt_chartRepAt_of_section (hV.contMDiffAt (x := t))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hs := (contDiffAt_riemannianCurveSpeed g hγ ht).inv
    (ne_of_gt (riemannianCurveSpeed_pos g ht))
  unfold riemannianCurveCurvature riemannianCurveUnitTangent
  erw [covDerivAlong_smulFun g γ (fun s => (riemannianCurveSpeed g γ s)⁻¹)
    (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t (hs.differentiableAt (by simp)) hr]
  simp only [map_smul, smul_apply, smul_eq_mul, map_add, add_apply, hN, mul_zero, zero_add]
  ring

end DifferentialGeometry.Geometry
