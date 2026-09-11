import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import DifferentialGeometry.Geometry.Metric.SmoothTangentScaling
import Mathlib.Analysis.SpecialFunctions.Sqrt



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def riemannianCurveUnitTangent (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  (riemannianCurveSpeed g γ t)⁻¹ • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1


theorem riemannianCurveSpeed_pos (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {t : ℝ} (ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    0 < riemannianCurveSpeed g γ t := Real.sqrt_pos.mpr (g.pos _ _ ht)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contDiffAt_riemannianCurveSpeed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    {t : ℝ} (ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    ContDiffAt ℝ ∞ (riemannianCurveSpeed g γ) t := by
  have hV : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)) :=
    contMDiffOn_univ.mp (contMDiffOn_source_partial isOpen_univ hγ.contMDiffOn (by simp) 1)
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun s => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (γ s)
        (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1))) t := by
    apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.contMDiffAt.comp t hγ.contMDiffAt
    · exact hV.contMDiffAt
    · exact hV.contMDiffAt
  exact (contMDiffAt_totalSpace.mp hs).2.contDiffAt.sqrt (ne_of_gt (g.pos _ _ ht))


theorem contDiff_riemannianCurveSpeed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    ContDiff ℝ ∞ (riemannianCurveSpeed g γ) :=
  contDiff_iff_contDiffAt.mpr (fun t => contDiffAt_riemannianCurveSpeed g hγ (hi t))



theorem contMDiff_riemannianCurveUnitTangent (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (γ t) (riemannianCurveUnitTangent g γ t)) := by
  have hV := contMDiffOn_univ.mp
    (contMDiffOn_source_partial isOpen_univ hγ.contMDiffOn (m := ∞) (by simp) 1)
  have hs := (contDiff_riemannianCurveSpeed g hγ hi).inv
    (fun t => ne_of_gt (riemannianCurveSpeed_pos g (hi t)))
  intro t
  exact contMDiffAt_tangent_smul hs.contMDiff.contMDiffAt hV.contMDiffAt


theorem riemannianCurveUnitTangent_inner_self (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {t : ℝ} (ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    g.inner (γ t) (riemannianCurveUnitTangent g γ t)
      (riemannianCurveUnitTangent g γ t) = 1 := by
  have hp := g.pos _ _ ht
  have hs := Real.sq_sqrt hp.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  simp only [riemannianCurveUnitTangent, riemannianCurveSpeed, map_smul,
    smul_apply, smul_eq_mul]
  field_simp [hn, hs]
  exact (div_eq_one_iff_eq (pow_ne_zero 2 hn)).mpr hs.symm

end DifferentialGeometry.Geometry
