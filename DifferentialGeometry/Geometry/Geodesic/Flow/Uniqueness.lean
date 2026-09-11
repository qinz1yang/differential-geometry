import DifferentialGeometry.Analysis.ODE.Flow.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Flow.VectorField

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isMIntegralCurveOn_geodesicVectorFieldChart_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {K : Set ℝ}
    (hsrc : ∀ t ∈ K, (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) K ↔
      IsMIntegralCurveOn f (geodesicVectorField (I := I) g) K := by
  constructor <;> intro hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht

theorem isMIntegralCurveAt_geodesicVectorFieldChart_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hsrc : (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t ↔
      IsMIntegralCurveAt f (geodesicVectorField (I := I) g) t := by
  constructor <;> intro hf
  all_goals
    have hcont := (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp
      hf.continuousAt
    have hN : (fun u => (f u).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
      hcont.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hsrc)
    obtain ⟨K, hK, hfK⟩ := isMIntegralCurveAt_iff.mp hf
    refine isMIntegralCurveAt_iff.mpr ⟨K ∩ (fun u => (f u).proj) ⁻¹'
      (chartAt H α).source, inter_mem hK hN, ?_⟩
  · exact (isMIntegralCurveOn_geodesicVectorFieldChart_iff g α
      (fun _ hu => hu.2)).mp (hfK.mono inter_subset_left)
  · exact (isMIntegralCurveOn_geodesicVectorFieldChart_iff g α
      (fun _ hu => hu.2)).mpr (hfK.mono inter_subset_left)

theorem integralCurve_eqOn [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    {f₁ f₂ : ℝ → TangentBundle I M} {K : Set ℝ} {t₀ : ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hf₁ : IsMIntegralCurveOn f₁ (geodesicVectorField (I := I) g) K)
    (hf₂ : IsMIntegralCurveOn f₂ (geodesicVectorField (I := I) g) K)
    (heq : f₁ t₀ = f₂ t₀) : EqOn f₁ f₂ K :=
  isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless hK hconn ht₀
    ((contMDiff_geodesicVectorField g).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hf₁ hf₂ heq

end DifferentialGeometry.Geometry.Riemannian.Geodesic
