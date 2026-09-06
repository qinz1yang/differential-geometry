import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import Mathlib.Analysis.Convex.Deriv


open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian


open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem deriv_comp_eq_inner_grad_velocity
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    deriv (f ∘ γ) t =
      g.inner (γ t) (gradFun (I := I) g f (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hγmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    hγ.contMDiffAt.mdifferentiableAt (by simp)
  let e : TangentSpace 𝓘(ℝ, ℝ) t :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1
  have he : e = (1 : TangentSpace 𝓘(ℝ, ℝ) t) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).injective
    simp only [e, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hd : deriv (f ∘ γ) t = mvfderiv 𝓘(ℝ, ℝ) (f ∘ γ) t e := by
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    change deriv (f ∘ γ) t =
      fderiv ℝ (f ∘ γ) t (NormedSpace.fromTangentSpace (𝕜 := ℝ) t e)
    rw [show NormedSpace.fromTangentSpace (𝕜 := ℝ) t e = 1 by
      exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).apply_symm_apply 1,
      fderiv_apply_one_eq_deriv]
  rw [hd, mvfderiv_comp_apply t hfmd hγmd e, he]
  exact (gradFun_metricDual (I := I) g f (γ t)
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)).symm

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv2_comp_geo_at
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} (hgeo : HasGeodesicEquationAt (I := I) g γ t) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  rw [hessFun_eq_abstract g hf]
  have h1 : (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1 =
      (1 : TangentSpace 𝓘(ℝ, ℝ) t) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  simpa only [iteratedDeriv_eq_iterate, h1] using
    (abstractHessian_apply_velocity_of_hasGeodesicEquationAt g
    (hf.contMDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hγ.contMDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (BoundarylessManifold.isInteriorPoint (I := I)) hgeo).symm


omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv2_comp_geo
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) (t : ℝ) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) :=
  deriv2_comp_geo_at (I := I) g hf hγ (hgeo t)

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv2_geo_on_at
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} (hgeo : HasGeodesicEquationAt (I := I) g γ t)
    (ht : γ t ∈ U) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU ht hf
  have hcomp : (F ∘ γ) =ᶠ[𝓝 t] (f ∘ γ) :=
    hγ.continuous.continuousAt.eventually hFf
  calc
    (deriv^[2] (f ∘ γ)) t = (deriv^[2] (F ∘ γ)) t := by
      exact Filter.EventuallyEq.deriv_eq hcomp.symm.deriv
    _ = hessFun (I := I) g F (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) :=
      deriv2_comp_geo_at (I := I) g hF hγ hgeo
    _ = hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
      rw [hessFun_congr (I := I) g hFf]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv2_comp_geo_on
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {t : ℝ} (ht : γ t ∈ U) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) :=
  deriv2_geo_on_at (I := I) g hU hf hγ (hgeo t) ht

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem strictConvex_geo_on
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {D : Set ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (interior D))
    (hD : Convex ℝ D)
    (hcont : ContinuousOn (f ∘ γ) D)
    (hmem : MapsTo γ (interior D) U)
    (hpos : ∀ t ∈ interior D,
      0 < hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)) :
    StrictConvexOn ℝ D (f ∘ γ) := by
  apply strictConvexOn_of_deriv2_pos hD hcont
  intro t ht
  rw [deriv2_geo_on_at (I := I) g hU hf hγ (hgeo t ht) (hmem ht)]
  exact hpos t ht

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem strictConvex_geo
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {D : Set ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn (f ∘ γ) D)
    (hmem : MapsTo γ (interior D) U)
    (hpos : ∀ t ∈ interior D,
      0 < hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)) :
    StrictConvexOn ℝ D (f ∘ γ) :=
  strictConvex_geo_on (I := I) g hU hf hγ
    (fun t _ => hgeo t) hD hcont hmem hpos

end Riemannian
end Geometry
end DifferentialGeometry
