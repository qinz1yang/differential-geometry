import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.NegativeDirection
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.Basic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

set_option autoImplicit false

open Set Filter Manifold Bundle
open scoped Topology Manifold ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem not_conj_of_min_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E)
    (hunit :
      g.inner p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u) = 1)
    (L : ℝ)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 L ≤
        arcLength (I := I) g η 0 L)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) L) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) := by
  classical
  let eP : TangentSpace I p ≃L[ℝ] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) p
  have huP : (show TangentSpace I p from u) = eP.symm u := by
    apply eP.injective
    rfl
  have hunitLegacy :
      g.inner p
        (show TangentSpace I p from u)
        (show TangentSpace I p from u) = 1 := by
    rw [huP]
    exact hunit
  intro hconj
  obtain ⟨z, hz, hJc_raw⟩ :=
    conjVec_jacobi_at (I := I) g hEnorm p u hc.1.ne' hconj
  let f : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + s • z) t
  let γ : ℝ → M := fun t => f 0 t
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) := by
    funext t
    simp only [γ, f, zero_smul, add_zero]
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s t) 0 (1 : ℝ)
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    have hvar := intrinsicVar_smooth (I := I) g hEnorm p u 0
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    have hcomp := hvar.comp hincl
    have heq :
        ((fun q : ℝ × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u + q.1 • (0 : E)) q.2) ∘
              fun t : ℝ => ((0 : ℝ), t)) = γ := by
      funext t
      simp only [γ, f, Function.comp_apply, zero_smul, add_zero]
    rw [← heq]
    exact hcomp
  have hgeo : IsGeodesic (I := I) g γ := by
    simpa only [γ, f, zero_smul, add_zero] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u)
  have hf_infty :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => f q.1 q.2) := by
    simpa only [f] using
      intrinsicVar_smooth (I := I) g hEnorm p u z
  have hJ_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)) := by
    simpa only [γ, J] using
      varField_smooth (I := I) f hf_infty
  have hJacobian : IsJacobiAlong (I := I) g γ J := by
    rw [hγ]
    simpa only [J, f] using
      intrinsic_jacobi (I := I) g hEnorm p u z
  have hJ0 : J 0 = 0 := by
    simpa only [γ, f, J, zero_smul, add_zero] using
      jacobiVar_zero (I := I) g hEnorm p u z
  have hJc : J c = 0 := by
    simpa only [γ, f, J] using hJc_raw
  have hunit0 :
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1 := by
    have hγ0 : γ 0 = p := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = u := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    rw [hγ0]
    change g.inner p
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1
    rw [hvel0]
    exact hunitLegacy
  have hDJ0 : (DJ 0 : E) = z := by
    change (covDerivAlong (I := I) g γ J 0 : E) = z
    have hcurve_ev :
        γ =ᶠ[𝓝 (0 : ℝ)]
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u) :=
      Filter.Eventually.of_forall fun t => congrFun hγ t
    have hfield_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
        (J t : E) =
          (show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ) : E) := by
      filter_upwards with t
      rfl
    have htransport :=
      covDerivAlong_congr_curve (I := I) g J
        (fun t : ℝ =>
          show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ))
        hcurve_ev hfield_ev
    exact htransport.trans
      (intrinsic_jacobi_d0 (I := I) g hEnorm p u z)
  have hDJ0_ne : DJ 0 ≠ 0 := by
    intro hzero
    apply hz
    rw [← hDJ0]
    exact hzero
  have hminγ :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
        η 0 = γ 0 → η L = γ L →
        arcLength (I := I) g γ 0 L ≤
          arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    have hη0' : η 0 = p := hη0.trans (by
      rw [hγ]
      exact intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u))
    have hηL' :
        η L = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) L := hηL.trans (by rw [hγ])
    simpa only [hγ] using hmin η hη hη0' hηL'
  exact jacobi_field_ne_zero_of_minimising_geodesic (I := I) g γ J
    hγ_smooth hJ_bundle.contMDiffOn isOpen_univ (subset_univ _)
    (hgeo.isGeodesicOn (Icc 0 L)) (fun t _ => hJacobian t)
    hunit0 hminγ hc hJ0 hDJ0_ne hJc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem not_conj_of_min
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E)
    (hunit :
      g.inner p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u) = 1)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 1) →
      η 0 = p →
      η 1 = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) 1 →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 1 ≤
        arcLength (I := I) g η 0 1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) :=
  not_conj_of_min_len (I := I) g hEnorm p u hunit 1
    hmin hc

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
