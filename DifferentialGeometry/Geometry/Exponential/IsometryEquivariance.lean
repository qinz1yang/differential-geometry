import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackCross

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
theorem pullbackMetric_eq_of_inner (g : SmoothRiemannianMetric I M) (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w) :
    Diffeomorph.pullbackMetricCross g F = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [Diffeomorph.pullbackMetricCross_inner]
  exact hF p v w

theorem isGeodesic_comp_isometry (g : SmoothRiemannianMetric I M) (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hg : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun t => F (γ t)) := by
  apply geodesic_mapCross g F γ hγ
  rwa [pullbackMetric_eq_of_inner g F hF]

variable [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expMapIntrinsic_isometry
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (p : M) (v : TangentSpace I p) :
    F (expMapIntrinsic (I := I) g hEnorm p v) =
      expMapIntrinsic (I := I) g hEnorm (F p) (mfderiv I I F p v) := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p v
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm p v
  have hg : IsGeodesic (I := I) g γ := intrinsicGeodesic_isGeodesic g hEnorm p v
  have h0 : γ 0 = p := intrinsicGeodesic_zero g hEnorm p v
  have hv : (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero g hEnorm p v
  apply geo_end_eq_intr g hEnorm (F p) (mfderiv I I F p v)
    (Γ := fun t => F (γ t)) (F.continuous.comp hγ.continuous).continuousOn
    ((isGeodesic_comp_isometry g F hF γ hγ hg).isGeodesicOn _) (congrArg F h0)
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
    (g := (F : M → M)) (f := γ) (x := 0)
    (F.contMDiff.mdifferentiable (by simp) (γ 0)) (hγ.mdifferentiable (by simp) 0) (1 : ℝ)
  have heq : (mfderiv 𝓘(ℝ, ℝ) I (fun t => F (γ t)) 0 1 : E) =
      (mfderiv I I F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) : E) := by
    exact hcomp
  erw [heq, hv, h0]

end DifferentialGeometry.Geometry.Riemannian.Exponential
