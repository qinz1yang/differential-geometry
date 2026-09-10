import DifferentialGeometry.Geometry.Comparison.Variation.TwistedExponential
import DifferentialGeometry.Geometry.Comparison.Variation.LocalSecondVariation
import DifferentialGeometry.Geometry.Curvature.Positive

noncomputable section
open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open Poincare.Geometry

namespace Poincare.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_negative_twisted_variation_of_parallel_normal_field
    (g : SmoothRiemannianMetric I M) (hsec : HasPositiveSectionalCurvature g)
    (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (γ : ℝ → M) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hg : IsGeodesicOn (I := I) g γ (Icc 0 L)) (htw : γ L = F (γ 0))
    (W : ∀ t, TangentSpace I (γ t))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨γ t, W t⟩ : TangentBundle I M)) (Ioo (-δ) (L + δ)))
    (hpar : ∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ W t = 0)
    (hunit : ∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (W t) (W t) = 1)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (horth : ∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (W t) = 0)
    (hWL : (W L : E) = (mfderiv I I F (γ 0) (W 0) : E)) :
    ∃ f : ℝ × ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f (univ ×ˢ Ioo (-δ) (L + δ)) ∧
      (fun t => f (0, t)) = γ ∧ (∀ s, f (s, L) = F (f (s, 0))) ∧
      deriv (deriv (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L)) 0 < 0 := by
  obtain ⟨f, hf, hc, ht, hv, hrad⟩ :=
    exists_twisted_variation_of_field g F hF γ W isOpen_Ioo hW L htw hWL
  have hc' : (fun t => f (0, t)) = γ := funext hc
  refine ⟨f, hf, hc', ht, ?_⟩
  have hparf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g (fun u => f (0, u))
        (centralVariationField (I := I) (Function.curry f)) t = 0 := by
    have hh := covDerivAlong_congr_curve g (t := t)
      (centralVariationField (I := I) (Function.curry f)) W
      (Filter.Eventually.of_forall hc) (Filter.Eventually.of_forall hv)
    exact hh.trans (hpar t ht)
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      0 < centralCurvatureDensity (I := I) g (Function.curry f) t := by
    have ho : g.inner (γ t) (W t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 0 :=
      (g.symm _ _ _).trans (horth t ht)
    have hh := riemann_contraction_pos_of_orthonormal g hsec (γ t) (W t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (hunit t ht) (hspeed t ht) ho
    unfold centralCurvatureDensity centralVariationField centralVelocity
    unfold DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationField
      DifferentialGeometry.Geometry.Riemannian.Variation.centralVelocity
    dsimp only [Function.curry]
    erw [hc', hc, hv]
    exact hh
  apply secondVariation_curveEnergy_neg_of_parallel_geodesicEndpoints_local g f hL
    (isOpen_univ.prod isOpen_Ioo) (fun p hp => ⟨mem_univ _, ?_⟩) hf
    (by rw [hc']; exact hg) ((hrad 0).isGeodesicOn univ 0 (mem_univ _))
    ((hrad L).isGeodesicOn univ 0 (mem_univ _)) hparf hpos
  constructor <;> linarith [hp.2.1, hp.2.2]

end Poincare.Geometry.Riemannian.Variation
