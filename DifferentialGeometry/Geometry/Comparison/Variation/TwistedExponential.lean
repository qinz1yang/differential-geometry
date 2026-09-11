import DifferentialGeometry.Geometry.Comparison.Variation.IntrinsicExponential
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointInterpolation
import DifferentialGeometry.Geometry.Geodesic.CompactDisplacement

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_twisted_endpoint_variation (g : SmoothRiemannianMetric I M)
    (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (htw : γ L = F (γ 0)) (v : TangentSpace I (γ 0)) :
    ∃ (δ : ℝ) (f : ℝ × ℝ → M), 0 < δ ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f (univ ×ˢ Ioo (-δ) (L + δ)) ∧
      (∀ t, f (0, t) = γ t) ∧
      (∀ s, f (s, L) = F (f (s, 0))) ∧
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, 0)) 0 1 : E) = (v : E) ∧
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, L)) 0 1 : E) =
        (mfderiv I I F (γ 0) v : E) ∧
      (∀ t, IsGeodesic (I := I) g (fun s => f (s, t))) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun p w => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g p w
  let D : TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ L) :=
    (mfderiv I I F (γ 0)).toLinearMap
  obtain ⟨δ, W, hδ, hW, hW0, hWL, _⟩ :=
    exists_smooth_endpoint_interpolation g γ hγ hL D v
  let f : ℝ × ℝ → M := fun p => expMapIntrinsic (I := I) g hEnorm (γ p.2) (p.1 • W p.2)
  have hrad := intrinsicExpVariation_radial g hEnorm γ W
  refine ⟨δ, f, hδ, ?_, fun t => (hrad t).2.1, ?_, ?_, ?_, fun t => (hrad t).1⟩
  · have hs := intrinsicExpVariation_contMDiffOn g hEnorm γ W isOpen_Ioo hW
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hs
    exact hs
  · intro s
    apply intrinsicExpVariation_twisted g hEnorm F hF γ W L htw
    exact hWL.trans (congrArg D hW0.symm)
  · exact (hrad 0).2.2.trans hW0
  · exact (hrad L).2.2.trans hWL

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_twisted_variation_of_field (g : SmoothRiemannianMetric I M)
    (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (γ : ℝ → M) (W : ∀ t, TangentSpace I (γ t)) {U : Set ℝ} (hU : IsOpen U)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨γ t, W t⟩ : TangentBundle I M)) U) (L : ℝ)
    (htw : γ L = F (γ 0))
    (hWL : (W L : E) = (mfderiv I I F (γ 0) (W 0) : E)) :
    ∃ f : ℝ × ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f (univ ×ˢ U) ∧
      (∀ t, f (0, t) = γ t) ∧
      (∀ s, f (s, L) = F (f (s, 0))) ∧
      (∀ t, (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, t)) 0 1 : E) = (W t : E)) ∧
      (∀ t, IsGeodesic (I := I) g (fun s => f (s, t))) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun p w => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g p w
  let f : ℝ × ℝ → M := fun p => expMapIntrinsic (I := I) g hEnorm (γ p.2) (p.1 • W p.2)
  have hrad := intrinsicExpVariation_radial g hEnorm γ W
  refine ⟨f, ?_, fun t => (hrad t).2.1, ?_, fun t => (hrad t).2.2, fun t => (hrad t).1⟩
  · have hs := intrinsicExpVariation_contMDiffOn g hEnorm γ W hU hW
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hs
    exact hs
  · exact intrinsicExpVariation_twisted g hEnorm F hF γ W L htw hWL

end DifferentialGeometry.Geometry.Riemannian.Variation
