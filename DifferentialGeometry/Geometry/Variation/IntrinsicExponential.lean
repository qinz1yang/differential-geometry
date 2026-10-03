import DifferentialGeometry.Geometry.Exponential.IsometryEquivariance

noncomputable section
open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (TangentSpace I : M → Type _)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicExpVariation_contMDiffOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (γ : ℝ → M)
    (W : ∀ t, TangentSpace I (γ t)) {U : Set ℝ} (hU : IsOpen U)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨γ t, W t⟩ : TangentBundle I M)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => expMapIntrinsic (I := I) g hEnorm (γ p.2) (p.1 • W p.2))
      (univ ×ˢ U) := by
  intro p hp
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : ℝ × ℝ => (⟨γ q.2, W q.2⟩ : TangentBundle I M)) p :=
    ((hW p.2 hp.2).contMDiffAt (hU.mem_nhds hp.2)).comp p contMDiffAt_snd
  have hlaunch : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : ℝ × ℝ => (⟨γ q.2, q.1 • W q.2⟩ : TangentBundle I M)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at hs ⊢
    refine ⟨hs.1, ?_⟩
    let e := trivializationAt E (TangentSpace I) (γ p.2)
    apply (contMDiffAt_fst.smul hs.2).congr_of_eventuallyEq
    have he : ∀ᶠ q in 𝓝 p, γ q.2 ∈ e.baseSet :=
      hs.1.continuousAt (e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ p.2)))
    filter_upwards [he] with q hq
    exact (e.linear ℝ hq).map_smul q.1 (W q.2)
  exact ((intrinsicExp_smooth g hEnorm).contMDiffAt.comp p hlaunch).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicExpVariation_radial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (γ : ℝ → M)
    (W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    let c := fun s => expMapIntrinsic (I := I) g hEnorm (γ t) (s • W t)
    IsGeodesic (I := I) g c ∧ c 0 = γ t ∧
      (mfderiv 𝓘(ℝ, ℝ) I c 0 1 : E) = (W t : E) := by
  have heq : (fun s => expMapIntrinsic (I := I) g hEnorm (γ t) (s • W t)) =
      intrinsicGeodesic (I := I) g hEnorm (γ t) (W t) := by
    funext s
    exact intrinsicGeodesic_smul g hEnorm (γ t) (W t) s
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact intrinsicGeodesic_isGeodesic g hEnorm (γ t) (W t)
  · exact (congrFun heq 0).trans (intrinsicGeodesic_zero g hEnorm (γ t) (W t))
  · rw [heq]
    exact intrinsicGeodesic_mfderiv_zero g hEnorm (γ t) (W t)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicExpVariation_twisted
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (γ : ℝ → M) (W : ∀ t, TangentSpace I (γ t)) (L : ℝ)
    (hγ : γ L = F (γ 0))
    (hW : (W L : E) = (mfderiv I I F (γ 0) (W 0) : E)) (s : ℝ) :
    expMapIntrinsic (I := I) g hEnorm (γ L) (s • W L) =
      F (expMapIntrinsic (I := I) g hEnorm (γ 0) (s • W 0)) := by
  rw [expMapIntrinsic_isometry g hEnorm F hF, map_smul]
  rw [hW, hγ]

end DifferentialGeometry.Geometry.Riemannian.Variation
