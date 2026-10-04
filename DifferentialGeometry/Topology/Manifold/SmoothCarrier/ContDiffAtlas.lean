import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Countable
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Metric

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Topology.Manifold

theorem SmoothCarrier.exists_of_contDiff_atlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] {ι : Type*} [Countable ι] {K : ℕ} (hK : 1 ≤ K)
    (ψ : ι → OpenPartialHomeomorph E X) (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hψ : ∀ j d, ContDiffOn ℝ K ((ψ j).trans (ψ d).symm) ((ψ j).trans (ψ d).symm).source)
    (hM : letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
      IsManifold 𝓘(ℝ, E) K X) :
    letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    letI := hM
    letI : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
    ∀ G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _),
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
       IsRiemannianManifold 𝓘(ℝ, E) X) →
      ∃ (A : SmoothCompatibleAtlas E X ι) (g : ι → E ≃ₜ E),
        (∀ j, A.chart j = (ψ j).symm.trans (g j).toOpenPartialHomeomorph) ∧
        (∀ j, (A.chart j).source = (ψ j).target ∧ (A.chart j).target = (ψ j).source) ∧
        (∀ j, ContDiff ℝ K (g j) ∧ ContDiff ℝ K (g j).symm) ∧
        (∀ j x, x ∉ (ψ j).source → g j x = x ∧ (g j).symm x = x) ∧
        (∀ j x, 0 < (fderiv ℝ (g j) x).det) ∧
        A.IsCompatible (fun j => (ψ j).symm) K ∧
        (∃ f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X K,
          ⇑f = SmoothCarrier.toBase A ∧ ⇑f.symm = SmoothCarrier.ofBase A) ∧
        (∀ x : SmoothCarrier A,
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) (SmoothCarrier.toBase A x)).comp
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) =
            ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x)) ∧
        (∀ y : X,
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) (SmoothCarrier.ofBase A y)).comp
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y) =
            ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) y)) ∧
        ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
            (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _),
          (∀ (x : SmoothCarrier A) (v w : E),
            G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
          (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
           letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
             ⟨G'.toRiemannianMetric⟩
           (∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
              ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ) ∧
           (∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
              ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ) ∧
           (∀ (γ : ℝ → SmoothCarrier A) (a b : ℝ),
              (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
              pathELength 𝓘(ℝ, E) (SmoothCarrier.toBase A ∘ γ) a b =
                pathELength 𝓘(ℝ, E) γ a b) ∧
           (∀ (γ : ℝ → X) (a b : ℝ),
              (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
              pathELength 𝓘(ℝ, E) (SmoothCarrier.ofBase A ∘ γ) a b =
                pathELength 𝓘(ℝ, E) γ a b) ∧
           (∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
              riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
           (∀ x y : SmoothCarrier A,
              dist x y = dist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
           IsRiemannianManifold 𝓘(ℝ, E) (SmoothCarrier A)) := by
  intro G hG
  have hφ : ∀ i j, ContDiffOn ℝ K ((ψ i).symm.symm.trans (ψ j).symm)
      ((ψ i).symm.symm.trans (ψ j).symm).source := by
    intro i j
    rw [OpenPartialHomeomorph.symm_symm]
    exact hψ i j
  obtain ⟨A, hst, hcomp, g, hchart, hreg, hfix, hdet⟩ :=
    exists_smoothCompatibleAtlas hK (fun j => (ψ j).symm) hcover hφ
  obtain ⟨f, hf, hf'⟩ :=
    SmoothCarrier.exists_diffeomorph_toBase A (fun j => (ψ j).symm) hcover hcomp
  obtain ⟨G', hG', hiso, hiso', hpath, hpath', hedist, hdist, hRiem⟩ :=
    SmoothCarrier.exists_pullback_metric A (fun j => (ψ j).symm) hcover hK hcomp hM G
  have hst' : ∀ j, (A.chart j).source = (ψ j).target ∧ (A.chart j).target = (ψ j).source := by
    intro j
    rw [← OpenPartialHomeomorph.symm_source (ψ j), ← OpenPartialHomeomorph.symm_target (ψ j)]
    exact hst j
  have hfix' : ∀ j x, x ∉ (ψ j).source → g j x = x ∧ (g j).symm x = x := by
    intro j x hx
    rw [← OpenPartialHomeomorph.symm_target (ψ j)] at hx
    exact hfix j x hx
  exact ⟨A, g, hchart, hst', hreg, hfix', hdet, hcomp, ⟨f, hf, hf'⟩,
    SmoothCarrier.mfderiv_ofBase_comp_mfderiv_toBase A (fun j => (ψ j).symm) hcover hK hcomp,
    SmoothCarrier.mfderiv_toBase_comp_mfderiv_ofBase A (fun j => (ψ j).symm) hcover hK hcomp,
    G', hG', hiso, hiso', hpath, hpath', hedist, hdist, hRiem hG⟩

end DifferentialGeometry.Topology.Manifold
