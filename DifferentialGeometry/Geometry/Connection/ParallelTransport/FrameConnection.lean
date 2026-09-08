import DifferentialGeometry.Geometry.Connection.OrthonormalFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.HorizontalLift

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem IsMetricCompatible.exists_horizontal_orthonormalFrame_lift_on_interval
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞) {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J)
    (p₀ : V (γ t₀) ≃ₗᵢ[ℝ] F) :
    ∃ p : ∀ t, V (γ t) ≃ₗᵢ[ℝ] F,
      p t₀ = p₀ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : ℝ × F => (⟨γ z.1, (p z.1).symm z.2⟩ : TotalSpace F V)) (J ×ˢ univ) ∧
      (∀ (e : Trivialization F (π F V)), ∀ [MemTrivializationAtlas e],
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
          (fun z : ℝ × F => p z.1 (e.symmL ℝ (γ z.1) z.2))
          {z | z.1 ∈ J ∧ γ z.1 ∈ e.baseSet}) ∧
      cov.IsHorizontalFrameOn γ J p ∧
      (letI : IsContinuousRiemannianBundle F V :=
         IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
       letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
       letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
       ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) 1
         (fun t => (⟨γ t, p t⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
           (fun x => V x ≃ₗᵢ[ℝ] F))) J ∧
       ∀ t ∈ J, cov.orthonormalFrameConnectionForm (n := 1) le_rfl
         (⟨γ t, p t⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
         (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
           (fun s => (⟨γ s, p s⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
             (fun x => V x ≃ₗᵢ[ℝ] F))) J t ((NormedSpace.fromTangentSpace t).symm 1)) = 0) := by
  obtain ⟨p, hp₀, hpi, hpf, hph, hpcont⟩ :=
    hmetric.exists_horizontal_frame_on_interval hcov hJ ht₀ hγ p₀
  refine ⟨p, hp₀, hpi, hpf, hph, ?_⟩
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  have hpc (w : F) : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 1
      (fun t => (⟨γ t, (p t).symm w⟩ : TotalSpace F V)) J :=
    (hpi.of_le (by simp)).comp
      ((contMDiff_id.prodMk (contMDiff_const (c := w))).contMDiffOn (s := J))
      (fun _ ht => ⟨ht, mem_univ _⟩)
  refine ⟨FiberBundle.contMDiffOn_orthonormalFrame_of_symm (F := F) V I 1 hpc, ?_⟩
  intro t ht
  ext w
  rw [cov.orthonormalFrameConnectionForm_curveWithin_apply le_rfl p (fun v => hpc v t ht),
    (hph w).2 t ht, map_zero, neg_zero]
  rfl

end CovariantDerivative
