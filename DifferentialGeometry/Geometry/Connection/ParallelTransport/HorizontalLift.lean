import DifferentialGeometry.Geometry.Connection.ParallelTransport.OrthonormalFrame
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Principal
import DifferentialGeometry.Geometry.Metric.BundleContinuity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

section HorizontalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  {W : Type*} [SeminormedAddCommGroup W] [Module ℝ W]

def IsHorizontalFrameOn (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (J : Set ℝ) (p : ∀ t, V (γ t) ≃ₗᵢ[ℝ] W) : Prop :=
  ∀ w : W,
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, (p t).symm w⟩ : TotalSpace F V)) J ∧
    ∀ t ∈ J, cov.derivAlongWithin γ (fun s => (p s).symm w) J t = 0

end HorizontalFrame

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem IsMetricCompatible.exists_horizontal_frame_on_interval
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
       ContinuousOn (fun t => (⟨γ t, p t⟩ :
         TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) J) := by
  classical
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  obtain ⟨Q, hQ₀, hQinner, hQi, hQf, hQp⟩ :=
    hmetric.exists_parallel_orthonormal_frame_on_interval hcov hJ ht₀ hγ p₀
  let p (t : ℝ) : V (γ t) ≃ₗᵢ[ℝ] F :=
    if ht : t ∈ J then (Q t).toLinearEquiv.isometryOfInner (hQinner t ht)
    else FiberBundle.linearIsometryEquivAt (F := F) V (γ t)
  have hpQ (t : ℝ) (ht : t ∈ J) : (p t).toContinuousLinearEquiv = Q t := by
    dsimp only [p]
    rw [dif_pos ht]
    ext v
    rfl
  have hpiQ (t : ℝ) (ht : t ∈ J) (w : F) : (p t).symm w = (Q t).symm w := by
    change (p t).toContinuousLinearEquiv.symm w = _
    rw [hpQ t ht]
  have hpi : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun z : ℝ × F => (⟨γ z.1, (p z.1).symm z.2⟩ : TotalSpace F V)) (J ×ˢ univ) :=
    hQi.congr (fun z hz => TotalSpace.mk_inj.mpr (hpiQ z.1 hz.1 z.2))
  have hs (w : F) : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) ∞
      (fun t => (⟨γ t, (p t).symm w⟩ : TotalSpace F V)) J :=
    hpi.comp ((contMDiff_id.prodMk (contMDiff_const (c := w))).contMDiffOn (s := J))
      (fun _ ht => ⟨ht, mem_univ _⟩)
  refine ⟨p, ?_, hpi, ?_, ?_, ?_⟩
  · ext v
    change (p t₀).toContinuousLinearEquiv v = p₀.toContinuousLinearEquiv v
    rw [hpQ t₀ ht₀, hQ₀]
  · intro e he
    apply (hQf e).congr
    intro z hz
    change (p z.1).toContinuousLinearEquiv _ = _
    rw [hpQ z.1 hz.1]
  · intro w
    refine ⟨(hs w).mdifferentiableOn (by simp), ?_⟩
    intro t ht
    rw [cov.derivAlongWithin_congr (fun s hs => hpiQ s hs w) (hpiQ t ht w)]
    exact hQp w t ht
  · exact FiberBundle.continuousOn_orthonormalFrame_of_symm V
      (fun w => (hs w).continuousOn)

end Existence

end CovariantDerivative
