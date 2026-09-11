import DifferentialGeometry.Geometry.Connection.ParallelTransport.VectorBundle

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem IsMetricCompatible.exists_parallel_orthonormal_frame_on_interval
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞) {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J)
    (p₀ : V (γ t₀) ≃ₗᵢ[ℝ] W) :
    ∃ Q : ∀ t, V (γ t) ≃L[ℝ] W,
      Q t₀ = p₀.toContinuousLinearEquiv ∧
      (∀ t ∈ J, ∀ v w : V (γ t), inner ℝ (Q t v) (Q t w) = inner ℝ v w) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : ℝ × W => (⟨γ z.1, (Q z.1).symm z.2⟩ : TotalSpace F V)) (J ×ˢ univ) ∧
      (∀ (e : Trivialization F (π F V)), ∀ [MemTrivializationAtlas e],
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, W) ∞
          (fun z : ℝ × F => Q z.1 (e.symmL ℝ (γ z.1) z.2))
          {z | z.1 ∈ J ∧ γ z.1 ∈ e.baseSet}) ∧
      ∀ w : W, ∀ t ∈ J,
        cov.derivAlongWithin γ (fun s => (Q s).symm w) J t = 0 := by
  have hγ₂ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => γ z.1) (J ×ˢ univ) :=
    hγ.comp contMDiffOn_fst (fun _ hz => hz.1)
  obtain ⟨T, hT₀, hTf, hTi, hTp, hTinner⟩ :=
    hmetric.exists_parallel_transport_on_interval (γ := fun t (_ : ℝ) => γ t)
      (IP := 𝓘(ℝ, ℝ)) hcov hJ ht₀ hγ₂
  let Q (t : ℝ) : V (γ t) ≃L[ℝ] W :=
    (T t 0).symm.trans p₀.toContinuousLinearEquiv
  have hT₀eq : T t₀ 0 = ContinuousLinearEquiv.refl ℝ (V (γ t₀)) := by
    ext v
    exact hT₀ 0 v
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Q, hT₀eq]
    rfl
  · intro t ht v w
    change inner ℝ (p₀ ((T t 0).symm v)) (p₀ ((T t 0).symm w)) = inner ℝ v w
    rw [p₀.inner_map_map]
    have h := hTinner t ht 0 ((T t 0).symm v) ((T t 0).symm w)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm
  · let e := trivializationAt F V (γ t₀)
    have he : γ t₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t₀)
    let A : W →L[ℝ] F :=
      (e.continuousLinearMapAt ℝ (γ t₀)).comp p₀.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, W))
        ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞
        (fun z : ℝ × W => ((z.1, (0 : ℝ)), A z.2)) :=
      (contMDiff_fst.prodMk (contMDiff_const (c := (0 : ℝ)))).prodMk
        (A.contMDiff.comp contMDiff_snd)
    have h := (hTf e).comp (hA.contMDiffOn (s := J ×ˢ univ))
      (fun z hz => ⟨hz.1, he⟩)
    apply h.congr
    intro z hz
    change (⟨γ z.1, T z.1 0 (p₀.symm z.2)⟩ : TotalSpace F V) =
      ⟨γ z.1, T z.1 0 (e.symmL ℝ (γ t₀) (A z.2))⟩
    congr 2
    exact (e.symmL_continuousLinearMapAt he (p₀.symm z.2)).symm
  · intro e _
    have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
        ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞
        (fun z : ℝ × F => ((z.1, (0 : ℝ)), z.2)) :=
      (contMDiff_fst.prodMk (contMDiff_const (c := (0 : ℝ)))).prodMk contMDiff_snd
    have h := (hTi e).comp
      (hA.contMDiffOn (s := {z : ℝ × F | z.1 ∈ J ∧ γ z.1 ∈ e.baseSet}))
      (fun z hz => hz)
    let e₀ := trivializationAt F V (γ t₀)
    have he₀ : γ t₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F V (γ t₀)
    have hc := ((e₀.contMDiffOn_iff (fun z hz => e₀.mem_source.mpr he₀)).mp h).2
    let A : F →L[ℝ] W :=
      p₀.toContinuousLinearEquiv.toContinuousLinearMap.comp (e₀.symmL ℝ (γ t₀))
    have ha := A.contMDiff.comp_contMDiffOn hc
    apply ha.congr
    intro z hz
    change p₀ ((T z.1 0).symm (e.symmL ℝ (γ z.1) z.2)) =
      p₀ (e₀.symmL ℝ (γ t₀)
        (e₀ ⟨γ t₀, (T z.1 0).symm (e.symmL ℝ (γ z.1) z.2)⟩).2)
    rw [← e₀.continuousLinearMapAt_apply_of_mem ℝ he₀,
      e₀.symmL_continuousLinearMapAt he₀]
  · intro w t ht
    exact hTp 0 (p₀.symm w) t ht

end CovariantDerivative
