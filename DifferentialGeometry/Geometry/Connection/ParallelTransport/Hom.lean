import DifferentialGeometry.Geometry.Connection.AlongCurveHom
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Piecewise
import DifferentialGeometry.Bundle.Equiv

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem derivAlongWithin_clm_section_apply_of_parallel
    (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
    (A : ∀ x, V₁ x →L[ℝ] V₂ x) {γ : ℝ → M} {Z : ∀ t, V₁ (γ t)}
    {J : Set ℝ} {t : ℝ}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x)) (γ t))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ A (γ t) = 0)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁))
      (fun s => TotalSpace.mk' F₁ (γ s) (Z s)) J t) :
    cov₂.derivAlongWithin γ (fun s => A (γ s) (Z s)) J t =
      A (γ t) (cov₁.derivAlongWithin γ Z J t) := by
  rw [derivAlongWithin_clm_apply cov₁ cov₂ γ (fun s => A (γ s)) Z
    (hA.comp_mdifferentiableWithinAt t hγ) hZ,
    derivAlongWithin_section _ hγ hA, hparallel, zero_apply, zero_apply, zero_add]

theorem IsPiecewiseParallelOn.map
    {cov₁ : CovariantDerivative I F₁ V₁} {cov₂ : CovariantDerivative I F₂ V₂}
    (A : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hA : MDifferentiable I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x)))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ A = 0)
    {γ : ℝ → M} {Z : ∀ t, V₁ (γ t)} {a b : ℝ}
    (hZ : cov₁.IsPiecewiseParallelOn γ Z a b) :
    cov₂.IsPiecewiseParallelOn γ (fun t => A (γ t) (Z t)) a b := by
  induction hZ with
  | of_parallel hγ hZ hp =>
      have hdγ := hγ.mdifferentiableOn (by simp)
      refine .of_parallel hγ ?_ ?_
      · intro t ht
        exact ((hA (γ t)).comp_mdifferentiableWithinAt t (hdγ t ht)).clm_bundle_apply (hZ t ht)
      · intro t ht
        rw [derivAlongWithin_clm_section_apply_of_parallel cov₁ cov₂ A (hA (γ t))
          (congrFun hparallel (γ t)) (hdγ t ht) (hZ t ht), hp t ht, map_zero]
  | trans hab hbc _ _ ihleft ihright => exact .trans hab hbc ihleft ihright

theorem isPiecewiseParallelOn_map_continuousLinearEquiv_iff
    {cov₁ : CovariantDerivative I F₁ V₁} {cov₂ : CovariantDerivative I F₂ V₂}
    (A : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x).toContinuousLinearMap))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ (fun x => (A x).toContinuousLinearMap) = 0)
    {γ : ℝ → M} {Z : ∀ t, V₁ (γ t)} {a b : ℝ} :
    cov₂.IsPiecewiseParallelOn γ (fun t => A (γ t) (Z t)) a b ↔
      cov₁.IsPiecewiseParallelOn γ Z a b := by
  have hAd := hA.mdifferentiable (by simp)
  constructor
  · intro hZ
    let : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
    have hAi : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) 1
        (fun x => TotalSpace.mk' (F₂ →L[ℝ] F₁) x (A x).symm.toContinuousLinearMap) := by
      simpa only [ContinuousLinearMap.inverse_equiv] using
        hA.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
    have hAid := hAi.mdifferentiable (by simp)
    generalize hw : (fun t => A (γ t) (Z t)) = W at hZ
    induction hZ with
    | @of_parallel a b hγ hW hp =>
        have hdγ := hγ.mdifferentiableOn (by simp)
        have hZdiff : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁))
            (fun t => TotalSpace.mk' F₁ (γ t) (Z t)) (Icc a b) := by
          intro t ht
          have h := ((hAid (γ t)).comp_mdifferentiableWithinAt t (hdγ t ht)).clm_bundle_apply
            (hW t ht)
          subst W
          simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h
        refine .of_parallel hγ hZdiff ?_
        intro t ht
        apply (A (γ t)).injective
        rw [map_zero]
        change (A (γ t)).toContinuousLinearMap (cov₁.derivAlongWithin γ Z (Icc a b) t) = 0
        rw [← derivAlongWithin_clm_section_apply_of_parallel cov₁ cov₂
          (fun x => (A x).toContinuousLinearMap) (hAd (γ t))
          (congrFun hparallel (γ t)) (hdγ t ht) (hZdiff t ht)]
        exact hw ▸ hp t ht
    | trans hab hbc _ _ ihleft ihright => exact .trans hab hbc ihleft ihright
  · intro hZ
    exact hZ.map (fun x => (A x).toContinuousLinearMap) hAd hparallel

theorem IsParallelSet.preimage
    {cov₁ : CovariantDerivative I F₁ V₁} {cov₂ : CovariantDerivative I F₂ V₂}
    {K : Set (TotalSpace F₂ V₂)} (hK : cov₂.IsParallelSet K)
    (A : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hA : MDifferentiable I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x)))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ A = 0) :
    cov₁.IsParallelSet
      ((fun p : TotalSpace F₁ V₁ => TotalSpace.mk' F₂ p.1 (A p.1 p.2)) ⁻¹' K) := by
  rw [isParallelSet_iff_piecewise_parallel]
  intro a b t₀ t γ Z hZ ht₀ ht
  exact hK.mem_iff_of_piecewise_parallel (hZ.map A hA hparallel) ht₀ ht

theorem isParallelSet_preimage_continuousLinearEquiv_iff
    {cov₁ : CovariantDerivative I F₁ V₁} {cov₂ : CovariantDerivative I F₂ V₂}
    (A : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x).toContinuousLinearMap))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ (fun x => (A x).toContinuousLinearMap) = 0)
    {K : Set (TotalSpace F₂ V₂)} :
    cov₁.IsParallelSet
        ((fun p : TotalSpace F₁ V₁ => TotalSpace.mk' F₂ p.1 (A p.1 p.2)) ⁻¹' K) ↔
      cov₂.IsParallelSet K := by
  constructor
  · intro hK
    rw [isParallelSet_iff_piecewise_parallel]
    intro a b t₀ t γ Z hZ ht₀ ht
    have hi : cov₁.IsPiecewiseParallelOn γ (fun s => (A (γ s)).symm (Z s)) a b :=
      (isPiecewiseParallelOn_map_continuousLinearEquiv_iff A hA hparallel).mp (by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hZ)
    have h := hK.mem_iff_of_piecewise_parallel hi ht₀ ht
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  · intro hK
    exact hK.preimage (fun x => (A x).toContinuousLinearMap)
      (hA.mdifferentiable (by simp)) hparallel

theorem clm_apply_piecewise_parallel_transport
    (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
    (hcov₂ : ContMDiffCovariantDerivative cov₂ ∞)
    (A : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hA : MDifferentiable I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x)))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ A = 0)
    {γ : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (P : ∀ t, V₁ (γ t₀) ≃L[ℝ] V₁ (γ t))
    (Q : ∀ t, V₂ (γ t₀) ≃L[ℝ] V₂ (γ t))
    (hP₀ : ∀ v, P t₀ v = v) (hQ₀ : ∀ v, Q t₀ v = v)
    (hP : ∀ v, cov₁.IsPiecewiseParallelOn γ (fun t => P t v) a b)
    (hQ : ∀ v, cov₂.IsPiecewiseParallelOn γ (fun t => Q t v) a b)
    {t : ℝ} (ht : t ∈ Icc a b) (v : V₁ (γ t₀)) :
    A (γ t) (P t v) = Q t (A (γ t₀) v) := by
  exact piecewise_parallel_section_eq_on_Icc cov₂ hcov₂ ((hP v).map A hA hparallel)
    (hQ (A (γ t₀) v)) ht₀ (by rw [hP₀, hQ₀]) t ht

theorem IsParallelSet.image
    {cov₁ : CovariantDerivative I F₁ V₁} {cov₂ : CovariantDerivative I F₂ V₂}
    {K : Set (TotalSpace F₁ V₁)} (hK : cov₁.IsParallelSet K)
    (hcov₁ : ContMDiffCovariantDerivative cov₁ ∞)
    (hcov₂ : ContMDiffCovariantDerivative cov₂ ∞)
    (A : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hA : MDifferentiable I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (A x)))
    (hparallel : DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ A = 0) :
    cov₂.IsParallelSet
      ((fun p : TotalSpace F₁ V₁ => TotalSpace.mk' F₂ p.1 (A p.1 p.2)) '' K) := by
  refine ⟨?_⟩
  intro a b t₀ γ Z ht₀ hγ hZ hZpar hinit t ht
  obtain ⟨⟨x, v⟩, hv, heq⟩ := hinit
  have hx : x = γ t₀ := congrArg TotalSpace.proj heq
  subst x
  have hvZ : A (γ t₀) v = Z t₀ := TotalSpace.mk_inj.mp heq
  obtain ⟨T, hT₀, hT⟩ := cov₁.exists_piecewise_parallel_transport_on_Icc
    hcov₁ (.of_contMDiffOn hγ) ht₀
  have hvK : (⟨γ t, T t v⟩ : TotalSpace F₁ V₁) ∈ K := by
    apply (hK.mem_iff_of_piecewise_parallel (hT v) ht₀ ht).mpr
    simpa only [hT₀] using hv
  have hEq : A (γ t) (T t v) = Z t :=
    cov₂.piecewise_parallel_section_eq_on_Icc hcov₂ ((hT v).map A hA hparallel)
      (.of_parallel hγ hZ hZpar) ht₀ (by simpa only [hT₀] using hvZ) t ht
  exact ⟨⟨γ t, T t v⟩, hvK, TotalSpace.mk_inj.mpr hEq⟩

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V] [ContMDiffVectorBundle ∞ F V I]

theorem exists_linearIsometryEquiv_conj_of_parallel_endomorphism
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {A : ∀ t, V (γ t) →L[ℝ] V (γ t)}
    {a b t₀ t : ℝ} (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hA : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F →L[ℝ] F))
      (fun s => (⟨γ s, A s⟩ : TotalSpace (F →L[ℝ] F)
        (fun x => V x →L[ℝ] V x))) (Icc a b))
    (hApar : ∀ s ∈ Icc a b,
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V F V cov cov).derivAlongWithin γ A (Icc a b) s = 0) :
    ∃ e : V (γ t₀) ≃ₗᵢ[ℝ] V (γ t),
      e.toContinuousLinearEquiv.conj (A t₀) = A t := by
  have hγparam : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : ℝ × ℝ => γ q.1) (Icc a b ×ˢ univ) :=
    hγ.comp contMDiffOn_fst (fun _ hq => hq.1)
  obtain ⟨T, hT₀, hTf, _, hTp, hTm⟩ :=
    hmetric.exists_parallel_transport_on_Icc (IP := 𝓘(ℝ, ℝ))
      (γ := fun t (_ : ℝ) => γ t) hcov ht₀ hγparam
  have hsmooth (v : V (γ t₀)) :
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) ∞
        (fun t => (⟨γ t, T t 0 v⟩ : TotalSpace F V)) (Icc a b) := by
    let e := trivializationAt F V (γ t₀)
    have he : γ t₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t₀)
    have harg : ContMDiff 𝓘(ℝ, ℝ)
        ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => ((t, (0 : ℝ)), e.continuousLinearMapAt ℝ (γ t₀) v)) :=
      (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
    have h := (hTf e).comp harg.contMDiffOn (fun _ ht => ⟨ht, he⟩)
    simpa only [Function.comp_def, e.symmL_continuousLinearMapAt he] using h
  have hdiff (v : V (γ t₀)) := (hsmooth v).mdifferentiableOn (by simp)
  have hcomm (v : V (γ t₀)) : A t (T t 0 v) = T t 0 (A t₀ v) := by
    apply cov.parallel_section_eq_on_Icc hcov ht₀ (hγ.of_le (by simp))
      (fun s hs => (hA s hs).clm_bundle_apply (hdiff v s hs)) (hdiff (A t₀ v))
      ?_ (hTp 0 (A t₀ v)) (by rw [hT₀, hT₀]) t ht
    intro s hs
    rw [derivAlongWithin_clm_apply cov cov γ A (fun r => T r 0 v)
      (hA s hs) (hdiff v s hs), hApar s hs, hTp 0 v s hs]
    simp only [zero_apply, map_zero, add_zero]
  let e := (T t 0).toLinearEquiv.isometryOfInner (hTm t ht 0)
  refine ⟨e, ?_⟩
  ext v
  change T t 0 (A t₀ ((T t 0).symm v)) = A t v
  rw [← hcomm, (T t 0).apply_symm_apply]

end CovariantDerivative
