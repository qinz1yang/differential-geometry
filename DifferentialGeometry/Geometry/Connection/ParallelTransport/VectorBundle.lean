import DifferentialGeometry.Geometry.Connection.AlongCurve
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.AlongCurve
import DifferentialGeometry.Analysis.ODE.Flow.BundleLinearODE
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

private theorem exists_parallel_transport_in_trivialization_on_Icc_of_lt
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {a b t₀ : ℝ}
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun p : ℝ × P => γ p.1 p.2) (Icc a b ×ˢ univ))
    (he : ∀ t ∈ Icc a b, ∀ p : P, γ t p ∈ e.baseSet) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
            TotalSpace F V)) ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ t₀ q.1.2, (T q.1.1 q.1.2).symm
            (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
        ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      ∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ Icc a b,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) (Icc a b) t = 0 := by
  classical
  let A : ℝ → P → F →L[ℝ] F := fun t p =>
    -cov.connectionForm e (γ t p)
      (mfderivWithin 𝓘(ℝ, ℝ) I (fun s => γ s p) (Icc a b) t
        ((NormedSpace.fromTangentSpace t).symm 1))
  have hvelocity := hγ.time_mfderivWithin (m := ∞) (uniqueDiffOn_Icc hab) (by simp)
  have hAcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun p : ℝ × P => A p.1 p.2) (Icc a b ×ˢ univ) :=
    ((cov.contMDiffOn_connectionForm hcov e).comp hvelocity
      (fun p hp => he p.1 hp.1 p.2)).neg
  have hAbundle : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × P => (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F)
        (fun x => Trivial P F x →L[ℝ] Trivial P F x))) (Icc a b ×ˢ univ) := by
    intro p hp
    rw [contMDiffWithinAt_hom_bundle]
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using hAcoord p hp
  obtain ⟨Φ, hΦ₀, hΦbundle, hΦinvbundle, hΦode, _, hΦinverse, _⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_fiberwise_linear_ode_solution_on_Icc
      (I := IP) (F := F) (V := Trivial P F) ht₀ A hAbundle
  change ℝ → P → F →L[ℝ] F at Φ
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun p : ℝ × P => (Φ p.1 p.2 : F →L[ℝ] F)) (Icc a b ×ˢ univ) := by
    intro p hp
    have h := hΦbundle p hp
    rw [contMDiffWithinAt_hom_bundle] at h
    simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using h.2
  have hΦinv : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun p : ℝ × P => ((Φ p.1 p.2).inverse : F →L[ℝ] F)) (Icc a b ×ˢ univ) := by
    intro p hp
    have h := hΦinvbundle p hp
    rw [contMDiffWithinAt_hom_bundle] at h
    simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using h.2
  let L (t : ℝ) (p : P) : V (γ t₀ p) →L[ℝ] V (γ t p) :=
    (e.symmL ℝ (γ t p)).comp ((Φ t p).comp (e.continuousLinearMapAt ℝ (γ t₀ p)))
  let K (t : ℝ) (p : P) : V (γ t p) →L[ℝ] V (γ t₀ p) :=
    (e.symmL ℝ (γ t₀ p)).comp
      ((Φ t p).inverse.comp (e.continuousLinearMapAt ℝ (γ t p)))
  have hKL (t : ℝ) (ht : t ∈ Icc a b) (p : P) : Function.LeftInverse (K t p) (L t p) := by
    intro v
    simp only [K, L, ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_symmL (he t ht p),
      (hΦinverse t ht p _).1, e.symmL_continuousLinearMapAt (he t₀ ht₀ p)]
  have hLK (t : ℝ) (ht : t ∈ Icc a b) (p : P) : Function.RightInverse (K t p) (L t p) := by
    intro v
    simp only [K, L, ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_symmL (he t₀ ht₀ p),
      (hΦinverse t ht p _).2, e.symmL_continuousLinearMapAt (he t ht p)]
  let T (t : ℝ) (p : P) : V (γ t₀ p) ≃L[ℝ] V (γ t p) :=
    if ht : t ∈ Icc a b then
      ContinuousLinearEquiv.equivOfInverse (L t p) (K t p) (hKL t ht p) (hLK t ht p)
    else
      (VectorBundle.continuousLinearEquivAt ℝ F V (γ t₀ p)).trans
        (VectorBundle.continuousLinearEquivAt ℝ F V (γ t p)).symm
  have hT (t : ℝ) (ht : t ∈ Icc a b) (p : P) (v : V (γ t₀ p)) :
      T t p v = e.symmL ℝ (γ t p) (Φ t p (e.continuousLinearMapAt ℝ (γ t₀ p) v)) := by
    simp only [T, dif_pos ht, ContinuousLinearEquiv.equivOfInverse_apply, L,
      ContinuousLinearMap.comp_apply]
  have hTinv (t : ℝ) (ht : t ∈ Icc a b) (p : P) (v : V (γ t p)) :
      (T t p).symm v =
        e.symmL ℝ (γ t₀ p) ((Φ t p).inverse (e.continuousLinearMapAt ℝ (γ t p) v)) := by
    simp only [T, dif_pos ht, ContinuousLinearEquiv.symm_equivOfInverse,
      ContinuousLinearEquiv.equivOfInverse_apply, K, ContinuousLinearMap.comp_apply]
  have hsmooth (B : ℝ → P → F →L[ℝ] F)
      (hB : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : ℝ × P => B p.1 p.2) (Icc a b ×ˢ univ))
      (δ : ℝ → P → M)
      (hδ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
        (fun p : ℝ × P => δ p.1 p.2) (Icc a b ×ˢ univ))
      (heδ : ∀ t ∈ Icc a b, ∀ p : P, δ t p ∈ e.baseSet) :
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨δ q.1.1 q.1.2, e.symmL ℝ (δ q.1.1 q.1.2) (B q.1.1 q.1.2 q.2)⟩ :
            TotalSpace F V)) ((Icc a b ×ˢ univ) ×ˢ univ) := by
    have hbase : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) I ∞
        (fun q : (ℝ × P) × F => δ q.1.1 q.1.2) ((Icc a b ×ˢ univ) ×ˢ univ) :=
      hδ.comp (f := fun q : (ℝ × P) × F => q.1)
        contMDiffOn_fst (fun _ hq => hq.1)
    have hval : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
        (fun q : (ℝ × P) × F => B q.1.1 q.1.2 q.2) ((Icc a b ×ˢ univ) ×ˢ univ) :=
      (hB.comp (f := fun q : (ℝ × P) × F => q.1)
      contMDiffOn_fst (fun _ hq => hq.1)).clm_apply contMDiffOn_snd
    have h := e.contMDiffOn_symm.comp (hbase.prodMk hval)
      (fun q hq => e.mem_target.mpr (heδ q.1.1 hq.1.1 q.1.2))
    apply h.congr
    intro q hq
    dsimp only [Function.comp_apply]
    rw [e.symmL_apply (heδ q.1.1 hq.1.1 q.1.2),
      e.mk_symm (heδ q.1.1 hq.1.1 q.1.2)]
  have hTsmooth : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : (ℝ × P) × F =>
        (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
          TotalSpace F V)) ((Icc a b ×ˢ univ) ×ˢ univ) := by
    apply (hsmooth Φ hΦ γ hγ he).congr
    intro q hq
    congr 1
    rw [hT q.1.1 hq.1.1 q.1.2, e.continuousLinearMapAt_symmL (he t₀ ht₀ q.1.2)]
  have hγ₀ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun p : ℝ × P => γ t₀ p.2) (Icc a b ×ˢ univ) :=
    hγ.comp (f := fun p : ℝ × P => (t₀, p.2))
      (contMDiffOn_const.prodMk contMDiffOn_snd) (fun _ _ => ⟨ht₀, mem_univ _⟩)
  have hTinvsmooth : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : (ℝ × P) × F =>
        (⟨γ t₀ q.1.2, (T q.1.1 q.1.2).symm
          (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
      ((Icc a b ×ˢ univ) ×ˢ univ) := by
    apply (hsmooth (fun t p => (Φ t p).inverse) hΦinv (fun _ p => γ t₀ p) hγ₀
      (fun _ _ p => he t₀ ht₀ p)).congr
    intro q hq
    congr 1
    rw [hTinv q.1.1 hq.1.1 q.1.2, e.continuousLinearMapAt_symmL (he q.1.1 hq.1.1 q.1.2)]
  refine ⟨T, ?_, hTsmooth, hTinvsmooth, ?_⟩
  · intro p v
    rw [hT t₀ ht₀ p v, hΦ₀ p, ContinuousLinearMap.id_apply,
      e.symmL_continuousLinearMapAt (he t₀ ht₀ p)]
  · intro p v t ht
    let v₀ := e.continuousLinearMapAt ℝ (γ t₀ p) v
    have hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s p, T s p v⟩ : TotalSpace F V)) (Icc a b) t := by
      have harg : ContMDiffWithinAt 𝓘(ℝ, ℝ)
          ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) ∞
          (fun s : ℝ => ((s, p), v₀)) (Icc a b) t :=
        (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const).prodMk contMDiffWithinAt_const
      have h := (hTsmooth ((t, p), v₀) ⟨⟨ht, mem_univ p⟩, mem_univ v₀⟩).comp
        (f := fun s : ℝ => ((s, p), v₀)) t harg
        (fun s hs => ⟨⟨hs, mem_univ p⟩, mem_univ v₀⟩)
      have h' := h.mdifferentiableWithinAt (by simp)
      simpa only [Function.comp_def, v₀, e.symmL_continuousLinearMapAt (he t₀ ht₀ p)] using h'
    have hcoord (s : ℝ) (hs : s ∈ Icc a b) :
        e.continuousLinearMapAt ℝ (γ s p) (T s p v) = Φ s p v₀ := by
      rw [hT s hs p v, e.continuousLinearMapAt_symmL (he s hs p)]
    have hD := (hΦode p v₀ t ht).congr hcoord (hcoord t ht)
    rw [cov.derivAlongWithin_eq e (he t ht p) hZ,
      hD.derivWithin (uniqueDiffOn_Icc hab t ht), hcoord t ht]
    simp only [A, neg_apply, neg_add_cancel, map_zero]

theorem exists_parallel_transport_in_trivialization_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun p : ℝ × P => γ p.1 p.2) (Icc a b ×ˢ univ))
    (he : ∀ t ∈ Icc a b, ∀ p : P, γ t p ∈ e.baseSet) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
            TotalSpace F V)) ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ t₀ q.1.2, (T q.1.1 q.1.2).symm
            (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
        ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      ∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ Icc a b,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) (Icc a b) t = 0 := by
  rcases lt_or_eq_of_le (ht₀.1.trans ht₀.2) with hab | hab
  · exact exists_parallel_transport_in_trivialization_on_Icc_of_lt cov hcov e hab ht₀ hγ he
  · subst b
    have hta : t₀ = a := le_antisymm ht₀.2 ht₀.1
    subst t₀
    simp only [Icc_self] at hγ he ⊢
    let T (t : ℝ) (p : P) : V (γ a p) ≃L[ℝ] V (γ t p) :=
      (VectorBundle.continuousLinearEquivAt ℝ F V (γ a p)).trans
        (VectorBundle.continuousLinearEquivAt ℝ F V (γ t p)).symm
    have hT (p : P) : T a p = ContinuousLinearEquiv.refl ℝ (V (γ a p)) := by
      ext v
      simp only [T, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
        ContinuousLinearEquiv.refl_apply]
    have hsmooth : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ q.1.1 q.1.2, e.symmL ℝ (γ q.1.1 q.1.2) q.2⟩ : TotalSpace F V))
        (({a} ×ˢ univ) ×ˢ univ) := by
      have hbase : ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) I ∞
          (fun q : (ℝ × P) × F => γ q.1.1 q.1.2) (({a} ×ˢ univ) ×ˢ univ) :=
        hγ.comp (f := fun q : (ℝ × P) × F => q.1)
          contMDiffOn_fst (fun _ hq => hq.1)
      have h := e.contMDiffOn_symm.comp (hbase.prodMk contMDiffOn_snd)
        (fun q hq => e.mem_target.mpr (he q.1.1 hq.1.1 q.1.2))
      apply h.congr
      intro q hq
      dsimp only [Function.comp_apply]
      rw [e.symmL_apply (he q.1.1 hq.1.1 q.1.2), e.mk_symm (he q.1.1 hq.1.1 q.1.2)]
    refine ⟨T, ?_, ?_, ?_, ?_⟩
    · intro p v
      rw [hT, ContinuousLinearEquiv.refl_apply]
    · apply hsmooth.congr
      rintro ⟨⟨t, p⟩, v⟩ hq
      have ht : t = a := hq.1.1
      subst t
      simp only [hT, ContinuousLinearEquiv.refl_apply]
    · apply hsmooth.congr
      rintro ⟨⟨t, p⟩, v⟩ hq
      have ht : t = a := hq.1.1
      subst t
      rw [hT]
      rfl
    · intro p v t ht
      have ht' : t = a := ht
      subst t
      exact cov.derivAlongWithin_singleton (fun s => γ s p) (fun s => T s p v) a

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
  [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

theorem IsMetricCompatible.exists_parallel_transport_in_trivialization_on_Icc
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun p : ℝ × P => γ p.1 p.2) (Icc a b ×ˢ univ))
    (he : ∀ t ∈ Icc a b, ∀ p : P, γ t p ∈ e.baseSet) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
            TotalSpace F V)) ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × P) × F =>
          (⟨γ t₀ q.1.2, (T q.1.1 q.1.2).symm
            (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
        ((Icc a b ×ˢ univ) ×ˢ univ) ∧
      (∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ Icc a b,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) (Icc a b) t = 0) ∧
      ∀ t ∈ Icc a b, ∀ p : P, ∀ v w : V (γ t₀ p),
        inner ℝ (T t p v) (T t p w) = inner ℝ v w := by
  obtain ⟨T, hT₀, hTsmooth, hTinv, hTpar⟩ :=
    cov.exists_parallel_transport_in_trivialization_on_Icc hcov e ht₀ hγ he
  refine ⟨T, hT₀, hTsmooth, hTinv, hTpar, ?_⟩
  have hdiff (p : P) (v : V (γ t₀ p)) :
      MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s p, T s p v⟩ : TotalSpace F V)) (Icc a b) := by
    intro t ht
    let v₀ := e.continuousLinearMapAt ℝ (γ t₀ p) v
    have harg : ContMDiffWithinAt 𝓘(ℝ, ℝ)
        ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) ∞
        (fun s : ℝ => ((s, p), v₀)) (Icc a b) t :=
      (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const).prodMk contMDiffWithinAt_const
    have h := (hTsmooth ((t, p), v₀) ⟨⟨ht, mem_univ p⟩, mem_univ v₀⟩).comp
      (f := fun s : ℝ => ((s, p), v₀)) t harg
      (fun s hs => ⟨⟨hs, mem_univ p⟩, mem_univ v₀⟩)
    have h' := h.mdifferentiableWithinAt (by simp)
    simpa only [Function.comp_def, v₀, e.symmL_continuousLinearMapAt (he t₀ ht₀ p)] using h'
  intro t ht p v w
  have h := hmetric.inner_eq_of_parallel (convex_Icc a b) (hdiff p v) (hdiff p w)
    (hTpar p v) (hTpar p w) ht ht₀
  simpa only [hT₀] using h

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

private theorem continuousOn_connectionForm_curve
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (he : ∀ t ∈ J, γ t ∈ e.baseSet) :
    ContinuousOn (fun t => cov.connectionForm e (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))) J := by
  have hγprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 1
      (fun q : ℝ × ℝ => γ q.1) (J ×ˢ univ) :=
    hγ.comp contMDiffOn_fst (fun _ hq => hq.1)
  have hvelocity := (hγprod.time_mfderivWithin (m := 0) (n := 1)
    (I := 𝓘(ℝ, ℝ)) (I' := I) (γ := fun t (_ : ℝ) => γ t) hJ (by simp)).continuousOn
  have hAprod : ContinuousOn (fun q : ℝ × ℝ => cov.connectionForm e (γ q.1)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J q.1
        ((NormedSpace.fromTangentSpace q.1).symm 1))) (J ×ˢ univ) :=
    ((cov.contMDiffOn_connectionForm hcov e).continuousOn).comp hvelocity
      (fun q hq => he q.1 hq.1)
  exact hAprod.comp (continuousOn_id.prodMk (continuousOn_const (c := (0 : ℝ))))
    (fun _ ht => ⟨ht, mem_univ 0⟩)

theorem parallel_section_eq_in_trivialization_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {a b t₀ : ℝ}
    {Z W : ∀ t : ℝ, V (γ t)} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (he : ∀ t ∈ Icc a b, γ t ∈ e.baseSet)
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0)
    (hWpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ W (Icc a b) t = 0)
    (hinit : Z t₀ = W t₀) : ∀ t ∈ Icc a b, Z t = W t := by
  rcases lt_or_eq_of_le (ht₀.1.trans ht₀.2) with hab | hab
  swap
  · intro t ht
    have htt₀ : t = t₀ := by linarith [ht.1, ht.2, ht₀.1, ht₀.2]
    subst t
    exact hinit
  let A : ℝ → F →L[ℝ] F := fun t => -cov.connectionForm e (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t ((NormedSpace.fromTangentSpace t).symm 1))
  have hA : ContinuousOn A (Icc a b) :=
    (continuousOn_connectionForm_curve cov hcov e (uniqueDiffOn_Icc hab) hγ he).neg
  have hode (U : ∀ t : ℝ, V (γ t))
      (hU : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, U t⟩ : TotalSpace F V)) (Icc a b))
      (hUpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ U (Icc a b) t = 0)
      (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => e.continuousLinearMapAt ℝ (γ s) (U s))
        (A t (e.continuousLinearMapAt ℝ (γ t) (U t))) (Icc a b) t := by
    have hc := (e.mdifferentiableWithinAt_totalSpace_iff I
      (fun s => (⟨γ s, U s⟩ : TotalSpace F V)) (e.mem_source.mpr (he t ht))).mp (hU t ht)
    have hcoord : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun s => e.continuousLinearMapAt ℝ (γ s) (U s)) (Icc a b) t := by
      apply hc.2.congr_of_eventuallyEq
      · filter_upwards [hc.1.continuousWithinAt.preimage_mem_nhdsWithin
          (e.open_baseSet.mem_nhds (he t ht))] with s hs
        exact e.continuousLinearMapAt_apply_of_mem ℝ hs (U s)
      · exact e.continuousLinearMapAt_apply_of_mem ℝ (he t ht) (U t)
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hcoord
    have hd := cov.derivAlongWithin_coord e (he t ht) (hU t ht)
    rw [hUpar t ht, map_zero] at hd
    have hv : derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (U s)) (Icc a b) t =
        A t (e.continuousLinearMapAt ℝ (γ t) (U t)) := by
      exact eq_neg_of_add_eq_zero_left hd.symm
    rw [← hv]
    exact hcoord.hasDerivWithinAt
  have hunique := DifferentialGeometry.Analysis.ODE.Flow.linear_ode_unique_on_Icc ht₀ hA
    (hode Z hZ hZpar) (hode W hW hWpar)
    (congrArg (e.continuousLinearMapAt ℝ (γ t₀)) hinit)
  intro t ht
  have h := congrArg (e.symmL ℝ (γ t)) (hunique ht)
  simpa only [e.symmL_continuousLinearMapAt (he t ht)] using h

end CovariantDerivative
