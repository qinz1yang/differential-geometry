import DifferentialGeometry.Geometry.Connection.AlongCurve
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.AlongCurve
import DifferentialGeometry.Analysis.ODE.Flow.BundleLinearODE
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import Mathlib.Topology.UnitInterval

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

private theorem exists_parallel_transport_in_trivialization_on_closed_interval
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

private theorem parallel_section_eq_in_trivialization_on_Icc
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

private theorem parallel_endpoint_eq_iff_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b : ℝ} {Z W : ∀ t : ℝ, V (γ t)} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0)
    (hWpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ W (Icc a b) t = 0) :
    (Z b = W b) ↔ Z a = W a := by
  let cover : M → Set (Icc a b) := fun x =>
    (fun t : Icc a b => γ t) ⁻¹' (trivializationAt F V x).baseSet
  have hcoverOpen : ∀ x, IsOpen (cover x) := fun x =>
    (trivializationAt F V x).open_baseSet.preimage hγ.continuousOn.domRestrict
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, cover x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, mem_baseSet_trivializationAt F V (γ t)⟩
  obtain ⟨τ, hτ₀, hmono, ⟨N, hN⟩, hτ⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcoverOpen hcover
  have hstep (n : ℕ) : (Z (τ (n + 1)) = W (τ (n + 1))) ↔ Z (τ n) = W (τ n) := by
    obtain ⟨x, hx⟩ := hτ n
    let e := trivializationAt F V x
    have hsub : Icc (τ n : ℝ) (τ (n + 1) : ℝ) ⊆ Icc a b := fun t ht =>
      ⟨(τ n).property.1.trans ht.1, ht.2.trans (τ (n + 1)).property.2⟩
    have he : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ), γ t ∈ e.baseSet := by
      intro t ht
      exact hx (show (⟨t, hsub ht⟩ : Icc a b) ∈ Icc (τ n) (τ (n + 1)) from ht)
    have hZsmall : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ),
        cov.derivAlongWithin γ Z (Icc (τ n : ℝ) (τ (n + 1) : ℝ)) t = 0 := fun t ht =>
      cov.derivAlongWithin_eq_zero_mono (hZ t (hsub ht)) hsub (hZpar t (hsub ht))
    have hWsmall : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ),
        cov.derivAlongWithin γ W (Icc (τ n : ℝ) (τ (n + 1) : ℝ)) t = 0 := fun t ht =>
      cov.derivAlongWithin_eq_zero_mono (hW t (hsub ht)) hsub (hWpar t (hsub ht))
    have hle : (τ n : ℝ) ≤ τ (n + 1) := hmono (Nat.le_succ n)
    constructor
    · intro hi
      exact cov.parallel_section_eq_in_trivialization_on_Icc hcov e (right_mem_Icc.mpr hle)
        (hγ.mono hsub) he (hZ.mono hsub) (hW.mono hsub) hZsmall hWsmall hi
        (τ n) (left_mem_Icc.mpr hle)
    · intro hi
      exact cov.parallel_section_eq_in_trivialization_on_Icc hcov e (left_mem_Icc.mpr hle)
        (hγ.mono hsub) he (hZ.mono hsub) (hW.mono hsub) hZsmall hWsmall hi
        (τ (n + 1)) (right_mem_Icc.mpr hle)
  have hall (n : ℕ) : (Z (τ n) = W (τ n)) ↔ Z (τ 0) = W (τ 0) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
  have hb := congrArg (fun t : ℝ => Z t = W t) (hN N le_rfl)
  have ha := congrArg (fun t : ℝ => Z t = W t) hτ₀
  exact (Iff.of_eq hb).symm.trans ((hall N).trans (Iff.of_eq ha))

theorem parallel_section_eq_on_interval
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ} {Z W : ∀ t : ℝ, V (γ t)}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) J)
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : TotalSpace F V)) J)
    (hZpar : ∀ t ∈ J, cov.derivAlongWithin γ Z J t = 0)
    (hWpar : ∀ t ∈ J, cov.derivAlongWithin γ W J t = 0)
    (hinit : Z t₀ = W t₀) : ∀ t ∈ J, Z t = W t := by
  have hpair {c d : ℝ} (hcd : c ≤ d) (hc : c ∈ J) (hd : d ∈ J) :
      (Z d = W d) ↔ Z c = W c := by
    have hsub : Icc c d ⊆ J := hJ.out' hc hd
    exact parallel_endpoint_eq_iff_on_Icc cov hcov hcd (hγ.mono hsub)
      (hZ.mono hsub) (hW.mono hsub)
      (fun t ht => cov.derivAlongWithin_eq_zero_mono (hZ t (hsub ht)) hsub (hZpar t (hsub ht)))
      (fun t ht => cov.derivAlongWithin_eq_zero_mono (hW t (hsub ht)) hsub (hWpar t (hsub ht)))
  intro t ht
  rcases le_total t t₀ with htt₀ | ht₀t
  · exact (hpair htt₀ ht ht₀).mp hinit
  · exact (hpair ht₀t ht₀ ht).mpr hinit

theorem parallel_section_eq_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b t₀ : ℝ} {Z W : ∀ t : ℝ, V (γ t)} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, W t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0)
    (hWpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ W (Icc a b) t = 0)
    (hinit : Z t₀ = W t₀) : ∀ t ∈ Icc a b, Z t = W t :=
  cov.parallel_section_eq_on_interval hcov ordConnected_Icc ht₀ hγ hZ hW hZpar hWpar hinit

private theorem exists_parallel_transport_on_Icc_of_left_endpoint
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b)) :
    ∃ T : ∀ t : ℝ, V (γ a) ≃L[ℝ] V (γ t),
      (∀ v : V (γ a), T a v = v) ∧
      (∀ v : V (γ a), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, T t v⟩ : TotalSpace F V)) (Icc a b)) ∧
      ∀ v : V (γ a), ∀ t ∈ Icc a b,
        cov.derivAlongWithin γ (fun s => T s v) (Icc a b) t = 0 := by
  classical
  let cover : M → Set (Icc a b) := fun x =>
    (fun t : Icc a b => γ t) ⁻¹' (trivializationAt F V x).baseSet
  have hcoverOpen : ∀ x, IsOpen (cover x) := fun x =>
    (trivializationAt F V x).open_baseSet.preimage hγ.continuousOn.domRestrict
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, cover x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, mem_baseSet_trivializationAt F V (γ t)⟩
  obtain ⟨τ, hτ₀, hmono, ⟨N, hN⟩, hτ⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcoverOpen hcover
  have hstep (n : ℕ) :
      ∃ T : ∀ t : ℝ, V (γ a) ≃L[ℝ] V (γ t),
        (∀ v : V (γ a), T a v = v) ∧
        (∀ v : V (γ a), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
          (fun t => (⟨γ t, T t v⟩ : TotalSpace F V)) (Icc a (τ n : ℝ))) ∧
        ∀ v : V (γ a), ∀ t ∈ Icc a (τ n : ℝ),
          cov.derivAlongWithin γ (fun s => T s v) (Icc a (τ n : ℝ)) t = 0 := by
    induction n with
    | zero =>
      rw [hτ₀, Icc_self]
      let T (t : ℝ) : V (γ a) ≃L[ℝ] V (γ t) :=
        (VectorBundle.continuousLinearEquivAt ℝ F V (γ a)).trans
          (VectorBundle.continuousLinearEquivAt ℝ F V (γ t)).symm
      refine ⟨T, ?_, ?_, ?_⟩
      · intro v
        simp only [T, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]
      · intro v t ht
        have hta : t = a := ht
        subst t
        apply (mdifferentiableWithinAt_const (c := (⟨γ a, T a v⟩ : TotalSpace F V))).congr
        · intro s hs
          have hsa : s = a := hs
          subst s
          rfl
        · rfl
      · intro v t ht
        have hta : t = a := ht
        subst t
        exact cov.derivAlongWithin_singleton γ (fun s => T s v) a
    | succ n ih =>
      obtain ⟨T, hT₀, hTdiff, hTpar⟩ := ih
      obtain ⟨x, hx⟩ := hτ n
      let e := trivializationAt F V x
      have hle : (τ n : ℝ) ≤ τ (n + 1) := hmono (Nat.le_succ n)
      have hsub : Icc (τ n : ℝ) (τ (n + 1) : ℝ) ⊆ Icc a b := fun t ht =>
        ⟨(τ n).property.1.trans ht.1, ht.2.trans (τ (n + 1)).property.2⟩
      have he : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ), γ t ∈ e.baseSet := by
        intro t ht
        exact hx (show (⟨t, hsub ht⟩ : Icc a b) ∈ Icc (τ n) (τ (n + 1)) from ht)
      have hγprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
          (fun q : ℝ × ℝ => γ q.1) (Icc (τ n : ℝ) (τ (n + 1) : ℝ) ×ˢ univ) :=
        (hγ.mono hsub).comp contMDiffOn_fst (fun _ hq => hq.1)
      obtain ⟨S, hS₀, hSsmooth, _, hSpar⟩ :=
        cov.exists_parallel_transport_in_trivialization_on_closed_interval
          (IP := 𝓘(ℝ, ℝ)) (γ := fun t (_ : ℝ) => γ t) hcov e (left_mem_Icc.mpr hle)
          hγprod (fun t ht _ => he t ht)
      let R (t : ℝ) : V (γ a) ≃L[ℝ] V (γ t) := (T (τ n)).trans (S t 0)
      have hR₀ (v : V (γ a)) : R (τ n) v = T (τ n) v := hS₀ 0 (T (τ n) v)
      have hRdiff (v : V (γ a)) : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
          (fun t => (⟨γ t, R t v⟩ : TotalSpace F V)) (Icc (τ n : ℝ) (τ (n + 1) : ℝ)) := by
        intro t ht
        let v₀ := e.continuousLinearMapAt ℝ (γ (τ n)) (T (τ n) v)
        have harg : ContMDiffWithinAt 𝓘(ℝ, ℝ)
            ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞
            (fun s : ℝ => ((s, (0 : ℝ)), v₀))
            (Icc (τ n : ℝ) (τ (n + 1) : ℝ)) t :=
          (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const).prodMk contMDiffWithinAt_const
        have h := (hSsmooth ((t, 0), v₀) ⟨⟨ht, mem_univ 0⟩, mem_univ v₀⟩).comp
          (f := fun s : ℝ => ((s, (0 : ℝ)), v₀)) t harg
          (fun _ hs => ⟨⟨hs, mem_univ 0⟩, mem_univ v₀⟩)
        have h' := h.mdifferentiableWithinAt (by simp)
        simpa only [Function.comp_def, v₀, R, ContinuousLinearEquiv.trans_apply,
          e.symmL_continuousLinearMapAt (he (τ n) (left_mem_Icc.mpr hle))] using h'
      let U (t : ℝ) : V (γ a) ≃L[ℝ] V (γ t) := if t ≤ τ n then T t else R t
      have hU (v : V (γ a)) :
          MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
            (fun t => (⟨γ t, U t v⟩ : TotalSpace F V)) (Icc a (τ (n + 1) : ℝ)) ∧
          ∀ t ∈ Icc a (τ (n + 1) : ℝ),
            cov.derivAlongWithin γ (fun s => U s v) (Icc a (τ (n + 1) : ℝ)) t = 0 := by
        have hγsmall := hγ.mono (Icc_subset_Icc_right (τ (n + 1)).property.2)
        have h := cov.parallel_piecewise_on_Icc ⟨(τ n).property.1, hle⟩
          (hγsmall.mdifferentiableOn (by simp)) (hTdiff v) (hRdiff v) (hTpar v)
          (hSpar 0 (T (τ n) v)) (hR₀ v).symm
        have hUapply (t : ℝ) : U t v = if t ≤ τ n then T t v else R t v := by
          dsimp only [U]
          split_ifs <;> rfl
        simp_rw [hUapply]
        exact h
      refine ⟨U, ?_, fun v => (hU v).1, fun v => (hU v).2⟩
      intro v
      dsimp only [U]
      rw [if_pos (τ n).property.1]
      exact hT₀ v
  have h := hstep N
  simpa only [hN N le_rfl] using h

private theorem exists_differentiable_parallel_transport_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b)) :
    ∃ T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t),
      (∀ v : V (γ t₀), T t₀ v = v) ∧
      (∀ v : V (γ t₀), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, T t v⟩ : TotalSpace F V)) (Icc a b)) ∧
      ∀ v : V (γ t₀), ∀ t ∈ Icc a b,
        cov.derivAlongWithin γ (fun s => T s v) (Icc a b) t = 0 := by
  obtain ⟨S, _, hSdiff, hSpar⟩ :=
    exists_parallel_transport_on_Icc_of_left_endpoint cov hcov (ht₀.1.trans ht₀.2) hγ
  let T (t : ℝ) : V (γ t₀) ≃L[ℝ] V (γ t) := (S t₀).symm.trans (S t)
  exact ⟨T, fun v => (S t₀).apply_symm_apply v,
    fun v => hSdiff ((S t₀).symm v), fun v => hSpar ((S t₀).symm v)⟩

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
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

private theorem contMDiffOn_parallel_section_in_trivialization
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ))
    (he : ∀ t ∈ Icc a b, ∀ p : P, γ t p ∈ e.baseSet)
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t p, Z t p⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ p : P, ∀ t ∈ Icc a b,
      cov.derivAlongWithin (fun s => γ s p) (fun s => Z s p) (Icc a b) t = 0)
    (hinit : ContMDiff IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod IP) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × P => (⟨γ q.1 q.2, Z q.1 q.2⟩ : TotalSpace F V))
      (Icc a b ×ˢ univ) := by
  obtain ⟨S, hS₀, hSsmooth, _, hSpar⟩ :=
    cov.exists_parallel_transport_in_trivialization_on_closed_interval hcov e ht₀ hγ he
  have hzcoord : ContMDiff IP 𝓘(ℝ, F) ∞
      (fun p => e.continuousLinearMapAt ℝ (γ t₀ p) (Z t₀ p)) := by
    have h := e.contMDiffOn.comp (hinit.contMDiffOn (s := (univ : Set P)))
      (fun p _ => e.mem_source.mpr (he t₀ ht₀ p))
    rw [contMDiffOn_univ] at h
    apply h.snd.congr
    intro p
    exact e.continuousLinearMapAt_apply_of_mem ℝ (he t₀ ht₀ p) (Z t₀ p)
  have hY : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × P => (⟨γ q.1 q.2, S q.1 q.2 (Z t₀ q.2)⟩ : TotalSpace F V))
      (Icc a b ×ˢ univ) := by
    have harg : ContMDiff (𝓘(ℝ, ℝ).prod IP) ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) ∞
        (fun q : ℝ × P => (q, e.continuousLinearMapAt ℝ (γ t₀ q.2) (Z t₀ q.2))) :=
      contMDiff_id.prodMk (hzcoord.comp contMDiff_snd)
    have h := hSsmooth.comp harg.contMDiffOn (fun q hq => ⟨hq, mem_univ _⟩)
    apply h.congr
    intro q hq
    simp only [Function.comp_def, e.symmL_continuousLinearMapAt (he t₀ ht₀ q.2)]
  have hYdiff (p : P) : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t p, S t p (Z t₀ p)⟩ : TotalSpace F V)) (Icc a b) := by
    have h := hY.comp (f := fun t : ℝ => (t, p))
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ ht => ⟨ht, mem_univ p⟩)
    exact h.mdifferentiableOn (by simp)
  have hγslice (p : P) : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => γ t p) (Icc a b) := by
    have h := hγ.comp (f := fun t : ℝ => (t, p))
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ ht => ⟨ht, mem_univ p⟩)
    exact h.of_le (by simp)
  have heq (p : P) : ∀ t ∈ Icc a b, Z t p = S t p (Z t₀ p) :=
    cov.parallel_section_eq_on_Icc hcov ht₀ (hγslice p) (hZ p) (hYdiff p)
      (hZpar p) (hSpar p (Z t₀ p)) (hS₀ p (Z t₀ p)).symm
  apply hY.congr
  intro q hq
  exact congrArg (fun v => (⟨γ q.1 q.2, v⟩ : TotalSpace F V)) (heq q.2 q.1 hq.1)

private theorem exists_contMDiffOn_parallel_section_in_trivialization
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)}
    {a b t₀ : ℝ} {p₀ : P} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Icc a b, γ s p₀ ∈ e.baseSet)
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s p, Z s p⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ p : P, ∀ s ∈ Icc a b,
      cov.derivAlongWithin (fun r => γ r p) (fun r => Z r p) (Icc a b) s = 0)
    (hinit : ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V)) U) :
    ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod IP) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : ℝ × U => (⟨γ q.1 q.2, Z q.1 q.2⟩ : TotalSpace F V))
        (Icc a b ×ˢ univ) := by
  obtain ⟨U₀, hp₀U₀, hinitU₀⟩ := hinit
  have hγres : Continuous (fun q : Icc a b × P => γ q.1 q.2) :=
    hγ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun q => ⟨q.1.property, mem_univ q.2⟩)
  have hcover : (univ : Set (Icc a b)) ×ˢ {p₀} ⊆
      (fun q : Icc a b × P => γ q.1 q.2) ⁻¹' e.baseSet := by
    rintro ⟨s, p⟩ ⟨_, hp⟩
    have hpp : p = p₀ := hp
    subst p
    exact he s s.property
  obtain ⟨u, v, _, hv, htu, hpv, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton
      (e.open_baseSet.preimage hγres) hcover
  let U : TopologicalSpace.Opens P := ⟨(U₀ : Set P) ∩ v, U₀.isOpen.inter hv⟩
  have hp₀U : p₀ ∈ U := ⟨hp₀U₀, hpv (mem_singleton p₀)⟩
  have heU : ∀ s ∈ Icc a b, ∀ p : U, γ s p ∈ e.baseSet := by
    intro s hs p
    exact huv (show ((⟨s, hs⟩ : Icc a b), (p : P)) ∈ u ×ˢ v from
      ⟨htu (mem_univ (⟨s, hs⟩ : Icc a b)), p.property.2⟩)
  have hinitU : ContMDiff IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p : U => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V)) := by
    rw [← contMDiffOn_univ]
    exact hinitU₀.comp (contMDiff_subtype_val (U := U)).contMDiffOn
      (fun p _ => p.property.1)
  have hγU : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × U => γ q.1 q.2) (Icc a b ×ˢ univ) := by
    have harg : ContMDiff (𝓘(ℝ, ℝ).prod IP) (𝓘(ℝ, ℝ).prod IP) ∞
        (fun q : ℝ × U => (q.1, (q.2 : P))) :=
      contMDiff_fst.prodMk ((contMDiff_subtype_val (U := U)).comp contMDiff_snd)
    exact hγ.comp harg.contMDiffOn (fun _ hq => ⟨hq.1, mem_univ _⟩)
  have hreg := contMDiffOn_parallel_section_in_trivialization cov hcov e ht₀ hγU heU
    (fun p : U => hZ p) (fun p : U => hZpar p) hinitU
  exact ⟨U, hp₀U, hreg⟩


private theorem exists_contMDiffOn_parallel_section_endpoint
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)}
    {a b t₀ t : ℝ} {p₀ : P} (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ))
    (he : ∀ s ∈ Icc a b, γ s p₀ ∈ e.baseSet)
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s p, Z s p⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ p : P, ∀ s ∈ Icc a b,
      cov.derivAlongWithin (fun r => γ r p) (fun r => Z r p) (Icc a b) s = 0)
    (hinit : ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V)) U) :
    ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ t p, Z t p⟩ : TotalSpace F V)) U := by
  obtain ⟨U, hp₀U, hreg⟩ :=
    exists_contMDiffOn_parallel_section_in_trivialization cov hcov e ht₀ hγ he hZ hZpar hinit
  have htU : ContMDiff IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p : U => (⟨γ t p, Z t p⟩ : TotalSpace F V)) := by
    have harg : ContMDiff IP (𝓘(ℝ, ℝ).prod IP) ∞ (fun p : U => (t, p)) :=
      contMDiff_const.prodMk contMDiff_id
    have h := hreg.comp (harg.contMDiffOn (s := univ)) (fun p _ => ⟨ht, mem_univ p⟩)
    rwa [contMDiffOn_univ] at h
  refine ⟨U, hp₀U, ?_⟩
  intro p hp
  have h := (contMDiffAt_subtype_iff (I := IP) (I' := I.prod 𝓘(ℝ, F)) (U := U)
    (f := fun p : P => (⟨γ t p, Z t p⟩ : TotalSpace F V)) (x := ⟨p, hp⟩)).mp (htU ⟨p, hp⟩)
  exact h.contMDiffWithinAt

private theorem exists_contMDiffOn_parallel_section_endpoint_iff
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)} {a b : ℝ} {p₀ : P}
    (hab : a ≤ b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ))
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t p, Z t p⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ p : P, ∀ t ∈ Icc a b,
      cov.derivAlongWithin (fun s => γ s p) (fun s => Z s p) (Icc a b) t = 0) :
    (∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ b p, Z b p⟩ : TotalSpace F V)) U) ↔
    ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ a p, Z a p⟩ : TotalSpace F V)) U := by
  let Q (t : ℝ) : Prop := ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
    ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p => (⟨γ t p, Z t p⟩ : TotalSpace F V)) U
  change Q b ↔ Q a
  have hγpoint : ContinuousOn (fun t => γ t p₀) (Icc a b) :=
    (hγ.comp (f := fun t : ℝ => (t, p₀))
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ ht => ⟨ht, mem_univ p₀⟩)).continuousOn
  let cover : M → Set (Icc a b) := fun x =>
    (fun t : Icc a b => γ t p₀) ⁻¹' (trivializationAt F V x).baseSet
  have hcoverOpen : ∀ x, IsOpen (cover x) := fun x =>
    (trivializationAt F V x).open_baseSet.preimage hγpoint.domRestrict
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, cover x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t p₀, mem_baseSet_trivializationAt F V (γ t p₀)⟩
  obtain ⟨τ, hτ₀, hmono, ⟨N, hN⟩, hτ⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcoverOpen hcover
  have hstep (n : ℕ) : Q (τ (n + 1)) ↔ Q (τ n) := by
    obtain ⟨x, hx⟩ := hτ n
    let e := trivializationAt F V x
    have hle : (τ n : ℝ) ≤ τ (n + 1) := hmono (Nat.le_succ n)
    have hsub : Icc (τ n : ℝ) (τ (n + 1) : ℝ) ⊆ Icc a b := fun t ht =>
      ⟨(τ n).property.1.trans ht.1, ht.2.trans (τ (n + 1)).property.2⟩
    have he : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ), γ t p₀ ∈ e.baseSet := by
      intro t ht
      exact hx (show (⟨t, hsub ht⟩ : Icc a b) ∈ Icc (τ n) (τ (n + 1)) from ht)
    have hZsmall : ∀ p : P, ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ),
        cov.derivAlongWithin (fun s => γ s p) (fun s => Z s p)
          (Icc (τ n : ℝ) (τ (n + 1) : ℝ)) t = 0 := fun p t ht =>
      cov.derivAlongWithin_eq_zero_mono (hZ p t (hsub ht)) hsub (hZpar p t (hsub ht))
    constructor
    · intro hQ
      exact exists_contMDiffOn_parallel_section_endpoint cov hcov e
        (right_mem_Icc.mpr hle) (left_mem_Icc.mpr hle) (hγ.mono (prod_mono_left hsub))
        he (fun p => (hZ p).mono hsub) hZsmall hQ
    · intro hQ
      exact exists_contMDiffOn_parallel_section_endpoint cov hcov e
        (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) (hγ.mono (prod_mono_left hsub))
        he (fun p => (hZ p).mono hsub) hZsmall hQ
  have hall (n : ℕ) : Q (τ n) ↔ Q (τ 0) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
  exact (Iff.of_eq (congrArg Q (hN N le_rfl))).symm.trans
    ((hall N).trans (Iff.of_eq (congrArg Q hτ₀)))

private theorem exists_contMDiffOn_parallel_section_slice
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)} {J : Set ℝ}
    {t₀ t : ℝ} {p₀ : P} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) (ht : t ∈ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (J ×ˢ univ))
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s p, Z s p⟩ : TotalSpace F V)) J)
    (hZpar : ∀ p : P, ∀ s ∈ J,
      cov.derivAlongWithin (fun r => γ r p) (fun r => Z r p) J s = 0)
    (hinit : ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V)) U) :
    ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
      ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
        (fun p => (⟨γ t p, Z t p⟩ : TotalSpace F V)) U := by
  let Q (r : ℝ) : Prop := ∃ U : TopologicalSpace.Opens P, p₀ ∈ U ∧
    ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p => (⟨γ r p, Z r p⟩ : TotalSpace F V)) U
  have hpair {c d : ℝ} (hcd : c ≤ d) (hc : c ∈ J) (hd : d ∈ J) : Q d ↔ Q c := by
    have hsub : Icc c d ⊆ J := hJ.out' hc hd
    exact exists_contMDiffOn_parallel_section_endpoint_iff cov hcov hcd
      (hγ.mono (prod_mono_left hsub)) (fun p => (hZ p).mono hsub)
      (fun p s hs => cov.derivAlongWithin_eq_zero_mono
        (hZ p s (hsub hs)) hsub (hZpar p s (hsub hs)))
  rcases le_total t t₀ with htt₀ | ht₀t
  · exact (hpair htt₀ ht ht₀).mp hinit
  · exact (hpair ht₀t ht₀ ht).mpr hinit


theorem contMDiffOn_parallel_section
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {Z : ∀ t : ℝ, ∀ p : P, V (γ t p)} {J : Set ℝ}
    {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (J ×ˢ univ))
    (hZ : ∀ p : P, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s p, Z s p⟩ : TotalSpace F V)) J)
    (hZpar : ∀ p : P, ∀ s ∈ J,
      cov.derivAlongWithin (fun r => γ r p) (fun r => Z r p) J s = 0)
    (hinit : ContMDiff IP (I.prod 𝓘(ℝ, F)) ∞
      (fun p => (⟨γ t₀ p, Z t₀ p⟩ : TotalSpace F V))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod IP) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × P => (⟨γ q.1 q.2, Z q.1 q.2⟩ : TotalSpace F V))
      (J ×ˢ univ) := by
  classical
  rintro ⟨t, p₀⟩ ⟨ht, _⟩
  have hslice := exists_contMDiffOn_parallel_section_slice cov hcov hJ ht₀ ht hγ hZ hZpar
    (p₀ := p₀) ⟨⊤, mem_univ p₀, hinit.contMDiffOn⟩
  let e := trivializationAt F V (γ t p₀)
  have he₀ : γ t p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t p₀)
  have hγpoint : ContinuousWithinAt (fun s => γ s p₀) J t :=
    ((hγ.comp (f := fun s : ℝ => (s, p₀))
      (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun _ hs => ⟨hs, mem_univ p₀⟩)) t ht).continuousWithinAt
  have hneigh : (fun s => γ s p₀) ⁻¹' e.baseSet ∈ 𝓝[J] t :=
    hγpoint (e.open_baseSet.mem_nhds he₀)
  obtain ⟨u, hu, husub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hneigh
  obtain ⟨c₀, d₀, ht₀K, hK₀nhds, hK₀sub⟩ := exists_Icc_mem_subset_of_mem_nhds hu
  obtain ⟨c₁, d₁, _, ht₁K, hK₁sub, hK₁nhds⟩ := hJ.exists_Icc_subset_mem_nhdsWithin ht ht
  let c := max c₀ c₁
  let d := min d₀ d₁
  have hK : Icc c d = Icc c₀ d₀ ∩ Icc c₁ d₁ := Icc_inter_Icc.symm
  have htK : t ∈ Icc c d := hK ▸ ⟨ht₀K, ht₁K⟩
  have hKsub : Icc c d ⊆ J := by
    rw [hK]
    exact inter_subset_right.trans hK₁sub
  have hKnhds : Icc c d ∈ 𝓝[J] t := by
    rw [hK]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds hK₀nhds) hK₁nhds
  have heK : ∀ s ∈ Icc c d, γ s p₀ ∈ e.baseSet := by
    intro s hs
    have hs' := hK ▸ hs
    exact husub ⟨hK₀sub hs'.1, hK₁sub hs'.2⟩
  obtain ⟨U, hp₀U, hreg⟩ := exists_contMDiffOn_parallel_section_in_trivialization
    cov hcov e htK (hγ.mono (prod_mono_left hKsub)) heK
    (fun p => (hZ p).mono hKsub)
    (fun p s hs => cov.derivAlongWithin_eq_zero_mono (hZ p s (hKsub hs))
      hKsub (hZpar p s (hKsub hs))) hslice
  let j : P → U := fun p => if hp : p ∈ U then ⟨p, hp⟩ else ⟨p₀, hp₀U⟩
  have hjcoe (p : P) (hp : p ∈ U) : (j p : P) = p := by
    dsimp only [j]
    split_ifs
    rfl
  have hj : ContMDiffAt IP IP ∞ j p₀ := by
    apply (ContMDiffAt.subtypeVal_comp_iff U j p₀).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hp₀U] with p hp
    exact hjcoe p hp
  have harg : ContMDiffAt (𝓘(ℝ, ℝ).prod IP) (𝓘(ℝ, ℝ).prod IP) ∞
      (fun q : ℝ × P => (q.1, j q.2)) (t, p₀) :=
    contMDiffAt_fst.prodMk (hj.comp (t, p₀) contMDiffAt_snd)
  have hlocal := (hreg (t, j p₀) ⟨htK, mem_univ _⟩).comp (t, p₀)
    (harg.contMDiffWithinAt (s := Icc c d ×ˢ (univ : Set P)))
    (show MapsTo (fun q : ℝ × P => (q.1, j q.2))
      (Icc c d ×ˢ univ) (Icc c d ×ˢ univ) from fun q hq => ⟨hq.1, mem_univ _⟩)
  have hprod : Icc c d ×ˢ (univ : Set P) ∈ 𝓝[J ×ˢ univ] (t, p₀) := by
    rw [nhdsWithin_prod_eq]
    exact prod_mem_prod hKnhds univ_mem
  apply (hlocal.mono_of_mem_nhdsWithin hprod).congr_of_eventuallyEq
  · have hparam : ∀ᶠ q : ℝ × P in 𝓝[J ×ˢ univ] (t, p₀), q.2 ∈ U :=
      (continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (U.isOpen.mem_nhds hp₀U)
    filter_upwards [hparam] with q hq
    exact congrArg (fun p : P => (⟨γ q.1 p, Z q.1 p⟩ : TotalSpace F V))
      (hjcoe q.2 hq).symm
  · exact congrArg (fun p : P => (⟨γ t p, Z t p⟩ : TotalSpace F V))
      (hjcoe p₀ hp₀U).symm

private theorem exists_differentiable_parallel_transport_on_interval
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) :
    ∃ T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t),
      (∀ v : V (γ t₀), T t₀ v = v) ∧
      (∀ v : V (γ t₀), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, T t v⟩ : TotalSpace F V)) J) ∧
      ∀ v : V (γ t₀), ∀ t ∈ J,
        cov.derivAlongWithin γ (fun s => T s v) J t = 0 := by
  classical
  have hex (t : J) : ∃ S : ∀ s : ℝ, V (γ t₀) ≃L[ℝ] V (γ s),
      (∀ v : V (γ t₀), S t₀ v = v) ∧
      (∀ v : V (γ t₀), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, S s v⟩ : TotalSpace F V)) (uIcc t₀ t)) ∧
      ∀ v : V (γ t₀), ∀ s ∈ uIcc t₀ t,
        cov.derivAlongWithin γ (fun r => S r v) (uIcc t₀ t) s = 0 :=
    exists_differentiable_parallel_transport_on_Icc cov hcov left_mem_uIcc
      (hγ.mono (hJ.uIcc_subset ht₀ t.property))
  choose S hS₀ hSdiff hSpar using hex
  let T (t : ℝ) : V (γ t₀) ≃L[ℝ] V (γ t) :=
    if ht : t ∈ J then S ⟨t, ht⟩ t else
      (VectorBundle.continuousLinearEquivAt ℝ F V (γ t₀)).trans
        (VectorBundle.continuousLinearEquivAt ℝ F V (γ t)).symm
  have hT (t : ℝ) (ht : t ∈ J) : T t = S ⟨t, ht⟩ t := by
    dsimp only [T]
    rw [dif_pos ht]
  have hlocal {a b : ℝ} (ht₀K : t₀ ∈ Icc a b) (hKsub : Icc a b ⊆ J)
      (R : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t))
      (hR₀ : ∀ v : V (γ t₀), R t₀ v = v)
      (hRdiff : ∀ v : V (γ t₀), MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, R t v⟩ : TotalSpace F V)) (Icc a b))
      (hRpar : ∀ v : V (γ t₀), ∀ t ∈ Icc a b,
        cov.derivAlongWithin γ (fun s => R s v) (Icc a b) t = 0) :
      ∀ v : V (γ t₀), ∀ t ∈ Icc a b, T t v = R t v := by
    intro v t ht
    let tj : J := ⟨t, hKsub ht⟩
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀K ht
    have heq := cov.parallel_section_eq_on_Icc hcov left_mem_uIcc
      ((hγ.mono (hJ.uIcc_subset ht₀ tj.property)).of_le (by simp))
      (hSdiff tj v) ((hRdiff v).mono hsub) (hSpar tj v)
      (fun s hs => cov.derivAlongWithin_eq_zero_mono
        (hRdiff v s (hsub hs)) hsub (hRpar v s (hsub hs)))
      ((hS₀ tj v).trans (hR₀ v).symm)
    rw [hT t (hKsub ht)]
    exact heq t right_mem_uIcc
  have hTd (v : V (γ t₀)) (t : ℝ) (ht : t ∈ J) :
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, T s v⟩ : TotalSpace F V)) J t ∧
      cov.derivAlongWithin γ (fun s => T s v) J t = 0 := by
    obtain ⟨a, b, ht₀K, htK, hKsub, hKnhds⟩ :=
      hJ.exists_Icc_subset_mem_nhdsWithin ht₀ ht
    obtain ⟨R, hR₀, hRdiff, hRpar⟩ :=
      exists_differentiable_parallel_transport_on_Icc cov hcov ht₀K (hγ.mono hKsub)
    have heq := hlocal ht₀K hKsub R hR₀ hRdiff hRpar v
    have hdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, T s v⟩ : TotalSpace F V)) (Icc a b) t :=
      (hRdiff v t htK).congr
        (fun s hs => congrArg (fun w => (⟨γ s, w⟩ : TotalSpace F V)) (heq s hs))
        (congrArg (fun w => (⟨γ t, w⟩ : TotalSpace F V)) (heq t htK))
    refine ⟨hdiff.mono_of_mem_nhdsWithin hKnhds, ?_⟩
    obtain ⟨u, hu, husub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hKnhds
    have hdom : J =ᶠ[𝓝 t] Icc a b := by
      filter_upwards [hu] with s hs
      exact propext ⟨fun hsJ => husub ⟨hs, hsJ⟩, fun hsK => hKsub hsK⟩
    rw [cov.derivAlongWithin_congr_set hdom,
      cov.derivAlongWithin_congr heq (heq t htK)]
    exact hRpar v t htK
  refine ⟨T, ?_, fun v t ht => (hTd v t ht).1, fun v t ht => (hTd v t ht).2⟩
  intro v
  rw [hT t₀ ht₀]
  exact hS₀ ⟨t₀, ht₀⟩ v

private theorem contMDiffOn_parallel_transport_apply
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (J ×ˢ univ))
    (T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p))
    (hT₀ : ∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v)
    (hTdiff : ∀ p : P, ∀ v : V (γ t₀ p),
      MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t p, T t p v⟩ : TotalSpace F V)) J)
    (hTpar : ∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ J,
      cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) J t = 0)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : (ℝ × P) × F =>
        (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
          TotalSpace F V))
      {q | q.1.1 ∈ J ∧ γ t₀ q.1.2 ∈ e.baseSet} := by
  classical
  have hγ₀ : ContMDiff IP I ∞ (γ t₀) := by
    have h := hγ.comp (s := univ) (f := fun p : P => (t₀, p))
      (contMDiffOn_const.prodMk contMDiffOn_id) (fun p _ => ⟨ht₀, mem_univ p⟩)
    rwa [contMDiffOn_univ] at h
  let U : TopologicalSpace.Opens P :=
    ⟨(γ t₀) ⁻¹' e.baseSet, e.open_baseSet.preimage hγ₀.continuous⟩
  have hγU : ContMDiffOn (𝓘(ℝ, ℝ).prod (IP.prod 𝓘(ℝ, F))) I ∞
      (fun q : ℝ × (U × F) => γ q.1 q.2.1) (J ×ˢ univ) := by
    have hparam : ContMDiff (𝓘(ℝ, ℝ).prod (IP.prod 𝓘(ℝ, F))) IP ∞
        (fun q : ℝ × (U × F) => (q.2.1 : P)) :=
      (contMDiff_subtype_val (U := U)).comp (contMDiff_fst.comp contMDiff_snd)
    exact hγ.comp (contMDiff_fst.prodMk hparam).contMDiffOn
      (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hinit : ContMDiff (IP.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
      (fun p : U × F =>
        (⟨γ t₀ p.1, T t₀ p.1 (e.symmL ℝ (γ t₀ p.1) p.2)⟩ : TotalSpace F V)) := by
    have hbase : ContMDiff (IP.prod 𝓘(ℝ, F)) I ∞
        (fun p : U × F => γ t₀ p.1) :=
      hγ₀.comp ((contMDiff_subtype_val (U := U)).comp contMDiff_fst)
    have h := e.contMDiffOn_symm.comp
      ((hbase.prodMk contMDiff_snd).contMDiffOn (s := univ))
      (fun p _ => e.mem_target.mpr p.1.property)
    rw [contMDiffOn_univ] at h
    apply h.congr
    intro p
    rw [hT₀, e.symmL_apply p.1.property, e.mk_symm p.1.property]
    rfl
  have hreg := cov.contMDiffOn_parallel_section hcov hJ ht₀ hγU
    (Z := fun t (p : U × F) => T t p.1 (e.symmL ℝ (γ t₀ p.1) p.2))
    (fun p => hTdiff p.1 (e.symmL ℝ (γ t₀ p.1) p.2))
    (fun p => hTpar p.1 (e.symmL ℝ (γ t₀ p.1) p.2)) hinit
  rintro ⟨⟨t, p₀⟩, v₀⟩ ⟨ht, hp₀⟩
  have hp₀U : p₀ ∈ U := hp₀
  let j : P → U := fun p => if hp : p ∈ U then ⟨p, hp⟩ else ⟨p₀, hp₀U⟩
  have hjcoe (p : P) (hp : p ∈ U) : (j p : P) = p := by
    dsimp only [j]
    split_ifs
    rfl
  have hj : ContMDiffAt IP IP ∞ j p₀ := by
    apply (ContMDiffAt.subtypeVal_comp_iff U j p₀).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hp₀U] with p hp
    exact hjcoe p hp
  have harg : ContMDiffAt ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F))
      (𝓘(ℝ, ℝ).prod (IP.prod 𝓘(ℝ, F))) ∞
      (fun q : (ℝ × P) × F => (q.1.1, (j q.1.2, q.2))) ((t, p₀), v₀) := by
    have hp : ContMDiffAt ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) IP ∞
        (fun q : (ℝ × P) × F => j q.1.2) ((t, p₀), v₀) :=
      hj.comp ((t, p₀), v₀) (contMDiffAt_snd.comp _ contMDiffAt_fst)
    exact (contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk (hp.prodMk contMDiffAt_snd)
  have h := (hreg (t, (j p₀, v₀)) ⟨ht, mem_univ _⟩).comp ((t, p₀), v₀)
    (harg.contMDiffWithinAt
      (s := {q : (ℝ × P) × F | q.1.1 ∈ J ∧ γ t₀ q.1.2 ∈ e.baseSet}))
    (show MapsTo (fun q : (ℝ × P) × F => (q.1.1, (j q.1.2, q.2)))
      {q | q.1.1 ∈ J ∧ γ t₀ q.1.2 ∈ e.baseSet} (J ×ˢ univ) from
      fun q hq => ⟨hq.1, mem_univ _⟩)
  apply h.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact congrArg (fun p : P =>
      (⟨γ q.1.1 p, T q.1.1 p (e.symmL ℝ (γ t₀ p) q.2)⟩ : TotalSpace F V))
      (hjcoe q.1.2 hq.2).symm
  · exact congrArg (fun p : P =>
      (⟨γ t p, T t p (e.symmL ℝ (γ t₀ p) v₀)⟩ : TotalSpace F V))
      (hjcoe p₀ hp₀U).symm

theorem exists_parallel_transport_on_interval
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (J ×ˢ univ)) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
              TotalSpace F V))
          {q | q.1.1 ∈ J ∧ γ t₀ q.1.2 ∈ e.baseSet}) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ t₀ q.1.2,
              (T q.1.1 q.1.2).symm (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
          {q | q.1.1 ∈ J ∧ γ q.1.1 q.1.2 ∈ e.baseSet}) ∧
      ∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ J,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) J t = 0 := by
  have hγslice (p : P) : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t => γ t p) J :=
    hγ.comp (f := fun t : ℝ => (t, p))
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ ht => ⟨ht, mem_univ p⟩)
  choose S hS₀ hSdiff hSpar using fun p : P =>
    exists_differentiable_parallel_transport_on_interval cov hcov hJ ht₀ (hγslice p)
  let T (t : ℝ) (p : P) : V (γ t₀ p) ≃L[ℝ] V (γ t p) := S p t
  have hforward := contMDiffOn_parallel_transport_apply cov hcov hJ ht₀ hγ T hS₀ hSdiff hSpar
  refine ⟨T, hS₀, hforward, ?_, hSpar⟩
  have hγ₀ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ t₀ q.2) (J ×ˢ univ) :=
    hγ.comp (contMDiffOn_const.prodMk contMDiffOn_snd)
      (fun q _ => ⟨ht₀, mem_univ q.2⟩)
  intro e _
  have h := contMDiffOn_bundle_map_symm (fun q : ℝ × P => T q.1 q.2) hγ₀
    (fun e₀ _ => by
      simpa only [mem_prod, mem_univ, and_true] using hforward e₀) e
  simpa only [mem_prod, mem_univ, and_true] using h

theorem exists_parallel_transport_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ)) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
              TotalSpace F V))
          {q | q.1.1 ∈ Icc a b ∧ γ t₀ q.1.2 ∈ e.baseSet}) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ t₀ q.1.2,
              (T q.1.1 q.1.2).symm (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
          {q | q.1.1 ∈ Icc a b ∧ γ q.1.1 q.1.2 ∈ e.baseSet}) ∧
      ∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ Icc a b,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) (Icc a b) t = 0 :=
  cov.exists_parallel_transport_on_interval hcov ordConnected_Icc ht₀ hγ

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
  obtain ⟨T, hT₀, hTforward, hTinverse, hTpar⟩ :=
    cov.exists_parallel_transport_on_Icc hcov ht₀ hγ
  exact ⟨T, hT₀,
    (hTforward e).mono (fun q hq => ⟨hq.1.1, he t₀ ht₀ q.1.2⟩),
    (hTinverse e).mono (fun q hq => ⟨hq.1.1, he q.1.1 hq.1.1 q.1.2⟩), hTpar⟩

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

theorem IsMetricCompatible.exists_parallel_transport_on_interval
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (J ×ˢ univ)) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
              TotalSpace F V))
          {q | q.1.1 ∈ J ∧ γ t₀ q.1.2 ∈ e.baseSet}) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ t₀ q.1.2,
              (T q.1.1 q.1.2).symm (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
          {q | q.1.1 ∈ J ∧ γ q.1.1 q.1.2 ∈ e.baseSet}) ∧
      (∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ J,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) J t = 0) ∧
      ∀ t ∈ J, ∀ p : P, ∀ v w : V (γ t₀ p),
        inner ℝ (T t p v) (T t p w) = inner ℝ v w := by
  obtain ⟨T, hT₀, hTsmooth, hTinv, hTpar⟩ :=
    cov.exists_parallel_transport_on_interval hcov hJ ht₀ hγ
  refine ⟨T, hT₀, hTsmooth, hTinv, hTpar, ?_⟩
  have hdiff (p : P) (v : V (γ t₀ p)) :
      MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s p, T s p v⟩ : TotalSpace F V)) J := by
    let e := trivializationAt F V (γ t₀ p)
    have he : γ t₀ p ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t₀ p)
    let v₀ := e.continuousLinearMapAt ℝ (γ t₀ p) v
    have harg : ContMDiff 𝓘(ℝ, ℝ)
        ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) ∞ (fun s : ℝ => ((s, p), v₀)) :=
      (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
    have h := (hTsmooth e).comp (harg.contMDiffOn (s := J)) (fun _ hs => ⟨hs, he⟩)
    have h' := h.mdifferentiableOn (by simp)
    simpa only [Function.comp_def, v₀, e.symmL_continuousLinearMapAt he] using h'
  intro t ht p v w
  have h := hmetric.inner_eq_of_parallel hJ.convex (hdiff p v) (hdiff p w)
    (hTpar p v) (hTpar p w) ht ht₀
  simpa only [hT₀] using h

theorem IsMetricCompatible.exists_parallel_transport_on_Icc
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → P → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod IP) I ∞
      (fun q : ℝ × P => γ q.1 q.2) (Icc a b ×ˢ univ)) :
    ∃ T : ∀ t : ℝ, ∀ p : P, V (γ t₀ p) ≃L[ℝ] V (γ t p),
      (∀ p : P, ∀ v : V (γ t₀ p), T t₀ p v = v) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ q.1.1 q.1.2, T q.1.1 q.1.2 (e.symmL ℝ (γ t₀ q.1.2) q.2)⟩ :
              TotalSpace F V))
          {q | q.1.1 ∈ Icc a b ∧ γ t₀ q.1.2 ∈ e.baseSet}) ∧
      (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
        ∀ [MemTrivializationAtlas e],
        ContMDiffOn ((𝓘(ℝ, ℝ).prod IP).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
          (fun q : (ℝ × P) × F =>
            (⟨γ t₀ q.1.2,
              (T q.1.1 q.1.2).symm (e.symmL ℝ (γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
          {q | q.1.1 ∈ Icc a b ∧ γ q.1.1 q.1.2 ∈ e.baseSet}) ∧
      (∀ p : P, ∀ v : V (γ t₀ p), ∀ t ∈ Icc a b,
        cov.derivAlongWithin (fun s => γ s p) (fun s => T s p v) (Icc a b) t = 0) ∧
      ∀ t ∈ Icc a b, ∀ p : P, ∀ v w : V (γ t₀ p),
        inner ℝ (T t p v) (T t p w) = inner ℝ v w :=
  hmetric.exists_parallel_transport_on_interval hcov ordConnected_Icc ht₀ hγ

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
  obtain ⟨T, hT₀, hTforward, hTinverse, hTpar, hTinner⟩ :=
    hmetric.exists_parallel_transport_on_Icc hcov ht₀ hγ
  exact ⟨T, hT₀,
    (hTforward e).mono (fun q hq => ⟨hq.1.1, he t₀ ht₀ q.1.2⟩),
    (hTinverse e).mono (fun q hq => ⟨hq.1.1, he q.1.1 hq.1.1 q.1.2⟩), hTpar, hTinner⟩

end CovariantDerivative
