import DifferentialGeometry.Topology.Manifold.LocalContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantSet
import DifferentialGeometry.Geometry.Connection.ParallelTransport.VectorBundle

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] in
private def fiberIsometry {x y : M} (h : x = y) : V x ≃ₗᵢ[ℝ] V y := by
  subst y
  exact LinearIsometryEquiv.refl ℝ (V x)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] in
omit [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] in
private theorem mk_fiberIsometry {x y : M} (h : x = y) (v : V x) :
    (⟨y, fiberIsometry h v⟩ : TotalSpace F V) = ⟨x, v⟩ := by
  subst y
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiffOn_fixed_fiber {EP : Type*} [NormedAddCommGroup EP]
    [NormedSpace ℝ EP] {HP : Type*} [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {x : M} {f : P → V x} {s : Set P}
    (hf : ContMDiffOn IP (I.prod 𝓘(ℝ, F)) ∞ (fun p => (⟨x, f p⟩ : TotalSpace F V)) s) :
    ContMDiffOn IP 𝓘(ℝ, V x) ∞ f s := by
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hc : ContMDiffOn IP 𝓘(ℝ, F) ∞ (fun p => e.continuousLinearMapAt ℝ x (f p)) s := by
    intro p hp
    have h := (contMDiffWithinAt_totalSpace.mp (hf p hp)).2
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ he] using h
  have h := (e.symmL ℝ x).contMDiff.comp_contMDiffOn hc
  simpa only [Function.comp_def, e.symmL_continuousLinearMapAt he] using h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
private theorem symmL_eq_fiberIsometry
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {x y : M} (h : x = y) (hy : y ∈ e.baseSet) (v : V y) :
    e.symmL ℝ x (e.continuousLinearMapAt ℝ y v) = (fiberIsometry h).symm v := by
  subst y
  exact e.symmL_continuousLinearMapAt hy v

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
private theorem symmL_fiberIsometry
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {x y : M} (h : x = y) (v : F) :
    e.symmL ℝ x v = (fiberIsometry h).symm (e.symmL ℝ y v) := by
  subst y
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem local_trivialization_of_parallel_transport
    (cov : CovariantDerivative I F V) (U : TopologicalSpace.Opens M) (x₀ : M)
    (Γ : ℝ → U → M)
    (hΓ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × U => Γ q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hΓ₀ : ∀ x : U, Γ 0 x = x₀) (hΓ₁ : ∀ x : U, Γ 1 x = x)
    (T : ∀ t : ℝ, ∀ x : U, V (Γ 0 x) ≃L[ℝ] V (Γ t x))
    (hT₀ : ∀ x v, T 0 x v = v)
    (hTf : ∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
      ∀ [MemTrivializationAtlas e],
      ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × U) × F => (⟨Γ q.1.1 q.1.2,
          T q.1.1 q.1.2 (e.symmL ℝ (Γ 0 q.1.2) q.2)⟩ : TotalSpace F V))
        {q | q.1.1 ∈ Icc (0 : ℝ) 1 ∧ Γ 0 q.1.2 ∈ e.baseSet})
    (hTi : ∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
      ∀ [MemTrivializationAtlas e],
      ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : (ℝ × U) × F => (⟨Γ 0 q.1.2,
          (T q.1.1 q.1.2).symm (e.symmL ℝ (Γ q.1.1 q.1.2) q.2)⟩ : TotalSpace F V))
        {q | q.1.1 ∈ Icc (0 : ℝ) 1 ∧ Γ q.1.1 q.1.2 ∈ e.baseSet})
    (hTp : ∀ x v t, t ∈ Icc (0 : ℝ) 1 →
      cov.derivAlongWithin (fun s => Γ s x) (fun s => T s x v) (Icc (0 : ℝ) 1) t = 0) :
  let Q : ∀ x : U, V x₀ ≃L[ℝ] V (x : M) := fun x =>
    ((fiberIsometry (hΓ₀ x)).symm.toContinuousLinearEquiv.trans (T 1 x)).trans
      (fiberIsometry (hΓ₁ x)).toContinuousLinearEquiv
  ContMDiff (I.prod 𝓘(ℝ, V x₀)) (I.prod 𝓘(ℝ, F)) ∞
    (fun q : U × V x₀ => (⟨(q.1 : M), Q q.1 q.2⟩ : TotalSpace F V)) ∧
  (∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
    ∀ [MemTrivializationAtlas e],
    ContMDiffOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V x₀) ∞
      (fun q : U × F => (Q q.1).symm (e.symmL ℝ (q.1 : M) q.2))
      {q | (q.1 : M) ∈ e.baseSet}) ∧
  ∀ K : Set (TotalSpace F V), cov.IsParallelSet K → ∀ x : U,
    Q x '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} =
      {v : V (x : M) | (⟨(x : M), v⟩ : TotalSpace F V) ∈ K} := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let Q : ∀ x : U, V x₀ ≃L[ℝ] V (x : M) := fun x =>
    ((fiberIsometry (hΓ₀ x)).symm.toContinuousLinearEquiv.trans (T 1 x)).trans
      (fiberIsometry (hΓ₁ x)).toContinuousLinearEquiv
  let e₀ := trivializationAt F V x₀
  have he₀ : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F V x₀
  have hQf (x : U) (v : V x₀) :
      (⟨(x : M), Q x v⟩ : TotalSpace F V) =
        ⟨Γ 1 x, T 1 x (e₀.symmL ℝ (Γ 0 x) (e₀.continuousLinearMapAt ℝ x₀ v))⟩ := by
    change (⟨(x : M), fiberIsometry (hΓ₁ x)
      (T 1 x ((fiberIsometry (hΓ₀ x)).symm v))⟩ : TotalSpace F V) = _
    rw [mk_fiberIsometry, symmL_eq_fiberIsometry e₀ (hΓ₀ x) he₀ v]
  have hforward : ContMDiff (I.prod 𝓘(ℝ, V x₀)) (I.prod 𝓘(ℝ, F)) ∞
      (fun q : U × V x₀ => (⟨(q.1 : M), Q q.1 q.2⟩ : TotalSpace F V)) := by
    have harg : ContMDiff (I.prod 𝓘(ℝ, V x₀))
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun q : U × V x₀ => (((1 : ℝ), q.1), e₀.continuousLinearMapAt ℝ x₀ q.2)) :=
      (contMDiff_const.prodMk contMDiff_fst).prodMk
        ((e₀.continuousLinearMapAt ℝ x₀).contMDiff.comp contMDiff_snd)
    have h := (hTf e₀).comp (harg.contMDiffOn (s := univ))
      (fun q _ => ⟨hone, by rw [hΓ₀]; exact he₀⟩)
    rw [contMDiffOn_univ] at h
    exact h.congr (fun q => hQf q.1 q.2)
  refine ⟨hforward, ?_, ?_⟩
  · intro e he
    have harg : ContMDiff (I.prod 𝓘(ℝ, F))
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun q : U × F => (((1 : ℝ), q.1), q.2)) :=
      (contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd
    have h := (hTi e).comp harg.contMDiffOn
      (fun q hq => ⟨hone, by rw [hΓ₁]; exact hq⟩)
    apply contMDiffOn_fixed_fiber (F := F) (I := I)
    apply h.congr
    intro q hq
    change (⟨x₀, fiberIsometry (hΓ₀ q.1)
      ((T 1 q.1).symm ((fiberIsometry (hΓ₁ q.1)).symm
        (e.symmL ℝ (q.1 : M) q.2)))⟩ : TotalSpace F V) = _
    dsimp only [Function.comp_apply]
    rw [mk_fiberIsometry, symmL_fiberIsometry e (hΓ₁ q.1)]
  · intro K hK x
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t => Γ t x) (Icc (0 : ℝ) 1) :=
      hΓ.comp (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ ht => ⟨ht, mem_univ x⟩)
    have hdiff (v : V (Γ 0 x)) : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨Γ t x, T t x v⟩ : TotalSpace F V)) (Icc (0 : ℝ) 1) := by
      have he : Γ 0 x ∈ e₀.baseSet := by rw [hΓ₀]; exact he₀
      have harg : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
          (fun t : ℝ => ((t, x), e₀.continuousLinearMapAt ℝ (Γ 0 x) v)) :=
        (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
      have h := ((hTf e₀).comp harg.contMDiffOn (fun _ ht => ⟨ht, he⟩)).mdifferentiableOn
        (by simp)
      simpa only [Function.comp_def, e₀.symmL_continuousLinearMapAt he] using h
    have hmem (v : V x₀) : (⟨(x : M), Q x v⟩ : TotalSpace F V) ∈ K ↔
        (⟨x₀, v⟩ : TotalSpace F V) ∈ K := by
      let v₀ := e₀.symmL ℝ (Γ 0 x) (e₀.continuousLinearMapAt ℝ x₀ v)
      have hstart : (⟨Γ 0 x, v₀⟩ : TotalSpace F V) = ⟨x₀, v⟩ := by
        dsimp only [v₀]
        rw [symmL_eq_fiberIsometry e₀ (hΓ₀ x) he₀ v]
        have h := mk_fiberIsometry (F := F) (hΓ₀ x) ((fiberIsometry (hΓ₀ x)).symm v)
        simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm
      rw [hQf]
      have h := hK.mem_iff_of_parallel hzero hone hγ (hdiff v₀) (hTp x v₀)
      simpa only [hT₀, hstart] using h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmem w).mpr hw
    · intro hv
      refine ⟨(Q x).symm v, ?_, (Q x).apply_symm_apply v⟩
      exact (hmem ((Q x).symm v)).mp
        (by simpa only [(Q x).apply_symm_apply, mem_ofPred_eq] using hv)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F] in
private theorem contMDiff_inverse_local_trivialization
    (U : TopologicalSpace.Opens M) (x₀ : M)
    (Q : ∀ x : U, V x₀ ≃L[ℝ] V (x : M))
    (hQ : ∀ (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)),
      ∀ [MemTrivializationAtlas e],
      ContMDiffOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V x₀) ∞
        (fun q : U × F => (Q q.1).symm (e.symmL ℝ (q.1 : M) q.2))
        {q | (q.1 : M) ∈ e.baseSet}) :
    ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V x₀) ∞
      (fun z : TopologicalSpace.Opens.comap
          ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U =>
        (Q ⟨z.val.proj, z.property⟩).symm z.val.2) := by
  let W := TopologicalSpace.Opens.comap
    ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U
  let b : W → U := fun z => ⟨z.val.proj, z.property⟩
  have hb : ContMDiff (I.prod 𝓘(ℝ, F)) I ∞ b := by
    apply (ContMDiff.subtypeVal_comp_iff U b).mp
    exact (contMDiff_proj V).comp contMDiff_subtype_val
  intro z₀
  let e := trivializationAt F V z₀.val.proj
  have he : z₀.val.proj ∈ e.baseSet := mem_baseSet_trivializationAt F V z₀.val.proj
  have hc : ContMDiffAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
      (fun z : W => (e z.val).2) z₀ :=
    (e.contMDiffAt_iff (e.mem_source.mpr he)).mp
      (contMDiff_subtype_val (U := W) z₀) |>.2
  have harg := (hb z₀).prodMk hc
  have hmem : ∀ᶠ z : W in 𝓝 z₀, z.val.proj ∈ e.baseSet :=
    ((FiberBundle.continuous_proj F V).comp continuous_subtype_val).continuousAt
      (e.open_baseSet.mem_nhds he)
  have h := ((hQ e).contMDiffAt
    ((e.open_baseSet.preimage (continuous_subtype_val.comp continuous_fst)).mem_nhds he)).comp
      z₀ harg
  apply h.congr_of_eventuallyEq
  filter_upwards [hmem] with z hz
  change (Q (b z)).symm z.val.2 = (Q (b z)).symm (e.symmL ℝ z.val.proj (e z.val).2)
  congr 1
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz, e.symmL_continuousLinearMapAt hz]

theorem exists_local_parallel_trivialization
    (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞) (x₀ : M) :
    ∃ (U : TopologicalSpace.Opens M) (hx₀ : x₀ ∈ U)
      (Q : ∀ x : U, V x₀ ≃L[ℝ] V (x : M)),
      (∀ v : V x₀, Q ⟨x₀, hx₀⟩ v = v) ∧
      ContMDiff (I.prod 𝓘(ℝ, V x₀)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : U × V x₀ => (⟨(q.1 : M), Q q.1 q.2⟩ : TotalSpace F V)) ∧
      ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V x₀) ∞
        (fun z : TopologicalSpace.Opens.comap
            ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U =>
          (Q ⟨z.val.proj, z.property⟩).symm z.val.2) ∧
      ∀ K : Set (TotalSpace F V), cov.IsParallelSet K → ∀ x : U,
        Q x '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} =
          {v : V (x : M) | (⟨(x : M), v⟩ : TotalSpace F V) ∈ K} := by
  obtain ⟨U, hx₀, Γ, hΓ, hΓ₀, hΓ₁, _, _⟩ :=
    exists_contMDiff_local_contraction (I := I) (n := ∞) x₀
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨T, hT₀, hTf, hTi, hTp⟩ :=
    cov.exists_parallel_transport_on_Icc hcov hzero hΓ
  let Q : ∀ x : U, V x₀ ≃L[ℝ] V (x : M) := fun x =>
    ((fiberIsometry (hΓ₀ x)).symm.toContinuousLinearEquiv.trans (T 1 x)).trans
      (fiberIsometry (hΓ₁ x)).toContinuousLinearEquiv
  obtain ⟨hQf, hQi, hQK⟩ :=
    local_trivialization_of_parallel_transport cov U x₀ Γ hΓ hΓ₀ hΓ₁ T hT₀ hTf hTi hTp
  let L : V x₀ ≃L[ℝ] V x₀ := Q ⟨x₀, hx₀⟩
  let Q' : ∀ x : U, V x₀ ≃L[ℝ] V (x : M) := fun x => L.symm.trans (Q x)
  refine ⟨U, hx₀, Q', ?_, ?_, ?_, ?_⟩
  · intro v
    exact L.apply_symm_apply v
  · exact hQf.comp (contMDiff_fst.prodMk
      (L.symm.toContinuousLinearMap.contMDiff.comp contMDiff_snd))
  · exact L.toContinuousLinearMap.contMDiff.comp
      (contMDiff_inverse_local_trivialization U x₀ Q hQi)
  · intro K hK x
    have hL := hQK K hK ⟨x₀, hx₀⟩
    have hLi : L.symm '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} =
        {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} := by
      calc
        _ = L.symm '' (L '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K}) :=
          congrArg (fun s : Set (V x₀) => L.symm '' s) hL.symm
        _ = _ := L.toEquiv.symm_image_image _
    change (fun v => Q x (L.symm v)) '' _ = _
    rw [← image_image, hLi]
    exact hQK K hK x

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem IsMetricCompatible.exists_local_isometric_trivialization
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    (hcov : ContMDiffCovariantDerivative cov ∞) (x₀ : M) :
    ∃ (U : TopologicalSpace.Opens M) (hx₀ : x₀ ∈ U)
      (Q : ∀ x : U, V x₀ ≃ₗᵢ[ℝ] V (x : M)),
      (∀ v : V x₀, Q ⟨x₀, hx₀⟩ v = v) ∧
      ContMDiff (I.prod 𝓘(ℝ, V x₀)) (I.prod 𝓘(ℝ, F)) ∞
        (fun q : U × V x₀ => (⟨(q.1 : M), Q q.1 q.2⟩ : TotalSpace F V)) ∧
      ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V x₀) ∞
        (fun z : TopologicalSpace.Opens.comap
            ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U =>
          (Q ⟨z.val.proj, z.property⟩).symm z.val.2) ∧
      ∀ K : Set (TotalSpace F V), cov.IsParallelSet K → ∀ x : U,
        Q x '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} =
          {v : V (x : M) | (⟨(x : M), v⟩ : TotalSpace F V) ∈ K} := by
  obtain ⟨U, hx₀, Γ, hΓ, hΓ₀, hΓ₁, _, _⟩ :=
    exists_contMDiff_local_contraction (I := I) (n := ∞) x₀
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨T, hT₀, hTf, hTi, hTp, hTm⟩ :=
    hmetric.exists_parallel_transport_on_Icc hcov hzero hΓ
  let R : ∀ x : U, V x₀ ≃L[ℝ] V (x : M) := fun x =>
    ((fiberIsometry (hΓ₀ x)).symm.toContinuousLinearEquiv.trans (T 1 x)).trans
      (fiberIsometry (hΓ₁ x)).toContinuousLinearEquiv
  obtain ⟨hQf, hQi, hQK⟩ :=
    local_trivialization_of_parallel_transport cov U x₀ Γ hΓ hΓ₀ hΓ₁ T hT₀ hTf hTi hTp
  have hnorm (x : U) (v : V x₀) : ‖R x v‖ = ‖v‖ := by
    change ‖fiberIsometry (hΓ₁ x) (T 1 x ((fiberIsometry (hΓ₀ x)).symm v))‖ = ‖v‖
    rw [LinearIsometryEquiv.norm_map]
    exact (((T 1 x).toLinearEquiv.isometryOfInner (hTm 1 hone x)).norm_map _).trans
      ((fiberIsometry (hΓ₀ x)).symm.norm_map v)
  let Q : ∀ x : U, V x₀ ≃ₗᵢ[ℝ] V (x : M) := fun x =>
    { (R x).toLinearEquiv with norm_map' := hnorm x }
  let L : V x₀ ≃ₗᵢ[ℝ] V x₀ := Q ⟨x₀, hx₀⟩
  let Q' : ∀ x : U, V x₀ ≃ₗᵢ[ℝ] V (x : M) := fun x => L.symm.trans (Q x)
  refine ⟨U, hx₀, Q', ?_, ?_, ?_, ?_⟩
  · intro v
    exact L.apply_symm_apply v
  · exact hQf.comp (contMDiff_fst.prodMk
      (L.symm.toLinearIsometry.toContinuousLinearMap.contMDiff.comp contMDiff_snd))
  · exact L.toLinearIsometry.toContinuousLinearMap.contMDiff.comp
      (contMDiff_inverse_local_trivialization U x₀ (fun x => (Q x).toContinuousLinearEquiv) hQi)
  · intro K hK x
    have hL := hQK K hK ⟨x₀, hx₀⟩
    have hLi : L.symm '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} =
        {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K} := by
      calc
        _ = L.symm '' (L '' {v : V x₀ | (⟨x₀, v⟩ : TotalSpace F V) ∈ K}) :=
          congrArg (fun s : Set (V x₀) => L.symm '' s) hL.symm
        _ = _ := L.toEquiv.symm_image_image _
    change (fun v => Q x (L.symm v)) '' _ = _
    rw [← image_image, hLi]
    exact hQK K hK x

end CovariantDerivative
