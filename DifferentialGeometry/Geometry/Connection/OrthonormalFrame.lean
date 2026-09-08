import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Connector
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Smooth

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

def coframeConnectionForm (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) (p : P) :
    TangentSpace IP p →L[ℝ] F →L[ℝ] F := by
  let e := trivializationAt F V (b p)
  let A : P → F →L[ℝ] F := fun z =>
    (e.continuousLinearMapAt ℝ (b z)).comp (q z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let B := (q p).toContinuousLinearEquiv.toContinuousLinearMap.comp (e.symmL ℝ (b p))
  let C := mvfderiv IP A p + ((ContinuousLinearMap.compL ℝ F F F).flip (A p)).comp
      ((cov.connectionForm e (b p)).comp (mfderiv IP I b p))
  exact -((ContinuousLinearMap.compL ℝ F F F B).comp C)

private theorem mdifferentiableAt_coframe_coord {b : P → M}
    (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (he : b p ∈ e.baseSet) :
    MDifferentiableAt IP 𝓘(ℝ, F →L[ℝ] F)
      (fun z => (e.continuousLinearMapAt ℝ (b z)).comp
        (q z).symm.toContinuousLinearEquiv.toContinuousLinearMap) p := by
  apply (contMDiffAt_clm_of_pointwise (n := 1) ?_).mdifferentiableAt (by simp)
  intro w
  have h := (e.contMDiffAt_iff (IB := I)
    (e.mem_source.mpr he)).mp (hq w)
  apply h.2.congr_of_eventuallyEq
  filter_upwards [h.1.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with z hz
  exact e.continuousLinearMapAt_apply_of_mem ℝ hz ((q z).symm w)

theorem coframeConnectionForm_apply (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p)
    (U : TangentSpace IP p) (w : F) :
    cov.coframeConnectionForm q p U w =
      -q p (cov.connector (⟨b p, (q p).symm w⟩ : TotalSpace F V)
        (mfderiv IP (I.prod 𝓘(ℝ, F))
          (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p U)) := by
  let e := trivializationAt F V (b p)
  have he : b p ∈ e.baseSet := mem_baseSet_trivializationAt F V (b p)
  let A : P → F →L[ℝ] F := fun z =>
    (e.continuousLinearMapAt ℝ (b z)).comp (q z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : MDifferentiableAt IP 𝓘(ℝ, F →L[ℝ] F) A p :=
    mdifferentiableAt_coframe_coord q hq e he
  have hd := congrArg (fun L => L U)
    (hA.mvfderiv_clm_apply (mdifferentiableAt_const (c := w)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hd
  rw [cov.connector_mfderiv_eq e he ((hq w).mdifferentiableAt (by simp))]
  unfold coframeConnectionForm
  change -q p (e.symmL ℝ (b p) ((mvfderiv IP A p U) w +
    cov.connectionForm e (b p) (mfderiv IP I b p U) (A p w))) = _
  rw [← hd]
  rfl

theorem coframeConnectionForm_smul_apply (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p)
    (g : F ≃ₗᵢ[ℝ] F) (U : TangentSpace IP p) (w : F) :
    cov.coframeConnectionForm (fun z => g • q z) p U w =
      g (cov.coframeConnectionForm q p U (g.symm w)) := by
  have hq' (v : F) : ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (g • q z).symm v⟩ : TotalSpace F V)) p := hq (g.symm v)
  rw [cov.coframeConnectionForm_apply _ hq', cov.coframeConnectionForm_apply _ hq,
    map_neg]
  rfl

variable {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

theorem coframeConnectionForm_comp_apply (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {f : Q → P} {x : Q}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) (f x))
    (hf : ContMDiffAt IQ IP 1 f x) (U : TangentSpace IQ x) (w : F) :
    cov.coframeConnectionForm (fun z => q (f z)) x U w =
      cov.coframeConnectionForm q (f x) (mfderiv IQ IP f x U) w := by
  rw [cov.coframeConnectionForm_apply _ (fun v => (hq v).comp x hf),
    cov.coframeConnectionForm_apply _ hq]
  congr 3
  exact congrArg (fun L => L U) (mfderiv_comp x
    ((hq w).mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)))

variable [IsContMDiffRiemannianBundle I 1 F V]

theorem IsMetricCompatible.coframeConnectionForm_mem_skewAdjoint
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p)
    (U : TangentSpace IP p) :
    cov.coframeConnectionForm q p U ∈ skewAdjoint.submodule ℝ (F →L[ℝ] F) := by
  change star (cov.coframeConnectionForm q p U) = -cov.coframeConnectionForm q p U
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    neg_apply, inner_neg_right]
  have h := hcov.mvfderiv_inner ((hq v).mdifferentiableAt (by simp))
    ((hq w).mdifferentiableAt (by simp)) U
  simp only [LinearIsometryEquiv.inner_map_map, mvfderiv_const,
    zero_apply] at h
  rw [cov.coframeConnectionForm_apply q hq U v,
    cov.coframeConnectionForm_apply q hq U w, inner_neg_left, inner_neg_right, neg_neg]
  rw [← (q p).symm.inner_map_map, ← (q p).symm.inner_map_map]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  linarith

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem coframeConnectionForm_eq_zero_iff (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p)
    (U : TangentSpace IP p) :
    cov.coframeConnectionForm q p U = 0 ↔ ∀ w : F,
      cov.connector (⟨b p, (q p).symm w⟩ : TotalSpace F V)
        (mfderiv IP (I.prod 𝓘(ℝ, F))
          (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p U) = 0 := by
  rw [ContinuousLinearMap.ext_iff]
  simp only [zero_apply, cov.coframeConnectionForm_apply q hq,
    neg_eq_zero, EmbeddingLike.map_eq_zero_iff]

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem coframeConnectionForm_curve_apply (cov : CovariantDerivative I F V)
    {γ : ℝ → M} (q : ∀ t, V (γ t) ≃ₗᵢ[ℝ] F) {t : ℝ}
    (hq : ∀ w : F, ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 1
      (fun s => (⟨γ s, (q s).symm w⟩ : TotalSpace F V)) t) (w : F) :
    cov.coframeConnectionForm q t ((NormedSpace.fromTangentSpace t).symm 1) w =
      -q t (cov.derivAlongWithin γ (fun s => (q s).symm w) univ t) := by
  rw [cov.coframeConnectionForm_apply _ hq]
  congr 2
  simpa only [mfderivWithin_univ] using
    cov.connector_mfderivWithin_curve (J := univ) ((hq w).mdifferentiableAt (by simp)).mdifferentiableWithinAt

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem coframeConnectionForm_curve_eq_zero_iff (cov : CovariantDerivative I F V)
    {γ : ℝ → M} (q : ∀ t, V (γ t) ≃ₗᵢ[ℝ] F) {t : ℝ}
    (hq : ∀ w : F, ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 1
      (fun s => (⟨γ s, (q s).symm w⟩ : TotalSpace F V)) t) :
    cov.coframeConnectionForm q t ((NormedSpace.fromTangentSpace t).symm 1) = 0 ↔
      ∀ w : F, cov.derivAlongWithin γ (fun s => (q s).symm w) univ t = 0 := by
  rw [ContinuousLinearMap.ext_iff]
  simp only [cov.coframeConnectionForm_curve_apply _ hq, zero_apply,
    neg_eq_zero, EmbeddingLike.map_eq_zero_iff]

section Smoothness

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [IsManifold IP ∞ P]

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem contMDiff_coframeConnectionForm (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F)
    (hq : ∀ w : F, ContMDiff IP (I.prod 𝓘(ℝ, F)) ∞
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V))) :
    ContMDiff IP.tangent 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun z : TangentBundle IP P => cov.coframeConnectionForm q z.proj z.snd) := by
  intro z
  apply contMDiffAt_clm_of_pointwise
  intro w
  have hK := (cov.contMDiff_connector hcov).comp
    ((hq w).contMDiff_tangentMap (m := ∞) (by simp))
  let a := stdOrthonormalBasis ℝ F
  have hb (i) : ContMDiff IP.tangent (I.prod 𝓘(ℝ, F)) ∞
      (fun z : TangentBundle IP P => (⟨b z.proj, (q z.proj).symm (a i)⟩ : TotalSpace F V)) :=
    (hq (a i)).comp (contMDiff_proj (TangentSpace IP))
  have hs : ContMDiff IP.tangent 𝓘(ℝ, F) ∞
      (fun z : TangentBundle IP P => -∑ i,
        inner ℝ ((q z.proj).symm (a i))
          (cov.connector (⟨b z.proj, (q z.proj).symm w⟩ : TotalSpace F V)
            (mfderiv IP (I.prod 𝓘(ℝ, F))
              (fun p => (⟨b p, (q p).symm w⟩ : TotalSpace F V)) z.proj z.snd)) • a i) := by
    apply ContMDiff.neg
    apply ContMDiff.sum
    intro i _
    exact ((hb i).inner_bundle hK).smul contMDiff_const
  apply (hs z).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [cov.coframeConnectionForm_apply (IP := IP) q (fun v => (hq v y.proj).of_le (by simp))]
  congr 1
  rw [← a.sum_repr (q y.proj _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [a.repr_apply_apply]
  congr 1
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (q y.proj).inner_map_map ((q y.proj).symm (a i)) _

end Smoothness

section FrameBundle

variable [IsManifold I 1 M]

def orthonormalFrameConnectionForm (cov : CovariantDerivative I F V)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p →L[ℝ]
      F →L[ℝ] F := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  exact cov.coframeConnectionForm (fun z => z.snd) p

private theorem contMDiff_orthonormalFrame_column (w : F) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ContMDiff (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, F)) 1
      (fun p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨p.proj, p.snd.symm w⟩ : TotalSpace F V)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  exact (FiberBundle.contMDiff_orthonormalFrame_symm_apply (F := F) V I 1).comp
    (contMDiff_id.prodMk (contMDiff_const (c := w)))

theorem IsMetricCompatible.orthonormalFrameConnectionForm_mem_skewAdjoint
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ∀ U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p,
      cov.orthonormalFrameConnectionForm p U ∈ skewAdjoint.submodule ℝ (F →L[ℝ] F) := by
  intro hR htop hchart U
  change cov.coframeConnectionForm (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd) p U ∈
    skewAdjoint.submodule ℝ (F →L[ℝ] F)
  exact hcov.coframeConnectionForm_mem_skewAdjoint
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun w => contMDiff_orthonormalFrame_column (I := I) w p) U

theorem orthonormalFrameConnectionForm_apply (cov : CovariantDerivative I F V)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ∀ (U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p) (w : F),
      cov.orthonormalFrameConnectionForm p U w =
        -p.snd (cov.connector (⟨p.proj, p.snd.symm w⟩ : TotalSpace F V)
          (mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
            (I.prod 𝓘(ℝ, F))
            (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
              (⟨z.proj, z.snd.symm w⟩ : TotalSpace F V)) p U)) := by
  intro hR htop hchart U w
  exact cov.coframeConnectionForm_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun v => contMDiff_orthonormalFrame_column (I := I) v p) U w

theorem orthonormalFrameConnectionForm_comp_apply (cov : CovariantDerivative I F V)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ∀ (U : TangentSpace IP p) (w : F),
      cov.orthonormalFrameConnectionForm (⟨b p, q p⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
        (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderiv IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
            (fun x => V x ≃ₗᵢ[ℝ] F))) p U) w =
        cov.coframeConnectionForm q p U w := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  intro U w
  have hQ := FiberBundle.contMDiffAt_orthonormalFrame_of_symm (F := F) V I 1 hq
  exact (cov.coframeConnectionForm_comp_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (IQ := IP) (f := fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
      (fun x => V x ≃ₗᵢ[ℝ] F))) (x := p)
    (fun v => contMDiff_orthonormalFrame_column (I := I) v
      (⟨b p, q p⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) hQ U w).symm

theorem orthonormalFrameConnectionForm_smul_apply (cov : CovariantDerivative I F V)
    (g : F ≃ₗᵢ[ℝ] F)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ∀ (U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p) (w : F),
      cov.orthonormalFrameConnectionForm
        (⟨p.proj, g • p.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
            (⟨z.proj, g • z.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
              (fun x => V x ≃ₗᵢ[ℝ] F))) p U) w =
        g (cov.orthonormalFrameConnectionForm p U (g.symm w)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  intro U w
  have hq (v : F) : ContMDiffAt
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) (I.prod 𝓘(ℝ, F)) 1
      (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨z.proj, (g • z.snd).symm v⟩ : TotalSpace F V)) p :=
    contMDiff_orthonormalFrame_column (I := I) (g.symm v) p
  rw [cov.orthonormalFrameConnectionForm_comp_apply _ hq]
  exact cov.coframeConnectionForm_smul_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun v => contMDiff_orthonormalFrame_column (I := I) v p) g U w

theorem orthonormalFrameConnectionForm_curveWithin_apply (cov : CovariantDerivative I F V)
    {γ : ℝ → M} (q : ∀ t, V (γ t) ≃ₗᵢ[ℝ] F) {J : Set ℝ} {t : ℝ}
    (hq : ∀ w : F, ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 1
      (fun s => (⟨γ s, (q s).symm w⟩ : TotalSpace F V)) J t) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
    ∀ w : F,
      cov.orthonormalFrameConnectionForm
        (⟨γ t, q t⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun s => (⟨γ s, q s⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
            (fun x => V x ≃ₗᵢ[ℝ] F))) J t ((NormedSpace.fromTangentSpace t).symm 1)) w =
        -q t (cov.derivAlongWithin γ (fun s => (q s).symm w) J t) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I 1
  intro w
  let Q := fun s => (⟨γ s, q s⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
  have hQ := (FiberBundle.contMDiffWithinAt_orthonormalFrame_of_symm
    (F := F) V I 1 hq).mdifferentiableWithinAt (by simp)
  rw [cov.orthonormalFrameConnectionForm_apply]
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · have hc := (contMDiff_orthonormalFrame_column (I := I) w (Q t)).mdifferentiableAt (by simp)
    have hd := congrArg (fun L => L ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv_comp_mfderivWithin t hc hQ hJ.uniqueMDiffWithinAt)
    change mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, (q s).symm w⟩ : TotalSpace F V)) J t
      ((NormedSpace.fromTangentSpace t).symm 1) = _ at hd
    change -q t (cov.connector _
      ((mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
        (I.prod 𝓘(ℝ, F)) (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F)
          (fun x => V x ≃ₗᵢ[ℝ] F) => (⟨z.proj, z.snd.symm w⟩ : TotalSpace F V)) (Q t)).comp
        (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          Q J t) ((NormedSpace.fromTangentSpace t).symm 1))) = _
    rw [← hd, cov.connector_mfderivWithin_curve ((hq w).mdifferentiableWithinAt (by simp))]
  · have hz : mfderivWithin 𝓘(ℝ, ℝ)
        (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) Q J t = 0 :=
      hQ.mfderivWithin.trans
        (fderivWithin_zero_of_not_uniqueDiffWithinAt
          (f := writtenInExtChartAt 𝓘(ℝ, ℝ)
            (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) t Q)
          (show ¬UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t from
            fun h => hJ h.uniqueDiffWithinAt))
    change -q t (cov.connector _
      (mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
        (I.prod 𝓘(ℝ, F)) (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F)
          (fun x => V x ≃ₗᵢ[ℝ] F) => (⟨z.proj, z.snd.symm w⟩ : TotalSpace F V)) (Q t)
        (mfderivWithin 𝓘(ℝ, ℝ)
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) Q J t
            ((NormedSpace.fromTangentSpace t).symm 1)))) = _
    rw [hz, zero_apply, map_zero, map_zero,
      cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ _ hJ]


end FrameBundle

end CovariantDerivative
