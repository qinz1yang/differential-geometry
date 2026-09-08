import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Connector
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Smooth
import DifferentialGeometry.Geometry.LieGroup.Orthogonal.LieAlgebra

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

private theorem connector_mfderiv_const_base (cov : CovariantDerivative I F V)
    {x : M} {Z : P → V x} {p : P}
    (hZ : ContMDiffAt IP 𝓘(ℝ, V x) 1 Z p) (U : TangentSpace IP p) :
    cov.connector (⟨x, Z p⟩ : TotalSpace F V)
      (mfderiv IP (I.prod 𝓘(ℝ, F)) (fun q => (⟨x, Z q⟩ : TotalSpace F V)) p U) =
      mvfderiv IP Z p U := by
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hz : ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun q => (⟨x, Z q⟩ : TotalSpace F V)) p := by
    apply (e.contMDiffAt_iff (IB := I) (e.mem_source.mpr he)).mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have h := (e.continuousLinearMapAt ℝ x).contMDiff.contMDiffAt.comp p hZ
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun q => (e.continuousLinearMapAt_apply_of_mem ℝ he (Z q)).symm))
  rw [cov.connector_mfderiv_eq e he (hz.mdifferentiableAt (by simp)), mfderiv_const,
    zero_apply, map_zero, zero_apply, add_zero]
  have hd := congrArg (fun L => L U)
    ((mdifferentiableAt_const (c := e.continuousLinearMapAt ℝ x)).mvfderiv_clm_apply
      (hZ.mdifferentiableAt (by simp)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hd
  rw [hd, e.symmL_continuousLinearMapAt he]

theorem coframeConnectionForm_smul_one_apply (cov : CovariantDerivative I F V)
    {x : M} (q : V x ≃ₗᵢ[ℝ] F)
    (U : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) (F ≃ₗᵢ[ℝ] F))
    (w : F) :
    cov.coframeConnectionForm
      (IP := 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (fun g : F ≃ₗᵢ[ℝ] F => g • q) 1 U w =
        (LinearIsometryEquiv.groupLieAlgebraEquiv U : F →L[ℝ] F) w := by
  let O := 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))
  have hi : ContMDiff O 𝓘(ℝ, F →L[ℝ] F) 1
      (fun g : F ≃ₗᵢ[ℝ] F => (g.symm : F →L[ℝ] F)) :=
    LinearIsometryEquiv.contMDiff_iff.mp contMDiff_id.inv
  have hZ (v : F) : ContMDiff O 𝓘(ℝ, V x) 1
      (fun g : F ≃ₗᵢ[ℝ] F => q.symm (g.symm v)) :=
    q.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp (hi.clm_apply (contMDiff_const (c := v)))
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hq (v : F) : ContMDiffAt O (I.prod 𝓘(ℝ, F)) 1
      (fun g : F ≃ₗᵢ[ℝ] F => (⟨x, (g • q).symm v⟩ : TotalSpace F V)) 1 := by
    apply (e.contMDiffAt_iff (IB := I) (e.mem_source.mpr he)).mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have h := (e.continuousLinearMapAt ℝ x).contMDiff.contMDiffAt.comp 1 (hZ v 1)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun g => (e.continuousLinearMapAt_apply_of_mem ℝ he (q.symm (g.symm v))).symm))
  rw [cov.coframeConnectionForm_apply _ hq]
  change -q (cov.connector _
    (mfderiv O (I.prod 𝓘(ℝ, F))
      (fun g : F ≃ₗᵢ[ℝ] F => (⟨x, q.symm (g.symm w)⟩ : TotalSpace F V)) 1 U)) = _
  rw [cov.connector_mfderiv_const_base (hZ w 1) U]
  have hd := congrArg (fun L => L U)
    ((mdifferentiableAt_const (c := q.symm.toContinuousLinearEquiv.toContinuousLinearMap)).mvfderiv_clm_apply
      ((hi.clm_apply (contMDiff_const (c := w)) 1).mdifferentiableAt (by simp)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hd
  change mvfderiv O (fun g : F ≃ₗᵢ[ℝ] F => q.symm (g.symm w)) 1 U =
    q.symm (mvfderiv O (fun g : F ≃ₗᵢ[ℝ] F => g.symm w) 1 U) at hd
  rw [hd, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.mvfderiv_symm_apply_one,
    neg_neg]


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

variable {n : ℕ∞ω} [ContMDiffVectorBundle n F V I]
  [IsContMDiffRiemannianBundle I n F V] [IsManifold I n M]

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
def orthonormalFrameConnectionForm (cov : CovariantDerivative I F V) (hn : 1 ≤ n)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p →L[ℝ]
      F →L[ℝ] F := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  exact cov.coframeConnectionForm (fun z => z.snd) p

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
private theorem contMDiff_orthonormalFrame_column (w : F) :
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, F)) n
      (fun p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨p.proj, p.snd.symm w⟩ : TotalSpace F V)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  exact (FiberBundle.contMDiff_orthonormalFrame_symm_apply (F := F) V I n).comp
    (contMDiff_id.prodMk (contMDiff_const (c := w)))

theorem IsMetricCompatible.orthonormalFrameConnectionForm_mem_skewAdjoint
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (hn : 1 ≤ n)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p,
      cov.orthonormalFrameConnectionForm hn p U ∈ skewAdjoint.submodule ℝ (F →L[ℝ] F) := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  intro hR htop hchart U
  change cov.coframeConnectionForm (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd) p U ∈
    skewAdjoint.submodule ℝ (F →L[ℝ] F)
  exact hcov.coframeConnectionForm_mem_skewAdjoint
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun w => (contMDiff_orthonormalFrame_column (I := I) (n := n) w p).of_le hn) U

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_apply (cov : CovariantDerivative I F V)
    (hn : 1 ≤ n)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    let : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ (U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p) (w : F),
      cov.orthonormalFrameConnectionForm hn p U w =
        -p.snd (cov.connector (⟨p.proj, p.snd.symm w⟩ : TotalSpace F V)
          (mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
            (I.prod 𝓘(ℝ, F))
            (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
              (⟨z.proj, z.snd.symm w⟩ : TotalSpace F V)) p U)) := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  intro hR htop hchart U w
  exact cov.coframeConnectionForm_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun v => (contMDiff_orthonormalFrame_column (I := I) (n := n) v p).of_le hn) U w

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_comp_apply (cov : CovariantDerivative I F V)
    (hn : 1 ≤ n)
    {b : P → M} (q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F) {p : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) 1
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) p) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ (U : TangentSpace IP p) (w : F),
      cov.orthonormalFrameConnectionForm hn (⟨b p, q p⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
        (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderiv IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
            (fun x => V x ≃ₗᵢ[ℝ] F))) p U) w =
        cov.coframeConnectionForm q p U w := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  intro U w
  have hQ := FiberBundle.contMDiffAt_orthonormalFrame_of_symm_of_le (F := F) V I n hn hq
  exact (cov.coframeConnectionForm_comp_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (IQ := IP) (f := fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
      (fun x => V x ≃ₗᵢ[ℝ] F))) (x := p)
    (fun v => (contMDiff_orthonormalFrame_column (I := I) (n := n) v
      (⟨b p, q p⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))).of_le hn) hQ U w).symm

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_smul_apply (cov : CovariantDerivative I F V)
    (hn : 1 ≤ n)
    (g : F ≃ₗᵢ[ℝ] F)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ (U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p) (w : F),
      cov.orthonormalFrameConnectionForm hn
        (⟨p.proj, g • p.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderiv (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
            (⟨z.proj, g • z.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
              (fun x => V x ≃ₗᵢ[ℝ] F))) p U) w =
        g (cov.orthonormalFrameConnectionForm hn p U (g.symm w)) := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  intro U w
  have hq (v : F) : ContMDiffAt
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) (I.prod 𝓘(ℝ, F)) n
      (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨z.proj, (g • z.snd).symm v⟩ : TotalSpace F V)) p :=
    contMDiff_orthonormalFrame_column (I := I) (g.symm v) p
  rw [cov.orthonormalFrameConnectionForm_comp_apply hn _ (fun v => (hq v).of_le hn)]
  exact cov.coframeConnectionForm_smul_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd)
    (fun v => (contMDiff_orthonormalFrame_column (I := I) (n := n) v p).of_le hn) g U w

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_curveWithin_apply (cov : CovariantDerivative I F V)
    (hn : 1 ≤ n)
    {γ : ℝ → M} (q : ∀ t, V (γ t) ≃ₗᵢ[ℝ] F) {J : Set ℝ} {t : ℝ}
    (hq : ∀ w : F, ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 1
      (fun s => (⟨γ s, (q s).symm w⟩ : TotalSpace F V)) J t) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ w : F,
      cov.orthonormalFrameConnectionForm hn
        (⟨γ t, q t⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
        (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun s => (⟨γ s, q s⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
            (fun x => V x ≃ₗᵢ[ℝ] F))) J t ((NormedSpace.fromTangentSpace t).symm 1)) w =
        -q t (cov.derivAlongWithin γ (fun s => (q s).symm w) J t) := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  intro w
  let Q := fun s => (⟨γ s, q s⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
  have hQ := (FiberBundle.contMDiffWithinAt_orthonormalFrame_of_symm_of_le
    (F := F) V I n hn hq).mdifferentiableWithinAt (by simp)
  rw [cov.orthonormalFrameConnectionForm_apply hn]
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · have hc := ((contMDiff_orthonormalFrame_column (I := I) (n := n) w (Q t)).of_le hn).mdifferentiableAt (by simp)
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


omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_fundamental_apply (cov : CovariantDerivative I F V) (hn : 1 ≤ n)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
    (U : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) (F ≃ₗᵢ[ℝ] F)) :
    letI : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    ∀ w : F,
      cov.orthonormalFrameConnectionForm hn p
        (mfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
          (fun g : F ≃ₗᵢ[ℝ] F => (⟨p.proj, g • p.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F)
            (fun x => V x ≃ₗᵢ[ℝ] F))) 1 U) w =
        (LinearIsometryEquiv.groupLieAlgebraEquiv U : F →L[ℝ] F) w := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  intro w
  let O := 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))
  have hi : ContMDiff O 𝓘(ℝ, F →L[ℝ] F) n
      (fun g : F ≃ₗᵢ[ℝ] F => (g.symm : F →L[ℝ] F)) :=
    LinearIsometryEquiv.contMDiff_iff.mp contMDiff_id.inv
  have hZ (v : F) : ContMDiff O 𝓘(ℝ, V p.proj) n
      (fun g : F ≃ₗᵢ[ℝ] F => p.snd.symm (g.symm v)) :=
    p.snd.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp
      (hi.clm_apply (contMDiff_const (c := v)))
  let e := trivializationAt F V p.proj
  have he : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt F V p.proj
  have hq (v : F) : ContMDiffAt O (I.prod 𝓘(ℝ, F)) n
      (fun g : F ≃ₗᵢ[ℝ] F => (⟨p.proj, (g • p.snd).symm v⟩ : TotalSpace F V)) 1 := by
    apply (e.contMDiffAt_iff (IB := I) (e.mem_source.mpr he)).mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have h := (e.continuousLinearMapAt ℝ p.proj).contMDiff.contMDiffAt.comp 1 (hZ v 1)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun g => (e.continuousLinearMapAt_apply_of_mem ℝ he (p.snd.symm (g.symm v))).symm))
  have h := cov.orthonormalFrameConnectionForm_comp_apply hn
    (IP := O) (fun g : F ≃ₗᵢ[ℝ] F => g • p.snd) (p := 1) (fun v => (hq v).of_le hn) U w
  exact h.trans (cov.coframeConnectionForm_smul_one_apply p.snd U w)

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
theorem orthonormalFrameConnectionForm_atlasDiffeomorph_apply
    (cov : CovariantDerivative I F V) (hn : 1 ≤ n)
    (k : ℕ∞ω) [ContMDiffVectorBundle k F V I]
    [IsContMDiffRiemannianBundle I k F V] [IsManifold I k M] (hk : 1 ≤ k)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let cn := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
    let ck := FiberBundle.orthonormalFrameChartedSpace (F := F) V I k
    ∀ (U : @TangentSpace ℝ _ _ _ _ _ _ (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn p)
      (w : F),
      cov.orthonormalFrameConnectionForm hk p
        (@mfderiv ℝ _ _ _ _ _ _
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn _ _ _ _ _
          (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ ck
          (FiberBundle.orthonormalFrameAtlasDiffeomorph V I n k hn hk) p U) w =
        cov.orthonormalFrameConnectionForm hn p U w := by
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le hn
  let : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let cn := FiberBundle.orthonormalFrameChartedSpace (F := F) V I n
  let ck := FiberBundle.orthonormalFrameChartedSpace (F := F) V I k
  dsimp only
  intro U w
  let := cn
  have hq (v : F) : ContMDiffAt
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) (I.prod 𝓘(ℝ, F)) 1
      (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨z.proj, z.snd.symm v⟩ : TotalSpace F V)) p :=
    (contMDiff_orthonormalFrame_column (I := I) (n := n) v p).of_le hn
  exact cov.orthonormalFrameConnectionForm_comp_apply
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) hk
    (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => z.snd) hq U w

end FrameBundle

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem contMDiff_orthonormalFrameConnectionForm (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I ∞
    letI := FiberBundle.orthonormalFrame_isManifold (F := F) V I ∞
    letI : ∀ p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F),
        TopologicalSpace (TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p) :=
      fun _ => inferInstance
    ContMDiff (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))).tangent
      𝓘(ℝ, F →L[ℝ] F) ∞
      (fun z : TangentBundle (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
        (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) =>
        cov.orthonormalFrameConnectionForm (n := ∞) (by simp) z.proj z.snd) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  let := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := FiberBundle.orthonormalFrameChartedSpace (F := F) V I ∞
  let := FiberBundle.orthonormalFrame_isManifold (F := F) V I ∞
  apply cov.contMDiff_coframeConnectionForm
    (IP := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) hcov
    (fun p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) => p.snd)
  intro w
  exact (FiberBundle.contMDiff_orthonormalFrame_symm_apply (F := F) V I ∞).comp
    (contMDiff_id.prodMk (contMDiff_const (c := w)))

end CovariantDerivative
