import DifferentialGeometry.Geometry.Connection.Regularity
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Bundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private theorem contMDiffAt_trivialization_symmL {n : ℕ∞ω}
    [ContMDiffVectorBundle n F V I]
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (v : F) {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y : M => (⟨y, e.symmL ℝ y v⟩ : TotalSpace F V)) x := by
  rw [e.contMDiffAt_section_iff hx]
  apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
  exact e.continuousLinearMapAt_symmL hy v

variable [FiniteDimensional ℝ F]

section FirstOrder

variable [ContMDiffVectorBundle 1 F V I]

def connectionForm (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (x : M) :
    TangentSpace I x →L[ℝ] F →L[ℝ] F := by
  classical
  let c := DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv (I := I) x
  by_cases hx : x ∈ e.baseSet
  · let L : F →ₗ[ℝ] E →L[ℝ] F :=
      { toFun := fun v => (e.continuousLinearMapAt ℝ x).comp
          ((cov (fun y => e.symmL ℝ y v) x).comp c.symm.toContinuousLinearMap)
        map_add' := by
          intro v w
          have hv := (contMDiffAt_trivialization_symmL
            (I := I) (n := 1) e v hx).mdifferentiableAt (by simp)
          have hw := (contMDiffAt_trivialization_symmL
            (I := I) (n := 1) e w hx).mdifferentiableAt (by simp)
          have heq : (fun y => e.symmL ℝ y (v + w)) =
              (fun y => e.symmL ℝ y v) + (fun y => e.symmL ℝ y w) := by
            funext y
            exact map_add _ v w
          rw [heq, cov.isCovariantDerivativeOnUniv.add hv hw]
          ext X
          simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
        map_smul' := by
          intro a v
          have hv := (contMDiffAt_trivialization_symmL
            (I := I) (n := 1) e v hx).mdifferentiableAt (by simp)
          have heq : (fun y => e.symmL ℝ y (a • v)) = a • (fun y => e.symmL ℝ y v) := by
            funext y
            exact map_smul _ a v
          rw [heq, cov.isCovariantDerivativeOnUniv.smul_const a hv]
          ext X
          simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
            RingHom.id_apply] }
    exact (LinearMap.toContinuousLinearMap L).flip.comp c.toContinuousLinearMap
  · exact 0

theorem connectionForm_apply (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet)
    (X : TangentSpace I x) (v : F) :
    cov.connectionForm e x X v =
      e.continuousLinearMapAt ℝ x (cov (fun y => e.symmL ℝ y v) x X) := by
  unfold connectionForm
  dsimp only
  rw [dif_pos hx]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    LinearMap.coe_toContinuousLinearMap', ContinuousLinearEquiv.coe_coe]
  change e.continuousLinearMapAt ℝ x
    (cov (fun y => e.symmL ℝ y v) x
      ((DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv (I := I) x X))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ F] in
private theorem mdifferentiableAt_trivialization_coord
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {σ : ∀ x : M, V x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x) :
    MDifferentiableAt I 𝓘(ℝ, F)
      (fun y => e.continuousLinearMapAt ℝ y (σ y)) x := by
  apply ((e.mdifferentiableAt_section_iff I σ hx).mp hσ).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact e.continuousLinearMapAt_apply_of_mem ℝ hy (σ y)

private def trivializationDerivative
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [e.IsLinear ℝ] (σ : ∀ x : M, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
  (e.symmL ℝ x).comp (mvfderiv I (fun y => e.continuousLinearMapAt ℝ y (σ y)) x)

omit [FiniteDimensional ℝ F] in
private theorem isCovariantDerivativeOn_trivializationDerivative
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn F (trivializationDerivative (I := I) e) e.baseSet where
  add {σ τ x} hσ hτ hx := by
    have hσ' := mdifferentiableAt_trivialization_coord e hx hσ
    have hτ' := mdifferentiableAt_trivialization_coord e hx hτ
    have heq : (fun y => e.continuousLinearMapAt ℝ y ((σ + τ) y)) =
        (fun y => e.continuousLinearMapAt ℝ y (σ y)) +
        (fun y => e.continuousLinearMapAt ℝ y (τ y)) := by
      funext y
      exact map_add _ _ _
    simp only [trivializationDerivative, heq, mvfderiv_add hσ' hτ',
      ContinuousLinearMap.comp_add]
  leibniz {σ g x} hσ hg hx := by
    have hσ' := mdifferentiableAt_trivialization_coord e hx hσ
    have heq : (fun y => e.continuousLinearMapAt ℝ y ((g • σ) y)) =
        g • (fun y => e.continuousLinearMapAt ℝ y (σ y)) := by
      funext y
      exact map_smul _ _ _
    simp only [trivializationDerivative, heq, mvfderiv_smul hg hσ']
    ext X
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, e.symmL_continuousLinearMapAt hx]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private theorem trivializationDerivative_symmL
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) (v : F) :
    trivializationDerivative (I := I) e (fun y => e.symmL ℝ y v) x = 0 := by
  have hd : HasMFDerivAt I 𝓘(ℝ, F)
      (fun y => e.continuousLinearMapAt ℝ y (e.symmL ℝ y v)) x 0 := by
    apply (hasMFDerivAt_const (I := I) (c := v) (x := x)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact e.continuousLinearMapAt_symmL hy v
  simp only [trivializationDerivative, mvfderiv, hd.mfderiv,
    ContinuousLinearMap.comp_zero]

theorem covariant_derivative_coord (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {σ : ∀ x : M, V x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x)
    (X : TangentSpace I x) :
    e.continuousLinearMapAt ℝ x (cov σ x X) =
      mvfderiv I (fun y => e.continuousLinearMapAt ℝ y (σ y)) x X +
        cov.connectionForm e x X (e.continuousLinearMapAt ℝ x (σ x)) := by
  let v := e.continuousLinearMapAt ℝ x (σ x)
  have hv := (contMDiffAt_trivialization_symmL
    (I := I) (n := 1) e v hx).mdifferentiableAt (by simp)
  have hcov := cov.isCovariantDerivativeOnUniv.mono (subset_univ e.baseSet)
  have hflat := isCovariantDerivativeOn_trivializationDerivative (I := I) e
  have hDσ := hcov.difference_apply hflat hx hσ
  have hDv := hcov.difference_apply hflat hx hv
  have hval : e.symmL ℝ x v = σ x := e.symmL_continuousLinearMapAt hx (σ x)
  rw [hval] at hDv
  have hEq : cov σ x - trivializationDerivative e σ x =
      cov (fun y => e.symmL ℝ y v) x := by
    rw [← hDσ, hDv, trivializationDerivative_symmL e hx v, sub_zero]
  have h := congrArg (fun L : TangentSpace I x →L[ℝ] V x =>
    e.continuousLinearMapAt ℝ x (L X)) hEq
  rw [connectionForm_apply cov e hx]
  simp only [sub_apply, map_sub, trivializationDerivative,
    ContinuousLinearMap.comp_apply, e.continuousLinearMapAt_symmL hx] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private theorem coordChangeL_eq
    (e e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {x : M}
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (v : F) :
    e'.coordChangeL ℝ e x v =
      e.continuousLinearMapAt ℝ x (e'.symmL ℝ x v) := by
  rw [e'.coordChangeL_apply' e ⟨hx', hx⟩, e.continuousLinearMapAt_apply_of_mem ℝ hx,
    e'.symmL_apply hx', e'.mk_symm hx']

theorem connectionForm_coordChange (cov : CovariantDerivative I F V)
    (e e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {x : M}
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (X : TangentSpace I x) (v : F) :
    e'.coordChangeL ℝ e x (cov.connectionForm e' x X v) =
      mvfderiv I (fun y => e'.coordChangeL ℝ e y v) x X +
        cov.connectionForm e x X (e'.coordChangeL ℝ e x v) := by
  have hv := (contMDiffAt_trivialization_symmL
    (I := I) (n := 1) e' v hx').mdifferentiableAt (by simp)
  have heq : (fun y => e'.coordChangeL ℝ e y v) =ᶠ[𝓝 x]
      (fun y => e.continuousLinearMapAt ℝ y (e'.symmL ℝ y v)) := by
    filter_upwards [e.open_baseSet.mem_nhds hx, e'.open_baseSet.mem_nhds hx'] with y hy hy'
    exact coordChangeL_eq e e' hy hy' v
  have hd : mvfderiv I (fun y => e'.coordChangeL ℝ e y v) x =
      mvfderiv I (fun y => e.continuousLinearMapAt ℝ y (e'.symmL ℝ y v)) x := by
    simp only [mvfderiv, heq.mfderiv_eq]
    rfl
  rw [coordChangeL_eq e e' hx hx', connectionForm_apply cov e' hx',
    e'.symmL_continuousLinearMapAt hx', hd, coordChangeL_eq e e' hx hx']
  exact cov.covariant_derivative_coord e hx hv X

end FirstOrder

section Smoothness

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [ContMDiffVectorBundle ∞ F V I]

theorem contMDiffOn_connectionForm (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun p : TangentBundle I M => cov.connectionForm e p.1 p.2)
      (TotalSpace.proj ⁻¹' e.baseSet) := by
  have hσ (v : F) : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun y : M => (⟨y, e.symmL ℝ y v⟩ : TotalSpace F V)) e.baseSet :=
    fun y hy => (contMDiffAt_trivialization_symmL (I := I) e v hy).contMDiffWithinAt
  have hD (v : F) := hcov.contMDiffOn e.open_baseSet (by simpa using hσ v)
  have hA (v : F) : ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, F)) ∞
      (fun p : TangentBundle I M =>
        (⟨p.1, cov (fun y => e.symmL ℝ y v) p.1 p.2⟩ : TotalSpace F V))
      (TotalSpace.proj ⁻¹' e.baseSet) := by
    have h := (hD v).comp (contMDiffOn_proj (F := E) (TangentSpace I)) (fun _ h => h)
    exact h.clm_bundle_apply contMDiffOn_id
  intro p hp
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  have h := (e.contMDiffOn.comp (hA v) (fun q hq => e.mem_source.mpr hq) p hp).snd
  apply h.congr
  · intro q hq
    rw [connectionForm_apply cov e hq]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hq _
  · rw [connectionForm_apply cov e hp]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hp _

end Smoothness

end CovariantDerivative
