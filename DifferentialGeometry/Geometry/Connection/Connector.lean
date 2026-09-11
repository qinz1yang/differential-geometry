import DifferentialGeometry.Geometry.Connection.AlongCurve
import DifferentialGeometry.Bundle.PartialMfderiv.Composition

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
  [FiniteDimensional ℝ F]

section FirstOrder

variable [ContMDiffVectorBundle 1 F V I]

def connector (cov : CovariantDerivative I F V) (z : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) z →L[ℝ] V z.proj :=
  let e := trivializationAt F V z.proj
  (e.symmL ℝ z.proj).comp
    (mvfderiv (I.prod 𝓘(ℝ, F))
      (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) z +
      ((ContinuousLinearMap.apply ℝ F (e.continuousLinearMapAt ℝ z.proj z.snd)).comp
        (cov.connectionForm e z.proj)).comp
        (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z))

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ F] in
private theorem mdifferentiableAt_fiber_coord
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {z : TotalSpace F V} (hz : z.proj ∈ e.baseSet) :
    MDifferentiableAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) z := by
  have h := ((e.mdifferentiableAt_totalSpace_iff I id
    (e.mem_source.mpr hz)).mp mdifferentiableAt_id).2
  apply h.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hz)] with y hy
  exact e.continuousLinearMapAt_apply_of_mem ℝ hy y.snd

theorem connector_mfderiv_section (cov : CovariantDerivative I F V)
    {σ : ∀ x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x) (X : TangentSpace I x) :
    cov.connector (⟨x, σ x⟩ : TotalSpace F V)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x X) = cov σ x X := by
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  have hcoord := mdifferentiableAt_fiber_coord (I := I) e (z := ⟨x, σ x⟩) he
  have hderiv := hcoord.mvfderiv_comp_apply (f := T% σ) hσ X
  have hproj : mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj (⟨x, σ x⟩ : TotalSpace F V)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x X) = X := by
    have h := congrArg (fun L => L X)
      (mfderiv_comp x (Bundle.mdifferentiable_proj V (⟨x, σ x⟩ : TotalSpace F V)) hσ)
    change mfderiv I I id x X = _ at h
    simpa only [mfderiv_id, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply] using h.symm
  change e.symmL ℝ x (mvfderiv (I.prod 𝓘(ℝ, F))
    (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) ⟨x, σ x⟩
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x X) +
    cov.connectionForm e x (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj ⟨x, σ x⟩
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x X))
      (e.continuousLinearMapAt ℝ x (σ x))) = _
  rw [hproj, ← hderiv]
  dsimp only [Function.comp_def]
  rw [← cov.covariant_derivative_coord e he hσ X,
    e.symmL_continuousLinearMapAt he]

private theorem connector_coordChange (cov : CovariantDerivative I F V)
    (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {z : TotalSpace F V} (he : z.proj ∈ e.baseSet) (he' : z.proj ∈ e'.baseSet)
    (U : TangentSpace (I.prod 𝓘(ℝ, F)) z) :
    e'.coordChangeL ℝ e z.proj
      (mvfderiv (I.prod 𝓘(ℝ, F))
        (fun y : TotalSpace F V => e'.continuousLinearMapAt ℝ y.proj y.snd) z U +
        cov.connectionForm e' z.proj
          (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z U)
          (e'.continuousLinearMapAt ℝ z.proj z.snd)) =
      mvfderiv (I.prod 𝓘(ℝ, F))
        (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) z U +
        cov.connectionForm e z.proj
          (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z U)
          (e.continuousLinearMapAt ℝ z.proj z.snd) := by
  let R : M → F →L[ℝ] F := fun x => e'.coordChangeL ℝ e x
  let w : TotalSpace F V → F := fun y => e.continuousLinearMapAt ℝ y.proj y.snd
  let w' : TotalSpace F V → F := fun y => e'.continuousLinearMapAt ℝ y.proj y.snd
  let X := mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z U
  have hπ : MDifferentiableAt (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z :=
    Bundle.mdifferentiable_proj V z
  have hR : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) R z.proj :=
    (contMDiffAt_coordChangeL (IB := I) (n := 1) he' he).mdifferentiableAt (by simp)
  have hRπ : MDifferentiableAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F →L[ℝ] F)
      (fun y : TotalSpace F V => R y.proj) z := hR.comp z hπ
  have hw' : MDifferentiableAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) w' z :=
    mdifferentiableAt_fiber_coord e' he'
  have hcoord (y : TotalSpace F V) (hy : y.proj ∈ e.baseSet)
      (hy' : y.proj ∈ e'.baseSet) : w y = R y.proj (w' y) := by
    dsimp only [w, w', R]
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [e'.coordChangeL_apply' e ⟨hy', hy⟩, ← e'.mk_symm hy',
      ← e'.symmL_apply (R := ℝ) hy', e'.symmL_continuousLinearMapAt hy',
      e.continuousLinearMapAt_apply_of_mem ℝ hy]
  have heq : w =ᶠ[𝓝 z] (fun y => R y.proj (w' y)) := by
    filter_upwards [(FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds he),
      (FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds
        (e'.open_baseSet.mem_nhds he')] with y hy hy'
    exact hcoord y hy hy'
  have hDw : mvfderiv (I.prod 𝓘(ℝ, F)) w z U =
      R z.proj (mvfderiv (I.prod 𝓘(ℝ, F)) w' z U) +
        mvfderiv (I.prod 𝓘(ℝ, F)) (fun y : TotalSpace F V => R y.proj) z U (w' z) := by
    have hd : mvfderiv (I.prod 𝓘(ℝ, F)) w z =
        mvfderiv (I.prod 𝓘(ℝ, F)) (fun y => R y.proj (w' y)) z := by
      simp only [mvfderiv, heq.mfderiv_eq]
      rfl
    rw [hd, hRπ.mvfderiv_clm_apply hw']
    rfl
  have hDR : mvfderiv (I.prod 𝓘(ℝ, F)) (fun y : TotalSpace F V => R y.proj) z U (w' z) =
      mvfderiv I (fun x => R x (w' z)) z.proj X := by
    have hc := (hR.clm_apply (mdifferentiableAt_const (c := w' z))).mvfderiv_comp_apply
      (f := TotalSpace.proj) hπ U
    have hd := congrArg (fun L => L U)
      (hRπ.mvfderiv_clm_apply (mdifferentiableAt_const (c := w' z)))
    simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hd
    exact hd.symm.trans hc
  have htrans := cov.connectionForm_coordChange e e' he he' X (w' z)
  change R z.proj (cov.connectionForm e' z.proj X (w' z)) =
    mvfderiv I (fun x => R x (w' z)) z.proj X +
      cov.connectionForm e z.proj X (R z.proj (w' z)) at htrans
  change R z.proj (mvfderiv (I.prod 𝓘(ℝ, F)) w' z U +
      cov.connectionForm e' z.proj X (w' z)) =
    mvfderiv (I.prod 𝓘(ℝ, F)) w z U + cov.connectionForm e z.proj X (w z)
  rw [map_add, htrans, ← hcoord z he he', hDw, hDR]
  abel

theorem connector_coord (cov : CovariantDerivative I F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {z : TotalSpace F V} (he : z.proj ∈ e.baseSet)
    (U : TangentSpace (I.prod 𝓘(ℝ, F)) z) :
    e.continuousLinearMapAt ℝ z.proj (cov.connector z U) =
      mvfderiv (I.prod 𝓘(ℝ, F))
        (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) z U +
        cov.connectionForm e z.proj
          (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z U)
          (e.continuousLinearMapAt ℝ z.proj z.snd) := by
  let e₀ := trivializationAt F V z.proj
  have he₀ : z.proj ∈ e₀.baseSet := mem_baseSet_trivializationAt F V z.proj
  have h := connector_coordChange cov e e₀ he he₀ U
  rw [e₀.coordChangeL_apply' e ⟨he₀, he⟩, ← e₀.mk_symm he₀,
    ← e₀.symmL_apply (R := ℝ) he₀,
    ← e.continuousLinearMapAt_apply_of_mem ℝ he] at h
  exact h

theorem connector_eq (cov : CovariantDerivative I F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {z : TotalSpace F V} (he : z.proj ∈ e.baseSet)
    (U : TangentSpace (I.prod 𝓘(ℝ, F)) z) :
    cov.connector z U = e.symmL ℝ z.proj
      (mvfderiv (I.prod 𝓘(ℝ, F))
        (fun y : TotalSpace F V => e.continuousLinearMapAt ℝ y.proj y.snd) z U +
        cov.connectionForm e z.proj
          (mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj z U)
          (e.continuousLinearMapAt ℝ z.proj z.snd)) := by
  rw [← cov.connector_coord e he U, e.symmL_continuousLinearMapAt he]

theorem connector_mfderivWithin_curve (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    cov.connector (⟨γ t, Z t⟩ : TotalSpace F V)
      (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t
          ((NormedSpace.fromTangentSpace t).symm 1)) = cov.derivAlongWithin γ Z J t := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · let e := trivializationAt F V (γ t)
    have he : γ t ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t)
    have hcoord := mdifferentiableAt_fiber_coord (I := I) e (z := ⟨γ t, Z t⟩) he
    have hD := hcoord.mvfderiv_comp_mfderivWithin_apply
      (f := fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) hZ hJ.uniqueMDiffWithinAt
        ((NormedSpace.fromTangentSpace t).symm 1)
    rw [mvfderivWithin, mfderivWithin_eq_fderivWithin] at hD
    change derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t = _ at hD
    have hπ := congrArg (fun L => L ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv_comp_mfderivWithin t
        (Bundle.mdifferentiable_proj V (⟨γ t, Z t⟩ : TotalSpace F V))
        hZ hJ.uniqueMDiffWithinAt)
    change mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1) = _ at hπ
    rw [cov.connector_eq e he, ← hD]
    change e.symmL ℝ (γ t) (_ + cov.connectionForm e (γ t)
      ((mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj ⟨γ t, Z t⟩).comp
        (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
          (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t)
          ((NormedSpace.fromTangentSpace t).symm 1)) _) = _
    rw [← hπ]
    rfl
  · have hzero : mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t = 0 :=
      hZ.mfderivWithin.trans
        (fderivWithin_zero_of_not_uniqueDiffWithinAt
          (f := writtenInExtChartAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) t
            (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)))
          (show ¬UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t from
            fun h => hJ h.uniqueDiffWithinAt))
    rw [hzero, zero_apply, map_zero,
      cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ Z hJ]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {IP : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

theorem connector_mfderivWithin_eq (cov : CovariantDerivative I F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {b : P → M} {Z : ∀ p, V (b p)} {s : Set P} {p : P}
    (he : b p ∈ e.baseSet) (hs : UniqueMDiffWithinAt IP s p)
    (hZ : MDifferentiableWithinAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p) (U : TangentSpace IP p) :
    cov.connector (⟨b p, Z p⟩ : TotalSpace F V)
      (mfderivWithin IP (I.prod 𝓘(ℝ, F))
        (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p U) =
      e.symmL ℝ (b p)
        (mvfderivWithin IP (fun q => e.continuousLinearMapAt ℝ (b q) (Z q)) s p U +
          cov.connectionForm e (b p) (mfderivWithin IP I b s p U)
            (e.continuousLinearMapAt ℝ (b p) (Z p))) := by
  have hcoord := mdifferentiableAt_fiber_coord (I := I) e (z := ⟨b p, Z p⟩) he
  have hD := hcoord.mvfderiv_comp_mfderivWithin_apply
    (f := fun q => (⟨b q, Z q⟩ : TotalSpace F V)) hZ hs U
  have hπ := congrArg (fun L => L U)
    (mfderiv_comp_mfderivWithin p
      (Bundle.mdifferentiable_proj V (⟨b p, Z p⟩ : TotalSpace F V)) hZ hs)
  change mfderivWithin IP I b s p U = _ at hπ
  rw [cov.connector_eq e he, ← hD]
  dsimp only [Function.comp_def]
  change e.symmL ℝ (b p) (_ + cov.connectionForm e (b p)
    ((mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj ⟨b p, Z p⟩).comp
      (mfderivWithin IP (I.prod 𝓘(ℝ, F))
        (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p) U) _) = _
  rw [← hπ]

theorem connector_mfderiv_eq (cov : CovariantDerivative I F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {b : P → M} {Z : ∀ p, V (b p)} {p : P} (he : b p ∈ e.baseSet)
    (hZ : MDifferentiableAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) p) (U : TangentSpace IP p) :
    cov.connector (⟨b p, Z p⟩ : TotalSpace F V)
      (mfderiv IP (I.prod 𝓘(ℝ, F))
        (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) p U) =
      e.symmL ℝ (b p)
        (mvfderiv IP (fun q => e.continuousLinearMapAt ℝ (b q) (Z q)) p U +
          cov.connectionForm e (b p) (mfderiv IP I b p U)
            (e.continuousLinearMapAt ℝ (b p) (Z p))) := by
  simpa only [mfderivWithin_univ, mvfderivWithin_univ] using
    cov.connector_mfderivWithin_eq e he (uniqueMDiffWithinAt_univ IP) hZ.mdifferentiableWithinAt U

end FirstOrder

section Smoothness

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [ContMDiffVectorBundle ∞ F V I]

theorem contMDiff_connector (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞) :
    ContMDiff (I.prod 𝓘(ℝ, F)).tangent (I.prod 𝓘(ℝ, F)) ∞
      (fun p : TangentBundle (I.prod 𝓘(ℝ, F)) (TotalSpace F V) =>
        (⟨p.proj.proj, cov.connector p.proj p.snd⟩ : TotalSpace F V)) := by
  intro p
  let e := trivializationAt F V p.proj.proj
  let U : Set (TotalSpace F V) := TotalSpace.proj ⁻¹' e.baseSet
  have hU : IsOpen U := e.open_baseSet.preimage (FiberBundle.continuous_proj F V)
  have hp : p.proj ∈ U := mem_baseSet_trivializationAt F V p.proj.proj
  let f : TotalSpace F V → F := fun z => e.continuousLinearMapAt ℝ z.proj z.snd
  have hf : ContMDiffOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ f U := by
    intro z hz
    have h := ((e.contMDiffAt_iff (IB := I) (IM := I.prod 𝓘(ℝ, F))
      (n := ∞) (f := id) (e.mem_source.mpr hz)).mp contMDiffAt_id).2
    apply ContMDiffAt.contMDiffWithinAt
    apply h.congr_of_eventuallyEq
    filter_upwards [(FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds hz)] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy y.snd
  have hT := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hD := (contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F) (n := ∞)).comp_contMDiffOn hT
  have hDU : TotalSpace.proj ⁻¹' U ∈ 𝓝 p :=
    (hU.preimage (FiberBundle.continuous_proj (E × F)
      (TangentSpace (I.prod 𝓘(ℝ, F))))).mem_nhds hp
  have hd : ContMDiffAt (I.prod 𝓘(ℝ, F)).tangent 𝓘(ℝ, F) ∞
      (fun q : TangentBundle (I.prod 𝓘(ℝ, F)) (TotalSpace F V) =>
        mvfderiv (I.prod 𝓘(ℝ, F)) f q.proj q.snd) p := by
    apply (hD.contMDiffAt hDU).congr_of_eventuallyEq
    filter_upwards [hDU] with q hq
    change mvfderiv (I.prod 𝓘(ℝ, F)) f q.proj q.snd =
      (mfderivWithin (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) f U q.proj q.snd : F)
    rw [mfderivWithin_of_isOpen hU hq]
    rfl
  have hπ : ContMDiff (I.prod 𝓘(ℝ, F)) I ∞
      (TotalSpace.proj : TotalSpace F V → M) := contMDiff_proj V
  have hπT := hπ.contMDiff_tangentMap (m := ∞) (by simp)
  have hA := ((cov.contMDiffOn_connectionForm hcov e).contMDiffAt
    ((e.open_baseSet.preimage (FiberBundle.continuous_proj E (TangentSpace I))).mem_nhds hp)).comp
      p (hπT p)
  have hfπ := (hf.contMDiffAt (hU.mem_nhds hp)).comp p
    (contMDiffAt_proj (TangentSpace (I.prod 𝓘(ℝ, F))))
  have hb : ContMDiffAt (I.prod 𝓘(ℝ, F)).tangent I ∞
      (fun q : TangentBundle (I.prod 𝓘(ℝ, F)) (TotalSpace F V) => q.proj.proj) p :=
    (hπ p.proj).comp p (contMDiffAt_proj (TangentSpace (I.prod 𝓘(ℝ, F))))
  apply (e.contMDiffAt_iff (IB := I)
    (f := fun q : TangentBundle (I.prod 𝓘(ℝ, F)) (TotalSpace F V) =>
      (⟨q.proj.proj, cov.connector q.proj q.snd⟩ : TotalSpace F V))
    (e.mem_source.mpr hp)).mpr
  refine ⟨hb, ?_⟩
  apply (hd.add (hA.clm_apply hfπ)).congr_of_eventuallyEq
  filter_upwards [hDU] with q hq
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hq]
  exact cov.connector_coord e hq q.snd

end Smoothness

end CovariantDerivative
