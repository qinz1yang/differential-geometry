import DifferentialGeometry.Geometry.Connection.ConnectionForm
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem derivWithin_comp_eq_mvfderiv
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {γ : ℝ → M} {f : M → G} {J : Set ℝ} {t : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t)
    (hf : MDifferentiableAt I 𝓘(ℝ, G) f (γ t))
    (hJ : UniqueDiffWithinAt ℝ J t) :
    derivWithin (fun s => f (γ s)) J t =
      mvfderiv I f (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)) := by
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
      TangentSpace 𝓘(ℝ, G) (f (γ t)) =>
        NormedSpace.fromTangentSpace (f (γ t))
          (L ((NormedSpace.fromTangentSpace t).symm 1)))
    (mfderiv_comp_mfderivWithin t hf hγ hJ.uniqueMDiffWithinAt)
  rw [mfderivWithin_eq_fderivWithin] at h
  exact h

private theorem mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt
    (γ : ℝ → M) {J : Set ℝ} {t : ℝ} (hJ : ¬UniqueDiffWithinAt ℝ J t) :
    mfderivWithin 𝓘(ℝ, ℝ) I γ J t = 0 := by
  by_cases hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t
  · exact hd.mfderivWithin.trans
      (fderivWithin_zero_of_not_uniqueDiffWithinAt
        (f := writtenInExtChartAt 𝓘(ℝ, ℝ) I t γ)
        (show ¬UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t from
          fun h => hJ h.uniqueDiffWithinAt))
  · exact mfderivWithin_zero_of_not_mdifferentiableWithinAt hd

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]

def derivAlongWithin (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) (J : Set ℝ) (t : ℝ) : V (γ t) :=
  let e := trivializationAt F V (γ t)
  e.symmL ℝ (γ t)
    (derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
      cov.connectionForm e (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
        (e.continuousLinearMapAt ℝ (γ t) (Z t)))

theorem derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt
    (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) {J : Set ℝ} {t : ℝ}
    (hJ : ¬UniqueDiffWithinAt ℝ J t) :
    cov.derivAlongWithin γ Z J t = 0 := by
  have hγ := mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ
  simp only [derivAlongWithin, derivWithin_zero_of_not_uniqueDiffWithinAt hJ, hγ,
    zero_apply, map_zero, zero_add]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiniteDimensional ℝ F] in
private theorem differentiableWithinAt_trivialization_coord_along
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    DifferentiableWithinAt ℝ (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t := by
  have h := (e.mdifferentiableWithinAt_totalSpace_iff I
    (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ
  apply mdifferentiableWithinAt_iff_differentiableWithinAt.mp
  apply h.2.congr_of_eventuallyEq
  · filter_upwards [h.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with s hs
    exact e.continuousLinearMapAt_apply_of_mem ℝ hs (Z s)
  · exact e.continuousLinearMapAt_apply_of_mem ℝ he (Z t)

private theorem derivAlongWithin_coordChange
    (cov : CovariantDerivative I F V)
    (e e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (he : γ t ∈ e.baseSet) (he' : γ t ∈ e'.baseSet)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    e'.coordChangeL ℝ e (γ t)
        (derivWithin (fun s => e'.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
          cov.connectionForm e' (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
            (e'.continuousLinearMapAt ℝ (γ t) (Z t))) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  let R : M → F →L[ℝ] F := fun x => e'.coordChangeL ℝ e x
  let z : ℝ → F := fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)
  let z' : ℝ → F := fun s => e'.continuousLinearMapAt ℝ (γ s) (Z s)
  let X := mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t :=
    ((e.mdifferentiableWithinAt_totalSpace_iff I
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hR : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) R (γ t) :=
    (contMDiffAt_coordChangeL (IB := I) (n := 1) he' he).mdifferentiableAt (by simp)
  have hRγ : DifferentiableWithinAt ℝ (fun s => R (γ s)) J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp
      (hR.comp_mdifferentiableWithinAt t hγ)
  have hz' : DifferentiableWithinAt ℝ z' J t :=
    differentiableWithinAt_trivialization_coord_along e' he' hZ
  have hcoord (s : ℝ) (hs : γ s ∈ e.baseSet) (hs' : γ s ∈ e'.baseSet) :
      z s = R (γ s) (z' s) := by
    dsimp only [z, z', R]
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [e'.coordChangeL_apply' e ⟨hs', hs⟩, ← e'.mk_symm hs',
      ← e'.symmL_apply (R := ℝ) hs', e'.symmL_continuousLinearMapAt hs',
      e.continuousLinearMapAt_apply_of_mem ℝ hs]
  have heq : z =ᶠ[𝓝[J] t] (fun s => R (γ s) (z' s)) := by
    filter_upwards [hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he), hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (e'.open_baseSet.mem_nhds he')] with s hs hs'
    exact hcoord s hs hs'
  have hDz : derivWithin z J t =
      derivWithin (fun s => R (γ s)) J t (z' t) + R (γ t) (derivWithin z' J t) := by
    rw [heq.derivWithin_eq (hcoord t he he'), derivWithin_clm_apply hRγ hz']
  have hDR : derivWithin (fun s => R (γ s)) J t (z' t) =
      mvfderiv I (fun x => R x (z' t)) (γ t) X := by
    have h := derivWithin_comp_eq_mvfderiv hγ
      (hR.clm_apply (mdifferentiableAt_const (c := z' t))) hJ
    rw [derivWithin_clm_apply hRγ (differentiableWithinAt_const (z' t)),
      derivWithin_fun_const, Pi.zero_apply, map_zero, add_zero] at h
    exact h
  have htrans := cov.connectionForm_coordChange e e' he he' X (z' t)
  change R (γ t) (cov.connectionForm e' (γ t) X (z' t)) =
    mvfderiv I (fun x => R x (z' t)) (γ t) X +
      cov.connectionForm e (γ t) X (R (γ t) (z' t)) at htrans
  change R (γ t) (derivWithin z' J t + cov.connectionForm e' (γ t) X (z' t)) =
    derivWithin z J t + cov.connectionForm e (γ t) X (z t)
  rw [map_add, htrans, ← hcoord t he he', hDz, hDR]
  abel

private theorem derivAlongWithin_coord_of_uniqueDiffWithinAt (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ Z J t) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  let e₀ := trivializationAt F V (γ t)
  have he₀ : γ t ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
  have h := derivAlongWithin_coordChange cov e e₀ he he₀ hJ hZ
  rw [e₀.coordChangeL_apply' e ⟨he₀, he⟩, ← e₀.mk_symm he₀,
    ← e₀.symmL_apply (R := ℝ) he₀, ← e.continuousLinearMapAt_apply_of_mem ℝ he] at h
  exact h

theorem derivAlongWithin_coord (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ Z J t) =
      derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t)) := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · exact derivAlongWithin_coord_of_uniqueDiffWithinAt cov e he hJ hZ
  · simp only [cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ Z hJ,
      derivWithin_zero_of_not_uniqueDiffWithinAt hJ,
      mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ, zero_apply, map_zero,
      zero_add]

theorem derivAlongWithin_eq (cov : CovariantDerivative I F V)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    cov.derivAlongWithin γ Z J t = e.symmL ℝ (γ t)
      (derivWithin (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t +
        cov.connectionForm e (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
          (e.continuousLinearMapAt ℝ (γ t) (Z t))) := by
  rw [← cov.derivAlongWithin_coord e he hZ, e.symmL_continuousLinearMapAt he]

theorem derivAlongWithin_section (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {σ : ∀ x : M, V x} {J : Set ℝ} {t : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) (γ t)) :
    cov.derivAlongWithin γ (fun s => σ (γ s)) J t =
      cov σ (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)) := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · let e := trivializationAt F V (γ t)
    have he : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (γ t)
    have hZ := hσ.comp_mdifferentiableWithinAt t hγ
    rw [cov.derivAlongWithin_eq e he hZ]
    have hσ' : MDifferentiableAt I 𝓘(ℝ, F)
        (fun x => e.continuousLinearMapAt ℝ x (σ x)) (γ t) := by
      apply ((e.mdifferentiableAt_section_iff I σ he).mp hσ).congr_of_eventuallyEq
      filter_upwards [e.open_baseSet.mem_nhds he] with x hx
      exact e.continuousLinearMapAt_apply_of_mem ℝ hx (σ x)
    rw [derivWithin_comp_eq_mvfderiv hγ hσ' hJ,
      ← cov.covariant_derivative_coord e he hσ, e.symmL_continuousLinearMapAt he]
  · simp only [cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ _ hJ,
      mfderivWithin_curve_eq_zero_of_not_uniqueDiffWithinAt (I := I) γ hJ, zero_apply, map_zero]

theorem derivAlongWithin_singleton (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) (t : ℝ) :
    cov.derivAlongWithin γ Z {t} t = 0 := by
  apply cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt
  simp only [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin,
    sdiff_self, nhdsWithin_empty, not_neBot]

theorem derivAlongWithin_congr_of_eventuallyEq (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZW : ∀ᶠ s in 𝓝[J] t, Z s = W s) (ht : Z t = W t) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ W J t := by
  let e := trivializationAt F V (γ t)
  have heq : (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) =ᶠ[𝓝[J] t]
      (fun s => e.continuousLinearMapAt ℝ (γ s) (W s)) := by
    filter_upwards [hZW] with s hs
    rw [hs]
  dsimp only [derivAlongWithin]
  rw [heq.derivWithin_eq (congrArg (e.continuousLinearMapAt ℝ (γ t)) ht), ht]

theorem derivAlongWithin_congr (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZW : ∀ s ∈ J, Z s = W s) (ht : Z t = W t) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ W J t := by
  apply cov.derivAlongWithin_congr_of_eventuallyEq _ ht
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hZW s hs

theorem derivAlongWithin_mono (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J K : Set ℝ} {t : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t)
    (hK : UniqueDiffWithinAt ℝ K t) (hKJ : K ⊆ J) :
    cov.derivAlongWithin γ Z K t = cov.derivAlongWithin γ Z J t := by
  let e := trivializationAt F V (γ t)
  have he : γ t ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t)
  have hγ := ((e.mdifferentiableWithinAt_totalSpace_iff I
    (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hcoord := differentiableWithinAt_trivialization_coord_along e he hZ
  rw [cov.derivAlongWithin_eq e he (hZ.mono hKJ), cov.derivAlongWithin_eq e he hZ,
    hγ.mfderivWithin_mono hK.uniqueMDiffWithinAt hKJ,
    (hcoord.hasDerivWithinAt.mono hKJ).derivWithin hK]

theorem derivAlongWithin_congr_set (cov : CovariantDerivative I F V)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {J K : Set ℝ} {t : ℝ}
    (hJK : J =ᶠ[𝓝 t] K) :
    cov.derivAlongWithin γ Z J t = cov.derivAlongWithin γ Z K t := by
  dsimp only [derivAlongWithin]
  rw [derivWithin_congr_set hJK, mfderivWithin_congr_set hJK]

end CovariantDerivative
