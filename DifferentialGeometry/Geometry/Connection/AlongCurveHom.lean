import DifferentialGeometry.Geometry.Connection.AlongCurve
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

section FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I]

theorem derivAlongWithin_clm_apply_of_eq_zero
    (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
    (γ : ℝ → M) (A : ∀ t, V₁ (γ t) →L[ℝ] V₂ (γ t))
    (Z : ∀ t, V₁ (γ t)) {J : Set ℝ} {t : ℝ}
    (hA : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun s => (⟨γ s, A s⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))) J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F₁ V₁)) J t)
    (hzero : Z t = 0) :
    cov₂.derivAlongWithin γ (fun s => A s (Z s)) J t =
      A t (cov₁.derivAlongWithin γ Z J t) := by
  let e₁ := trivializationAt F₁ V₁ (γ t)
  let e₂ := trivializationAt F₂ V₂ (γ t)
  have he₁ : γ t ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ V₁ (γ t)
  have he₂ : γ t ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ V₂ (γ t)
  have hAc := (mdifferentiableWithinAt_hom_bundle _).mp hA
  have hZc := (mdifferentiableWithinAt_totalSpace I _).mp hZ
  have hpre₁ : ∀ᶠ s in 𝓝[J] t, γ s ∈ e₁.baseSet :=
    hAc.1.continuousWithinAt.preimage_mem_nhdsWithin (e₁.open_baseSet.mem_nhds he₁)
  have hpre₂ : ∀ᶠ s in 𝓝[J] t, γ s ∈ e₂.baseSet :=
    hAc.1.continuousWithinAt.preimage_mem_nhdsWithin (e₂.open_baseSet.mem_nhds he₂)
  let B : ℝ → F₁ →L[ℝ] F₂ := fun s => ContinuousLinearMap.inCoordinates
    F₁ V₁ F₂ V₂ (γ t) (γ s) (γ t) (γ s) (A s)
  let z : ℝ → F₁ := fun s => e₁.continuousLinearMapAt ℝ (γ s) (Z s)
  let az : ℝ → F₂ := fun s => e₂.continuousLinearMapAt ℝ (γ s) (A s (Z s))
  have hB : DifferentiableWithinAt ℝ B J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp hAc.2
  have hz : DifferentiableWithinAt ℝ z J t := by
    apply (mdifferentiableWithinAt_iff_differentiableWithinAt.mp hZc.2).congr_of_eventuallyEq
    · filter_upwards [hpre₁] with s hs
      exact e₁.continuousLinearMapAt_apply_of_mem ℝ hs (Z s)
    · exact e₁.continuousLinearMapAt_apply_of_mem ℝ he₁ (Z t)
  have hz0 : z t = 0 := by simp [z, hzero]
  have haz0 : az t = 0 := by simp [az, hzero]
  have hcoord (s : ℝ) (hs₁ : γ s ∈ e₁.baseSet) (hs₂ : γ s ∈ e₂.baseSet) :
      az s = B s (z s) := by
    dsimp only [az, B, z]
    rw [ContinuousLinearMap.inCoordinates_eq hs₁ hs₂]
    change e₂.continuousLinearMapAt ℝ (γ s) (A s (Z s)) =
      e₂.continuousLinearEquivAt ℝ (γ s) hs₂
        (A s ((e₁.continuousLinearEquivAt ℝ (γ s) hs₁).symm
          (e₁.continuousLinearMapAt ℝ (γ s) (Z s))))
    rw [← Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e₁ hs₁,
      ContinuousLinearEquiv.symm_apply_apply,
      Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e₂ hs₂]
  have heq : az =ᶠ[𝓝[J] t] fun s => B s (z s) := by
    filter_upwards [hpre₁, hpre₂] with s hs₁ hs₂
    exact hcoord s hs₁ hs₂
  have hderiv : derivWithin az J t = B t (derivWithin z J t) := by
    rw [heq.derivWithin_eq (hcoord t he₁ he₂), derivWithin_clm_apply hB hz, hz0,
      map_zero, zero_add]
  change e₂.symmL ℝ (γ t)
      (derivWithin az J t + cov₂.connectionForm e₂ (γ t) _ (az t)) =
    A t (e₁.symmL ℝ (γ t)
      (derivWithin z J t + cov₁.connectionForm e₁ (γ t) _ (z t)))
  rw [haz0, hz0, map_zero, map_zero, add_zero, add_zero, hderiv]
  dsimp only [B]
  rw [ContinuousLinearMap.inCoordinates_eq he₁ he₂]
  change e₂.symmL ℝ (γ t)
      (e₂.continuousLinearEquivAt ℝ (γ t) he₂
        (A t ((e₁.continuousLinearEquivAt ℝ (γ t) he₁).symm (derivWithin z J t)))) = _
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e₂ he₂,
    e₂.symmL_continuousLinearMapAt he₂,
    e₁.symm_continuousLinearEquivAt_eq he₁]

end FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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
  [ContMDiffVectorBundle 1 F₂ V₂ I]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)] [T2Space M] in
private theorem hom_trivialization_coord_apply
    (e₁ : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ V₁ → M))
    (e₂ : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ V₂ → M))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet)
    (A : V₁ x →L[ℝ] V₂ x) (v : F₁) :
    (e₁.continuousLinearMap (RingHom.id ℝ) e₂).continuousLinearMapAt ℝ x A v =
      e₂.continuousLinearMapAt ℝ x (A (e₁.symmL ℝ x v)) := by
  rw [(e₁.continuousLinearMap (RingHom.id ℝ) e₂).continuousLinearMapAt_apply_of_mem ℝ ⟨hx₁, hx₂⟩]
  rfl

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)] [T2Space M] in
private theorem hom_trivialization_symm_apply
    (e₁ : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ V₁ → M))
    (e₂ : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ V₂ → M))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet)
    (A : F₁ →L[ℝ] F₂) (v : F₁) :
    (e₁.continuousLinearMap (RingHom.id ℝ) e₂).symmL ℝ x A (e₁.symmL ℝ x v) =
      e₂.symmL ℝ x (A v) := by
  apply (e₂.continuousLinearEquivAt ℝ x hx₂).injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq]
  rw [← hom_trivialization_coord_apply e₁ e₂ hx₁ hx₂,
    (e₁.continuousLinearMap (RingHom.id ℝ) e₂).continuousLinearMapAt_symmL ⟨hx₁, hx₂⟩,
    e₂.continuousLinearMapAt_symmL hx₂]

private theorem connectionForm_hom_apply
    (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
    (e₁ : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ V₁ → M))
    (e₂ : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ V₂ → M))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet)
    (X : TangentSpace I x) (A : F₁ →L[ℝ] F₂) (v : F₁) :
    (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂).connectionForm
        (e₁.continuousLinearMap (RingHom.id ℝ) e₂) x X A v =
      cov₂.connectionForm e₂ x X (A v) - A (cov₁.connectionForm e₁ x X v) := by
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have hx : x ∈ e.baseSet := ⟨hx₁, hx₂⟩
  let τ := fun y => e.symmL ℝ y A
  let Y := fun y => e₁.symmL ℝ y v
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun y => (⟨y, τ y⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))) x := by
    rw [e.mdifferentiableAt_section_iff I _ hx]
    apply (mdifferentiableAt_const (c := A)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e.continuousLinearMapAt_symmL hy A
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁))
      (fun y => (⟨y, Y y⟩ : TotalSpace F₁ V₁)) x := by
    rw [e₁.mdifferentiableAt_section_iff I _ hx₁]
    apply (mdifferentiableAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁] with y hy
    rw [← e₁.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e₁.continuousLinearMapAt_symmL hy v
  have hAY : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂))
      (fun y => (⟨y, e₂.symmL ℝ y (A v)⟩ : TotalSpace F₂ V₂)) x := by
    rw [e₂.mdifferentiableAt_section_iff I _ hx₂]
    apply (mdifferentiableAt_const (c := (A v))).congr_of_eventuallyEq
    filter_upwards [e₂.open_baseSet.mem_nhds hx₂] with y hy
    rw [← e₂.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e₂.continuousLinearMapAt_symmL hy (A v)
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hEq : ∀ᶠ y in 𝓝 x, τ y (Y y) = e₂.symmL ℝ y (A v) := by
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁, e₂.open_baseSet.mem_nhds hx₂]
      with y hy₁ hy₂
    exact hom_trivialization_symm_apply e₁ e₂ hy₁ hy₂ A v
  have hcovEq := cov₂.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hτ.clm_bundle_apply hY) hAY Filter.univ_mem hEq
  rw [connectionForm_apply _ _ hx]
  change e.continuousLinearMapAt ℝ x
    (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ τ x X) v = _
  rw [hom_trivialization_coord_apply e₁ e₂ hx₁ hx₂, ← hW,
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M F₁ V₁ F₂ V₂ cov₁ cov₂ τ hτ W.mdifferentiableAt hY,
    hcovEq, hW, map_sub]
  rw [connectionForm_apply cov₂ e₂ hx₂, connectionForm_apply cov₁ e₁ hx₁]
  congr 1
  have h := hom_trivialization_coord_apply e₁ e₂ hx₁ hx₂ (τ x)
    (e₁.continuousLinearMapAt ℝ x (cov₁ Y x X))
  rw [e₁.symmL_continuousLinearMapAt hx₁] at h
  rw [show e.continuousLinearMapAt ℝ x (τ x) = A from
    e.continuousLinearMapAt_symmL hx A] at h
  exact h.symm

theorem derivAlongWithin_clm_apply
    (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)
    (γ : ℝ → M) (A : ∀ t, V₁ (γ t) →L[ℝ] V₂ (γ t))
    (Z : ∀ t, V₁ (γ t)) {J : Set ℝ} {t : ℝ}
    (hA : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun s => (⟨γ s, A s⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))) J t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F₁))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F₁ V₁)) J t) :
    cov₂.derivAlongWithin γ (fun s => A s (Z s)) J t =
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
        I M F₁ V₁ F₂ V₂ cov₁ cov₂).derivAlongWithin γ A J t) (Z t) +
          A t (cov₁.derivAlongWithin γ Z J t) := by
  let e₁ := trivializationAt F₁ V₁ (γ t)
  let e₂ := trivializationAt F₂ V₂ (γ t)
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have he₁ : γ t ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ V₁ (γ t)
  have he₂ : γ t ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ V₂ (γ t)
  have he : γ t ∈ e.baseSet := ⟨he₁, he₂⟩
  let cov := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
    I M F₁ V₁ F₂ V₂ cov₁ cov₂
  have hAc := (mdifferentiableWithinAt_hom_bundle _).mp hA
  have hZc := (mdifferentiableWithinAt_totalSpace I _).mp hZ
  have hpre₁ : ∀ᶠ s in 𝓝[J] t, γ s ∈ e₁.baseSet :=
    hAc.1.continuousWithinAt.preimage_mem_nhdsWithin (e₁.open_baseSet.mem_nhds he₁)
  have hpre₂ : ∀ᶠ s in 𝓝[J] t, γ s ∈ e₂.baseSet :=
    hAc.1.continuousWithinAt.preimage_mem_nhdsWithin (e₂.open_baseSet.mem_nhds he₂)
  let B : ℝ → F₁ →L[ℝ] F₂ := fun s => ContinuousLinearMap.inCoordinates
    F₁ V₁ F₂ V₂ (γ t) (γ s) (γ t) (γ s) (A s)
  let z : ℝ → F₁ := fun s => e₁.continuousLinearMapAt ℝ (γ s) (Z s)
  let az : ℝ → F₂ := fun s => e₂.continuousLinearMapAt ℝ (γ s) (A s (Z s))
  have hB : DifferentiableWithinAt ℝ B J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp hAc.2
  have hz : DifferentiableWithinAt ℝ z J t := by
    apply (mdifferentiableWithinAt_iff_differentiableWithinAt.mp hZc.2).congr_of_eventuallyEq
    · filter_upwards [hpre₁] with s hs
      exact e₁.continuousLinearMapAt_apply_of_mem ℝ hs (Z s)
    · exact e₁.continuousLinearMapAt_apply_of_mem ℝ he₁ (Z t)
  have hBcoord (s : ℝ) (hs₁ : γ s ∈ e₁.baseSet) (hs₂ : γ s ∈ e₂.baseSet) :
      e.continuousLinearMapAt ℝ (γ s) (A s) = B s := by
    rw [e.continuousLinearMapAt_apply_of_mem ℝ ⟨hs₁, hs₂⟩]
    rfl
  have hBvalue (s : ℝ) (hs₁ : γ s ∈ e₁.baseSet) (hs₂ : γ s ∈ e₂.baseSet)
      (w : V₁ (γ s)) :
      B s (e₁.continuousLinearMapAt ℝ (γ s) w) =
        e₂.continuousLinearMapAt ℝ (γ s) (A s w) := by
    rw [← hBcoord s hs₁ hs₂, hom_trivialization_coord_apply e₁ e₂ hs₁ hs₂,
      e₁.symmL_continuousLinearMapAt hs₁]
  have heq : az =ᶠ[𝓝[J] t] fun s => B s (z s) := by
    filter_upwards [hpre₁, hpre₂] with s hs₁ hs₂
    exact (hBvalue s hs₁ hs₂ (Z s)).symm
  have hderiv : derivWithin az J t = derivWithin B J t (z t) +
      B t (derivWithin z J t) := by
    rw [heq.derivWithin_eq (hBvalue t he₁ he₂ (Z t)).symm, derivWithin_clm_apply hB hz]
  have hBC : (fun s => e.continuousLinearMapAt ℝ (γ s) (A s)) =ᶠ[𝓝[J] t] B := by
    filter_upwards [hpre₁, hpre₂] with s hs₁ hs₂
    exact hBcoord s hs₁ hs₂
  have hDA := cov.derivAlongWithin_coord e he hA
  rw [hBC.derivWithin_eq (hBcoord t he₁ he₂), hBcoord t he₁ he₂] at hDA
  apply (e₂.continuousLinearEquivAt ℝ (γ t) he₂).injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq, map_add]
  have hleft := cov₂.derivAlongWithin_coord e₂ he₂ (hA.clm_bundle_apply hZ)
  have hright := cov₁.derivAlongWithin_coord e₁ he₁ hZ
  change e₂.continuousLinearMapAt ℝ (γ t)
    (cov₂.derivAlongWithin γ (fun s => A s (Z s)) J t) =
      e₂.continuousLinearMapAt ℝ (γ t) ((cov.derivAlongWithin γ A J t) (Z t)) +
        e₂.continuousLinearMapAt ℝ (γ t) (A t (cov₁.derivAlongWithin γ Z J t))
  rw [hleft, ← hBvalue t he₁ he₂ (cov₁.derivAlongWithin γ Z J t)]
  have hcoordDA := hom_trivialization_coord_apply e₁ e₂ he₁ he₂
    (cov.derivAlongWithin γ A J t) (z t)
  rw [show e₁.symmL ℝ (γ t) (z t) = Z t from
    e₁.symmL_continuousLinearMapAt he₁ (Z t), hDA] at hcoordDA
  rw [← hcoordDA, hright]
  change derivWithin az J t + cov₂.connectionForm e₂ (γ t) _ (az t) =
    (derivWithin B J t + cov.connectionForm e (γ t) _ (B t)) (z t) +
      B t (derivWithin z J t + cov₁.connectionForm e₁ (γ t) _ (z t))
  rw [hderiv, show az t = B t (z t) from (hBvalue t he₁ he₂ (Z t)).symm]
  simp only [add_apply, map_add]
  rw [connectionForm_hom_apply cov₁ cov₂ e₁ e₂ he₁ he₂]
  abel

end CovariantDerivative
