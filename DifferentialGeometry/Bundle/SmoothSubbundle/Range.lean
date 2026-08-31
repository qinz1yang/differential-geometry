import DifferentialGeometry.Bundle.SmoothSubbundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

noncomputable section

open Bundle Module Set
open scoped Manifold

universe u uE uH uM uF uG uF₁ uF₂ uV₁ uV₂

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞}

private theorem exists_range_frame
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (A : M → F →L[𝕜] G)
    (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n A W)
    (k : ℕ) (hrange : ∀ x ∈ W, finrank 𝕜 (A x).range = k)
    (x₀ : M) (hx₀ : x₀ ∈ W) :
    ∃ (U : Set M) (s : Fin k → M → G),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ x ∈ U, LinearIndependent 𝕜 (s · x)) ∧
      (∀ x ∈ U, Submodule.span 𝕜 (Set.range (s · x)) = (A x).range) ∧
      (∀ i, ContMDiffOn I 𝓘(𝕜, G) n (s i) U) := by
  classical
  let b : Basis (Fin k) 𝕜 (A x₀).range :=
    Module.finBasisOfFinrankEq 𝕜 (A x₀).range (hrange x₀ hx₀)
  let v : Fin k → F := fun i => Classical.choose (b i).property
  have hv (i : Fin k) : A x₀ (v i) = b i :=
    Classical.choose_spec (b i).property
  let s : Fin k → M → G := fun i x => A x (v i)
  let t : M → Fin k → G := fun x i => s i x
  have ht : ContMDiffOn I 𝓘(𝕜, Fin k → G) n t W := by
    rw [contMDiffOn_pi_space]
    intro i
    exact hA.clm_apply contMDiffOn_const
  have hs₀ : LinearIndependent 𝕜 (s · x₀) := by
    have hb : LinearIndependent 𝕜 ((A x₀).range.subtype ∘ b) :=
      b.linearIndependent.map' (A x₀).range.subtype
        (Submodule.ker_subtype (A x₀).range)
    have hs : (s · x₀) = (A x₀).range.subtype ∘ b := by
      funext i
      exact hv i
    rw [hs]
    exact hb
  let U : Set M := W ∩ t ⁻¹' {f | LinearIndependent 𝕜 f}
  have hU : IsOpen U :=
    ht.continuousOn.isOpen_inter_preimage hW isOpen_setOfPred_linearIndependent
  have hx₀U : x₀ ∈ U := by
    refine ⟨hx₀, ?_⟩
    simpa [t] using hs₀
  refine ⟨U, s, hU, hx₀U, inter_subset_left, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.2
  · intro x hx
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact LinearMap.mem_range_self (A x).toLinearMap (v i)
    · rw [hrange x hx.1]
      simpa using finrank_span_eq_card hx.2
  · intro i
    exact (hA.clm_apply contMDiffOn_const).mono inter_subset_left

variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {V₁ : M → Type uV₁} [TopologicalSpace (TotalSpace F₁ V₁)]
variable [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
variable [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
variable {V₂ : M → Type uV₂} [TopologicalSpace (TotalSpace F₂ V₂)]
variable [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
variable [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]

namespace ContMDiffVectorSubbundle

variable [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
variable [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ I]
variable [VectorBundle 𝕜 F₂ V₂] [ContMDiffVectorBundle n F₂ V₂ I]
variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

theorem exists_range_frameOn
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)) W)
    (k : ℕ) (hrange : ∀ x ∈ W, finrank 𝕜 (A x).range = k)
    (x₀ : M) (hx₀ : x₀ ∈ W) :
    ∃ (U : Set M) (s : Fin k → (x : M) → V₂ x),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
        IsSubbundleFrameOn (I := I) (F := F₂) (n := n)
          (fun x => (A x).range) s U := by
  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let eA := e₁.continuousLinearMap (RingHom.id 𝕜) e₂
  let W' : Set M := W ∩ (e₁.baseSet ∩ e₂.baseSet)
  let a : M → F₁ →L[𝕜] F₂ := fun x =>
    (eA (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x))).2
  have hW' : IsOpen W' := hW.inter (e₁.open_baseSet.inter e₂.open_baseSet)
  have hx₀W' : x₀ ∈ W' := ⟨hx₀, mem_baseSet_trivializationAt F₁ V₁ x₀,
    mem_baseSet_trivializationAt F₂ V₂ x₀⟩
  have hmaps : MapsTo
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)) W' eA.source := by
    intro x hx
    rw [eA.source_eq]
    change x ∈ eA.baseSet
    simpa [eA, W'] using hx.2
  have ha : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n a W' := by
    exact ((eA.contMDiffOn_iff hmaps).mp (hA.mono inter_subset_left)).2
  have hrange_a : ∀ x ∈ W', finrank 𝕜 (a x).range = k := by
    intro x hx
    let ex₁ : V₁ x ≃ₗ[𝕜] F₁ := e₁.linearEquivAt (R := 𝕜) x hx.2.1
    let ex₂ : V₂ x ≃ₗ[𝕜] F₂ := e₂.linearEquivAt (R := 𝕜) x hx.2.2
    have ha_apply (v : F₁) : a x v = ex₂ (A x (ex₁.symm v)) := by
      change (e₂.linearMapAt 𝕜 x) (A x (e₁.symmL 𝕜 x v)) =
        ex₂ (A x (ex₁.symm v))
      dsimp only [ex₁, ex₂]
      rw [e₂.linearMapAt_def_of_mem hx.2.2, e₁.symmL_apply hx.2.1]
      change (e₂.linearEquivAt 𝕜 x hx.2.2)
        (A x ((e₁.linearEquivAt 𝕜 x hx.2.1).symm v)) = _
      rfl
    have hrange_eq : (a x).range = Submodule.map ex₂.toLinearMap (A x).range := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨A x (ex₁.symm v), LinearMap.mem_range_self (A x).toLinearMap _, ?_⟩
        exact (ha_apply v).symm
      · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
        refine ⟨ex₁ v, ?_⟩
        simp [ha_apply]
    rw [hrange_eq, LinearEquiv.finrank_map_eq, hrange x hx.1]
  obtain ⟨U, t, hU, hx₀U, hUW', htli, htspan, ht⟩ :=
    exists_range_frame a W' hW' ha k hrange_a x₀ hx₀W'
  let s : Fin k → (x : M) → V₂ x := fun i x => e₂.symmL 𝕜 x (t i x)
  refine ⟨U, s, hU, hx₀U, fun _ hx => (hUW' hx).1, ?_⟩
  have hUe₂ : U ⊆ e₂.baseSet := fun _ hx => (hUW' hx).2.2
  have hcoord_range (x : M) (hx : x ∈ W') (v : F₂) :
      e₂.symmL 𝕜 x v ∈ (A x).range ↔ v ∈ (a x).range := by
    let ex₁ : V₁ x ≃ₗ[𝕜] F₁ := e₁.linearEquivAt (R := 𝕜) x hx.2.1
    let ex₂ : V₂ x ≃ₗ[𝕜] F₂ := e₂.linearEquivAt (R := 𝕜) x hx.2.2
    have ha_apply (w : F₁) : a x w = ex₂ (A x (ex₁.symm w)) := by
      change (e₂.linearMapAt 𝕜 x) (A x (e₁.symmL 𝕜 x w)) =
        ex₂ (A x (ex₁.symm w))
      dsimp only [ex₁, ex₂]
      rw [e₂.linearMapAt_def_of_mem hx.2.2, e₁.symmL_apply hx.2.1]
      change (e₂.linearEquivAt 𝕜 x hx.2.2)
        (A x ((e₁.linearEquivAt 𝕜 x hx.2.1).symm w)) = _
      rfl
    have hrange_eq : (a x).range = Submodule.map ex₂.toLinearMap (A x).range := by
      ext y
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨A x (ex₁.symm w), LinearMap.mem_range_self (A x).toLinearMap _, ?_⟩
        exact (ha_apply w).symm
      · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
        refine ⟨ex₁ w, ?_⟩
        simp [ha_apply]
    have hsymm : e₂.symmL 𝕜 x v = ex₂.symm v := by
      rw [e₂.symmL_apply hx.2.2]
      rfl
    rw [hsymm, hrange_eq, Submodule.mem_map_equiv]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    let ex₂ : V₂ x ≃ₗ[𝕜] F₂ := e₂.linearEquivAt (R := 𝕜) x (hUe₂ hx)
    apply LinearIndependent.of_comp ex₂.toLinearMap
    have hs : (⇑ex₂.toLinearMap ∘ (s · x)) = (t · x) := by
      funext i
      change ex₂ (e₂.symmL 𝕜 x (t i x)) = t i x
      rw [e₂.symmL_apply (hUe₂ hx)]
      exact ex₂.apply_symm_apply (t i x)
    rw [hs]
    exact htli x hx
  · intro x hx
    let ex₂ : V₂ x ≃ₗ[𝕜] F₂ := e₂.linearEquivAt (R := 𝕜) x (hUe₂ hx)
    let _ : FiniteDimensional 𝕜 (V₂ x) :=
      FiniteDimensional.of_injective ex₂.toLinearMap ex₂.injective
    have hsli : LinearIndependent 𝕜 (s · x) := by
      apply LinearIndependent.of_comp ex₂.toLinearMap
      have hs : (⇑ex₂.toLinearMap ∘ (s · x)) = (t · x) := by
        funext i
        change ex₂ (e₂.symmL 𝕜 x (t i x)) = t i x
        rw [e₂.symmL_apply (hUe₂ hx)]
        exact ex₂.apply_symm_apply (t i x)
      rw [hs]
      exact htli x hx
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      apply (hcoord_range x (hUW' hx) (t i x)).mpr
      rw [← htspan x hx]
      exact Submodule.subset_span (Set.mem_range_self i)
    · rw [hrange x (hUW' hx).1]
      simpa using finrank_span_eq_card hsli
  · intro i
    apply (e₂.contMDiffOn_section_iff hU hUe₂).mpr
    exact (ht i).congr fun x hx => by
      simp [s, e₂.symmL_apply, hUe₂ hx]

def range
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hrange : ∀ x, finrank 𝕜 (A x).range = k) :
    ContMDiffVectorSubbundle (I := I) (F := F₂) (V := V₂) (n := n) where
  fiber x := (A x).range
  rank := k
  exists_isSubbundleFrameOn x₀ := by
    obtain ⟨U, s, hU, hx₀U, _, hs⟩ :=
      exists_range_frameOn A Set.univ isOpen_univ hA.contMDiffOn
        k (fun x _ => hrange x) x₀ (Set.mem_univ x₀)
    exact ⟨U, s, hU, hx₀U, hs⟩

@[simp]
theorem range_fiber
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hrange : ∀ x, finrank 𝕜 (A x).range = k) (x : M) :
    (range A hA k hrange).fiber x = (A x).range :=
  rfl

@[simp]
theorem range_rank
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hrange : ∀ x, finrank 𝕜 (A x).range = k) :
    (range A hA k hrange).rank = k :=
  rfl

theorem exists_smooth_range
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hrange : ∀ x, finrank 𝕜 (A x).range = k) :
    ∃ S : ContMDiffVectorSubbundle (I := I) (F := F₂) (V := V₂) (n := n),
      S.rank = k ∧ ∀ x, S.fiber x = (A x).range := by
  let S := ContMDiffVectorSubbundle.range A hA k hrange
  exact ⟨S, range_rank A hA k hrange, fun x => range_fiber A hA k hrange x⟩

theorem exists_smooth_range_frame
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hrange : ∀ x, finrank 𝕜 (A x).range = k) (x : M) :
    ∃ (U : Set M) (s : Fin k → (y : M) → V₂ y),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, LinearIndependent 𝕜 (s · y)) ∧
      (∀ y ∈ U, Submodule.span 𝕜 (Set.range (s · y)) = (A y).range) ∧
      (∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F₂)) n
        (fun y => TotalSpace.mk' F₂ y (s i y)) U) := by
  obtain ⟨U, s, hU, hxU, _, hs⟩ := exists_range_frameOn A Set.univ isOpen_univ
    hA.contMDiffOn k (fun y _ => hrange y) x (Set.mem_univ x)
  exact ⟨U, s, hU, hxU, fun y hy => hs.linearIndependent hy,
    fun y hy => hs.spans hy, hs.contMDiffOn⟩

end ContMDiffVectorSubbundle
