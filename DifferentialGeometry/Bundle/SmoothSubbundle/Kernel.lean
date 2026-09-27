import DifferentialGeometry.Bundle.SmoothSubbundle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Complemented
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

private theorem exists_kernel_frame
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (A : M → F →L[𝕜] G)
    (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n A W)
    (k : ℕ) (hker : ∀ x ∈ W, finrank 𝕜 (A x).ker = k)
    (x₀ : M) (hx₀ : x₀ ∈ W) :
    ∃ (U : Set M) (s : Fin k → M → F),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ x ∈ U, LinearIndependent 𝕜 (s · x)) ∧
      (∀ x ∈ U, Submodule.span 𝕜 (Set.range (s · x)) = (A x).ker) ∧
      (∀ i, ContMDiffOn I 𝓘(𝕜, F) n (s i) U) := by
  let K : Submodule 𝕜 F := (A x₀).ker
  obtain ⟨P, hKP⟩ := K.exists_isCompl
  let A₀P : P →L[𝕜] G := (A x₀).domRestrict P
  have hA₀P : Function.Injective A₀P := by
    intro p q hpq
    apply Subtype.ext
    have hpq' : (p : F) - q ∈ K := by
      change A x₀ ((p : F) - q) = 0
      simpa [A₀P] using sub_eq_zero.mpr hpq
    have hpqP : (p : F) - q ∈ P := P.sub_mem p.2 q.2
    have hz : (p : F) - q ∈ (⊥ : Submodule 𝕜 F) :=
      hKP.disjoint.le_bot ⟨hpq', hpqP⟩
    exact sub_eq_zero.mp (by simpa using hz)
  let eP : P ≃ₗ[𝕜] A₀P.range := LinearEquiv.ofInjective A₀P.toLinearMap hA₀P
  obtain ⟨Q, hRQ⟩ := A₀P.range.exists_isCompl
  let Llin : G →ₗ[𝕜] P := eP.symm.toLinearMap.comp
    (A₀P.range.projectionOnto Q hRQ)
  let L : G →L[𝕜] P := LinearMap.toContinuousLinearMap Llin
  have hLA₀P (p : P) : L (A₀P p) = p := by
    change Llin (A₀P p) = p
    dsimp only [Llin, LinearMap.comp_apply]
    rw [show A₀P.range.projectionOnto Q hRQ (A₀P p) =
        ⟨A₀P p, LinearMap.mem_range_self A₀P.toLinearMap p⟩ by
      exact Submodule.projectionOnto_apply_left hRQ
        (⟨A₀P p, LinearMap.mem_range_self A₀P.toLinearMap p⟩ : A₀P.range)]
    exact eP.symm_apply_apply p
  let _ : CompleteSpace P := FiniteDimensional.complete 𝕜 P
  let D : M → P →L[𝕜] P := fun x => L.comp ((A x).domRestrict P)
  have hD : ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) n D W := by
    simpa only [D, ContinuousLinearMap.domRestrict] using
      contMDiffOn_const.clm_comp (hA.clm_comp contMDiffOn_const)
  have hDx₀ : D x₀ = ContinuousLinearMap.id 𝕜 P := by
    ext p
    exact congr_arg Subtype.val (hLA₀P p)
  let U : Set M := W ∩ D ⁻¹' {T | IsUnit T}
  have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage hW Units.isOpen
  have hx₀U : x₀ ∈ U := by
    refine ⟨hx₀, ?_⟩
    change IsUnit (D x₀)
    rw [hDx₀]
    exact isUnit_one
  have hDinv : ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) n
      (fun x => (D x).inverse) U := by
    intro x hx
    have hDi : (D x).IsInvertible := by
      let u : (P →L[𝕜] P)ˣ := IsUnit.unit hx.2
      refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
      exact hx.2.unit_spec
    exact hDi.contDiffAt_map_inverse.comp_contMDiffWithinAt
      ((hD.mono inter_subset_left) x hx)
  let graph : M → K →L[𝕜] F := fun x =>
    K.subtypeL - P.subtypeL.comp ((D x).inverse.comp (L.comp ((A x).domRestrict K)))
  have hgraph : ContMDiffOn I 𝓘(𝕜, K →L[𝕜] F) n graph U := by
    have hAK : ContMDiffOn I 𝓘(𝕜, K →L[𝕜] G) n
        (fun x => (A x).domRestrict K) W := by
      simpa only [ContinuousLinearMap.domRestrict] using hA.clm_comp contMDiffOn_const
    have hLAK : ContMDiffOn I 𝓘(𝕜, K →L[𝕜] P) n
        (fun x => L.comp ((A x).domRestrict K)) W :=
      contMDiffOn_const.clm_comp hAK
    have hinvLAK : ContMDiffOn I 𝓘(𝕜, K →L[𝕜] P) n
        (fun x => (D x).inverse.comp (L.comp ((A x).domRestrict K))) U :=
      hDinv.clm_comp (hLAK.mono inter_subset_left)
    have hPinvLAK : ContMDiffOn I 𝓘(𝕜, K →L[𝕜] F) n
        (fun x => P.subtypeL.comp
          ((D x).inverse.comp (L.comp ((A x).domRestrict K)))) U :=
      contMDiffOn_const.clm_comp hinvLAK
    simpa only [graph] using contMDiffOn_const.sub hPinvLAK
  have hPdim : finrank 𝕜 P + k = finrank 𝕜 F := by
    rw [← hker x₀ hx₀]
    exact Submodule.finrank_add_eq_of_isCompl hKP.symm
  have hrange_dim (x : M) (hx : x ∈ W) :
      finrank 𝕜 (A x).range + k = finrank 𝕜 F := by
    rw [← hker x hx]
    exact (A x).toLinearMap.finrank_range_add_finrank_ker
  have hgraph_ker (x : M) (hx : x ∈ U) (v : K) : graph x v ∈ (A x).ker := by
    have hDi : (D x).IsInvertible := by
      let u : (P →L[𝕜] P)ˣ := IsUnit.unit hx.2
      refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
      exact hx.2.unit_spec
    have hAPinj : Function.Injective ((A x).domRestrict P) := by
      intro p q hpq
      apply hDi.injective
      simpa [D] using congr_arg L hpq
    have hrangeP_le : ((A x).domRestrict P).range ≤ (A x).range := by
      rintro y ⟨p, rfl⟩
      exact LinearMap.mem_range_self (A x).toLinearMap p
    have hrangeP_dim : finrank 𝕜 ((A x).domRestrict P).range = finrank 𝕜 P :=
      LinearMap.finrank_range_of_inj hAPinj
    have hrange_eq : ((A x).domRestrict P).range = (A x).range := by
      apply Submodule.eq_of_le_of_finrank_eq hrangeP_le
      rw [hrangeP_dim]
      exact Nat.add_right_cancel (hPdim.trans (hrange_dim x hx.1).symm)
    have hLzero : L (A x (graph x v)) = 0 := by
      simp only [graph, sub_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, ContinuousLinearMap.domRestrict_apply, map_sub]
      change L (A x v) - D x ((D x).inverse (L (A x v))) = 0
      rw [hDi.self_apply_inverse]
      exact sub_self _
    obtain ⟨p, hp⟩ : ∃ p : P, (A x).domRestrict P p = A x (graph x v) := by
      have : A x (graph x v) ∈ (A x).range := LinearMap.mem_range_self _ _
      rw [← hrange_eq] at this
      exact this
    have hDp : D x p = 0 := by
      rw [show D x p = L ((A x).domRestrict P p) by rfl, hp, hLzero]
    have : p = 0 := hDi.injective (hDp.trans (map_zero (D x)).symm)
    change A x (graph x v) = 0
    rw [← hp, this, map_zero]
  let b : Basis (Fin k) 𝕜 K := Module.finBasisOfFinrankEq 𝕜 K (hker x₀ hx₀)
  let s : Fin k → M → F := fun i x => graph x (b i)
  refine ⟨U, s, hU, hx₀U, inter_subset_left, ?_, ?_, ?_⟩
  · intro x hx
    apply LinearIndependent.of_comp (K.projectionOnto P hKP)
    have hsproj : (K.projectionOnto P hKP) ∘ (s · x) = b := by
      funext i
      simp [s, graph, Submodule.projectionOnto_apply_left hKP,
        Submodule.projectionOnto_apply_right hKP]
    rw [hsproj]
    exact b.linearIndependent
  · intro x hx
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact hgraph_ker x hx (b i)
    · rw [hker x hx.1]
      have hsli : LinearIndependent 𝕜 (s · x) := by
        apply LinearIndependent.of_comp (K.projectionOnto P hKP)
        have hsproj : (K.projectionOnto P hKP) ∘ (s · x) = b := by
          funext i
          simp [s, graph, Submodule.projectionOnto_apply_left hKP,
            Submodule.projectionOnto_apply_right hKP]
        rw [hsproj]
        exact b.linearIndependent
      simpa using finrank_span_eq_card hsli
  · intro i
    exact (hgraph.clm_apply contMDiffOn_const).congr fun x hx => rfl

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

theorem exists_kernel_frameOn
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)) W)
    (k : ℕ) (hker : ∀ x ∈ W, finrank 𝕜 (A x).ker = k)
    (x₀ : M) (hx₀ : x₀ ∈ W) :
    ∃ (U : Set M) (s : Fin k → (x : M) → V₁ x),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
        IsSubbundleFrameOn (I := I) (F := F₁) (n := n)
          (fun x => (A x).ker) s U := by
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
  have hker_a : ∀ x ∈ W', finrank 𝕜 (a x).ker = k := by
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
    have hker_eq : (a x).ker = Submodule.map ex₁.toLinearMap (A x).ker := by
      ext v
      constructor
      · intro hv
        rw [Submodule.mem_map]
        refine ⟨ex₁.symm v, ?_, ex₁.apply_symm_apply v⟩
        change A x (ex₁.symm v) = 0
        apply ex₂.injective
        simpa [ha_apply] using hv
      · rintro ⟨v, hv, rfl⟩
        change a x (ex₁ v) = 0
        rw [ha_apply]
        simpa using congr_arg ex₂ hv
    rw [hker_eq, LinearEquiv.finrank_map_eq, hker x hx.1]
  obtain ⟨U, t, hU, hx₀U, hUW', htli, htspan, ht⟩ :=
    exists_kernel_frame a W' hW' ha k hker_a x₀ hx₀W'
  let s : Fin k → (x : M) → V₁ x := fun i x => e₁.symmL 𝕜 x (t i x)
  refine ⟨U, s, hU, hx₀U, fun _ hx => (hUW' hx).1, ?_⟩
  have hUe₁ : U ⊆ e₁.baseSet := fun _ hx => (hUW' hx).2.1
  have hcoord_ker (x : M) (hx : x ∈ W') (v : F₁) :
      a x v = 0 ↔ A x (e₁.symmL 𝕜 x v) = 0 := by
    let ex₂ : V₂ x ≃ₗ[𝕜] F₂ := e₂.linearEquivAt (R := 𝕜) x hx.2.2
    have ha_apply : a x v = ex₂ (A x (e₁.symmL 𝕜 x v)) := by
      change (e₂.linearMapAt 𝕜 x) (A x (e₁.symmL 𝕜 x v)) =
        ex₂ (A x (e₁.symmL 𝕜 x v))
      dsimp only [ex₂]
      rw [e₂.linearMapAt_def_of_mem hx.2.2]
      change (e₂.linearEquivAt 𝕜 x hx.2.2) (A x (e₁.symmL 𝕜 x v)) = _
      rfl
    constructor
    · intro hv
      apply ex₂.injective
      simpa [ha_apply] using hv
    · intro hv
      rw [ha_apply]
      simpa using congr_arg ex₂ hv
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    let ex₁ : V₁ x ≃ₗ[𝕜] F₁ := e₁.linearEquivAt (R := 𝕜) x (hUe₁ hx)
    apply LinearIndependent.of_comp ex₁.toLinearMap
    have hs : (⇑ex₁.toLinearMap ∘ (s · x)) = (t · x) := by
      funext i
      change ex₁ (e₁.symmL 𝕜 x (t i x)) = t i x
      rw [e₁.symmL_apply (hUe₁ hx)]
      exact ex₁.apply_symm_apply (t i x)
    rw [hs]
    exact htli x hx
  · intro x hx
    let ex₁ : V₁ x ≃ₗ[𝕜] F₁ := e₁.linearEquivAt (R := 𝕜) x (hUe₁ hx)
    let _ : FiniteDimensional 𝕜 (V₁ x) :=
      FiniteDimensional.of_injective ex₁.toLinearMap ex₁.injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      change A x (s i x) = 0
      apply (hcoord_ker x (hUW' hx) (t i x)).mp
      have htmem : t i x ∈ (a x).ker := by
        rw [← htspan x hx]
        exact Submodule.subset_span (Set.mem_range_self i)
      exact htmem
    · rw [hker x (hUW' hx).1]
      have hsli : LinearIndependent 𝕜 (s · x) := by
        apply LinearIndependent.of_comp ex₁.toLinearMap
        have hs : (⇑ex₁.toLinearMap ∘ (s · x)) = (t · x) := by
          funext i
          change ex₁ (e₁.symmL 𝕜 x (t i x)) = t i x
          rw [e₁.symmL_apply (hUe₁ hx)]
          exact ex₁.apply_symm_apply (t i x)
        rw [hs]
        exact htli x hx
      simpa using finrank_span_eq_card hsli
  · intro i
    apply (e₁.contMDiffOn_section_iff hU hUe₁).mpr
    exact (ht i).congr fun x hx => by
      simp [s, e₁.symmL_apply, hUe₁ hx]

def kernel
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hker : ∀ x, finrank 𝕜 (A x).ker = k) :
    ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n) where
  fiber x := (A x).ker
  rank := k
  exists_isSubbundleFrameOn x₀ := by
    obtain ⟨U, s, hU, hx₀U, _, hs⟩ :=
      exists_kernel_frameOn A Set.univ isOpen_univ hA.contMDiffOn
        k (fun x _ => hker x) x₀ (Set.mem_univ x₀)
    exact ⟨U, s, hU, hx₀U, hs⟩

@[simp]
theorem kernel_fiber
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hker : ∀ x, finrank 𝕜 (A x).ker = k) (x : M) :
    (kernel A hA k hker).fiber x = (A x).ker :=
  rfl

@[simp]
theorem kernel_rank
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hker : ∀ x, finrank 𝕜 (A x).ker = k) :
    (kernel A hA k hker).rank = k :=
  rfl

end ContMDiffVectorSubbundle
