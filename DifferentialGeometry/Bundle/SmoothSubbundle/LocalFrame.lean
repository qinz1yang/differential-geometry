import DifferentialGeometry.Bundle.SmoothSubbundle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold Topology

section LeftInverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private theorem exists_contMDiffOn_leftInverse_of_comp_eq_id
    [CompleteSpace F] (A : M → F →L[𝕜] G)
    (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n A W)
    (x₀ : M) (hx₀ : x₀ ∈ W) (L : G →L[𝕜] F)
    (hL : L.comp (A x₀) = ContinuousLinearMap.id 𝕜 F) :
    ∃ (U : Set M) (B : M → G →L[𝕜] F),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      ContMDiffOn I 𝓘(𝕜, G →L[𝕜] F) n B U ∧
      ∀ x ∈ U, (B x).comp (A x) = ContinuousLinearMap.id 𝕜 F := by
  let D : M → F →L[𝕜] F := fun x => L.comp (A x)
  have hD : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] F) n D W :=
    contMDiffOn_const.clm_comp hA
  let U : Set M := W ∩ D ⁻¹' {T | IsUnit T}
  have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage hW Units.isOpen
  have hx₀U : x₀ ∈ U := by
    refine ⟨hx₀, ?_⟩
    change IsUnit (L.comp (A x₀))
    rw [hL]
    exact isUnit_one
  have hDi (x : M) (hx : x ∈ U) : (D x).IsInvertible := by
    let u : (F →L[𝕜] F)ˣ := IsUnit.unit hx.2
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    exact hx.2.unit_spec
  have hDinv : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] F) n
      (fun x => (D x).inverse) U := by
    intro x hx
    exact (hDi x hx).contDiffAt_map_inverse.comp_contMDiffWithinAt
      ((hD.mono inter_subset_left) x hx)
  refine ⟨U, fun x => (D x).inverse.comp L, hU, hx₀U, inter_subset_left,
    hDinv.clm_comp contMDiffOn_const, ?_⟩
  intro x hx
  ext v
  exact (hDi x hx).inverse_apply_self v

private theorem exists_contMDiffOn_leftInverse_of_injective
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G]
    (A : M → F →L[𝕜] G) (W : Set M) (hW : IsOpen W)
    (hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n A W)
    (x₀ : M) (hx₀ : x₀ ∈ W) (hAx₀ : Function.Injective (A x₀)) :
    ∃ (U : Set M) (B : M → G →L[𝕜] F),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      ContMDiffOn I 𝓘(𝕜, G →L[𝕜] F) n B U ∧
      ∀ x ∈ U, (B x).comp (A x) = ContinuousLinearMap.id 𝕜 F := by
  let _ : FiniteDimensional 𝕜 F :=
    FiniteDimensional.of_injective (A x₀).toLinearMap hAx₀
  let _ : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    (A x₀).toLinearMap (LinearMap.ker_eq_bot_of_injective hAx₀)
  exact exists_contMDiffOn_leftInverse_of_comp_eq_id A W hW hA x₀ hx₀
    L.toContinuousLinearMap (ContinuousLinearMap.ext fun v => LinearMap.congr_fun hL v)

private theorem exists_contMDiffOn_frame_leftInverse
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] {ι : Type*} [Fintype ι]
    (s : ι → M → G) (W : Set M) (hW : IsOpen W)
    (hs : ∀ i, ContMDiffOn I 𝓘(𝕜, G) n (s i) W)
    (x₀ : M) (hx₀ : x₀ ∈ W) (hsx₀ : LinearIndependent 𝕜 (s · x₀)) :
    ∃ (U : Set M) (B : M → G →L[𝕜] (ι → 𝕜)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      ContMDiffOn I 𝓘(𝕜, G →L[𝕜] (ι → 𝕜)) n B U ∧
      ∀ x ∈ U, ∀ c : ι → 𝕜, B x (∑ i, c i • s i x) = c := by
  classical
  let A : M → (ι → 𝕜) →L[𝕜] G := fun x =>
    (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := G) ι).symm (s · x)
  have hA_apply (x : M) (c : ι → 𝕜) : A x c = ∑ i, c i • s i x := by
    exact LinearEquiv.piRing_symm_apply 𝕜 (s · x) c
  have hA : ContMDiffOn I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] G) n A W := by
    exact (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := G) ι).symm.toContinuousLinearMap
      |>.contMDiff.comp_contMDiffOn (contMDiffOn_pi_space.mpr hs)
  have hAx₀ : Function.Injective (A x₀) := by
    intro c d hcd
    apply hsx₀.fintypeLinearCombination_injective
    simpa only [Fintype.linearCombination_apply, hA_apply] using hcd
  obtain ⟨U, B, hU, hx₀U, hUW, hB, hBA⟩ :=
    exists_contMDiffOn_leftInverse_of_injective A W hW hA x₀ hx₀ hAx₀
  refine ⟨U, B, hU, hx₀U, hUW, hB, ?_⟩
  intro x hx c
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hA_apply] using
    congrArg (fun T : (ι → 𝕜) →L[𝕜] (ι → 𝕜) => T c) (hBA x hx)

private theorem exists_contMDiffOn_frame_coeff
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] {ι : Type*} [Fintype ι]
    (s : ι → M → G) (W : Set M) (hW : IsOpen W)
    (hs : ∀ i, ContMDiffOn I 𝓘(𝕜, G) n (s i) W)
    (x₀ : M) (hx₀ : x₀ ∈ W) (hsx₀ : LinearIndependent 𝕜 (s · x₀))
    (σ : M → G) (hσ : ContMDiffOn I 𝓘(𝕜, G) n σ W)
    (hσmem : ∀ x ∈ W, σ x ∈ Submodule.span 𝕜 (Set.range (s · x))) :
    ∃ (U : Set M) (c : ι → M → 𝕜),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ i, ContMDiffOn I 𝓘(𝕜, 𝕜) n (c i) U) ∧
      ∀ x ∈ U, σ x = ∑ i, c i x • s i x := by
  obtain ⟨U, B, hU, hx₀U, hUW, hB, hBA⟩ :=
    exists_contMDiffOn_frame_leftInverse s W hW hs x₀ hx₀ hsx₀
  let c : ι → M → 𝕜 := fun i x => B x (σ x) i
  have hc : ∀ i, ContMDiffOn I 𝓘(𝕜, 𝕜) n (c i) U := by
    exact contMDiffOn_pi_space.mp (hB.clm_apply (hσ.mono hUW))
  refine ⟨U, c, hU, hx₀U, hUW, hc, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ : ∃ a : ι → 𝕜, ∑ i, a i • s i x = σ x := by
    have hmem := hσmem x (hUW hx)
    rw [← Fintype.range_linearCombination] at hmem
    exact hmem
  have hcoord : B x (σ x) = a := by
    rw [← ha]
    exact hBA x hx a
  simpa only [c, hcoord] using ha.symm

end LeftInverse

section Coefficients

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [FiniteDimensional 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [VectorBundle 𝕜 F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

theorem IsSubbundleFrameOn.exists_contMDiffOn_coeff
    {ι : Type*} [Fintype ι] {S : ∀ x, Submodule 𝕜 (V x)}
    {s : ι → (x : M) → V x} {W : Set M}
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    (hW : IsOpen W) {x₀ : M} (hx₀ : x₀ ∈ W)
    (σ : (x : M) → V x)
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (σ x)) W)
    (hσmem : ∀ x ∈ W, σ x ∈ S x) :
    ∃ (U : Set M) (c : ι → M → 𝕜),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ i, ContMDiffOn I 𝓘(𝕜, 𝕜) n (c i) U) ∧
      ∀ x ∈ U, σ x = ∑ i, c i x • s i x := by
  let e := trivializationAt F V x₀
  let W' : Set M := W ∩ e.baseSet
  have hW' : IsOpen W' := hW.inter e.open_baseSet
  have hx₀W' : x₀ ∈ W' := ⟨hx₀, mem_baseSet_trivializationAt F V x₀⟩
  let t : ι → M → F := fun i x => (e (TotalSpace.mk' F x (s i x))).2
  let τ : M → F := fun x => (e (TotalSpace.mk' F x (σ x))).2
  have ht : ∀ i, ContMDiffOn I 𝓘(𝕜, F) n (t i) W' := by
    intro i
    exact (e.contMDiffOn_section_iff hW' inter_subset_right).mp
      ((hs.contMDiffOn i).mono inter_subset_left)
  have hτ : ContMDiffOn I 𝓘(𝕜, F) n τ W' :=
    (e.contMDiffOn_section_iff hW' inter_subset_right).mp (hσ.mono inter_subset_left)
  have htx₀ : LinearIndependent 𝕜 (t · x₀) := by
    let ex : V x₀ ≃ₗ[𝕜] F := e.linearEquivAt 𝕜 x₀ hx₀W'.2
    exact (hs.linearIndependent hx₀).map' ex.toLinearMap
      (LinearMap.ker_eq_bot_of_injective ex.injective)
  have hτmem : ∀ x ∈ W', τ x ∈ Submodule.span 𝕜 (Set.range (t · x)) := by
    intro x hx
    have hmem := hσmem x hx.1
    rw [← hs.spans hx.1, ← Fintype.range_linearCombination] at hmem
    obtain ⟨a, ha⟩ := hmem
    rw [← Fintype.range_linearCombination]
    refine ⟨a, ?_⟩
    have heq := congrArg (e.linearMapAt 𝕜 x) ha
    simpa only [Fintype.linearCombination_apply, map_sum, map_smul,
      e.coe_linearMapAt_of_mem hx.2] using heq
  obtain ⟨U, c, hU, hx₀U, hUW', hc, hcoeff⟩ :=
    exists_contMDiffOn_frame_coeff t W' hW' ht x₀ hx₀W' htx₀ τ hτ hτmem
  refine ⟨U, c, hU, hx₀U, fun x hx => (hUW' hx).1, hc, ?_⟩
  intro x hx
  apply (e.linearEquivAt 𝕜 x (hUW' hx).2).injective
  simpa only [map_sum, map_smul, Trivialization.linearEquivAt_apply, τ, t] using hcoeff x hx

end Coefficients

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable {n : WithTop ℕ∞} {ι : Type*} {S : ∀ x, Submodule 𝕜 (V x)}
variable {s : ι → (x : M) → V x} {W : Set M}

namespace IsSubbundleFrameOn

def toBasisAt (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) : Module.Basis ι 𝕜 (S x) :=
  (Module.Basis.span (hs.linearIndependent hx)).map (LinearEquiv.ofEq _ _ (hs.spans hx))

@[simp]
theorem toBasisAt_apply (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) (i : ι) : (hs.toBasisAt hx i : V x) = s i x := by
  simp [toBasisAt]

def coeff (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    (i : ι) (x : M) : S x →ₗ[𝕜] 𝕜 := by
  classical
  exact if hx : x ∈ W then (hs.toBasisAt hx).coord i else 0

@[simp]
theorem coeff_apply_of_mem
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) (i : ι) (v : S x) :
    hs.coeff i x v = (hs.toBasisAt hx).repr v i := by
  simp [coeff, hx]

theorem coeff_sum_eq [Fintype ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) (v : S x) :
    (v : V x) = ∑ i, hs.coeff i x v • s i x := by
  have hsum := congrArg (fun v' : S x => (v' : V x)) ((hs.toBasisAt hx).sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, toBasisAt_apply,
    coeff_apply_of_mem hs hx] using hsum.symm

theorem coeff_eq_of_eq_sum [Fintype ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) (v : S x) (a : ι → 𝕜)
    (ha : (v : V x) = ∑ i, a i • s i x) :
    (fun i => hs.coeff i x v) = a := by
  apply (hs.linearIndependent hx).fintypeLinearCombination_injective
  exact (hs.coeff_sum_eq hx v).symm.trans ha

def subtypeSection (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    (i : ι) (x : M) : S x := by
  classical
  exact if hx : x ∈ W then ⟨s i x, hs.mem_fiber hx i⟩ else 0

@[simp]
theorem subtypeSection_coe_of_mem
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {x : M} (hx : x ∈ W) (i : ι) : (hs.subtypeSection i x : V x) = s i x := by
  simp [subtypeSection, hx]

theorem contMDiffOn_subtypeSection_coe
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (hs.subtypeSection i x : V x)) W := by
  apply (hs.contMDiffOn i).congr
  intro x hx
  simp [hs.subtypeSection_coe_of_mem hx]

theorem coeff_mono_apply
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {U : Set M} (hUW : U ⊆ W) {x : M} (hx : x ∈ U) (i : ι) (v : S x) :
    (hs.mono hUW).coeff i x v = hs.coeff i x v := by
  rw [coeff_apply_of_mem _ hx, coeff_apply_of_mem _ (hUW hx)]
  rfl

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]

theorem exists_contMDiffOn_coeff_extension [Fintype ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    (hW : IsOpen W) {x₀ : M} (hx₀ : x₀ ∈ W) :
    let e := trivializationAt F V x₀
    ∃ (U : Set M) (B : M → F →L[𝕜] (ι → 𝕜)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∩ e.baseSet ∧
      ContMDiffOn I 𝓘(𝕜, F →L[𝕜] (ι → 𝕜)) n B U ∧
      ∀ x ∈ U, ∀ v : S x,
        B x ((e (TotalSpace.mk' F x (v : V x))).2) = fun i => hs.coeff i x v := by
  let e := trivializationAt F V x₀
  let W' : Set M := W ∩ e.baseSet
  have hW' : IsOpen W' := hW.inter e.open_baseSet
  have hx₀W' : x₀ ∈ W' := ⟨hx₀, mem_baseSet_trivializationAt F V x₀⟩
  let t : ι → M → F := fun i x => (e (TotalSpace.mk' F x (s i x))).2
  have ht : ∀ i, ContMDiffOn I 𝓘(𝕜, F) n (t i) W' := by
    intro i
    exact (e.contMDiffOn_section_iff hW' inter_subset_right).mp
      ((hs.contMDiffOn i).mono inter_subset_left)
  have htx₀ : LinearIndependent 𝕜 (t · x₀) := by
    let ex : V x₀ ≃ₗ[𝕜] F := e.linearEquivAt 𝕜 x₀ hx₀W'.2
    exact (hs.linearIndependent hx₀).map' ex.toLinearMap
      (LinearMap.ker_eq_bot_of_injective ex.injective)
  obtain ⟨U, B, hU, hx₀U, hUW', hB, hBt⟩ :=
    exists_contMDiffOn_frame_leftInverse t W' hW' ht x₀ hx₀W' htx₀
  refine ⟨U, B, hU, hx₀U, hUW', hB, ?_⟩
  intro x hx v
  have heq := congrArg (e.linearMapAt 𝕜 x) (hs.coeff_sum_eq (hUW' hx).1 v)
  have hcoord : (e (TotalSpace.mk' F x (v : V x))).2 =
      ∑ i, hs.coeff i x v • t i x := by
    simpa only [map_sum, map_smul, e.coe_linearMapAt_of_mem (hUW' hx).2] using heq
  rw [hcoord]
  exact hBt x hx (fun i => hs.coeff i x v)

theorem contMDiffOn_coeff [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    (hW : IsOpen W) (σ : (x : M) → S x)
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (σ x : V x)) W) (i : ι) :
    ContMDiffOn I 𝓘(𝕜, 𝕜) n (fun x => hs.coeff i x (σ x)) W := by
  let _ : Fintype ι := Fintype.ofFinite ι
  intro x hx
  obtain ⟨U, c, hU, hx₀U, hUW, hc, hcoeff⟩ :=
    hs.exists_contMDiffOn_coeff hW hx (fun y => (σ y : V y)) hσ (fun y _ => (σ y).property)
  have heq : (fun y => hs.coeff i y (σ y)) =ᶠ[𝓝 x] c i := by
    filter_upwards [hU.mem_nhds hx₀U] with y hy
    exact congrFun (hs.coeff_eq_of_eq_sum (hUW hy) (σ y) (fun j => c j y) (hcoeff y hy)) i
  exact ((hc i).contMDiffAt (hU.mem_nhds hx₀U)).congr_of_eventuallyEq heq
    |>.contMDiffWithinAt

theorem contMDiffOn_coeff_of_subset [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {U : Set M} (hU : IsOpen U) (hUW : U ⊆ W) (σ : (x : M) → S x)
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (σ x : V x)) U) (i : ι) :
    ContMDiffOn I 𝓘(𝕜, 𝕜) n (fun x => hs.coeff i x (σ x)) U := by
  refine ((hs.mono hUW).contMDiffOn_coeff hU σ hσ i).congr ?_
  intro x hx
  exact (hs.coeff_mono_apply hUW hx i (σ x)).symm

end IsSubbundleFrameOn
