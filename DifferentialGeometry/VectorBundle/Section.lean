/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import DifferentialGeometry.VectorBundle.Equiv
import DifferentialGeometry.VectorBundle.Frame

/-!

# Sections of Vector Bundles

This file introduces notation for smooth sections and shows that they form a module
over the ring of smooth scalar-valued functions.

## Notation

* `Γ^n(V)` : the space of `C^n` sections of a `C^n` vector bundle with fiber family `V`.

## Main Results

* `ContMDiffSection.instSMulContMDiffMap` : smooth scalar functions act on smooth sections
  by pointwise multiplication.
* `ContMDiffSection.instModuleContMDiffMap` : smooth sections of a vector bundle over `M`
  form a module over `C^n(M, 𝕜)`.

## Tags

section, vector bundle, smooth section, module, smooth functions

## Future generalization to `𝕜 : RCLike`

The VBC lemma is hard-coded to `ℝ` but mathematically holds for any `𝕜 : RCLike`
on the fibers with an ℝ-smooth base. Blockers, in order:

1. **`ContMDiffVectorBundleHom` ties the fiber field to `IB`'s base field**
   (see `Equiv.lean`). Until this is decoupled, the generalized lemma cannot
   even be stated. Foundational blocker.
2. **No `Module C^n(I,M;𝕜) Cₛ^n(I;F,V)` instance for the mixed setup.** Needs a
   mixed `ContMDiff.smul_section` — mathlib's proof template works if the
   trivialization linearity witness is taken from `[VectorBundle 𝕜 F V]` instead
   of the base field's.
3. **Local frame step:** `Module.finBasis ℝ F₁` / `Trivialization.localFrame` are
   tied to `I`'s base field. Workaround: build the `𝕜`-frame by hand via
   `e.linearEquivAt 𝕜` and feed smoothness directly to the non-frame version of
   `exists_contMDiffSection_eqOn_nhd` in `Frame.lean` — this is the step that
   helper was designed to unblock.
4. **Bump-function multiplication:** cast real bumps via `RCLike.ofReal`.
5. **`ofLinearMapSection` smoothness argument:** mechanical `ℝ → 𝕜` substitution.

Recommended order: do (1) as a standalone change to `Equiv.lean` first, then
(2)-(5) can land together in this file.
-/

set_option autoImplicit false

open scoped Manifold ContDiff
open Bundle

/-! ## Module over smooth functions -/

section ModuleOverSmoothFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

namespace ContMDiffSection

/-- Smooth scalar-valued functions act on smooth sections by pointwise scalar multiplication. -/
instance instSMulContMDiffMap : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s => ⟨fun x => f x • s x, f.2.smul_section s.contMDiff⟩⟩

@[simp]
theorem coe_smulContMDiffMap (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    ⇑(f • s) = fun x => f x • s x :=
  rfl

/-- Smooth sections of a vector bundle over `M` form a module over the ring of smooth
scalar-valued functions `C^n(M, 𝕜)`. -/
instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := by ext x; exact one_smul 𝕜 (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul 𝕜 (s x)

end ContMDiffSection

end ModuleOverSmoothFunctions

/-! ## Induced map on sections from a bundle map -/

section MapSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace ContMDiffVectorBundleHom

/-- A smooth vector bundle map `Φ : E₁ → E₂` covering the identity induces a
`C^n(M, 𝕜)`-linear map on smooth sections `Γ(E₁) → Γ(E₂)` by `σ ↦ Φ ∘ σ`. -/
noncomputable def mapSection
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; F₂, E₂⟯ := by
  obtain ⟨baseMap, toFun, hc, φ, compat⟩ := Φ
  subst hΦ
  exact
  { toFun := fun σ =>
      ⟨fun x => φ x (σ x), (hc.comp σ.contMDiff).congr fun x => (compat x (σ x)).symm⟩
    map_add' := fun σ τ => by ext x; exact (φ x).map_add (σ x) (τ x)
    map_smul' := fun f σ => by ext x; exact (φ x).map_smul (f x) (σ x) }

/-- `mapSection` relates to `toFun` via: `Φ.toFun ⟨x, σ x⟩ = ⟨x, (mapSection hΦ σ) x⟩`.
This is the key bridge between the total-space and section-space views. -/
theorem mapSection_apply :
    ∀ (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M),
    Φ.toFun ⟨x, σ x⟩ = ⟨x, (Φ.mapSection hΦ σ) x⟩
  | ⟨_, _, _, _, compat⟩, rfl, σ, x => compat x (σ x)

/-- A smooth vector bundle homomorphism is tensorial: its fiberwise action on sections
respects scalar multiplication and addition at each point. -/
theorem tensorialAt
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂) (x : M) :
    TensorialAt I F₁ (fun σ => Φ.fiberLinearMap x (σ x)) x :=
  ⟨fun _ _ => map_smul (Φ.fiberLinearMap x) _ _,
   fun _ _ => map_add (Φ.fiberLinearMap x) _ _⟩

end ContMDiffVectorBundleHom

/-! ## Auxiliary lemmas for sections -/

section SectionAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Evaluating a finite sum of smooth sections at a point equals the sum of pointwise values. -/
theorem ContMDiffSection.finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    (∑ i ∈ s, f i : Cₛ^n⟮I; F, V⟯) x = ∑ i ∈ s, f i x := by
  change (ContMDiffSection.coeAddHom I F (↑n) V (∑ i ∈ s, f i)) x = _
  rw [map_sum]; simp [ContMDiffSection.coeAddHom_apply, Finset.sum_apply]

/-- For any point `p` and fiber vector `v`, there exists a smooth global section with value
`v` at `p`. Constructed by writing `v` in a local frame and extending via bump functions. -/
theorem ContMDiffSection.exists_eq_at
    [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I]
    (p : M) (v : V p) : ∃ (σ : Cₛ^n⟮I; F, V⟯), σ p = v := by
  let e := trivializationAt F V p
  let b := Module.finBasis ℝ F
  have he : p ∈ e.baseSet := mem_baseSet_trivializationAt F V p
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑n) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  refine ⟨∑ i, ((hframe.toBasisAt he).repr v i) • s' i, ?_⟩
  rw [ContMDiffSection.finset_sum_apply]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  simp_rw [hs'.self_of_nhds, ← hframe.toBasisAt_coe he]
  exact (hframe.toBasisAt he).sum_repr v

end SectionAux

/-! ## Vector Bundle Characterization Lemma

**Statement.** Let `E₁`, `E₂` be smooth vector bundles over a smooth manifold `M`.
A map `F : Γ(E₁) → Γ(E₂)` is `C^n(M)`-linear if and only if there exists a smooth
vector bundle map `Φ : E₁ → E₂` covering the identity such that `F(σ) = Φ ∘ σ`.

**Proof sketch.**
The forward direction is `ContMDiffVectorBundleHom.mapSection`. For the converse,
suppose `F : Γ(E₁) → Γ(E₂)` is `C^n(M)`-linear.

1. *F acts locally*: If `σ₁ = σ₂` on an open set `U ⊆ M`, then `F(σ₁) = F(σ₂)` on `U`.
   Let `τ = σ₁ - σ₂`. For `p ∈ U`, choose a smooth bump `ψ` supported in `U` with `ψ(p) = 1`.
   Then `ψ • τ = 0` globally, so `ψ · F(τ) = F(ψ • τ) = 0`, giving `F(τ)(p) = 0`.

2. *F acts pointwise*: If `σ₁(p) = σ₂(p)` then `F(σ₁)(p) = F(σ₂)(p)`.
   Write `τ = σ₁ - σ₂` with `τ(p) = 0`. Using a local frame `(σ₁, …, σₖ)` for `E₁` near `p`,
   write `τ = ∑ uⁱ • σᵢ` with `uⁱ(p) = 0`. Extend to global sections via bump functions;
   then `F(τ)(p) = ∑ uⁱ(p) · F(σᵢ')(p) = 0`.

3. *Define the bundle map*: For `⟨p, v⟩ ∈ E₁`, set `Φ(p, v) = F(v')(p)` where `v'` is any
   global section with `v'(p) = v`. By step 2 this is well-defined, covers the identity,
   and is fiberwise linear (since `F` is linear).

4. *Smoothness*: In local frames `(σᵢ)` for `E₁` and `(τⱼ)` for `E₂` over a neighborhood
   of `p`, the bundle map is represented by the smooth matrix `Aⱼⁱ` where
   `F(σᵢ') = ∑ⱼ Aⱼⁱ • τⱼ`, giving `Φ(q, v) = ∑ᵢⱼ vⁱ Aⱼⁱ(q) τⱼ(q)`. -/

/-! ### Helper lemmas: F acts locally and pointwise -/

section ActsHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [ContMDiffVectorBundle n F₁ E₁ I]

omit [FiniteDimensional ℝ F₁] [ContMDiffVectorBundle n F₁ E₁ I] h1n in
/-- A `C^n(M,ℝ)`-linear map `F` on sections is local: if `σ` vanishes on an open set `U`,
then `F σ` vanishes on `U`. -/
theorem ContMDiffVectorBundleHom.linearMap_acts_locally
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ : Cₛ^n⟮I; F₁, E₁⟯) {U : Set M} (hU : IsOpen U)
    (hσU : ∀ x ∈ U, σ x = 0) : ∀ p ∈ U, (F σ) p = 0 := by
  intro p hp
  obtain ⟨ψ, -, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hU.mem_nhds hp)
  let ψ' : C^n⟮I, M; ℝ⟯ :=
    ⟨ψ, ψ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  have hψσ : ψ' • σ = 0 := by
    ext x
    simp only [ContMDiffSection.coe_smulContMDiffMap, Pi.zero_apply, ContMDiffSection.coe_zero]
    by_cases hx : x ∈ Function.support (ψ : M → ℝ)
    · exact smul_eq_zero_of_right _ (hσU x (hψsupp (subset_closure hx)))
    · simp only [Function.mem_support, not_not] at hx
      exact smul_eq_zero_of_left hx _
  have key : ψ' • F σ = 0 := by rw [← F.map_smul, hψσ, map_zero]
  have := DFunLike.congr_fun key p
  simp only [ContMDiffSection.coe_smulContMDiffMap, ContMDiffSection.coe_zero,
    Pi.zero_apply] at this
  rwa [show (ψ' p : ℝ) = 1 from ψ.eq_one, one_smul] at this

/-- A `C^n(M,ℝ)`-linear map `F` on sections is pointwise: if `σ₁(p) = σ₂(p)` then
`F(σ₁)(p) = F(σ₂)(p)`. -/
theorem ContMDiffVectorBundleHom.linearMap_acts_pointwise
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ₁ σ₂ : Cₛ^n⟮I; F₁, E₁⟯) (p : M) (hσ : σ₁ p = σ₂ p) :
    (F σ₁) p = (F σ₂) p := by
  -- Derive C^1 vector bundle structure from C^n via monotonicity
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  suffices h : ∀ (τ : Cₛ^n⟮I; F₁, E₁⟯), τ p = 0 → (F τ) p = 0 by
    have h₁ := h (σ₁ - σ₂) (by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact hσ)
    simp only [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
    exact h₁
  intro τ hτ
  let e := trivializationAt F₁ E₁ p
  let b := Module.finBasis ℝ F₁
  have he : p ∈ e.baseSet := mem_baseSet_trivializationAt F₁ E₁ p
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑n) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  obtain ⟨χ, -, hχsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
    (e.open_baseSet.mem_nhds he)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(ℝ) (↑n)
      (fun x => χ x • hframe.coeff i x (τ x)) := by
    intro i
    have hsmooth_lfc : ContMDiff I 𝓘(ℝ) (↑n)
        (fun x => χ x • e.localFrame_coeff I b i x (τ x)) := by
      intro x
      by_cases hx : x ∈ tsupport (χ : M → ℝ)
      · exact (χ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.smul
          (contMDiffAt_localFrame_coeff b (hχsupp hx) τ.contMDiff.contMDiffAt i)
      · have hχ_zero : ∀ᶠ y in nhds x, (χ : M → ℝ) y = 0 := by
          apply Filter.Eventually.mono
            ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hx)
          intro y hy
          exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
        exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          (hχ_zero.mono fun y hy => by simp [hy])
    refine hsmooth_lfc.congr fun x => ?_
    by_cases hx : x ∈ e.baseSet
    · have hbasis : e.basisAt b hx = hframe.toBasisAt hx := by
        ext j; simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame,
          Trivialization.basisAt, hx]
      simp only [hframe.coeff_apply_of_mem hx,
        e.localFrame_coeff_apply_of_mem_baseSet b hx, hbasis]
    · simp [hframe.coeff_apply_of_notMem hx,
        e.localFrame_coeff_apply_of_notMem_baseSet b hx]
  let u' : Fin (Module.finrank ℝ F₁) → C^n⟮I, M; ℝ⟯ := fun i =>
    ⟨fun x => χ x • hframe.coeff i x (τ x), hcoeff_smooth i⟩
  have hu'_zero : ∀ i, (u' i) p = 0 := by
    intro i; change χ p • hframe.coeff i p (τ p) = 0
    rw [χ.eq_one, one_smul, hτ, map_zero]
  have hτ_eq_near : ∀ᶠ x in nhds p, τ x = ∑ i, (u' i) x • (s' i) x := by
    filter_upwards [hs', χ.eventuallyEq_one,
      e.open_baseSet.mem_nhds he] with x hs'x hχx hx
    change τ x = ∑ i, (χ x • hframe.coeff i x (τ x)) • (s' i) x
    simp only [show χ x = (1 : M → ℝ) x from hχx, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq (⇑τ) hx]
    congr 1; ext i; rw [hs'x i]
  obtain ⟨W, hW_open, hpW, hW_vanish⟩ : ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, (τ - ∑ i, u' i • s' i) x = 0 := by
    obtain ⟨W, hW_nhds, hW⟩ := Filter.Eventually.exists_mem hτ_eq_near
    obtain ⟨W', hW'W, hW'_open, hpW'⟩ := mem_nhds_iff.mp hW_nhds
    exact ⟨W', hW'_open, hpW', fun x hx => by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero,
        ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      exact hW x (hW'W hx)⟩
  have h_local := linearMap_acts_locally F (τ - ∑ i, u' i • s' i) hW_open hW_vanish p hpW
  rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h_local
  rw [h_local, map_sum]
  simp_rw [F.map_smul]
  rw [ContMDiffSection.finset_sum_apply]
  simp only [ContMDiffSection.coe_smulContMDiffMap]
  exact Finset.sum_eq_zero fun i _ => by rw [hu'_zero i, zero_smul]

end ActsHelpers

section VBC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]

/-- **Vector Bundle Characterization Lemma.** Every `C^n(M, ℝ)`-linear map between spaces
of smooth sections is induced by a smooth vector bundle homomorphism covering the identity. -/
noncomputable def ContMDiffVectorBundleHom.ofLinearMapSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  -- Derive C^1 structures from C^n via monotonicity
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  -- Use the extracted helper lemma acts_pointwise
  have acts_pointwise := ContMDiffVectorBundleHom.linearMap_acts_pointwise F
  -- ===== Existence of global sections with prescribed value =====
  have exists_section : ∀ (p : M) (v : E₁ p),
      ∃ (σ : Cₛ^n⟮I; F₁, E₁⟯), σ p = v := ContMDiffSection.exists_eq_at
  -- ===== Step 3: Define the fiberwise linear map =====
  -- φ(x)(v) := F(σ')(x) where σ' is any global section with σ'(x) = v.
  -- Well-defined by acts_pointwise, linear because F is linear.
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => (F (exists_section x v).choose) x
      map_add' := fun v w => by
        -- φ(v+w) = F(choose(v+w))(x) = F(choose(v) + choose(w))(x)
        --        = F(choose(v))(x) + F(choose(w))(x) = φ(v) + φ(w)
        let σ_v := (exists_section x v).choose
        let σ_w := (exists_section x w).choose
        let σ_vw := (exists_section x (v + w)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have hw : σ_w x = w := (exists_section x w).choose_spec
        have h_add : (σ_v + σ_w) x = v + w := by
          simp [ContMDiffSection.coe_add, Pi.add_apply, hv, hw]
        calc (F σ_vw) x
            = (F (σ_v + σ_w)) x := acts_pointwise σ_vw (σ_v + σ_w) x
                ((exists_section x (v + w)).choose_spec ▸ h_add ▸ rfl)
          _ = (F σ_v) x + (F σ_w) x := by
                rw [map_add, ContMDiffSection.coe_add, Pi.add_apply]
      map_smul' := fun c v => by
        -- φ(c•v) = F(choose(c•v))(x) = F(c • choose(v))(x) = c • F(choose(v))(x)
        let σ_v := (exists_section x v).choose
        let σ_cv := (exists_section x (c • v)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have h_smul : (c • σ_v) x = c • v := by
          simp [ContMDiffSection.coe_smul, Pi.smul_apply, hv]
        -- Wrap c as a constant smooth function
        let c' : C^n⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
        have hc_eq : c • σ_v = c' • σ_v := by
          ext y; simp [ContMDiffSection.coe_smulContMDiffMap, ContMDiffSection.coe_smul, c']
        calc (F σ_cv) x
            = (F (c • σ_v)) x := acts_pointwise σ_cv (c • σ_v) x
                ((exists_section x (c • v)).choose_spec ▸ h_smul ▸ rfl)
          _ = c • (F σ_v) x := by
                rw [hc_eq, F.map_smul, ContMDiffSection.coe_smulContMDiffMap]; rfl }
  -- φ agrees with F on sections: φ(x)(σ(x)) = F(σ)(x)
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = (F σ) x :=
    fun σ x => acts_pointwise _ σ x (exists_section x (σ x)).choose_spec
  -- ===== Step 4: The total space map is smooth =====
  -- In local frames (σᵢ) for E₁ and (τⱼ) for E₂, the map is represented by the
  -- smooth matrix Aⱼⁱ where F(σᵢ') = ∑ⱼ Aⱼⁱ • τⱼ.
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by
    -- Suffices to show ContMDiffAt at each point p₀ of the total space
    intro p₀
    -- Decompose into base + fiber via contMDiffAt_totalSpace
    rw [contMDiffAt_totalSpace]
    refine ⟨?_, ?_⟩
    · -- Base component: fun p => p.proj is smooth (just projection)
      exact (contMDiff_proj E₁).contMDiffAt
    · -- Fiber component: show smoothness of the trivialized fiber map
      let e₁ := trivializationAt F₁ E₁ p₀.proj
      let e₂ := trivializationAt F₂ E₂ p₀.proj
      let b₁ := Module.finBasis ℝ F₁
      have he₁ : p₀.proj ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
      have he₂ : p₀.proj ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
      have hframe₁ := e₁.isLocalFrameOn_localFrame_baseSet I (↑n) b₁
      obtain ⟨σ', hσ'⟩ := hframe₁.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
      -- Near p₀: (e₂ ⟨q, φ(q)(v)⟩).2 = ∑ᵢ b₁.repr((e₁ ⟨q,v⟩).2) i • (e₂ ⟨q, F(σᵢ')(q)⟩).2
      have hφ_eq : ∀ᶠ x in nhds p₀,
          (e₂ ⟨x.proj, φ x.proj x.2⟩).2 =
          ∑ i, b₁.repr (e₁ x).2 i •
            (e₂ ⟨x.proj, (F (σ' i)) x.proj⟩).2 := by
        -- Need: q ∈ e₁.baseSet ∩ e₂.baseSet and σ'ᵢ(q) = localFrame b₁ i q
        have h_base : ∀ᶠ x in nhds p₀,
            x.proj ∈ e₁.baseSet ∧ x.proj ∈ e₂.baseSet :=
          (e₁.open_baseSet.inter e₂.open_baseSet).preimage
            (FiberBundle.continuous_proj F₁ E₁) |>.mem_nhds ⟨he₁, he₂⟩
        have h_σ'_pull : ∀ᶠ x in nhds p₀,
            ∀ i, (σ' i) x.proj = e₁.localFrame b₁ i x.proj := by
          have := hσ'.mono (fun q hq => hq)
          exact this.filter_mono
            ((FiberBundle.continuous_proj F₁ E₁).continuousAt)
        filter_upwards [h_base, h_σ'_pull] with ⟨q, v⟩ ⟨hq₁, hq₂⟩ hσ'q
        let le₁ := e₁.linearEquivAt ℝ q hq₁
        let le₂ := e₂.linearEquivAt ℝ q hq₂
        -- v = ∑ᵢ b₁.repr(le₁ v)(i) • le₁⁻¹(bᵢ), so φ(q)(v) = ∑ᵢ ... • F(σ'ᵢ)(q)
        have hv_decomp : v = ∑ i, b₁.repr (le₁ v) i • le₁.symm (b₁ i) := by
          calc v = le₁.symm (le₁ v) := (le₁.symm_apply_apply v).symm
            _ = le₁.symm (∑ i, b₁.repr (le₁ v) i • b₁ i) := by rw [b₁.sum_repr]
            _ = _ := by rw [map_sum]; congr 1; ext j; rw [LinearEquiv.map_smul]
        have hφv : φ q v = ∑ i, b₁.repr (le₁ v) i • (F (σ' i)) q := by
          conv_lhs => rw [hv_decomp]
          simp only [map_sum, LinearMap.map_smul]
          congr 1; ext j; congr 1
          rw [show le₁.symm (b₁ j) = e₁.localFrame b₁ j q from by
            simp [Trivialization.localFrame, hq₁, Trivialization.basisAt, le₁]]
          rw [← hσ'q j]; exact φ_spec (σ' j) q
        rw [hφv]
        simp only [show ∀ w : E₂ q, (e₂ ⟨q, w⟩).2 = le₂ w from fun _ => rfl]
        rw [map_sum]; simp only [map_smul]; rfl
      -- Step 2: The smooth function is ContMDiffAt
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hφ_eq
      apply ContMDiffAt.sum
      intro i _
      apply ContMDiffAt.smul
      · -- b₁.repr((e₁ x).2) i is smooth: linear map composed with smooth trivialization
        -- (e₁ x).2 is smooth on the total space (fiber component of id in trivialization)
        have h_e₁_snd : ContMDiffAt (I.prod 𝓘(ℝ, F₁)) 𝓘(ℝ, F₁) (↑n)
            (fun x => (e₁ x).2) p₀ :=
          (contMDiffAt_totalSpace (f := _root_.id)).mp contMDiffAt_id |>.2
        -- b₁.repr (·) i is a continuous linear map F₁ → ℝ, hence smooth
        -- Compose: x ↦ (e₁ x).2 ↦ b₁.repr((e₁ x).2) i
        have hcl : ContDiff ℝ (↑n) (fun w : F₁ => b₁.repr w i) :=
          (ContinuousLinearMap.proj i |>.comp
            b₁.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
        exact hcl.contDiffAt.contMDiffAt.comp _ h_e₁_snd
      · -- (e₂ ⟨q, F(σᵢ')(q)⟩).2 is smooth in (q,v): it only depends on q,
        -- and F(σᵢ') is a smooth section
        -- F(σ'ᵢ) is a smooth section, so (e₂ ⟨q, F(σ'ᵢ)(q)⟩).2 is smooth in q
        have h_sect : ContMDiffAt I 𝓘(ℝ, F₂) (↑n)
            (fun q => (e₂ ⟨q, (F (σ' i)) q⟩).2) p₀.proj :=
          (contMDiffAt_section p₀.proj).mp (F (σ' i)).contMDiff.contMDiffAt
        -- Compose with the projection x ↦ x.proj (smooth on total space)
        exact h_sect.comp _ (contMDiff_proj E₁).contMDiffAt
  -- ===== Package everything =====
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩

/-- The bundle hom constructed by `ofLinearMapSection` covers the identity. -/
theorem ContMDiffVectorBundleHom.ofLinearMapSection_baseMap
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    (ofLinearMapSection F).baseMap = _root_.id := rfl

/-- The bundle hom constructed by `ofLinearMapSection` represents `F` on sections:
`F σ = (ofLinearMapSection F).mapSection ... σ`. The proof uses `acts_pointwise`:
`(ofLinearMapSection F).fiberLinearMap x v = F(choose v)(x)`, and since `choose(σ x)`
agrees with `σ` at `x`, the result follows from `acts_pointwise`. -/
theorem ContMDiffVectorBundleHom.ofLinearMapSection_spec
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) (σ) :
    F σ = (ofLinearMapSection F).mapSection (ofLinearMapSection_baseMap F) σ := by
  ext x
  -- (ofLinearMapSection F).mapSection σ x = (φ x) (σ x)
  -- = F(choose(σ x))(x) by definition of ofLinearMapSection
  -- = F(σ)(x) by acts_pointwise, since choose(σ x) and σ agree at x
  exact (linearMap_acts_pointwise F σ _ x
    (ContMDiffSection.exists_eq_at x (σ x)).choose_spec.symm)

omit h1n in
/-- `mapSection` followed by the characterization lemma recovers the original bundle map
on each fiber: if `Φ` and `Ψ` both cover the identity and induce the same map on sections,
then they agree fiberwise. -/
theorem ContMDiffVectorBundleHom.ofLinearMapSection_mapSection
    (Φ Ψ : ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (hΨ : Ψ.baseMap = _root_.id)
    (h_eq : ∀ σ, Φ.mapSection hΦ σ = Ψ.mapSection hΨ σ) :
    Φ.toFun = Ψ.toFun := by
  -- Suffices to show Φ.toFun p = Ψ.toFun p for all p
  -- Use: Φ.toFun ⟨x,v⟩ = ⟨id x, φ x v⟩ and (mapSection σ)(x) = φ x (σ x) after subst
  -- So for σ with σ(x) = v: Φ.toFun ⟨x,v⟩ = ⟨x, (mapSection σ)(x)⟩ = ⟨x, (Ψ.mapSection σ)(x)⟩ = Ψ.toFun ⟨x,v⟩
  funext ⟨x, v⟩
  obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (n := n) x v
  rw [Φ.mapSection_apply hΦ, Ψ.mapSection_apply hΨ, h_eq]

/-- **Corollary.** A `C^n(M, ℝ)`-linear equivalence between spaces of smooth sections
is induced by a smooth vector bundle equivalence covering the identity. -/
noncomputable def ContMDiffVectorBundleEquiv.ofLinearEquivSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ ≃ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleEquiv ℝ I n F₁ E₁ F₂ E₂ := by
  -- Extract the bundle hom covering the identity from the characterization lemma
  let Φ := ContMDiffVectorBundleHom.ofLinearMapSection F.toLinearMap
  let hΦ : Φ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.toLinearMap
  have hΦ_spec : ∀ σ, F σ = Φ.mapSection hΦ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.toLinearMap
  let Ψ := ContMDiffVectorBundleHom.ofLinearMapSection F.symm.toLinearMap
  let hΨ : Ψ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.symm.toLinearMap
  have hΨ_spec : ∀ σ, F.symm σ = Ψ.mapSection hΨ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.symm.toLinearMap
  -- Φ and Ψ are mutual inverses on the total space
  have hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (n := n) x v
    rw [Φ.mapSection_apply hΦ, Ψ.mapSection_apply hΨ (Φ.mapSection hΦ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Ψ.mapSection hΨ (Φ.mapSection hΦ σ) = σ from by
        rw [← hΨ_spec, ← hΦ_spec]; simp) x
  have hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₂) (n := n) x v
    rw [Ψ.mapSection_apply hΨ, Φ.mapSection_apply hΦ (Ψ.mapSection hΨ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Φ.mapSection hΦ (Ψ.mapSection hΨ σ) = σ from by
        rw [← hΦ_spec, ← hΨ_spec]; simp) x
  exact ContMDiffVectorBundleEquiv.ofMutualInverseHoms Φ Ψ hΦ hΨΦ hΦΨ

open FiberBundle in
/-- A tensorial operation on sections that preserves smoothness induces a smooth vector bundle
homomorphism covering the identity. This is the converse of `tensorialAt`: given
`Ψ : (Π x, E₁ x) → (Π x, E₂ x)` that is tensorial at every point and maps smooth sections
to smooth sections, we construct a `ContMDiffVectorBundleHom`.

The fiberwise linear map is constructed via `TensorialAt.pointwise`: since the operation is
tensorial, it depends only on the pointwise value of the section, not its germ. Smoothness of
the total-space map follows from the local frame decomposition. -/
noncomputable def ContMDiffVectorBundleHom.ofTensorialAt
    (Ψ : (Π x : M, E₁ x) → (Π x : M, E₂ x))
    (hΨ : ∀ x, TensorialAt I F₁ (fun σ => Ψ σ x) x)
    (hΨ_smooth : ∀ σ : Cₛ^n⟮I; F₁, E₁⟯,
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) n (T% (Ψ ⇑σ))) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  -- Derive C^1 structures from C^n via monotonicity
  have h1n' : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1n.out
  have hn_ne : (↑n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le h1n').ne'
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I := ContMDiffVectorBundle.of_le h1n'
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I := ContMDiffVectorBundle.of_le h1n'
  -- ===== Step 1: Define the fiberwise linear map via tensoriality =====
  -- φ(x)(v) := Ψ(extend F₁ v)(x). Linear by TensorialAt + pointwise.
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => Ψ (extend F₁ v) x
      map_add' := fun v₁ v₂ => by
        rw [← (hΨ x).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
            (mdifferentiableAt_extend ..)) (by simp)
      map_smul' := fun c v => by
        dsimp
        rw [← (hΨ x).smul (f := fun _ => c) (mdifferentiable_const ..)
          (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)) (by simp) }
  -- φ agrees with Ψ on smooth sections: φ(x)(σ(x)) = Ψ(σ)(x)
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = Ψ (⇑σ) x :=
    fun σ x => (hΨ x).pointwise (mdifferentiableAt_extend ..)
      (σ.contMDiff.contMDiffAt.mdifferentiableAt hn_ne) (by simp)
  -- ===== Step 2: The total space map is smooth =====
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by
    intro p₀
    rw [contMDiffAt_totalSpace]
    refine ⟨(contMDiff_proj E₁).contMDiffAt, ?_⟩
    let e₁ := trivializationAt F₁ E₁ p₀.proj
    let e₂ := trivializationAt F₂ E₂ p₀.proj
    let b₁ := Module.finBasis ℝ F₁
    have he₁ : p₀.proj ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
    have he₂ : p₀.proj ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
    have hframe₁ := e₁.isLocalFrameOn_localFrame_baseSet I (↑n) b₁
    obtain ⟨σ', hσ'⟩ := hframe₁.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    -- Near p₀: (e₂ ⟨q, φ(q)(v)⟩).2 = ∑ᵢ b₁.repr((e₁ ⟨q,v⟩).2) i • (e₂ ⟨q, Ψ(σᵢ')(q)⟩).2
    have hφ_eq : ∀ᶠ x in nhds p₀,
        (e₂ ⟨x.proj, φ x.proj x.2⟩).2 =
        ∑ i, b₁.repr (e₁ x).2 i •
          (e₂ ⟨x.proj, Ψ (⇑(σ' i)) x.proj⟩).2 := by
      have h_base : ∀ᶠ x in nhds p₀,
          x.proj ∈ e₁.baseSet ∧ x.proj ∈ e₂.baseSet :=
        (e₁.open_baseSet.inter e₂.open_baseSet).preimage
          (FiberBundle.continuous_proj F₁ E₁) |>.mem_nhds ⟨he₁, he₂⟩
      have h_σ'_pull : ∀ᶠ x in nhds p₀,
          ∀ i, (σ' i) x.proj = e₁.localFrame b₁ i x.proj := by
        have := hσ'.mono (fun q hq => hq)
        exact this.filter_mono ((FiberBundle.continuous_proj F₁ E₁).continuousAt)
      filter_upwards [h_base, h_σ'_pull] with ⟨q, v⟩ ⟨hq₁, hq₂⟩ hσ'q
      let le₁ := e₁.linearEquivAt ℝ q hq₁
      let le₂ := e₂.linearEquivAt ℝ q hq₂
      have hv_decomp : v = ∑ i, b₁.repr (le₁ v) i • le₁.symm (b₁ i) := by
        calc v = le₁.symm (le₁ v) := (le₁.symm_apply_apply v).symm
          _ = le₁.symm (∑ i, b₁.repr (le₁ v) i • b₁ i) := by rw [b₁.sum_repr]
          _ = _ := by rw [map_sum]; congr 1; ext j; rw [LinearEquiv.map_smul]
      have hφv : φ q v = ∑ i, b₁.repr (le₁ v) i • Ψ (⇑(σ' i)) q := by
        conv_lhs => rw [hv_decomp]
        simp only [map_sum, LinearMap.map_smul]
        congr 1; ext j; congr 1
        rw [show le₁.symm (b₁ j) = e₁.localFrame b₁ j q from by
          simp [Trivialization.localFrame, hq₁, Trivialization.basisAt, le₁]]
        rw [← hσ'q j]; exact φ_spec (σ' j) q
      rw [hφv]
      simp only [show ∀ w : E₂ q, (e₂ ⟨q, w⟩).2 = le₂ w from fun _ => rfl]
      rw [map_sum]; simp only [map_smul]; rfl
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hφ_eq
    apply ContMDiffAt.sum
    intro i _
    apply ContMDiffAt.smul
    · have h_e₁_snd : ContMDiffAt (I.prod 𝓘(ℝ, F₁)) 𝓘(ℝ, F₁) (↑n)
          (fun x => (e₁ x).2) p₀ :=
        (contMDiffAt_totalSpace (f := _root_.id)).mp contMDiffAt_id |>.2
      have hcl : ContDiff ℝ (↑n) (fun w : F₁ => b₁.repr w i) :=
        (ContinuousLinearMap.proj i |>.comp
          b₁.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
      exact hcl.contDiffAt.contMDiffAt.comp _ h_e₁_snd
    · have h_sect : ContMDiffAt I 𝓘(ℝ, F₂) (↑n)
          (fun q => (e₂ ⟨q, Ψ (⇑(σ' i)) q⟩).2) p₀.proj :=
        (contMDiffAt_section p₀.proj).mp (hΨ_smooth (σ' i)).contMDiffAt
      exact h_sect.comp _ (contMDiff_proj E₁).contMDiffAt
  -- ===== Package everything =====
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩

end VBC

end MapSection
