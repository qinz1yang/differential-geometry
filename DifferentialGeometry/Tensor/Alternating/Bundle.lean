/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle

/-!
# The vector bundle of continuous alternating maps

We define the (topological) vector bundle of continuous alternating maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, and normed spaces `F₁` and `F₂`, we define
`⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯` (notation for `Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂ x`) to be
a type synonym for `fun x ↦ ⋀^ι⟮𝕜; E₁ x; E₂ x⟯`, the sigma-type of continuous alternating maps
fibrewise from `E₁ x` to `E₂ x`. If the `E₁` and `E₂` are vector bundles with model fibers `F₁` and
`F₂`, then this will be a vector bundle with model fiber `F₁ [⋀^ι]→L[𝕜] F₂`.

The topology is constructed from the trivializations for `E₁` and `E₂` and the norm-topology on the
model fiber `F₁ [⋀^ι]→L[𝕜] F₂` using the `vector_prebundle` construction.  This
is a bit awkward because it introduces a spurious (?) dependence on the normed space structure of
the model fiber.

Similar constructions should be possible (but are yet to be formalized) for bundles of continuous
symmetric maps, multilinear maps in general, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `Bundle.continuousAlternatingMap.vectorBundle`: continuous alternating maps between
  vector bundles form a vector bundle.  (FIXME Notation `⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯`.)

## Implementation notes

The development of the alternating bundle here is unsatisfactory because it is linear rather than
semilinear, so e.g. the bundle of alternating conjugate-linear maps, needed for Dolbeault
cohomology, is not constructed.

The wider development of linear-algebraic constructions on vector bundles (the hom-bundle, the
alternating-maps bundle, the direct-sum bundle, possibly in the future the bundles of multilinear
and symmetric maps) is also unsatisfactory, in that it proceeds construction by construction rather
than according to some generalization which works for all of them. But it is not clear what a
suitable generalization would be which also covers the semilinear case, as well as other important
cases such as fractional powers of line bundles (needed for the density bundle).
-/

noncomputable section

open Bundle Set ContinuousAlternatingMap

section defs
variable (𝕜 : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] (ι : Type*) [Fintype ι]
variable {B : Type*}

set_option linter.unusedVariables false in
/-- The bundle of continuous `ι`-slot alternating maps between the topological vector bundles `E₁`
and `E₂`. At each point `x : B`, the fiber is `(E₁ x) [⋀^ι]→L[𝕜] (E₂ x)`.
We intentionally include `F₁` and `F₂` as (phantom) arguments so that typeclass instances on
this type can refer to them. The notation `⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯` is introduced below for the
partial application (without the basepoint `x`). -/
protected def Bundle.continuousAlternatingMap (F₁ : Type*) (E₁ : B → Type*)
    [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)] [Π x, TopologicalSpace (E₁ x)]
    (F₂ : Type*) (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
    [Π x, TopologicalSpace (E₂ x)] (x : B) : Type _ :=
  (E₁ x) [⋀^ι]→L[𝕜] (E₂ x)
-- deriving Inhabited FIXME

-- FIXME, notation more consistent with `F₁ [⋀^ι]→L[𝕜] F₂`?
notation3 "⋀^" ι "⟮" 𝕜 "; " F₁ ", " E₁ "; " F₂ ", " E₂ "⟯" =>
  Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂

variable (F₁ : Type*) (E₁ : B → Type*) [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)]
variable [Π x, TopologicalSpace (E₁ x)]
variable (F₂ : Type*) (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
variable [Π x, TopologicalSpace (E₂ x)]
variable [Π x, ContinuousAdd (E₂ x)]

instance (x : B) : AddCommMonoid (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) := by

  dsimp [Bundle.continuousAlternatingMap]
  infer_instance

variable [∀ x, ContinuousSMul 𝕜 (E₂ x)]

instance (x : B) : Module 𝕜 (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) :=
  inferInstanceAs (Module 𝕜 ((E₁ x) [⋀^ι]→L[𝕜] (E₂ x)))

end defs

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (ι : Type*) [Fintype ι]
variable {B : Type*} [TopologicalSpace B]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (E₁ : B → Type*) [Π x, AddCommMonoid (E₁ x)] [Π x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  (E₂ : B → Type*) [Π x, AddCommMonoid (E₂ x)] [Π x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {F₁ E₁ F₂ E₂}
variable (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Pretrivialization

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuousAlternatingMapCoordChange σ e₁ e₁' e₂ e₂'` is the coordinate
change function between the two induced (pre)trivializations
`Pretrivialization.continuousAlternatingMap σ e₁ e₂` and
`Pretrivialization.continuousAlternatingMap σ e₁' e₂'` of `Bundle.ContinuousAlternatingMap`. -/
def continuousAlternatingMapCoordChange
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
  ((e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) :
    (F₁ [⋀^ι]→L[𝕜] F₂) ≃L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

/-- The coordinate change function between two pretrivializations of the alternating-maps bundle
is continuous on the intersection of their base sets. -/
theorem continuousOn_continuousAlternatingMapCoordChange
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
  ContinuousOn (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
    ((e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  let f₁ (b : B) : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
    := ContinuousAlternatingMap.compContinuousLinearMapCLM (e₁'.coordChangeL 𝕜 e₁ b)
  let f₂ (b : B) : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
    := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι (e₂.coordChangeL 𝕜 e₂' b)
  have h₁ : ContinuousOn f₁ (e₁.baseSet ∩ e₁'.baseSet) := by
    let l : B → (F₁ →L[𝕜] F₁) := fun b ↦ (e₁'.coordChangeL 𝕜 e₁ b)
    have : f₁ = ContinuousAlternatingMap.compContinuousLinearMapCLM ∘ l := rfl
    rw [this]
    apply Continuous.comp_continuousOn
    · exact ContinuousLinearMap.compContinuousAlternatingMapCLM_cont (𝕜 := 𝕜) (ι := ι)
    · dsimp [l]
      rw [inter_comm]
      exact continuousOn_coordChange 𝕜 e₁' e₁
  have h₂ : ContinuousOn f₂ (e₂.baseSet ∩ e₂'.baseSet) := by
    let l : B → (F₂ →L[𝕜] F₂) := fun b ↦ (e₂.coordChangeL 𝕜 e₂' b)
    have : f₂ = (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι) ∘ l := rfl
    rw [this]
    apply Continuous.comp_continuousOn
    · exact (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι).cont
    · dsimp [l]
      exact continuousOn_coordChange 𝕜 e₂ e₂'
  have hf : continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' = fun b ↦ (f₂ b).comp (f₁ b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, continuousAlternatingMapCoordChange,
      ContinuousLinearEquiv.continuousAlternatingMapCongr]
    dsimp [f₁, f₂, compContinuousLinearMapCLM, ContinuousLinearMap.compContinuousAlternatingMap,
      compContinuousLinearMap]
  rw [hf]
  apply ContinuousOn.clm_comp
  · apply ContinuousOn.mono
    · exact h₂
    · intro a ha
      exact ⟨ha.1.2, ha.2.2⟩
  · apply ContinuousOn.mono
    · exact h₁
    · intro a ha
      exact ⟨ha.1.1, ha.2.1⟩

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂` is the induced pretrivialization for the
continuous `ι`-slot alternating maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous alternating maps is equipped with the right
topological vector bundle structure. -/
def continuousAlternatingMap : Pretrivialization (F₁ [⋀^ι]→L[𝕜] F₂)
    (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) where
  toFun p := ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩
  invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := (Bundle.TotalSpace.proj) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ ↦ by
    rw [TotalSpace.mk_inj]
    dsimp [Bundle.continuousAlternatingMap]
    ext v
    refine (e₂.symmₗ_linearMapAt h₂ _).trans ?_
    dsimp
    congr
    ext i
    exact e₁.symmₗ_linearMapAt h₁ _
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
    ext v
    · dsimp
    refine (e₂.linearMapAt_symmₗ h₂ _).trans ?_
    dsimp
    congr
    ext i
    exact e₁.linearMapAt_symmₗ h₁ _
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The pretrivialization `Pretrivialization.continuousAlternatingMap` is fiberwise linear:
it acts on each fiber by pre- and post-composing with the linear maps given by the trivializations
`e₁` and `e₂`, which is a linear operation. -/
instance continuousAlternatingMap.isLinear
    [Π x, ContinuousAdd (E₂ x)] [Π x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
  { map_add := fun L L' ↦ by
      ext v
      show (e₂.continuousLinearMapAt 𝕜 x)
        (((L + L').compContinuousLinearMap (e₁.symmL 𝕜 x)) v) =
        (e₂.continuousLinearMapAt 𝕜 x) ((L.compContinuousLinearMap (e₁.symmL 𝕜 x)) v) +
        (e₂.continuousLinearMapAt 𝕜 x) ((L'.compContinuousLinearMap (e₁.symmL 𝕜 x)) v)
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, ← map_add]
      congr 1
    map_smul := fun c L ↦ by
      ext v
      show (e₂.continuousLinearMapAt 𝕜 x)
        (((c • L).compContinuousLinearMap (e₁.symmL 𝕜 x)) v) =
        c • (e₂.continuousLinearMapAt 𝕜 x) ((L.compContinuousLinearMap (e₁.symmL 𝕜 x)) v)
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, ← map_smul]
      congr 1 }

omit [Fintype ι] in
theorem continuousAlternatingMap_apply (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯))
  : (continuousAlternatingMap 𝕜 ι e₁ e₂) p =
    ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl

omit [Fintype ι] in
theorem continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
    ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl

omit [Fintype ι] in
@[simp] theorem baseSet_continuousAlternatingMap :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

variable [Π x, ContinuousAdd (E₂ x)]

omit [Fintype ι] in
/-- The inverse of the pretrivialization, applied at a point `b` in both base sets.
This is the user-friendly form of `continuousAlternatingMap_symm_apply`, taking an explicit
membership proof `hb` rather than working on the total space. -/
theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L =
    (e₂.symmL 𝕜 b).compContinuousAlternatingMap
    (L.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 b) := by
  rw [Bundle.Pretrivialization.symm_apply]
  · rfl
  exact hb

/-- The coordinate change function agrees with applying the pretrivialization `e₁' e₂'` to the
image of `b, L` under the inverse pretrivialization `e₁ e₂`. This shows that
`continuousAlternatingMapCoordChange` encodes the transition between the two local frames. -/
theorem continuousAlternatingMapCoordChange_apply (b : B)
  (hb : b ∈ (e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ [⋀^ι]→L[𝕜] F₂) :
  continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
  (continuousAlternatingMap 𝕜 ι e₁' e₂'
    (TotalSpace.mk b ((continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L))).2 := by
  ext v
  have H₁ : (e₁'.coordChangeL 𝕜 e₁ b) ∘ v = (e₁.linearMapAt 𝕜 b) ∘ (e₁'.symm b) ∘ v := by
    ext i
    dsimp
    rw [e₁'.coordChangeL_apply e₁ ⟨hb.2.1, hb.1.1⟩, e₁.coe_linearMapAt_of_mem hb.1.1]
  have H₂ (v : F₂) : (e₂.coordChangeL 𝕜 e₂' b) v = ((e₂'.linearMapAt 𝕜 b) ∘ (e₂.symm b)) v := by
    dsimp
    rw [e₂.coordChangeL_apply e₂' ⟨hb.1.2, hb.2.2⟩, e₂'.coe_linearMapAt_of_mem hb.2.2]
  have H₂' : Trivialization.coordChangeL 𝕜 e₂ e₂' b = (e₂'.linearMapAt 𝕜 b) ∘ (e₂.symm b) := by
    ext v
    exact H₂ v
  simp [Pretrivialization.continuousAlternatingMap_apply, continuousAlternatingMapCoordChange,
    Pretrivialization.continuousAlternatingMap_symm_apply' _ _ _ _ hb.1, H₁, H₂']

end Pretrivialization

open Pretrivialization
variable (F₁ E₁ F₂ E₂)
variable [Π x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable [Π x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Topology on the continuous `ι`-slot alternating maps between the respective fibers at a point of
two "normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `F₁`, `F₂` respectively. The topology we put on the continuous `ι`-slot
alternating maps is the topology coming from the norm on alternating maps from `F₁` to `F₂`. -/
instance (x : B) : TopologicalSpace (⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x) :=
  TopologicalSpace.induced
    ((Pretrivialization.continuousAlternatingMap 𝕜 ι
      (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)) ∘ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) x)
    inferInstance

variable [Π x, ContinuousAdd (E₂ x)] [Π x, ContinuousSMul 𝕜 (E₂ x)]

/-- The continuous `ι`-slot alternating maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.Bundle.continuousAlternatingMap.vectorPrebundle :
    VectorPrebundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ where
  pretrivializationAtlas :=
    {e |  ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
      e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousAlternatingMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousAlternatingMapCoordChange_apply 𝕜 ι e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing x := ⟨rfl⟩

/-- Topology on the total space of the continuous `ι`-slot alternating maps between two "normable"
vector bundles over the same base. -/
instance Bundle.continuousAlternatingMap.topologicalSpace_totalSpace :
    TopologicalSpace (TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `ι`-slot alternating maps between two vector bundles form a fiber bundle. -/
instance _root_.Bundle.continuousAlternatingMap.fiberBundle :
    FiberBundle (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous `ι`-slot alternating maps between two vector bundles form a vector bundle. -/
instance _root_.Bundle.continuousAlternatingMap.vectorBundle :
    VectorBundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ :=
  (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `ι`-slot alternating maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
def Bundle.Trivialization.continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance _root_.Bundle.continuousAlternatingMap.memTrivializationAtlas :
    MemTrivializationAtlas (e₁.continuousAlternatingMap 𝕜 ι e₂ :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯)) where
  out := ⟨_, ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩, rfl⟩

@[simp] theorem Bundle.Trivialization.baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem Bundle.Trivialization.continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
    ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
      p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x₀).source =
    π (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ ⁻¹'
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯ x₀).target =
    ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

end

section smooth

open scoped Bundle Manifold

open Bundle Pretrivialization

variable {𝕜 ι B F₁ F₂ M : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M] {n : ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

variable {F₃ F₄ : Type*}
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]

local notation "AE₁E₂" => Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

omit [∀ (x : B), IsTopologicalAddGroup (E₂ x)] [∀ (x : B), ContinuousSMul 𝕜 (E₂ x)] in
/-- The coordinate change function for the alternating-maps bundle is smooth (of class `C^∞`) on
the intersection of the base sets of the two trivializations, whenever the input bundles
`E₁`, `E₂` are smooth vector bundles. -/
theorem contMDiffOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle ⊤ F₁ E₁ IB] [ContMDiffVectorBundle ⊤ F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) ⊤
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := ⊤)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := ⊤)
  have h₁_prod_h₂ := (h₁.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (s := e₁'.baseSet ∩ e₁.baseSet) (by mfld_set_tac)).prodMk
      (h₂.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      (s := e₂.baseSet ∩ e₂'.baseSet) (by mfld_set_tac))
  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι q.2)
  have hs : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
      (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ s := by
    let t (p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
        ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι p.2
    have ht : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) ⊤ t := by
          refine ContMDiff.clm_apply ?hg ?hf
          · exact contMDiff_const
          · exact contMDiff_snd
    exact ContMDiff.prodMk contMDiff_fst ht
  exact ((contMDiff_snd.clm_comp ((ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff
    (𝕜 := 𝕜) (ι := ι) (F₁ := F₁) (F₂ := F₂)).comp contMDiff_fst)).comp hs).comp_contMDiffOn
    (s := (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))) h₁_prod_h₂

variable [ContMDiffVectorBundle ⊤ F₁ E₁ IB] [ContMDiffVectorBundle ⊤ F₂ E₂ IB]

/-- The vector prebundle of continuous alternating maps is smooth: its coordinate change functions
are `C^∞`. This is the key step before promoting the prebundle to a smooth vector bundle. -/
instance Bundle.continuousAlternatingMap.vectorPrebundle.isSmooth :
   (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB ⊤ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange IB, ?_⟩
    · rintro b hb v
      apply continuousAlternatingMapCoordChange_apply
      exact hb

/-- If `E₁` and `E₂` are smooth vector bundles, then the bundle of continuous `ι`-slot alternating
maps from `E₁` to `E₂` is also a smooth vector bundle. -/
instance SmoothVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle ⊤ (F₁ [⋀^ι]→L[𝕜] F₂) (Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂) IB
  := (Bundle.continuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

-- Notation for total space of continuous alternating bundle
notation "𝒜⟮" 𝕜 "," ι ";"  F₁ "," E₁ ";"  F₂ "," E₂ "⟯" =>
  Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

end smooth

noncomputable section charted
variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {m : ℕ}

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

/-- The total space of the bundle of real-valued alternating `m`-forms on a manifold `M` is a
charted space. The model space is `ModelProd HM (EM [⋀^Fin m]→L[ℝ] ℝ)`, where `HM` and `EM`
are the chart model spaces for the base manifold `M`. -/
instance ChartedSpace.alternatingBundle : ChartedSpace (ModelProd HM (EM [⋀^Fin m]→L[ℝ] ℝ))
    𝒜⟮ℝ,Fin m;EM,TangentSpace IM;ℝ,Bundle.Trivial M ℝ⟯ := inferInstance

end charted
