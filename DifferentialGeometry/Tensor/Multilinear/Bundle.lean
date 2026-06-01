/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Comp
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle

/-!
# The vector bundle of continuous multilinear maps

We define the (topological) vector bundle of continuous multilinear maps from a vector bundle
to the scalar field.

Given a bundle `E : B → Type*` with model fiber `F`, and `s : ℕ`, we define
`Bundle.continuousMultilinearMap 𝕜 s F E x` to be a type synonym for
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜`, the continuous `s`-multilinear maps
on the fiber `E x` valued in `𝕜`. If `E` is a vector bundle with model fiber `F`, then this
is a vector bundle with model fiber `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜`.

The topology is constructed from the trivializations for `E` and the norm-topology on the
model fiber using the `VectorPrebundle` construction, following the pattern of
`Bundle.continuousAlternatingMap`.

## Main Definitions

* `Bundle.continuousMultilinearMap.vectorBundle`: continuous multilinear maps on a
  vector bundle form a vector bundle.

## Tags

multilinear map, vector bundle, tensor bundle
-/

noncomputable section

open Bundle Set

/-! ## Type definition and algebraic instances -/

section defs
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ)
variable {B : Type*}

set_option linter.unusedVariables false in
/-- The bundle of continuous `s`-slot multilinear maps from a topological vector bundle `E`
to the scalar field `𝕜`. At each point `x : B`, the fiber is
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜`.
We intentionally include `F` as a (phantom) argument so that typeclass instances on
this type can refer to it.

Marked `@[reducible]` so the type is transparent during instance synthesis. This
collapses the topology diamond between the bundle topology
(`instTopologicalSpaceContinuousMultilinearMap`) and the standard `ContinuousMultilinearMap`
topology, enabling section-level lifts of fiberwise iso constructions. -/
@[reducible]
protected def Bundle.continuousMultilinearMap (F : Type*) (E : B → Type*)
    [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)] [Π x, TopologicalSpace (E x)]
    (x : B) : Type _ :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜

variable (F : Type*) (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
variable [Π x, TopologicalSpace (E x)]

instance Bundle.continuousMultilinearMap.instAddCommMonoid (x : B) :
    AddCommMonoid (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

instance Bundle.continuousMultilinearMap.instModule (x : B) :
    Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (Module 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))

end defs

/-! ## Pretrivialization -/

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ)
variable {B : Type*} [TopologicalSpace B]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]

/-- Abbreviation for the model fiber of the multilinear bundle. -/
local notation "MLF" => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable {F E}
variable (e e' : Trivialization F (π F E))

namespace Pretrivialization

variable [e.IsLinear 𝕜] [e'.IsLinear 𝕜]

/-- The coordinate change function between two pretrivializations of the multilinear-maps bundle.
Given trivializations `e` and `e'` of `E`, the coordinate change precomposes each argument
with `e'.coordChangeL 𝕜 e b`. -/
def continuousMultilinearMapCoordChange (b : B) : MLF →L[𝕜] MLF :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin s => e'.coordChangeL 𝕜 e b)

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- The coordinate change function between two pretrivializations of the multilinear-maps bundle
is continuous on the intersection of their base sets. -/
theorem continuousOn_continuousMultilinearMapCoordChange
    [VectorBundle 𝕜 F E] [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (continuousMultilinearMapCoordChange 𝕜 s e e')
      (e.baseSet ∩ e'.baseSet) := by
  have hg : ContinuousOn (fun b => (e'.coordChangeL 𝕜 e b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) := by
    rw [inter_comm]
    exact continuousOn_coordChange 𝕜 e' e
  have hcomp : Continuous (fun (L : F →L[𝕜] F) =>
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin s => L) : MLF →L[𝕜] MLF)) := by
    have h_bound := (ContinuousMultilinearMap.compContinuousLinearMapMultilinear 𝕜
      (fun _ : Fin s => F) (fun _ : Fin s => F) 𝕜 :
      MultilinearMap 𝕜 (fun _ : Fin s => F →L[𝕜] F)
        (MLF →L[𝕜] MLF)).continuous_of_bound 1
      (fun f => by simp only [one_mul]; exact
        ContinuousMultilinearMap.norm_compContinuousLinearMapL_le (G := 𝕜) f)
    exact h_bound.comp (continuous_pi fun _ => continuous_id)
  exact hcomp.comp_continuousOn hg

/-- Given a trivialization `e` for a vector bundle `E` over a base `B`,
`Pretrivialization.continuousMultilinearMap 𝕜 s e` is the induced pretrivialization for the
continuous `s`-multilinear maps from `E` to `𝕜`. The pretrivialization acts by precomposing
each argument with the inverse of the trivialization. -/
def continuousMultilinearMap : Pretrivialization MLF
    (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) where
  toFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩
  invFun p := ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 p.1)⟩
  source := (Bundle.TotalSpace.proj) ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := fun ⟨x, L⟩ h ↦ by
    rw [TotalSpace.mk_inj]
    dsimp [Bundle.continuousMultilinearMap]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact e.symmₗ_linearMapAt h (v i)
  right_inv' := fun ⟨x, f⟩ ⟨hx, _⟩ ↦ by
    ext v
    · rfl
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact e.linearMapAt_symmₗ hx (v i)
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The pretrivialization is fiberwise linear. -/
instance continuousMultilinearMap.isLinear :
    (Pretrivialization.continuousMultilinearMap 𝕜 s e).IsLinear 𝕜 where
  linear _ _ :=
  { map_add := fun _ _ ↦ rfl
    map_smul := fun _ _ ↦ by ext; rfl }

theorem continuousMultilinearMap_apply
    (p : TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :
    (continuousMultilinearMap 𝕜 s e) p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩ :=
  rfl

theorem continuousMultilinearMap_symm_apply (p : B × MLF) :
    (continuousMultilinearMap 𝕜 s e).toPartialEquiv.symm p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 p.1)⟩ :=
  rfl

@[simp] theorem baseSet_continuousMultilinearMap :
    (Pretrivialization.continuousMultilinearMap 𝕜 s e).baseSet = e.baseSet :=
  rfl

theorem continuousMultilinearMap_symm_apply' {b : B} (hb : b ∈ e.baseSet) (L : MLF) :
    (continuousMultilinearMap 𝕜 s e).symm b L =
    L.compContinuousLinearMap (fun _ => e.continuousLinearMapAt 𝕜 b) := by
  rw [Bundle.Pretrivialization.symm_apply]
  · rfl
  exact hb

/-- The coordinate change function agrees with applying pretrivialization `e'` to the
image of `(b, L)` under the inverse pretrivialization `e`. -/
theorem continuousMultilinearMapCoordChange_apply (b : B)
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (L : MLF) :
    continuousMultilinearMapCoordChange 𝕜 s e e' b L =
    (continuousMultilinearMap 𝕜 s e'
      (TotalSpace.mk b ((continuousMultilinearMap 𝕜 s e).symm b L))).2 := by
  ext v
  simp only [continuousMultilinearMapCoordChange,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    continuousMultilinearMap_apply, continuousMultilinearMap_symm_apply' _ _ _ hb.1]
  congr 1; funext i
  erw [Trivialization.coordChangeL_apply (R := 𝕜) e' e ⟨hb.2, hb.1⟩]
  exact (congr_fun (e.coe_linearMapAt_of_mem (R := 𝕜) hb.1) _).symm

end Pretrivialization

/-! ## Vector prebundle and bundle instances -/

open Pretrivialization
variable (F E)
variable [Π x : B, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Topology on the continuous `s`-multilinear maps at each point, induced by the trivialization. -/
instance (x : B) : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TopologicalSpace.induced
    ((Pretrivialization.continuousMultilinearMap 𝕜 s
      (trivializationAt F E x)) ∘ TotalSpace.mk' MLF x)
    inferInstance

/-- The continuous `s`-multilinear maps from a topological vector bundle to `𝕜` form a
`VectorPrebundle`. -/
def _root_.Bundle.continuousMultilinearMap.vectorPrebundle :
    VectorPrebundle 𝕜 MLF (Bundle.continuousMultilinearMap 𝕜 s F E) where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = Pretrivialization.continuousMultilinearMap 𝕜 s e}
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    haveI := he
    exact Pretrivialization.continuousMultilinearMap.isLinear 𝕜 s e
  pretrivializationAt x := Pretrivialization.continuousMultilinearMap 𝕜 s
    (trivializationAt F E x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F E x
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    haveI := he; haveI := he'
    exact ⟨continuousMultilinearMapCoordChange 𝕜 s e e',
      continuousOn_continuousMultilinearMapCoordChange 𝕜 s e e',
      continuousMultilinearMapCoordChange_apply 𝕜 s e e'⟩
  totalSpaceMk_isInducing x := ⟨rfl⟩

/-- Topology on the total space of the continuous `s`-multilinear maps bundle. -/
instance Bundle.continuousMultilinearMap.topologicalSpace_totalSpace :
    TopologicalSpace (TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).totalSpaceTopology

/-- The continuous `s`-multilinear maps from a vector bundle to `𝕜` form a fiber bundle. -/
instance _root_.Bundle.continuousMultilinearMap.fiberBundle :
    FiberBundle MLF (Bundle.continuousMultilinearMap 𝕜 s F E) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).toFiberBundle

/-- The continuous `s`-multilinear maps from a vector bundle to `𝕜` form a vector bundle. -/
instance _root_.Bundle.continuousMultilinearMap.vectorBundle :
    VectorBundle 𝕜 MLF (Bundle.continuousMultilinearMap 𝕜 s F E) :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).toVectorBundle

variable [he : MemTrivializationAtlas e] {F E}

/-- Given a trivialization `e` in the atlas for vector bundle `E`, the induced trivialization
for the continuous `s`-multilinear maps from `E` to `𝕜`. -/
def Bundle.Trivialization.continuousMultilinearMap :
    Trivialization MLF (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e, he, rfl⟩

instance _root_.Bundle.continuousMultilinearMap.memTrivializationAtlas :
    MemTrivializationAtlas (e.continuousMultilinearMap 𝕜 s :
    Trivialization MLF (π MLF (Bundle.continuousMultilinearMap 𝕜 s F E))) where
  out := ⟨_, ⟨e, inferInstance, rfl⟩, rfl⟩

@[simp] theorem Bundle.Trivialization.baseSet_continuousMultilinearMap :
    (e.continuousMultilinearMap 𝕜 s).baseSet = e.baseSet :=
  rfl

theorem Bundle.Trivialization.continuousMultilinearMap_apply
    (p : TotalSpace MLF (Bundle.continuousMultilinearMap 𝕜 s F E)) :
    e.continuousMultilinearMap 𝕜 s p =
    ⟨p.1, p.2.compContinuousLinearMap (fun _ => e.symmL 𝕜 p.1)⟩ :=
  rfl

end

/-! ## Smoothness -/

section smooth

open scoped Bundle Manifold

open Bundle Set Pretrivialization

variable {𝕜 B F : Type*} {E : B → Type*} (s : ℕ)
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {e e' : Trivialization F (π F E)}
  [FiniteDimensional 𝕜 F]
  (n : WithTop ℕ∞)

local notation "MLF" => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

set_option linter.unusedSectionVars false in
/-- The coordinate change function for the multilinear-maps bundle is `C^n`. -/
theorem contMDiffOn_continuousMultilinearMapCoordChange
    [ContMDiffVectorBundle n F E IB]
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(𝕜, MLF →L[𝕜] MLF) n
      (continuousMultilinearMapCoordChange 𝕜 s e e')
      (e.baseSet ∩ e'.baseSet) := by
  have h_coord : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b => (e'.coordChangeL 𝕜 e b : F →L[𝕜] F))
      (e'.baseSet ∩ e.baseSet) :=
    contMDiffOn_coordChangeL (IB := IB) e' e
  have h_diag : ContMDiff 𝓘(𝕜, F →L[𝕜] F) 𝓘(𝕜, MLF →L[𝕜] MLF) n
      (fun L : F →L[𝕜] F =>
        (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin s => L) :
          MLF →L[𝕜] MLF)) := by
    rw [contMDiff_iff_contDiff]
    exact ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff.of_le le_top
  exact h_diag.comp_contMDiffOn (h_coord.mono (by rw [Set.inter_comm]))

variable [ContMDiffVectorBundle n F E IB]

/-- The vector prebundle of continuous multilinear maps is `C^n`. -/
instance Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth :
    (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    haveI := he; haveI := he'
    refine ⟨continuousMultilinearMapCoordChange 𝕜 s e e',
      contMDiffOn_continuousMultilinearMapCoordChange s IB n, ?_⟩
    rintro b hb v
    exact continuousMultilinearMapCoordChange_apply 𝕜 s e e' b hb v

/-- If `E` is a `C^n` vector bundle, then the bundle of continuous `s`-multilinear maps
from `E` to `𝕜` is also a `C^n` vector bundle. -/
instance SmoothVectorBundle.continuousMultilinearMap :
    ContMDiffVectorBundle n MLF (Bundle.continuousMultilinearMap 𝕜 s F E) IB :=
  (Bundle.continuousMultilinearMap.vectorPrebundle 𝕜 s F E).contMDiffVectorBundle IB

end smooth
