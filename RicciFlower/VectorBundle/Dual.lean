/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions
/-!
# The dual bundle of a vector bundle

This file defines `Bundle.dual 𝕜 E`, the dual bundle of a vector bundle `E : B → Type*`,
whose fiber at `x : B` is the continuous dual `E x →L[𝕜] 𝕜`.

The construction is realized as a special case of the hom bundle (`Bundle.ContinuousLinearMap`)
where the codomain is the trivial `𝕜`-bundle `Bundle.Trivial B 𝕜`. This means all bundle
instances — `TopologicalSpace`, `FiberBundle`, `VectorBundle`, and `ContMDiffVectorBundle` —
are inherited automatically from the hom bundle and the trivial bundle's smooth structures
in Mathlib.

## Main Definitions

* `Bundle.dual 𝕜 E` : the dual bundle, with model fiber `F →L[𝕜] 𝕜`.

## Tags

dual bundle, vector bundle, cotangent
-/

noncomputable section

open Bundle

namespace Bundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*}
variable (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)]

/-- The dual bundle of a vector bundle `E`: at each point `x : B`, the fiber is the
continuous dual `E x →L[𝕜] 𝕜`. Realized as a special case of the hom bundle with the
trivial `𝕜`-bundle as the codomain. -/
abbrev dual : B → Type _ :=
  fun x => E x →L[𝕜] Bundle.Trivial B 𝕜 x

end Bundle

/-! ## Sanity check: the dual bundle inherits all the standard instances -/

section InstanceCheck

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

example (x : B) : Bundle.dual 𝕜 E x = (E x →L[𝕜] 𝕜) := rfl

-- The hom bundle topology applies (via the Trivial 𝕜-bundle as codomain).
example : TopologicalSpace (TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)) := inferInstance

example : FiberBundle (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

example : VectorBundle 𝕜 (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

end InstanceCheck

/-! ## Smooth structure -/

section Smooth

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

-- The smooth vector bundle instance for the dual bundle is inherited from the hom-bundle's
-- smoothness instance combined with the trivial bundle being a smooth vector bundle.
example : ContMDiffVectorBundle n (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) IB := inferInstance

end Smooth

end
