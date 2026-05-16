/-
Authors: Jack McCarthy
-/
import RicciFlower.Tensor.Mixed.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom
/-!
# Mixed multilinear bundle instances

This file establishes the topological, fiber bundle, vector bundle, and smooth vector bundle
instances for the mixed multilinear bundle, whose fiber at `x : B` is
`Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x`.

The bundle is constructed as the hom bundle between the `r`-multilinear and `s`-multilinear
bundles, using `Bundle.ContinuousLinearMap`.

## Main Definitions

* `Bundle.continuousMultilinearMap.mixedTopology`: topology on the total space.
* `Bundle.continuousMultilinearMap.mixedFiberBundle`: fiber bundle instance.
* `Bundle.continuousMultilinearMap.mixedVectorBundle`: vector bundle instance.
* `Bundle.continuousMultilinearMap.mixedSmoothVectorBundle`: smooth vector bundle instance.

## Tags

multilinear map, mixed tensor, vector bundle, hom bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r s : ℕ}

/-!
## Bundle instances

The mixed multilinear bundle is the hom bundle from the `r`-multilinear bundle
to the `s`-multilinear bundle, using `Bundle.ContinuousLinearMap`.
-/

/-- Topology on the total space of the mixed multilinear bundle, induced by viewing it
as the hom bundle between two multilinear bundles. -/
noncomputable instance mixedTopology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

/-- The mixed multilinear bundle is a fiber bundle. -/
noncomputable instance mixedFiberBundle (r s : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      (mixedTopology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

/-- The mixed multilinear bundle is a vector bundle. -/
noncomputable instance mixedVectorBundle (r s : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (mixedTopology r s) _
      (mixedFiberBundle r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

/-!
## Smooth bundle instance
-/

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

/-- The mixed multilinear bundle is a `C^n` vector bundle. -/
noncomputable instance mixedSmoothVectorBundle (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (mixedTopology r s) _
      (mixedFiberBundle r s)
      (mixedVectorBundle r s) :=
  ContMDiffVectorBundle.continuousLinearMap

end smooth

end Bundle.continuousMultilinearMap

end
